import Init.Data.UInt.Basic
import Init.Data.Option.Basic
import Lean.Elab.Do

namespace Protobuf.Varint

open Except

inductive VarintError where
  | end
  | unexpectedEnd
  deriving Inhabited, Repr

private
partial
def decUvarintCore [Stream ρ UInt8] (xs : ρ) (shift acc : Nat)
    (first : Bool := false) : Except VarintError (Nat × ρ) :=
  match Stream.next? xs with
  | some (x, xs') =>
    if x &&& 0x80 = 0 then
      ok ((x &&& 0b1111111).toNat <<< shift + acc, xs')
    else
      decUvarintCore xs' (shift + 7) ((x &&& 0b1111111).toNat <<< shift + acc)
  | none => error $ if first then VarintError.end else VarintError.unexpectedEnd

/--
Decode an unsigned varint from `xs`.
-/
def decUvarint [Stream ρ UInt8] (xs : ρ) : Except VarintError (Nat × ρ) :=
  decUvarintCore xs 0 0 (first := true)

/--
Decode an unsigned varint from `xs`, or panic if one cannot be decoded.
-/
def decUvarint! [Stream ρ UInt8] [Inhabited ρ] (xs : ρ) : Nat × ρ :=
  match decUvarint xs with
  | ok res => res
  | error VarintError.end => panic! "stream was empty"
  | error VarintError.unexpectedEnd => panic! "stream contained invalid uvarint"

private
partial
def decVarintCore [Stream ρ UInt8] (xs : ρ) (shift : Nat) (acc : Int)
    (negative : Bool) : Except VarintError (Int × ρ) :=
  match Stream.next? xs with
  | some (x, xs') =>
    let x' := if negative then
        -(Int.ofNat ((x &&& 0b1111111).toNat <<< shift))
      else
        Int.ofNat ((x &&& 0b1111111).toNat <<< shift)
    if x &&& 0x80 = 0 then
      ok (x' + acc, xs')
    else
      decVarintCore xs' (shift + 7) (x' + acc) negative
  | none => error VarintError.unexpectedEnd

/--
Decode a varint from `xs`.
-/
def decVarint [Stream ρ UInt8] (xs : ρ) : Except VarintError (Int × ρ) :=
  match Stream.next? xs with
  | some (x, xs') =>
    let negative := x &&& 1 = 1
    let x' := if negative then
        -(Int.ofNat (x >>> 1 &&& 0b111111).toNat + 1)
      else
        Int.ofNat (x >>> 1 &&& 0b111111).toNat
    if x &&& 0x80 = 0 then
      ok (x', xs')
    else
      decVarintCore xs' 6 x' negative
  | none => error VarintError.end

/--
Decode a varint from `xs`, or panic if one cannot be decoded.
-/
def decVarint! [Stream ρ UInt8] [Inhabited ρ] (xs : ρ) : Int × ρ :=
  match decVarint xs with
  | ok res => res
  | error VarintError.end => panic! "stream was empty"
  | error VarintError.unexpectedEnd => panic! "stream contained invalid varint"

inductive BoundedVarintError where
  | end
  | unexpectedEnd
  | overflow
  deriving Inhabited, Repr

/-
PERF: Alternate core implementation for bounded uvarints that reports overflow
immediately when one is guaranteed.
-/

/--
Decode an unsigned varint which should fit in a `UInt32` from `xs`.
-/
def decUvarint32 [Stream ρ UInt8] (xs : ρ) :
    Except BoundedVarintError (UInt32 × ρ) :=
  match decUvarintCore xs 0 0 (first := true) with
  | error VarintError.end => error BoundedVarintError.end
  | error VarintError.unexpectedEnd => error BoundedVarintError.unexpectedEnd
  | ok (n, xs') =>
    if h : n < UInt32.size then
      ok (UInt32.ofNatCore n h, xs')
    else
      error BoundedVarintError.overflow

/--
Decode an unsigned varint which should fit in a `UInt32` from `xs`, or panic if
one cannot be decoded.
-/
def decUvarint32! [Stream ρ UInt8] [Inhabited ρ] (xs : ρ) : UInt32 × ρ :=
  match decUvarint32 xs with
  | ok res => res
  | error BoundedVarintError.end => panic! "stream was empty"
  | error BoundedVarintError.unexpectedEnd =>
    panic! "stream contained invalid uvarint"
  | error BoundedVarintError.overflow =>
    panic! "stream contained uvarint that overflowed uint32"

/--
Decode an unsigned varint which should fit in a `UInt64` from `xs`.
-/
def decUvarint64 [Stream ρ UInt8] (xs : ρ) :
    Except BoundedVarintError (UInt64 × ρ) :=
  match decUvarintCore xs 0 0 (first := true) with
  | error VarintError.end => error BoundedVarintError.end
  | error VarintError.unexpectedEnd => error BoundedVarintError.unexpectedEnd
  | ok (n, xs') =>
    if h : n < UInt64.size then
      ok (UInt64.ofNatCore n h, xs')
    else
      error BoundedVarintError.overflow

/--
Decode an unsigned varint which should fit in a `UInt64` from `xs`, or panic if
one cannot be decoded.
-/
def decUvarint64! [Stream ρ UInt8] [Inhabited ρ] (xs : ρ) : UInt64 × ρ :=
  match decUvarint64 xs with
  | ok res => res
  | error BoundedVarintError.end => panic! "stream was empty"
  | error BoundedVarintError.unexpectedEnd =>
    panic! "stream contained invalid uvarint"
  | error BoundedVarintError.overflow =>
    panic! "stream contained uvarint that overflowed uint64"

/--
Encode `n` as an unsigned varint.
-/
partial
def encUvarint (n : Nat) : List UInt8 := if n ≤ 0b1111111 then
    [UInt8.ofNat n]
  else
    UInt8.ofNat ((n &&& 0b1111111) ||| 0b10000000) :: encUvarint (n >>> 7)

/--
Encode `i` as a varint.
-/
def encVarint (i : Int) : List UInt8 :=
  if i < 0 then
    encUvarint $ (-i - 1).toNat <<< 1 ||| 1
  else
    encUvarint $ i.toNat <<< 1

end Protobuf.Varint
