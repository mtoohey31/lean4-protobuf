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
def readUvarintCore [Stream ρ UInt8] (xs : ρ) (shift acc : Nat)
    (first : Bool := false) : Except VarintError (Nat × ρ) :=
  match Stream.next? xs with
  | some (x, xs') =>
    if x &&& 0x80 = 0 then
      ok ((x &&& 0b1111111).toNat <<< shift + acc, xs')
    else
      readUvarintCore xs' (shift + 7) (x.toNat <<< shift + acc)
  | none => error $ if first then VarintError.end else VarintError.unexpectedEnd

/--
Read an unsigned varint from `xs`.
-/
private
def readUvarint [Stream ρ UInt8] (xs : ρ) : Except VarintError (Nat × ρ) :=
  readUvarintCore xs 0 0 (first := true)

/--
Read an unsigned varint from `xs`, or panic if one cannot be read.
-/
def readUvarint! [Stream ρ UInt8] [Inhabited ρ] (xs : ρ) : Nat × ρ :=
  match readUvarint xs with
  | ok res => res
  | error VarintError.end => panic! "stream was empty"
  | error VarintError.unexpectedEnd => panic! "stream contained invalid uvarint"

private
partial
def readVarintCore [Stream ρ UInt8] (xs : ρ) (shift : Nat) (acc : Int)
    (negative : Bool) : Except VarintError (Int × ρ) :=
  match Stream.next? xs with
  | some (x, xs') =>
    let x' := if negative then
        (Int.ofNat ((x &&& 0b1111111).toNat <<< shift) - (0x80 <<< shift))
      else
        Int.ofNat ((x &&& 0b1111111).toNat <<< shift)
    if x &&& 0x80 = 0 then
      ok (x' + acc, xs')
    else
      readVarintCore xs' (shift + 7) (x' + acc) negative
  | none => error VarintError.unexpectedEnd

/--
Read a varint from `xs`.
-/
def readVarint [Stream ρ UInt8] (xs : ρ) : Except VarintError (Int × ρ) :=
  match Stream.next? xs with
  | some (x, xs') =>
    let negative := x &&& 1 = 1
    let x' := if negative then
        (Int.ofNat (x >>> 1 &&& 0b111111).toNat - 0x40)
      else
        Int.ofNat (x >>> 1 &&& 0b111111).toNat
    if x &&& 0x80 = 0 then
      ok (x', xs')
    else
      readVarintCore xs' 6 x' negative
  | none => error VarintError.end

/--
Read a varint from `xs`, or panic if one cannot be read.
-/
def readVarint! [Stream ρ UInt8] [Inhabited ρ] (xs : ρ) : Int × ρ :=
  match readVarint xs with
  | ok res => res
  | error VarintError.end => panic! "stream was empty"
  | error VarintError.unexpectedEnd => panic! "stream contained invalid varint"

-- TODO: readUvarint{8,16,32,64}!?

end Protobuf.Varint
