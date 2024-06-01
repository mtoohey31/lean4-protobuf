import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.UInt.Basic
import Init.Data.Option.Basic
import Lean.Elab.Do
import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Div
import Protobuf.Data.SizedStream

namespace Protobuf.Varint

open Except

inductive VarintError where
  | end
  | unexpectedEnd
  deriving Inhabited, Repr

inductive BoundedVarintError where
  | end
  | unexpectedEnd
  | overflow
  deriving Inhabited, Repr

private
inductive Output (acc : Nat) where
  | unbounded
  | bounded (bound : Nat) (inBound : acc < bound) (outType : Type)
    (ofNatCore : (n : Nat) → (h : n < bound) → outType)

-- TODO: Support partial dec- variants that operate on unsized streams.

set_option linter.unusedVariables false in
private
def decUvarintCore [SizedStream ρ UInt8] (xs : ρ) (shift acc : Nat)
    (output : Output acc := Output.unbounded) (first : Bool := false) :
    let (errorType, outType) := match output with
      | Output.unbounded => (VarintError, Nat)
      | Output.bounded _ _ outType _ => (BoundedVarintError, outType)
    Except errorType (outType × ρ) :=
  match h : Stream.next? xs with
  | some (x, xs') =>
    if x &&& 0x80 = 0 then
      let out := (x &&& 0b1111111).toNat <<< shift + acc
      match output with
      | Output.unbounded => ok (out, xs')
      | Output.bounded bound inBound _ ofNatCore =>
        if h' : out ≥ bound then
          error BoundedVarintError.overflow
        else
          ok (ofNatCore out (by linarith), xs')
    else
      let acc' := (x &&& 0b1111111).toNat <<< shift + acc
      match output with
      | Output.unbounded => decUvarintCore xs' (shift + 7) acc'
      | Output.bounded bound _ outType ofNatCore =>
        if h' : acc' ≥ bound then
          error BoundedVarintError.overflow
        else
          let output' := Output.bounded bound (by linarith) outType ofNatCore
          decUvarintCore xs' (shift + 7) acc' output'
  | none => error $ match first, output with
    | true, Output.unbounded => VarintError.end
    | false, Output.unbounded => VarintError.unexpectedEnd
    | true, Output.bounded _ _ _ _ => BoundedVarintError.end
    | false, Output.bounded _ _ _ _ => BoundedVarintError.unexpectedEnd
termination_by SizedStream.size xs
decreasing_by
  all_goals simp_wf <;> apply SizedStream.size_dec xs xs' h

/--
Decode an unsigned varint from `xs`.
-/
def decUvarint [SizedStream ρ UInt8] (xs : ρ) : Except VarintError (Nat × ρ) :=
  decUvarintCore xs 0 0 (first := true)

/--
Decode an unsigned varint from `xs`, or panic if one cannot be decoded.
-/
def decUvarint! [SizedStream ρ UInt8] [Inhabited ρ] (xs : ρ) : Nat × ρ :=
  match decUvarint xs with
  | ok res => res
  | error VarintError.end => panic! "stream was empty"
  | error VarintError.unexpectedEnd => panic! "stream contained invalid uvarint"

set_option linter.unusedVariables false in
private
def decVarintCore [SizedStream ρ UInt8] (xs : ρ) (shift : Nat) (acc : Int)
    (negative : Bool) : Except VarintError (Int × ρ) :=
  match h : Stream.next? xs with
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
termination_by SizedStream.size xs
decreasing_by
  all_goals simp_wf
  apply SizedStream.size_dec xs xs' h

/--
Decode a varint from `xs`.
-/
def decVarint [SizedStream ρ UInt8] (xs : ρ) : Except VarintError (Int × ρ) :=
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
def decVarint! [SizedStream ρ UInt8] [Inhabited ρ] (xs : ρ) : Int × ρ :=
  match decVarint xs with
  | ok res => res
  | error VarintError.end => panic! "stream was empty"
  | error VarintError.unexpectedEnd => panic! "stream contained invalid varint"

private
def getOk! [Inhabited α] (s : String) : Except BoundedVarintError α → α
  | ok x => x
  | error BoundedVarintError.end => panic! "stream was empty"
  | error BoundedVarintError.unexpectedEnd =>
    panic! "stream contained invalid uvarint"
  | error BoundedVarintError.overflow =>
    panic! "stream contained uvarint that overflowed " ++ s

/--
Decode an unsigned varint which should fit in a `UInt8` from `xs`.
-/
def decUvarint8 [SizedStream ρ UInt8] (xs : ρ) :
    Except BoundedVarintError (UInt8 × ρ) :=
  let output := Output.bounded UInt8.size (by decide) UInt8 UInt8.ofNatCore
  decUvarintCore xs 0 0 output

/--
Decode an unsigned varint which should fit in a `UInt8` from `xs`, or panic if
one cannot be decoded.
-/
def decUvarint8! [SizedStream ρ UInt8] [Inhabited ρ] (xs : ρ) : UInt8 × ρ :=
  getOk! "UInt8" $ decUvarint8 xs

/--
Decode an unsigned varint which should fit in a `UInt16` from `xs`.
-/
def decUvarint16 [SizedStream ρ UInt8] (xs : ρ) :
    Except BoundedVarintError (UInt16 × ρ) :=
  let output := Output.bounded UInt16.size (by decide) UInt16 UInt16.ofNatCore
  decUvarintCore xs 0 0 output

/--
Decode an unsigned varint which should fit in a `UInt16` from `xs`, or panic if
one cannot be decoded.
-/
def decUvarint16! [SizedStream ρ UInt8] [Inhabited ρ] (xs : ρ) : UInt16 × ρ :=
  getOk! "UInt16" $ decUvarint16 xs

/--
Decode an unsigned varint which should fit in a `UInt32` from `xs`.
-/
def decUvarint32 [SizedStream ρ UInt8] (xs : ρ) :
    Except BoundedVarintError (UInt32 × ρ) :=
  let output := Output.bounded UInt32.size (by decide) UInt32 UInt32.ofNatCore
  decUvarintCore xs 0 0 output

/--
Decode an unsigned varint which should fit in a `UInt32` from `xs`, or panic if
one cannot be decoded.
-/
def decUvarint32! [SizedStream ρ UInt8] [Inhabited ρ] (xs : ρ) : UInt32 × ρ :=
  getOk! "UInt32" $ decUvarint32 xs

/--
Decode an unsigned varint which should fit in a `UInt64` from `xs`.
-/
def decUvarint64 [SizedStream ρ UInt8] (xs : ρ) :
    Except BoundedVarintError (UInt64 × ρ) :=
  let output := Output.bounded UInt64.size (by decide) UInt64 UInt64.ofNatCore
  decUvarintCore xs 0 0 output

/--
Decode an unsigned varint which should fit in a `UInt64` from `xs`, or panic if
one cannot be decoded.
-/
def decUvarint64! [SizedStream ρ UInt8] [Inhabited ρ] (xs : ρ) : UInt64 × ρ :=
  getOk! "UInt64" $ decUvarint64 xs

def encUvarintCore (n : Nat) (acc : List UInt8) : List UInt8 :=
  if h : n ≤ 0b1111111 then
    UInt8.ofNatCore n (lt_of_le_of_lt h (by decide)) :: acc.reverse
  else
    let x := (n &&& 0b1111111) ||| 0b10000000
    have : x < UInt8.size := by
      have and_lt : n &&& 0b1111111 < 2 ^ 8 := Nat.and_lt_two_pow n (by decide)
      exact Nat.or_lt_two_pow and_lt (by decide)
    encUvarintCore (n >>> 7) (UInt8.ofNatCore x this :: acc)
termination_by n
decreasing_by
  all_goals simp_wf
  show Nat.shiftRight n 7 < n
  simp [Nat.shiftRight, Nat.div_div_eq_div_mul]
  apply Nat.div_lt_self
  . linarith
  . decide

/--
Encode `n` as an unsigned varint.
-/
def encUvarint (n : Nat) : List UInt8 := encUvarintCore n []

def intToVarintEncNat (i : Int) : Nat :=
  if i < 0 then (-i - 1).toNat <<< 1 ||| 1 else i.toNat <<< 1

/--
Encode `i` as a varint.
-/
def encVarint (i : Int) : List UInt8 := encUvarint $ intToVarintEncNat i

/--
Encode `n` which fits in a `UInt8` as an unsigned varint.
-/
def encUvarint8 (n : UInt8) : List UInt8 := encUvarint n.toNat

/--
Encode `n` which fits in a `UInt16` as an unsigned varint.
-/
def encUvarint16 (n : UInt16) : List UInt8 := encUvarint n.toNat

/--
Encode `n` which fits in a `UInt32` as an unsigned varint.
-/
def encUvarint32 (n : UInt32) : List UInt8 := encUvarint n.toNat

/--
Encode `n` which fits in a `UInt64` as an unsigned varint.
-/
def encUvarint64 (n : UInt64) : List UInt8 := encUvarint n.toNat

private
theorem encUvarintCore_length_ge : (encUvarintCore n l).length ≥ 1 := by
  rw [encUvarintCore]
  by_cases h : n ≤ 127
  . simp [dif_pos h]
    linarith
  . simp [dif_neg h]
    exact encUvarintCore_length_ge
termination_by n
decreasing_by
  all_goals simp_wf
  show Nat.shiftRight n 7 < n
  simp [Nat.shiftRight, Nat.div_div_eq_div_mul]
  apply Nat.div_lt_self
  . linarith
  . decide

theorem encUvarint_length_ge : (encUvarint n).length ≥ 1 := by
  rw [encUvarint]
  exact encUvarintCore_length_ge

private
theorem clog2_eq_clog2_shiftRight_add (s : Nat) (b : 1 ≤ n >>> s) :
  Nat.clog 2 (n + 1) = Nat.clog 2 (n >>> s + 1) + s := by
  induction' s with s ih
  . simp [Nat.shiftRight]
  . have b' : 1 ≤ n >>> s := by
      change 1 ≤ Nat.shiftRight n s
      change 1 ≤ Nat.shiftRight n s.succ at b
      rw [Nat.shiftRight] at b
      apply le_trans
      . show 1 ≤ 2
        decide
      . show 1 * 2 ≤ Nat.shiftRight n s
        apply Nat.mul_le_of_le_div
        exact b
    have : (n >>> s + 1 + 2 - 1) / 2 = n >>> (s + 1) + 1 := by
      simp
      show Nat.shiftRight n s / 2 = Nat.shiftRight n (s + 1)
      simp [Nat.shiftRight]
    calc
      Nat.clog 2 (n + 1) = Nat.clog 2 (n >>> s + 1) + s := ih b'
      _ = Nat.clog 2 (n >>> (s + 1) + 1) + s + 1 := by
        rw [Nat.clog_of_two_le (by decide) (by linarith), this]
        linarith

private
theorem divCeil_add_same (a b : Nat) (h : 1 ≤ b) : (a + b) ⌈/⌉ b = a ⌈/⌉ b + 1 := by
  dsimp [Nat.instCeilDiv]
  nth_rw 1 [Nat.div_eq]
  rw [if_pos]
  . rw [Nat.sub_right_comm, Nat.add_sub_assoc (by trivial), Nat.add_assoc,
        ← Nat.add_sub_assoc (by trivial), Nat.add_sub_cancel]
  . constructor
    . linarith
    . rw [Nat.add_sub_assoc (by trivial), Nat.add_assoc, Nat.add_comm, Nat.add_assoc]
      nth_rw 1 [← Nat.add_zero b]
      apply Nat.add_le_add
      . trivial
      . exact Nat.zero_le _

private
theorem encUvarintCore_length_le :
  (encUvarintCore n l).length ≤ l.length + max 1 (Nat.clog 2 (n + 1) ⌈/⌉ 7) := by
  rw [encUvarintCore]
  by_cases h : n ≤ 127
  . simp [dif_pos h]
    by_cases h : 0 < n
    . have : Nat.clog 2 (n + 1) ⌈/⌉ 7 = 1 := by
        dsimp [Nat.instCeilDiv]
        rw [Nat.div_eq, if_pos]
        . nth_rw 3 [← zero_add 1]
          apply (add_left_inj 1).mpr
          apply (Nat.div_eq_zero_iff _).mpr
          . simp
            apply @Nat.lt_of_add_lt_add_right _ _ 1
            simp
            rw [Nat.sub_add_cancel]
            . apply lt_of_le_of_lt
              . apply Nat.clog_mono_right 2
                . show n + 1 ≤ 128
                  linarith
              have : 128 = 2 ^ 7 := by linarith
              rw [this, Nat.clog_pow]
              . decide
              . decide
            . apply Nat.clog_pos
              . decide
              . linarith
          . decide
        . constructor
          . decide
          . apply (Nat.sub_le_sub_iff_right _).mp
            . show 7 - 6 ≤ Nat.clog 2 (n + 1) + 6 - 6
              simp
              apply Nat.clog_pos
              . decide
              . linarith
            . linarith
      rw [this, Nat.max_self]
    . simp at h
      rw [h]
      rw [max_eq_left]
      simp [Nat.clog_zero_right]
  . have h' : 1 ≤ n >>> 7 := by
      simp at h
      change 128 ≤ n at h
      show 1 ≤ Nat.shiftRight n 7
      simp [Nat.shiftRight, Nat.div_div_eq_div_mul]
      show 1 ≤ n / 128
      exact (Nat.one_le_div_iff (by decide)).mpr h
    simp [dif_neg h]
    have prepend_length : ∀ x, List.length (x :: l) = List.length l + 1 := by simp
    have shiftRight7_bound : Nat.clog 2 (n + 1) ⌈/⌉ 7 =
      Nat.clog 2 (n >>> 7 + 1) ⌈/⌉ 7 + 1 := by
      rw [clog2_eq_clog2_shiftRight_add 7 h']
      apply divCeil_add_same
      decide
    let x := n &&& 127 ||| 128
    have : x < UInt8.size := by
      have and_lt : n &&& 127 < 2 ^ 8 := Nat.and_lt_two_pow n (by decide)
      exact Nat.or_lt_two_pow and_lt (by decide)
    let x' := UInt8.ofNatCore x this
    have : List.length l + max 1 (Nat.clog 2 (n + 1) ⌈/⌉ 7) =
      List.length (x' :: l) + max 1 (Nat.clog 2 (n >>> 7 + 1) ⌈/⌉ 7) := by
      calc
        List.length l + max 1 (Nat.clog 2 (n + 1) ⌈/⌉ 7) =
          List.length l + Nat.clog 2 (n + 1) ⌈/⌉ 7 := by
            rw [max_eq_right]
            dsimp [Nat.instCeilDiv]
            rw [Nat.div_eq, if_pos]
            . apply le_add_left
              trivial
            . constructor
              . decide
              . apply (Nat.sub_le_sub_iff_right _).mp
                . show 7 - 6 ≤ Nat.clog 2 (n + 1) + 6 - 6
                  simp
                  apply Nat.clog_pos
                  . decide
                  . linarith
                . linarith
        _ = List.length (x' :: l) + Nat.clog 2 (n >>> 7 + 1) ⌈/⌉ 7 := by
          rw [prepend_length, shiftRight7_bound]
          linarith
        _ = List.length (x' :: l) + max 1 (Nat.clog 2 (n >>> 7 + 1) ⌈/⌉ 7) := by
          have : 1 ≤ Nat.clog 2 (n >>> 7 + 1) ⌈/⌉ 7 := by
            dsimp [Nat.instCeilDiv]
            rw [Nat.div_eq, if_pos]
            . apply le_add_left
              trivial
            . constructor
              . decide
              . apply (Nat.sub_le_sub_iff_right _).mp
                . show 7 - 6 ≤ Nat.clog 2 (n >>> 7 + 1) + 6 - 6
                  simp
                  apply Nat.clog_pos
                  . decide
                  . linarith
                . linarith
          nth_rw 1 [← max_eq_right this]
    rw [this]
    exact encUvarintCore_length_le
termination_by n
decreasing_by
  all_goals simp_wf
  show Nat.shiftRight n 7 < n
  simp [Nat.shiftRight, Nat.div_div_eq_div_mul]
  apply Nat.div_lt_self
  . linarith
  . decide

theorem encUvarint_length_le :
  (encUvarint n).length ≤ max 1 (Nat.clog 2 (n + 1) ⌈/⌉ 7) := by
  have : 0 = @List.length UInt8 [] := by simp
  rw [encUvarint, ← zero_add (_ ⌈/⌉ 7), this]
  by_cases h : 1 ≤ (Nat.clog 2 (n + 1) ⌈/⌉ 7)
  . rw [max_eq_right]
    . rw [← max_eq_right h]
      exact encUvarintCore_length_le
    . rw [← this]
      simp
      exact h
  . simp at h
    rw [h]
    simp
    apply le_trans
    . show (encUvarintCore n []).length ≤ @List.length UInt8 [] + max 1 (Nat.clog 2 (n + 1) ⌈/⌉ 7)
      exact encUvarintCore_length_le
    . rw [← this, max_eq_left]
      linarith

theorem encVarint_length_le :
  (encVarint n).length ≤ max 1 (Nat.clog 2 (intToVarintEncNat n + 1) ⌈/⌉ 7) := by
  rw [encVarint]
  exact encUvarint_length_le

theorem encUvarint8_length_ge : (encUvarint8 n).length ≥ 1 := by
  rw [encUvarint8]
  exact encUvarint_length_ge

theorem encUvarint8_length_le : (encUvarint8 n).length ≤ 2 := by
  apply le_trans
  . exact encUvarint_length_le
  . simp
    apply le_trans
    . apply Nat.clog_mono_right
      . show UInt8.toNat n + 1 ≤ UInt8.size
        exact Fin.prop n.val
    . have : UInt8.size = 2 ^ 8 := by linarith
      rw [this]
      rw [Nat.clog_pow] <;> decide

theorem encUvarint16_length_ge : (encUvarint16 n).length ≥ 1 := by
  rw [encUvarint16]
  exact encUvarint_length_ge

theorem encUvarint16_length_le : (encUvarint16 n).length ≤ 3 := by
  apply le_trans
  . exact encUvarint_length_le
  . simp
    apply le_trans
    . apply Nat.clog_mono_right
      . show UInt16.toNat n + 1 ≤ UInt16.size
        exact Fin.prop n.val
    . have : UInt16.size = 2 ^ 16 := by linarith
      rw [this]
      rw [Nat.clog_pow] <;> decide

theorem encUvarint32_length_ge : (encUvarint32 n).length ≥ 1 := by
  rw [encUvarint32]
  exact encUvarint_length_ge

theorem encUvarint32_length_le : (encUvarint32 n).length ≤ 5 := by
  apply le_trans
  . exact encUvarint_length_le
  . simp
    apply le_trans
    . apply Nat.clog_mono_right
      . show UInt32.toNat n + 1 ≤ UInt32.size
        exact Fin.prop n.val
    . have : UInt32.size = 2 ^ 32 := by linarith
      rw [this]
      rw [Nat.clog_pow] <;> decide

theorem encUvarint64_length_ge : (encUvarint64 n).length ≥ 1 := by
  rw [encUvarint64]
  exact encUvarint_length_ge

theorem encUvarint64_length_le : (encUvarint64 n).length ≤ 10 := by
  apply le_trans
  . exact encUvarint_length_le
  . simp
    apply le_trans
    . apply Nat.clog_mono_right
      . show UInt64.toNat n + 1 ≤ UInt64.size
        exact Fin.prop n.val
    . have : UInt64.size = 2 ^ 64 := by linarith
      rw [this]
      rw [Nat.clog_pow] <;> decide

end Protobuf.Varint
