import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.UInt.Basic
import Init.Data.Option.Basic
import Lean.Elab.Do
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Set.Function
import Mathlib.Data.UInt
import Mathlib.Tactic
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
  | bounded (bound : Nat) (inBound : acc < bound)

def Output.outType : Output acc → Type
  | unbounded => Nat
  | bounded bound _ => Σ' acc : Nat, acc < bound

def Output.errorType : Output acc → Type
  | unbounded => VarintError
  | bounded _ _ => BoundedVarintError

-- TODO: Support partial dec- variants that operate on unsized streams.

set_option linter.unusedVariables false in
private
def decCore [SizedStream ρ UInt8] (xs : ρ) (shift acc : Nat)
    (output : Output acc := Output.unbounded) (first : Bool := false) :
    Except (Output.errorType output) (Output.outType output × ρ) :=
  match h : Stream.next? xs with
  | some (x, xs') =>
    if x &&& 0x80 = 0 then
      let out := (x &&& 0b1111111).toNat <<< shift + acc
      match output with
      | Output.unbounded => ok (out, xs')
      | Output.bounded bound inBound =>
        if h' : out ≥ bound then
          error BoundedVarintError.overflow
        else
          ok (PSigma.mk out (by linarith), xs')
    else
      let acc' := (x &&& 0b1111111).toNat <<< shift + acc
      match output with
      | Output.unbounded => decCore xs' (shift + 7) acc'
      | Output.bounded bound inBound =>
        if h' : acc' ≥ bound then
          error BoundedVarintError.overflow
        else
          let output' := Output.bounded bound (lt_of_not_ge h')
          decCore xs' (shift + 7) acc' output'
  | none => error $ match first, output with
    | true, Output.unbounded => VarintError.end
    | false, Output.unbounded => VarintError.unexpectedEnd
    | true, Output.bounded _ _ => BoundedVarintError.end
    | false, Output.bounded _ _ => BoundedVarintError.unexpectedEnd
termination_by SizedStream.size xs
decreasing_by
  all_goals simp_wf <;> apply SizedStream.size_dec xs xs' h

/--
Decode an unsigned varint from `xs`.
-/
def decUvarint [SizedStream ρ UInt8] (xs : ρ) : Except VarintError (Nat × ρ) :=
  decCore xs 0 0 (first := true)

/--
Decode an unsigned varint from `xs`, or panic if one cannot be decoded.
-/
def decUvarint! [SizedStream ρ UInt8] [Inhabited ρ] (xs : ρ) : Nat × ρ :=
  match decUvarint xs with
  | ok res => res
  | error VarintError.end => panic! "stream was empty"
  | error VarintError.unexpectedEnd => panic! "stream contained invalid uvarint"

def varintEncNatToInt (n : Nat) : Int :=
  let n' := Int.ofNat (n >>> 1)
  if n.testBit 0 then -(n' + 1) else n'

private
def Prod.map_fst (f : α → γ) : α × β → γ × β | (fst, snd) => (f fst, snd)

/--
Decode a varint from `xs`.
-/
def decVarint [SizedStream ρ UInt8] (xs : ρ) : Except VarintError (Int × ρ) :=
  (decCore xs 0 0 Output.unbounded true).map $ Prod.map_fst varintEncNatToInt

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
  let output := Output.bounded UInt8.size (by decide)
  (decCore xs 0 0 output true).map fun (⟨n, h⟩, f) ↦ (UInt8.ofNatCore n h, f)

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
  let output := Output.bounded UInt16.size (by decide)
  (decCore xs 0 0 output true).map fun (⟨n, h⟩, f) ↦ (UInt16.ofNatCore n h, f)

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
  let output := Output.bounded UInt32.size (by decide)
  (decCore xs 0 0 output true).map fun (⟨n, h⟩, f) ↦ (UInt32.ofNatCore n h, f)

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
  let output := Output.bounded UInt64.size (by decide)
  (decCore xs 0 0 output true).map fun (⟨n, h⟩, f) ↦ (UInt64.ofNatCore n h, f)

/--
Decode an unsigned varint which should fit in a `UInt64` from `xs`, or panic if
one cannot be decoded.
-/
def decUvarint64! [SizedStream ρ UInt8] [Inhabited ρ] (xs : ρ) : UInt64 × ρ :=
  getOk! "UInt64" $ decUvarint64 xs

private
theorem and_or_lt_size : n &&& 0b1111111 ||| 0b10000000 < UInt8.size := by
  have and_lt : n &&& 127 < 2 ^ 8 := Nat.and_lt_two_pow n (by decide)
  exact Nat.or_lt_two_pow and_lt (by decide)

private
def encCore (n : Nat) (acc : List UInt8) : List UInt8 :=
  if h : n ≤ 0b1111111 then
    (UInt8.ofNatCore n (lt_of_le_of_lt h (by decide)) :: acc).reverse
  else
    let x := (n &&& 0b1111111) ||| 0b10000000
    encCore (n >>> 7) (UInt8.ofNatCore x and_or_lt_size :: acc)
termination_by n
decreasing_by
  all_goals simp_wf
  show Nat.shiftRight n 7 < n
  simp [Nat.shiftRight, Nat.div_div_eq_div_mul]
  apply Nat.div_lt_self
  . linarith
  . decide

private
theorem encCore_append_acc_eq
  : encCore n (xs ++ ys) = ys.reverse ++ encCore n xs := by
  rw [encCore]
  split
  · case _ h =>
    rw [encCore, dif_pos h, ← List.cons_append, List.reverse_append]
  · case _ h =>
    simp
    rw [← List.cons_append, encCore_append_acc_eq]
    nth_rw 2 [encCore]
    rw [dif_neg h]

/--
Encode `n` as an unsigned varint.
-/
def encUvarint (n : Nat) : List UInt8 := encCore n []

def intToVarintEncNat (i : Int) : Nat :=
  if i < 0 then (-i - 1).toNat <<< 1 ||| 1 else i.toNat <<< 1

-- Inlined from https://github.com/leanprover/lean4/blame/873ef2d894af80d8fc672e35f7e28bae314a1f6f/src/Init/Data/Nat/Bitwise/Lemmas.lean#L91-L94
private
theorem toNat_testBit (x i : Nat) :
    (x.testBit i).toNat = x / 2 ^ i % 2 := by
  rw [Nat.testBit_to_div_mod]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) <;> simp_all

private
theorem or_one_mod_two_eq_one : (x ||| 1) % 2 = 1 := by
  rw [← Nat.div_one (x ||| 1)]
  nth_rw 2 [← Nat.pow_zero 2]
  rw [← toNat_testBit (x ||| 1) 0, Nat.testBit_or]
  simp

private
theorem shiftLeft_one_or_one_shiftRight_one_eq_self (n : Nat)
  : (n <<< 1 ||| 1) >>> 1 = n := by
  simp [Nat.shiftLeft_eq, Nat.shiftRight_succ _ _]
  simp [HOr.hOr, OrOp.or, Nat.lor, Nat.bitwise]
  split
  . case _ h =>
    rw [h]
    simp
  . rw [Nat.succ_div_of_not_dvd _]
    . rw [← mul_two]
      simp
    . rw [← mul_two, mul_comm]
      simp
      rw [Nat.mul_add_mod]
      decide

theorem intToVarintEncNat_RightInverse_varintEncNatToInt :
  Function.RightInverse intToVarintEncNat varintEncNatToInt := by
  dsimp [Function.RightInverse]
  intro i
  rw [varintEncNatToInt, intToVarintEncNat]
  by_cases h : i < 0
  . simp
    rw [if_pos h, or_one_mod_two_eq_one, if_pos rfl,
        shiftLeft_one_or_one_shiftRight_one_eq_self, ← Int.pred_toNat,
        Int.toNat_of_nonneg] <;> linarith
  . simp
    have : 1 = Int.succ 0 := by decide
    rw [if_neg h, Nat.shiftLeft_eq, pow_one, Nat.mul_mod_left,
      if_neg (by decide), Nat.shiftRight_succ _ _]
    simp
    rw [Int.toNat_of_nonneg]
    linarith

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
theorem encCore_length_ge : (encCore n l).length ≥ 1 := by
  rw [encCore]
  by_cases h : n ≤ 127
  . simp [dif_pos h]
  . simp [dif_neg h]
    exact encCore_length_ge
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
  exact encCore_length_ge

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
theorem divCeil_add_same (a b : Nat) (h : 1 ≤ b) :
  (a + b) ⌈/⌉ b = a ⌈/⌉ b + 1 := by
  dsimp [Nat.instCeilDiv]
  nth_rw 1 [Nat.div_eq]
  rw [if_pos]
  . rw [Nat.sub_right_comm, Nat.add_sub_assoc (by trivial), Nat.add_assoc,
        ← Nat.add_sub_assoc (by trivial), Nat.add_sub_cancel]
  . constructor
    . linarith
    . rw [Nat.add_sub_assoc (by trivial), Nat.add_assoc, Nat.add_comm,
          Nat.add_assoc]
      nth_rw 1 [← Nat.add_zero b]
      apply Nat.add_le_add
      . trivial
      . exact Nat.zero_le _

private
theorem encCore_length_le
  : (encCore n l).length ≤ l.length + max 1 (Nat.clog 2 (n + 1) ⌈/⌉ 7) := by
  rw [encCore]
  by_cases h : n ≤ 127
  . simp [dif_pos h]
  . have h' : 1 ≤ n >>> 7 := by
      simp at h
      change 128 ≤ n at h
      show 1 ≤ Nat.shiftRight n 7
      simp [Nat.shiftRight, Nat.div_div_eq_div_mul]
      show 1 ≤ n / 128
      exact (Nat.one_le_div_iff (by decide)).mpr h
    simp [dif_neg h]
    have prepend_length : ∀ x, List.length (x :: l) = List.length l + 1 := by
      simp
    have shiftRight7_bound : Nat.clog 2 (n + 1) ⌈/⌉ 7 =
      Nat.clog 2 (n >>> 7 + 1) ⌈/⌉ 7 + 1 := by
      rw [clog2_eq_clog2_shiftRight_add 7 h']
      apply divCeil_add_same
      decide
    let x := n &&& 127 ||| 128
    let x' := UInt8.ofNatCore x and_or_lt_size
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
    exact encCore_length_le
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
      exact encCore_length_le
    . rw [← this]
      simp
      exact h
  . simp at h
    rw [h]
    simp
    apply le_trans
    . show (encCore n []).length ≤ @List.length UInt8 [] +
        max 1 (Nat.clog 2 (n + 1) ⌈/⌉ 7)
      exact encCore_length_le
    . rw [← this, max_eq_left]
      linarith

theorem encVarint_length_le :
  (encVarint n).length ≤ max 1 (Nat.clog 2 (intToVarintEncNat n + 1) ⌈/⌉ 7)
  := by
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

private
theorem shiftRight_shiftLeft (n s : Nat) : (n >>> s) <<< s + n % (2 ^ s) = n :=
  by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.div_add_mod']

private
theorem shiftLeft_right_distrib {a b s : Nat}
  : (a + b) <<< s = a <<< s + b <<< s := by
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.right_distrib]

private
theorem UInt8.ne_of_val_ne {a b : UInt8} (h : a.val ≠ b.val) : a ≠ b :=
  fun h' ↦ absurd (UInt8.val_eq_of_eq h') h

private
theorem decCore_unbounded_right_inv_encCore (first : Bool := true)
  : decCore (encCore n [] ++ l) shift acc (first := first) =
    ok (n <<< shift + acc, l) := by
  rw [decCore, encCore]
  simp
  by_cases h₀ : n ≤ 127
  . rw [dif_pos h₀] -- there's only one entry remaining in the encoding
    dsimp [Stream.next?, List.reverse]
    rw [if_pos (by
      show _ &&& 128 = 0
      dsimp [UInt8.ofNatCore, HAnd.hAnd, AndOp.and, UInt8.land, Fin.land]
      simp
      congr
      simp [Nat.land, Nat.bitwise, Nat.div_div_eq_div_mul]
      intro _ _ _ _ _ _ _ _
      rw [Nat.div_eq_of_lt (by linarith)]
    )]
    congr
    show (n &&& 127) % UInt8.size = n
    have : n &&& 127 = n := by
      have : 127 = 2 ^ 7 - 1 := by simp
      rw [this, Nat.and_pow_two_identity (by linarith)]
    rw [this]
    simp
    linarith
  . rw [dif_neg h₀] -- there are more entries
    dsimp [Stream.next?]
    split
    . case _ x xs' h₁ => -- the encoding is non-empty
      split at h₁
      . contradiction
      case _ x' xs'' h₂ =>
      simp at h₁
      rw [h₁.left, h₁.right, ← List.nil_append [_],
          encCore_append_acc_eq (xs := [])] at h₂
      simp at h₂
      have : x &&& 128 ≠ 0 := by
        rw [← h₂.left]
        dsimp [UInt8.ofNatCore, HAnd.hAnd, AndOp.and, UInt8.land, Fin.land]
        simp
        push_neg
        apply UInt8.ne_of_val_ne
        apply Fin.ne_of_val_ne
        simp
        show ((n &&& 127 ||| 128) &&& 2 ^ 7) % UInt8.size ≠ 0
        rw [Nat.and_two_pow _ 7, Nat.testBit_or]
        simp
      rw [if_neg this, ← shiftRight_shiftLeft n 7, shiftLeft_right_distrib,
          ← Nat.shiftLeft_add, Nat.add_comm 7 shift, Nat.add_assoc,
          ← Nat.and_pow_two_is_mod n 7, (by decide : 2 ^ 7 - 1 = 127),
          ← decCore_unbounded_right_inv_encCore (first := false)]
      have : UInt8.toNat (x &&& 127) = n &&& 127 := by
        rw [← h₂.left]
        dsimp [UInt8.toNat, UInt8.ofNatCore, HAnd.hAnd, AndOp.and, UInt8.land,
               Fin.land]
        simp
        show ((n &&& 127 ||| (2 ^ 7 * 1)) &&& (2 ^ 7 - 1)) % (2 ^ 8) = n &&& 127
        have : n &&& 127 < 2 ^ 7 := by
          apply Nat.and_lt_two_pow
          decide
        rw [Nat.lor_comm, Nat.and_pow_two_is_mod,
            ← Nat.mul_add_lt_is_or this _, Nat.mul_one,
            Nat.add_mod_left, Nat.mod_eq_of_lt this,
            Nat.mod_eq_of_lt (by linarith)]
      congr
      exact symm h₂.right
    . case _ h₁ => -- the encoding is empty
      absurd h₁
      split
      . case _ heq =>
        induction l with
        | nil =>
          rw [List.append_nil] at heq
          have : (encCore (n >>> 7) _).length = 0 := by
            rw [heq]
            simp
          absurd this
          apply Nat.ne_of_gt
          apply encCore_length_ge
        | cons _ _ => simp at heq
      . case _ => simp

private
theorem decCore_bounded_right_inv_encCore
  (bound : Nat) (inBound : acc < bound) (first : Bool := true)
  : decCore (encCore n [] ++ l) shift acc (Output.bounded bound inBound) first =
    ok (⟨n <<< shift + acc, sorry⟩, l) := by sorry

theorem encUvarint_right_inv_decUvarint :
  decUvarint (encUvarint n ++ l) = ok (n, l) := by
  rw [decUvarint, encUvarint, decCore_unbounded_right_inv_encCore]
  simp

theorem encVarint_right_inv_decVarint :
  decVarint (encVarint i ++ l) = ok (i, l) := by
  rw [decVarint, encVarint, encUvarint, decCore_unbounded_right_inv_encCore]
  simp [Except.map, Prod.map_fst]
  apply intToVarintEncNat_RightInverse_varintEncNatToInt

theorem encUvarint8_right_inv_decUvarint8 :
  decUvarint8 (encUvarint8 n ++ l) = ok (n, l) := by
  rw [decUvarint8, encUvarint8, encUvarint]
  simp
  rw [decCore_bounded_right_inv_encCore (UInt8.size) (by decide)]
  congr

theorem encUvarint16_right_inv_decUvarint16 :
  decUvarint16 (encUvarint16 n ++ l) = ok (n, l) := by
  rw [decUvarint16, encUvarint16, encUvarint]
  simp
  rw [decCore_bounded_right_inv_encCore (UInt16.size) (by decide)]
  congr

theorem encUvarint32_right_inv_decUvarint32 :
  decUvarint32 (encUvarint32 n ++ l) = ok (n, l) := by
  rw [decUvarint32, encUvarint32, encUvarint]
  simp
  rw [decCore_bounded_right_inv_encCore (UInt32.size) (by decide)]
  congr

theorem encUvarint64_right_inv_decUvarint64 :
  decUvarint64 (encUvarint64 n ++ l) = ok (n, l) := by
  rw [decUvarint64, encUvarint64, encUvarint]
  simp
  rw [decCore_bounded_right_inv_encCore (UInt64.size) (by decide)]
  congr

end Protobuf.Varint
