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
inductive Output (acc : ℕ) where
  | unbounded
  | bounded (bound : ℕ) (inBound : acc < bound)

def Output.outType : Output acc → Type
  | unbounded => ℕ
  | bounded bound _ => Σ' acc : ℕ, acc < bound

def Output.errorType : Output acc → Type
  | unbounded => VarintError
  | bounded _ _ => BoundedVarintError

-- TODO: Support partial dec- variants that operate on unsized streams.

set_option linter.unusedVariables false in
private
def decCore [SizedStream ρ UInt8] (xs : ρ) (shift acc : ℕ)
    (output : Output acc := Output.unbounded) (first : Bool := false)
    : Except (Output.errorType output) (Output.outType output × ρ) :=
  match h : Stream.next? xs with
  | some (x, xs') =>
    if x &&& 0x80 = 0 then
      let out := (x &&& 0b1111111).toNat <<< shift + acc
      match output with
      | Output.unbounded => ok (out, xs')
      | Output.bounded bound inBound =>
        if h' : out < bound then
          ok (PSigma.mk out h', xs')
        else
          error BoundedVarintError.overflow
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
  all_goals simp_wf; exact SizedStream.size_dec xs xs' h

/--
Decode an unsigned varint from `xs`.
-/
def decUvarint [SizedStream ρ UInt8] (xs : ρ) : Except VarintError (ℕ × ρ) :=
  decCore xs 0 0 (first := true)

/--
Decode an unsigned varint from `xs`, or panic if one cannot be decoded.
-/
def decUvarint! [SizedStream ρ UInt8] [Inhabited ρ] (xs : ρ) : ℕ × ρ :=
  match decUvarint xs with
  | ok res => res
  | error VarintError.end => panic! "stream was empty"
  | error VarintError.unexpectedEnd => panic! "stream contained invalid uvarint"

def varintEncNatToInt (n : ℕ) : ℤ :=
  let n' := Int.ofNat (n >>> 1)
  if n.testBit 0 then -(n' + 1) else n'

/--
Decode a varint from `xs`.
-/
def decVarint [SizedStream ρ UInt8] (xs : ρ) : Except VarintError (ℤ × ρ) :=
  (decCore xs 0 0 Output.unbounded true).map
    fun (r, xs) ↦ (varintEncNatToInt r, xs)

/--
Decode a varint from `xs`, or panic if one cannot be decoded.
-/
def decVarint! [SizedStream ρ UInt8] [Inhabited ρ] (xs : ρ) : ℤ × ρ :=
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
    panic! s!"stream contained uvarint that overflowed {s}"

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
theorem shiftRight7_lt_self (npos : 0 < n) : n >>> 7 < n := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_self
  · exact npos
  · decide

private
def encCore (n : ℕ) (acc : List UInt8) : List UInt8 :=
  if h : n ≤ 0b1111111 then
    (UInt8.ofNatCore n (lt_of_le_of_lt h (by decide)) :: acc).reverse
  else
    let x := (n &&& 0b1111111) ||| 0b10000000
    encCore (n >>> 7) (UInt8.ofNatCore x and_or_lt_size :: acc)
termination_by n
decreasing_by
  all_goals simp_wf
  apply shiftRight7_lt_self
  apply Nat.lt_trans (m := 127)
  · decide
  · exact Nat.lt_of_not_le h

private
theorem encCore_append_acc_eq
  : encCore n (xs ++ ys) = ys.reverse ++ encCore n xs := by
  rw [encCore]
  split
  · case _ h =>
    rw [encCore, dif_pos h, ← List.cons_append, List.reverse_append]
  · case _ h =>
    show encCore (n >>> 7) (UInt8.ofNatCore (n &&& 127 ||| 128) _ :: (xs ++ ys))
      = List.reverse ys ++ encCore n xs
    rw [← List.cons_append, encCore_append_acc_eq]
    nth_rw 2 [encCore]
    rw [dif_neg h]
termination_by n
decreasing_by
  all_goals simp_wf
  apply shiftRight7_lt_self
  apply Nat.lt_trans (m := 127)
  · decide
  · apply Nat.lt_of_not_le
    assumption

/--
Encode `n` as an unsigned varint.
-/
def encUvarint (n : ℕ) : List UInt8 := encCore n []

def intToVarintEncNat (i : ℤ) : ℕ :=
  if i < 0 then (-i - 1).toNat <<< 1 ||| 1 else i.toNat <<< 1

private
theorem toNat_testBit (x i : ℕ) : (x.testBit i).toNat = x / 2 ^ i % 2 := by
  rw [Nat.testBit_to_div_mod]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with (h | h)
  · rw [h]
    show Bool.toNat (decide False) = 0
    rw [decide_False, Bool.toNat_false]
  · rw [h]
    show Bool.toNat (decide True) = 1
    rw [decide_True, Bool.toNat_true]

private
theorem or_one_and_one_eq_one : (x ||| 1) &&& 1 = 1 := by
  rw [← Nat.div_one (x ||| 1)]
  have : 1 = 2 ^ 1 - 1 := by rfl
  nth_rw 2 [← Nat.pow_zero 2, this]
  rw [Nat.and_pow_two_is_mod _ _, ← toNat_testBit (x ||| 1) 0, Nat.testBit_or,
      Nat.testBit_zero, Nat.testBit_zero, Nat.mod_succ]
  show Bool.toNat (decide (x % 2 = 1) || decide True) = 1
  rw [decide_True, Bool.or_true, Bool.toNat_true]

private
theorem shiftLeft_one_or_one_shiftRight_one_eq_self (n : ℕ)
  : (n <<< 1 ||| 1) >>> 1 = n := by
  rw [Nat.shiftLeft_eq, pow_one, Nat.shiftRight_succ, Nat.shiftRight_zero,
      HOr.hOr, instHOr, OrOp.or, Nat.instOrOpNat, Nat.lor]
  unfold Nat.bitwise
  split
  . case _ h =>
    rw [if_pos (by rfl)]
    cases Nat.eq_zero_of_mul_eq_zero h
    · case _ h =>
      rw [h]
    · contradiction
  . rw [if_neg (by trivial)]
    unfold_let
    have add_add_eq_mul_two {x : ℕ} : x + x = 2 * x := by
      rw [Nat.succ_mul, Nat.one_mul]
    have mul_two_add_one_div_two_eq_self {x : ℕ} : (2 * x + 1) / 2 = x := by
      rw [Nat.mul_add_div (by decide), (by decide : 1 / 2 = 0), Nat.add_zero]
    have bitwise_eq {a b : ℕ} : Nat.bitwise or a b = a ||| b := by
      rw [HOr.hOr, instHOr, OrOp.or, Nat.instOrOpNat, Nat.lor]
    rw [if_pos (by
          have : decide (1 % 2 = 1) = true := by
            rw [Nat.mod_eq_of_lt (by decide)]
            show decide True = true
            rw [decide_True]
          rw [this, Bool.or_true]
        ), add_add_eq_mul_two, mul_two_add_one_div_two_eq_self, bitwise_eq,
        (by decide : 1 / 2 = 0), Nat.zero_or, Nat.mul_div_cancel _ (by decide)]

private
theorem Int.ofNat_toNat (inonneg : 0 ≤ i) : Int.ofNat i.toNat = i := by
  rw [Int.ofNat_eq_coe, Int.toNat_of_nonneg inonneg]

theorem intToVarintEncNat_RightInverse_varintEncNatToInt
  : Function.RightInverse intToVarintEncNat varintEncNatToInt := by
  intro i
  rw [varintEncNatToInt, intToVarintEncNat]
  by_cases h : i < 0
  . unfold_let
    rw [Nat.testBit, if_pos h, if_pos (by
          rw [Nat.shiftRight_zero, or_one_and_one_eq_one]
          rfl
        ), shiftLeft_one_or_one_shiftRight_one_eq_self, Int.ofNat_toNat _,
        Int.sub_add_cancel, Int.neg_neg _]
    apply sub_nonneg.mpr
    exact Int.neg_pos_of_neg h
  . unfold_let
    rw [if_neg h, if_neg (by
      rw [Nat.testBit_shiftLeft, (by rfl : decide _ = false),Bool.false_and]
      push_neg
      exact Bool.false_ne_true
      ), Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      Nat.mul_div_cancel _ (by decide), Int.ofNat_toNat]
    push_neg at h
    exact h

/--
Encode `i` as a varint.
-/
def encVarint (i : ℤ) : List UInt8 := encUvarint $ intToVarintEncNat i

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
theorem Nat.clog2_add_one_pos (npos : 0 < n) : 0 < Nat.clog 2 (n + 1) := by
  apply Nat.clog_pos
  · decide
  · show 1 + 1 ≤ n + 1
    apply Nat.add_le_add_right
    exact Nat.succ_le_of_lt npos

private
theorem divCeil_add_self (a b : ℕ) (h : 1 ≤ b) : (a + b) ⌈/⌉ b = a ⌈/⌉ b + 1
  := by
  dsimp only [Nat.instCeilDiv]
  nth_rw 1 [Nat.div_eq]
  rw [if_pos]
  . rw [Nat.sub_right_comm, Nat.add_sub_assoc (Nat.le_refl _), Nat.add_assoc,
        ← Nat.add_sub_assoc (Nat.le_refl _), Nat.add_sub_cancel]
  . constructor
    . exact Nat.lt_of_succ_le h
    . rw [Nat.add_sub_assoc h, Nat.add_assoc, Nat.add_comm, Nat.add_assoc]
      nth_rw 1 [← Nat.add_zero b]
      exact Nat.add_le_add (Nat.le_refl _) (Nat.zero_le _)

private
theorem clog2_eq_clog2_shiftRight_add (s : ℕ) (b : 1 ≤ n >>> s) :
  Nat.clog 2 (n + 1) = Nat.clog 2 (n >>> s + 1) + s := by
  induction' s with s ih
  . rw [Nat.zero_eq, add_zero, Nat.shiftRight_zero]
  . have b' : 1 ≤ n >>> s := by
      show 1 ≤ Nat.shiftRight n s
      change 1 ≤ Nat.shiftRight n s.succ at b
      rw [Nat.shiftRight] at b
      apply Nat.le_trans
      . show 1 ≤ 2
        decide
      . show 1 * 2 ≤ _
        exact Nat.mul_le_of_le_div _ _ _ b
    have two_le : 2 ≤ n >>> s + 1 := by
      show 1 + 1 ≤ _
      exact Nat.add_le_add_right b' _
    rw [ih b', Nat.succ_eq_add_one, Nat.clog_of_two_le (by decide) two_le,
        Nat.shiftRight_add, Nat.shiftRight_eq_div_pow _ 1, Nat.pow_one,
        Nat.add_assoc _ 1 2, Nat.add_comm 1 2, ← Nat.add_assoc _ 2 1,
        Nat.add_sub_cancel, Nat.add_assoc _ 1 s,
        Nat.add_div_right _ (by decide), Nat.add_comm s 1, Nat.succ_eq_add_one]

private
theorem encCore_length_eq
  : (encCore n l).length = l.length + max 1 (Nat.clog 2 (n + 1) ⌈/⌉ 7) := by
  rw [encCore]
  split
  · case _ nle =>
    rw [List.length_reverse, List.length_cons]
    by_cases nzero : n = 0
    · have : ¬(1 < 2 ∧ 1 < 1) := by
        rintro ⟨_, _⟩
        contradiction
      rw [nzero, zero_add, Nat.clog, dif_neg this, Nat.ceilDiv_eq_add_pred_div,
          (by decide : (0 + 7 - 1) / 7 = 0), max_eq_left (by decide)]
    · have clog_pos := Nat.clog2_add_one_pos (Nat.zero_lt_of_ne_zero nzero)
      have clog_le : Nat.clog 2 (n + 1) ≤ 7 := by
        apply Nat.le_trans
        · show Nat.clog 2 (n + 1) ≤ Nat.clog 2 128
          apply Nat.clog_mono_right
          rw [Nat.add_one, (by decide : 128 = Nat.succ 127)]
          exact Nat.succ_le_succ nle
        · rw [(by decide : 128 = 2 ^ 7), Nat.clog_pow _ _ (by decide)]
      have : Nat.clog 2 (n + 1) ⌈/⌉ 7 = 1 := by
        rw [Nat.ceilDiv_eq_add_pred_div, add_comm,
            Nat.add_sub_assoc (Nat.succ_le_of_lt clog_pos) _,
            Nat.add_div_left _ (by decide),
            (Nat.div_eq_zero_iff (by decide)).mpr]
        apply Nat.sub_one_lt_of_le clog_pos clog_le
      rw [this, max_self]
  · case _ h =>
    push_neg at h
    unfold_let
    rw [encCore_length_eq, List.length_cons, ← Nat.add_one, Nat.add_assoc,
        add_comm (a := 1)]
    apply (add_right_inj l.length).mpr
    have shift_pos : 0 < n >>> 7 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_pos
      · show 128 ≤ n
        apply h
      · decide
    have clog_shift_pos := Nat.clog2_add_one_pos (n := n >>> 7) shift_pos
    have clog_pos := by
      apply Nat.clog2_add_one_pos
      push_neg at h
      apply Nat.lt_trans
      · show 0 < 127
        decide
      · exact h
    have one_le_clog : 1 ≤ Nat.clog 2 (n + 1) ⌈/⌉ 7 := by
      rw [Nat.ceilDiv_eq_add_pred_div,  add_comm,
          Nat.add_sub_assoc (Nat.succ_le_of_lt clog_pos) _,
          Nat.add_div_left _ (by decide), ← Nat.add_one]
      exact Nat.le_add_left 1 _
    have one_le_clog_shift : 1 ≤ Nat.clog 2 (n >>> 7 + 1) ⌈/⌉ 7 := by
      rw [Nat.ceilDiv_eq_add_pred_div,  add_comm,
          Nat.add_sub_assoc (Nat.succ_le_of_lt clog_shift_pos) _,
          Nat.add_div_left _ (by decide), ← Nat.add_one]
      exact Nat.le_add_left 1 _
    calc
      max 1 (Nat.clog 2 (n >>> 7 + 1) ⌈/⌉ 7) + 1 =
        Nat.clog 2 (n >>> 7 + 1) ⌈/⌉ 7 + 1 := by
        rw [Nat.max_eq_right one_le_clog_shift]
      _ = Nat.clog 2 (n + 1) ⌈/⌉ 7 := by
        rw [← divCeil_add_self _ _ (by decide),
            ← clog2_eq_clog2_shiftRight_add 7]
        exact shift_pos
      _ = max 1 (Nat.clog 2 (n + 1) ⌈/⌉ 7) := by
        rw [Nat.max_eq_right one_le_clog]
termination_by n
decreasing_by
  all_goals simp_wf
  apply shiftRight7_lt_self
  apply Nat.lt_trans (m := 127)
  · decide
  · apply Nat.lt_of_not_le
    assumption

theorem encUvarint_length_eq
  : (encUvarint n).length = max 1 (Nat.clog 2 (n + 1) ⌈/⌉ 7) := by
  rw [encUvarint, ← zero_add (max _ _), ← List.length_nil]
  exact encCore_length_eq

theorem encVarint_length_eq
  : (encVarint n).length = max 1 (Nat.clog 2 (intToVarintEncNat n + 1) ⌈/⌉ 7)
  := by rw [encVarint]; exact encUvarint_length_eq

theorem encUvarint8_length_eq
  : (encUvarint8 n).length = max 1 (Nat.clog 2 (n.toNat + 1) ⌈/⌉ 7)
  := by rw [encUvarint8]; apply encUvarint_length_eq

theorem encUvarint16_length_eq
  : (encUvarint16 n).length = max 1 (Nat.clog 2 (n.toNat + 1) ⌈/⌉ 7)
  := by rw [encUvarint16]; apply encUvarint_length_eq

theorem encUvarint32_length_eq
  : (encUvarint32 n).length = max 1 (Nat.clog 2 (n.toNat + 1) ⌈/⌉ 7)
  := by rw [encUvarint32]; apply encUvarint_length_eq

theorem encUvarint64_length_eq
  : (encUvarint64 n).length = max 1 (Nat.clog 2 (n.toNat + 1) ⌈/⌉ 7)
  := by rw [encUvarint64]; apply encUvarint_length_eq

private
theorem length_pos_of_length_eq_max_one {f : α → List UInt8}
  (h : (f n).length = max 1 a) : 0 < (f n).length := by
  rw [h]
  apply Nat.lt_of_lt_of_le
  · show 0 < 1
    decide
  · exact le_max_left _ _

theorem encUvarint_length_pos : 0 < (encUvarint n).length :=
  length_pos_of_length_eq_max_one encUvarint_length_eq

theorem encVarint_length_pos : 0 < (encVarint n).length :=
  length_pos_of_length_eq_max_one encVarint_length_eq

theorem encUvarint8_length_pos : 0 < (encUvarint8 n).length :=
  length_pos_of_length_eq_max_one encUvarint8_length_eq

theorem encUvarint16_length_pos : 0 < (encUvarint16 n).length :=
  length_pos_of_length_eq_max_one encUvarint16_length_eq

theorem encUvarint32_length_pos : 0 < (encUvarint32 n).length :=
  length_pos_of_length_eq_max_one encUvarint32_length_eq

theorem encUvarint64_length_pos : 0 < (encUvarint64 n).length :=
  length_pos_of_length_eq_max_one encUvarint64_length_eq

private
theorem length_le_of_eq_bound_of_bound_size_eq {f : α → List UInt8} (size : ℕ)
  (toNat : α → ℕ) (bound_pos : 0 < bound) (toNat_n_lt_bound : toNat n < size)
  (eq_bound : (f n).length = max 1 (Nat.clog 2 (toNat n + 1) ⌈/⌉ 7))
  (bound_size_eq : Nat.clog 2 size ⌈/⌉ 7 = bound)
  : (f n).length ≤ bound := by
  apply Nat.le_trans
  · exact Nat.le_of_eq eq_bound
  · apply max_le
    · exact bound_pos
    · rw [← bound_size_eq, Nat.ceilDiv_eq_add_pred_div,
          Nat.ceilDiv_eq_add_pred_div]
      apply Nat.div_le_div_right
      apply Nat.sub_le_sub_right
      apply Nat.add_le_add_right
      apply Nat.clog_mono_right
      apply Nat.succ_le_of_lt
      exact toNat_n_lt_bound

-- TODO: Maybe upstream to mathlib this since `Nat.clog_pow` seems to take
-- forever for some reason?
private
theorem clog_pow (b x : ℕ) (hb : 1 < b) : Nat.clog b (b ^ x) = x := by
  by_cases h : x = 0
  · rw [h]
    rw [Nat.pow_zero, Nat.clog_one_right]
  · rw [Nat.clog, dif_pos (⟨hb, Nat.one_lt_pow h hb⟩), letFun,
        Nat.add_sub_assoc (Nat.le_of_lt hb) (b ^ x),
        Nat.add_div (Nat.le_of_lt hb), if_neg (by
          push_neg
          rw [Nat.mod_eq_zero_of_dvd (dvd_pow_self b h), Nat.zero_add]
          exact Nat.mod_lt _ (Nat.lt_of_succ_lt hb)
        ), add_zero]
    nth_rw 3 [← Nat.pow_one b]
    rw [Nat.pow_div (Nat.zero_lt_of_ne_zero h) (Nat.lt_of_succ_lt hb),
        (Nat.div_eq_zero_iff (Nat.lt_of_succ_lt hb)).mpr
          (Nat.sub_lt_self Nat.one_pos (Nat.le_of_lt hb)), add_zero,
        clog_pow _ _ hb, Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero h)]
termination_by x
decreasing_by
  all_goals simp_wf
  exact Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.one_pos

theorem encUvarint8_length_le : (encUvarint8 n).length ≤ 2 := by
  apply length_le_of_eq_bound_of_bound_size_eq UInt8.size UInt8.toNat
    Nat.two_pos n.val.isLt encUvarint8_length_eq
  rw [Nat.ceilDiv_eq_add_pred_div, (by decide : UInt8.size = 2 ^ 8),
      clog_pow _ 8 Nat.one_lt_two]

theorem encUvarint16_length_le : (encUvarint16 n).length ≤ 3 := by
  apply length_le_of_eq_bound_of_bound_size_eq UInt16.size UInt16.toNat
    (by decide) n.val.isLt encUvarint16_length_eq
  rw [Nat.ceilDiv_eq_add_pred_div, (by decide : UInt16.size = 2 ^ 16),
      clog_pow _ 16 Nat.one_lt_two]

theorem encUvarint32_length_le : (encUvarint32 n).length ≤ 5 := by
  apply length_le_of_eq_bound_of_bound_size_eq UInt32.size UInt32.toNat
    (by decide) n.val.isLt encUvarint32_length_eq
  rw [Nat.ceilDiv_eq_add_pred_div, (by decide : UInt32.size = 2 ^ 32),
      clog_pow _ 32 Nat.one_lt_two]

theorem encUvarint64_length_le : (encUvarint64 n).length ≤ 10 := by
  apply length_le_of_eq_bound_of_bound_size_eq UInt64.size UInt64.toNat
    (by decide) n.val.isLt encUvarint64_length_eq
  rw [Nat.ceilDiv_eq_add_pred_div, (by decide : UInt64.size = 2 ^ 64),
      clog_pow _ 64 Nat.one_lt_two]

private
theorem shiftRight_shiftLeft (n s : ℕ) : (n >>> s) <<< s + n % (2 ^ s) = n :=
  by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.div_add_mod']

private
theorem shiftLeft_right_distrib {a b s : ℕ}
  : (a + b) <<< s = a <<< s + b <<< s := by
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.right_distrib]

private
theorem UInt8.ne_of_val_ne {a b : UInt8} (h : a.val ≠ b.val) : a ≠ b :=
  fun h' ↦ absurd (UInt8.val_eq_of_eq h') h

private
theorem UInt8.ofNatCore_eq_ofNat
  : ∀ h : n < UInt8.size, UInt8.ofNatCore n h = UInt8.ofNat n := by
  intro h
  rw [UInt8.ofNatCore, UInt8.ofNat, Fin.ofNat]
  simp only [Nat.mod_eq_of_lt h]

private
theorem decCore_unbounded_right_inv_encCore (first : Bool := true)
  : decCore (encCore n [] ++ l) shift acc (first := first) =
    ok (n <<< shift + acc, l) := by
  have and_128_lt {a : ℕ} : a &&& 2 ^ 7 < 2 ^ 8 :=
    Nat.and_lt_two_pow _ (by decide)
  rw [decCore, encCore]
  by_cases n ≤ 127
  · case _ nle =>
    rw [dif_pos nle, List.reverse_singleton, List.singleton_append]
    simp only
    have nlt : n < 2 ^ 7 := by
      show n < 128
      exact Nat.lt_succ_of_le nle
    have : UInt8.ofNat n &&& 128 = 0 := by
      dsimp only [UInt8.ofNatCore, HAnd.hAnd, AndOp.and, UInt8.land, Fin.land]
      rw [Nat.mod_eq_of_lt (by decide : 128 < 255 + 1)]
      apply UInt8.eq_of_val_eq
      apply Fin.eq_of_val_eq
      simp only
      show (n % 256 &&& 2 ^ 7) % 2 ^ 8 = 0
      rw [Nat.mod_eq_of_lt and_128_lt,
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt nle (by decide)),
          Nat.and_two_pow, Nat.testBit_lt_two_pow nlt, Bool.toNat_false,
          Nat.zero_mul]
    rw [UInt8.ofNatCore_eq_ofNat, if_pos this,
        (by decide : (127 : UInt8) = 2 ^ 7 - 1)]
    dsimp only [UInt8.ofNatCore, (· &&& ·), AndOp.and, UInt8.land, Fin.land]
    have : Nat.land n ↑((2 : UInt8) ^ 7 - 1).val = n := by
      show n &&& (2 ^ 7 - 1) = n
      rw [Nat.and_pow_two_is_mod, Nat.mod_eq_of_lt nlt]
    simp only [this,
               Nat.mod_eq_of_lt (Nat.lt_trans nlt (by decide : _ < UInt8.size)),
               UInt8.toNat]
  · case _ ltn =>
    rw [dif_neg ltn]
    simp only
    push_neg at ltn
    rw [← List.nil_append [_], encCore_append_acc_eq (xs := []),
        List.reverse_singleton, List.singleton_append, List.cons_append]
    simp only [Stream.next?]
    have : UInt8.ofNat (n &&& 127 ||| 128) &&& 128 ≠ 0 := by
      dsimp only [UInt8.ofNatCore, HAnd.hAnd, AndOp.and, UInt8.land, Fin.land]
      apply UInt8.ne_of_val_ne
      apply Fin.ne_of_val_ne
      rw [Nat.mod_eq_of_lt (by decide : 128 < 255 + 1)]
      show ((n &&& 127 ||| 2 ^ 7) % 2 ^ 8 &&& 2 ^ 7) % 2 ^ 8 ≠ 0
      rw [Nat.mod_eq_of_lt and_128_lt, Nat.and_two_pow,
          Nat.mod_eq_of_lt
            (Nat.or_lt_two_pow (Nat.and_lt_two_pow _ (by decide)) (by decide)),
          Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true]
      decide
    rw [UInt8.ofNatCore_eq_ofNat, if_neg this]
    have : UInt8.toNat (UInt8.ofNat (n &&& 127 ||| 128) &&& 127) =
      n &&& 127 := by
      dsimp only [UInt8.toNat, UInt8.ofNatCore, HAnd.hAnd, AndOp.and,
                  UInt8.land, Fin.land, HOr.hOr, OrOp.or, UInt8.lor, Fin.lor]
      rw [Nat.mod_eq_of_lt (by decide : 127 < 255 + 1)]
      show ((n &&& 127 ||| (2 ^ 7 * 1)) % 2 ^ 8 &&& 2 ^ 7 - 1) % 2 ^ 8 =
        n &&& 127
      have and_127_lt {a : ℕ} : a &&& 127 < 2 ^ 7 :=
        Nat.and_lt_two_pow _ (by decide)
      have add_and_127_lt : 2 ^ 7 + (n &&& 127) < 2 ^ 8 := by
        apply Nat.lt_of_lt_of_le
        · show _ < 2 ^ 7 + 2 ^ 7
          apply Nat.add_lt_add_left
          apply Nat.and_lt_two_pow
          decide
        · show 2 ^ 8 ≤ _
          exact Nat.le_refl _
      rw [Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (by decide)),
          Nat.and_pow_two_is_mod, Nat.lor_comm,
          ← Nat.mul_add_lt_is_or and_127_lt _, Nat.mul_one,
          Nat.mod_eq_of_lt (b := 2 ^ 8) add_and_127_lt, Nat.add_mod_left,
          Nat.mod_eq_of_lt and_127_lt]
    rw [this, decCore_unbounded_right_inv_encCore (first := false),
        Nat.add_comm shift 7, Nat.shiftLeft_add, ← Nat.add_assoc,
        ← shiftLeft_right_distrib, (by decide : 127 = 2 ^ 7 - 1),
        Nat.and_pow_two_is_mod, shiftRight_shiftLeft]
termination_by n
decreasing_by
  all_goals simp_wf
  apply shiftRight7_lt_self
  apply Nat.lt_trans (m := 127)
  · decide
  · apply Nat.lt_of_not_le
    assumption

private
theorem decCore_bounded_right_inv_encCore (bound : ℕ)
  (acc_inBound : acc < bound) (res_inBound : n <<< shift + acc < bound)
  (first : Bool := true) : decCore (encCore n [] ++ l) shift acc
    (Output.bounded bound acc_inBound) first =
    ok (⟨n <<< shift + acc, res_inBound⟩, l) := by
  have and_128_lt {a : ℕ} : a &&& 2 ^ 7 < 2 ^ 8 :=
    Nat.and_lt_two_pow _ (by decide)
  rw [decCore, encCore]
  by_cases n ≤ 127
  · case _ nle =>
    rw [dif_pos nle, List.reverse_singleton, List.singleton_append]
    simp only
    have nlt : n < 2 ^ 7 := by
      show n < 128
      exact Nat.lt_succ_of_le nle
    have : UInt8.ofNat n &&& 128 = 0 := by
      dsimp only [UInt8.ofNatCore, HAnd.hAnd, AndOp.and, UInt8.land, Fin.land]
      rw [Nat.mod_eq_of_lt (by decide : 128 < 255 + 1)]
      apply UInt8.eq_of_val_eq
      apply Fin.eq_of_val_eq
      simp only
      show (n % 256 &&& 2 ^ 7) % 2 ^ 8 = 0
      rw [Nat.mod_eq_of_lt and_128_lt,
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt nle (by decide)),
          Nat.and_two_pow, Nat.testBit_lt_two_pow nlt, Bool.toNat_false,
          Nat.zero_mul]
    rw [UInt8.ofNatCore_eq_ofNat, if_pos this,
        (by decide : (127 : UInt8) = 2 ^ 7 - 1)]
    dsimp only [UInt8.ofNatCore, (· &&& ·), AndOp.and, UInt8.land, Fin.land]
    have : Nat.land n ↑((2 : UInt8) ^ 7 - 1).val = n := by
      show n &&& (2 ^ 7 - 1) = n
      rw [Nat.and_pow_two_is_mod, Nat.mod_eq_of_lt nlt]
    simp only [this,
               Nat.mod_eq_of_lt (Nat.lt_trans nlt (by decide : _ < UInt8.size)),
               UInt8.toNat]
    rw [dif_pos res_inBound] -- bounded-specific
  · case _ ltn =>
    rw [dif_neg ltn]
    simp only
    push_neg at ltn
    rw [← List.nil_append [_], encCore_append_acc_eq (xs := []),
        List.reverse_singleton, List.singleton_append, List.cons_append]
    simp only [Stream.next?]
    have : UInt8.ofNat (n &&& 127 ||| 128) &&& 128 ≠ 0 := by
      dsimp only [UInt8.ofNatCore, HAnd.hAnd, AndOp.and, UInt8.land, Fin.land]
      apply UInt8.ne_of_val_ne
      apply Fin.ne_of_val_ne
      rw [Nat.mod_eq_of_lt (by decide : 128 < 255 + 1)]
      show ((n &&& 127 ||| 2 ^ 7) % 2 ^ 8 &&& 2 ^ 7) % 2 ^ 8 ≠ 0
      rw [Nat.mod_eq_of_lt and_128_lt, Nat.and_two_pow,
          Nat.mod_eq_of_lt
            (Nat.or_lt_two_pow (Nat.and_lt_two_pow _ (by decide)) (by decide)),
          Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true]
      decide
    rw [UInt8.ofNatCore_eq_ofNat, if_neg this]
    have eq_and_127 : UInt8.toNat (UInt8.ofNat (n &&& 127 ||| 128) &&& 127) =
      n &&& 127 := by
      dsimp only [UInt8.toNat, UInt8.ofNatCore, HAnd.hAnd, AndOp.and,
                  UInt8.land, Fin.land, HOr.hOr, OrOp.or, UInt8.lor, Fin.lor]
      rw [Nat.mod_eq_of_lt (by decide : 127 < 255 + 1)]
      show ((n &&& 127 ||| (2 ^ 7 * 1)) % 2 ^ 8 &&& 2 ^ 7 - 1) % 2 ^ 8 =
        n &&& 127
      have and_127_lt {a : ℕ} : a &&& 127 < 2 ^ 7 :=
        Nat.and_lt_two_pow _ (by decide)
      have add_and_127_lt : 2 ^ 7 + (n &&& 127) < 2 ^ 8 := by
        apply Nat.lt_of_lt_of_le
        · show _ < 2 ^ 7 + 2 ^ 7
          apply Nat.add_lt_add_left
          apply Nat.and_lt_two_pow
          decide
        · show 2 ^ 8 ≤ _
          exact Nat.le_refl _
      rw [Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (by decide)),
          Nat.and_pow_two_is_mod, Nat.lor_comm,
          ← Nat.mul_add_lt_is_or and_127_lt _, Nat.mul_one,
          Nat.mod_eq_of_lt (b := 2 ^ 8) add_and_127_lt, Nat.add_mod_left,
          Nat.mod_eq_of_lt and_127_lt]
    -- bounded-specific
    have and_127_inBound : ¬(n &&& 127) <<< shift + acc ≥ bound := by
      push_neg
      apply Nat.lt_of_le_of_lt
      · show _ ≤ n <<< shift + acc
        apply Nat.add_le_add_iff_right.mpr
        rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
        apply Nat.mul_le_mul_right
        show n &&& 2 ^ 7 - 1 ≤ n
        rw [Nat.and_pow_two_is_mod]
        exact Nat.mod_le _ _
      · exact res_inBound
    have res'_eq_res : n >>> 7 <<< (shift + 7) + ((n &&& 127) <<< shift + acc) =
      n <<< shift + acc := by
      rw [Nat.add_comm shift 7, Nat.shiftLeft_add, ← Nat.add_assoc,
          ← shiftLeft_right_distrib, (by decide : 127 = 2 ^ 7 - 1),
          Nat.and_pow_two_is_mod, shiftRight_shiftLeft n 7]
    rw [eq_and_127, dif_neg and_127_inBound,
        decCore_bounded_right_inv_encCore (first := false), Except.ok.injEq,
        Prod.mk.injEq, PSigma.mk.injEq]
    · constructor
      · constructor
        · exact res'_eq_res
        · congr!
      · rfl
    · rwa [res'_eq_res]
termination_by n
decreasing_by
  all_goals simp_wf
  apply shiftRight7_lt_self
  apply Nat.lt_trans (m := 127)
  · decide
  · apply Nat.lt_of_not_le
    assumption

theorem encUvarint_right_inv_decUvarint
  : decUvarint (encUvarint n ++ l) = ok (n, l) := by
  rw [decUvarint, encUvarint, decCore_unbounded_right_inv_encCore, Nat.add_zero,
      Nat.shiftLeft_zero]

theorem encVarint_right_inv_decVarint
  : decVarint (encVarint i ++ l) = ok (i, l) := by
  rw [decVarint, encVarint, encUvarint, decCore_unbounded_right_inv_encCore,
      Except.map, Nat.add_zero, Nat.shiftLeft_zero]
  show ok (_, _) = ok _
  rw [intToVarintEncNat_RightInverse_varintEncNatToInt]

theorem encUvarint8_right_inv_decUvarint8
  : decUvarint8 (encUvarint8 n ++ l) = ok (n, l) := by
  rw [decUvarint8, encUvarint8, encUvarint]
  unfold_let
  rw [decCore_bounded_right_inv_encCore UInt8.size (by decide)]
  rfl

theorem encUvarint16_right_inv_decUvarint16
  : decUvarint16 (encUvarint16 n ++ l) = ok (n, l) := by
  rw [decUvarint16, encUvarint16, encUvarint]
  unfold_let
  rw [decCore_bounded_right_inv_encCore UInt16.size (by decide)]
  rfl

theorem encUvarint32_right_inv_decUvarint32
  : decUvarint32 (encUvarint32 n ++ l) = ok (n, l) := by
  rw [decUvarint32, encUvarint32, encUvarint]
  unfold_let
  rw [decCore_bounded_right_inv_encCore UInt32.size (by decide)]
  rfl

theorem encUvarint64_right_inv_decUvarint64
  : decUvarint64 (encUvarint64 n ++ l) = ok (n, l) := by
  rw [decUvarint64, encUvarint64, encUvarint]
  unfold_let
  rw [decCore_bounded_right_inv_encCore UInt64.size (by decide)]
  rfl

end Protobuf.Varint
