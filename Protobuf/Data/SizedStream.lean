/-
TODO: Make this more general if possible so it doesn't say the collection has a
specific size, just that it will eventually end, and that the amount of `drop`s
until it ends are strictly decreasing.
-/

class SizedStream (stream : Type u) (value : outParam (Type v))
  extends Stream stream value where
  size : stream → Nat
  size_dec : ∀ xs xs' : stream, next? xs = some (x, xs') → size xs' < size xs

instance : SizedStream (List α) α where
  size := List.length
  size_dec := by
    intro x xs xs' xseq
    dsimp [Stream.next?] at xseq
    cases xs
    . case _ => contradiction
    . case _ y ys =>
      simp at xseq
      rw [xseq.2]
      exact Nat.lt.base _
