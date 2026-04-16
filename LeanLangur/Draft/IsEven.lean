import Mathlib

@[grind cases]
inductive IsEven : Nat → Prop
  | zeroEven : IsEven 0
  | addTwoEven (h : IsEven n) : IsEven (n + 2)

open IsEven

@[grind .]
theorem zero_even : IsEven 0 := by
  apply zeroEven

@[grind .]
theorem addTwo_even (n: Nat) (h: IsEven n) :
  IsEven (n + 2) := by
    apply addTwoEven
    assumption

theorem IsEven_two_mul (n : Nat) : IsEven (2 * n) := by
  induction n <;> grind

theorem succ_odd_of_isEven {n : Nat}
  (h : IsEven n) :
    ¬ IsEven (n + 1) := by
  induction h <;> grind

theorem nOrSuccNeven (n : Nat) : IsEven n ∨ IsEven (n + 1)
  := by
  induction n <;> grind
