def smallestI (xs : List Nat) : Nat :=
  match xs with
  | [x] =>  x
  | x ::y ::zs =>
     min x (smallestI (y :: zs))
  | [] => 0

#eval smallestI [3, 1, 4, 1, 5, 9] -- should return some 1


-- Given a function and a hypothesis that the list is not empty, we can define the smallest function as follows:

def smallest (l: List Nat) (h: l ≠ []) : Nat :=
  match l with
  | x :: [] => x
  | x :: y :: zs =>
      min x (smallest (y :: zs) (by simp))

#eval smallest [3, 1, 4, 0, 5, 9] (by simp) -- should return some 1

theorem smallest_mem (l: List Nat) (h: l ≠ []) :
  smallest l h ∈ l := by
  fun_induction smallest <;> grind

theorem smallest_le_all (l: List Nat) (h: l ≠ []) (x: Nat) (hx: x ∈ l) :
  smallest l h ≤ x := by
  fun_induction smallest <;> grind


#eval smallest [3, 1, 4, 21, 0, 5, 9] (by simp) -- should return some 1

-- How do you check for negative numbers
