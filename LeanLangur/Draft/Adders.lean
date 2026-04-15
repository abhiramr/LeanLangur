namespace langur

#eval 3 + 4

#eval "Hello, " ++ "world!"

#eval [1, 2, 3] ++ [4, 5]

#synth Add Nat

open Add

#eval add 3 7


#check add

/--
error: failed to synthesize instance of type class
  Add String

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval add "Hello, " "world!"

instance : Add String where
  add x y := x ++ " " ++ y

#eval add "Hello," "world!"

/--
error: failed to synthesize instance of type class
  Add (?m.12 × ?m.14)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval add (3, 4) (5, 6)

instance {α β : Type} [Add α ][Add β] : Add (α × β) where
  add := fun (a, b) (c, d) ↦ (a + c, b + d)

#eval (3, 4) + (5, 6)

#eval (3, 4, 5) + (6, 7, 8)

set_option pp.all true in
#synth Add (Nat × Nat × String)

instance : HAdd α (List α) (List α) where
  hAdd x xs := x :: xs

#eval 3 + [4, 5]


end langur
