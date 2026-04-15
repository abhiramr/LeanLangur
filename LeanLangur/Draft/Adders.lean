namespace langur

instance : HAdd α (List α) (List α) where
  hAdd x xs := x :: xs

#eval 3 + [4, 5]

instance {α β : Type} [HAdd α α α][HAdd β β β] : HAdd (α × β) (α × β) (α × β) where
  hAdd := fun (a, b) (c, d) ↦ (a + c, b + d)

#eval (3, 4) + (5, 6)

#eval (3, 4, 5) + (6, 7, 8)

end langur
