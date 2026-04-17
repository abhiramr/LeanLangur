
#eval 3+4

#eval "hello" ++ "world"


open Add
#eval add 1 3

#check add -- Gives the type of add, which is Nat → Nat → Nat


#guard_msgs in
#eval add "Hello" "World"

instance : Add String where
  add s t := s ++ "  " ++ t

#eval add "Hello" "World" -- should return "Hello World"

#eval "Hello" + "world"


-- Type classes more

#eval (1, 2) + (3, 4) -- should return (4, 6)

instance {α β :Type}[Add α][Add β] :
 Add (α × β) where
 add := fun(a1, b1) (a2, b2) => (a1 + a2, b1 + b2)

 #eval (1, 2) + (3, 4) -- should return (4, 6)


---

#eval (1, 2, "Hello") + (3, 4, "World") -- should return (4, 6, "Hello World")
