

-- List operations

def doubleList(α : Type) (l: List α): List α:=
  l ++ l

#eval doubleList Nat [1, 2, 3] -- should return [1, 2, 3, 1, 2, 3]

#eval doubleList String ["a", "b"] -- should return ["a", "b", "a", "b"]



#guard_msgs in
#eval doubleList Nat _


def dblList {α: Type} (l: List α) : List α :=
  l ++ l

#eval dblList [1, 2, 3] -- should return [1, 2, 3, 1, 2, 3]


def pairs (α β : Type) (l1 : List α) (l2 : List β) : List (α × β) :=
  do
    let x ← l1
    let y ← l2
    return (x, y)
