class NonAtom (α : Type) where
    firstAtom : α
    secondAtom : α
    firstNeqSecond : firstAtom ≠ secondAtom

def firstAtom (α : Type) [c: NonAtom α] : α := c.firstAtom
def secondAtom (α : Type) [c: NonAtom α] : α := c.secondAtom
theorem firstAtomNeqSecond (α : Type) [c: NonAtom α] : firstAtom α  ≠ secondAtom α := c.firstNeqSecond

instance : NonAtom Nat where
    firstAtom := 0
    secondAtom := 1
    firstNeqSecond := by decide

instance: NonAtom Bool where
    firstAtom := false
    secondAtom := true
    firstNeqSecond := by decide

instance [NonAtom α] : NonAtom (List α) where
    firstAtom := []
    secondAtom := [firstAtom α]
    firstNeqSecond := by simp

instance [Inhabited α] : NonAtom (Option α) where
    firstAtom := none
    secondAtom := some (default : α)
    firstNeqSecond := by simp

instance [NonAtom α] : NonAtom (α × α) where
    firstAtom := (firstAtom α, firstAtom α)
    secondAtom := (secondAtom α, secondAtom α)
    firstNeqSecond := by simp [firstAtomNeqSecond α]

instance [NonAtom α] : Inhabited α where
    default := firstAtom α

instance [NonAtom α] [Inhabited β] : NonAtom (α × β) where
    firstAtom := (firstAtom α, (default : β))
    secondAtom := (secondAtom α, (default : β))
    firstNeqSecond := by simp [firstAtomNeqSecond α]

instance [Inhabited α] [NonAtom β] : NonAtom (α × β) where
    firstAtom := ((default : α), firstAtom β)
    secondAtom := ((default : α), secondAtom β)
    firstNeqSecond := by simp [firstAtomNeqSecond β]

#eval firstAtom <| Nat × Unit

#eval secondAtom <| Nat × Nat
