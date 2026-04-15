import Mathlib

variable {α : Type}[LinearOrder α]

inductive BinarySearchTree (α : Type) where
  | leaf : α → BinarySearchTree α
  | node : α → BinarySearchTree α → BinarySearchTree α → BinarySearchTree α
deriving Repr, Inhabited

open BinarySearchTree

@[grind ., simp]
def BinarySearchTree.mem {α : Type} : BinarySearchTree α → α → Prop
  | leaf x, y => x = y
  | node _ l r, y => BinarySearchTree.mem l y ∨ BinarySearchTree.mem r y

@[grind .]
instance {α : Type} : Membership α (BinarySearchTree α) where
  mem := BinarySearchTree.mem

@[grind ., simp]
theorem mem_leaf {α : Type} (x y : α) :
    y ∈ leaf x ↔ x = y := by
    simp [Membership.mem]

@[grind ., simp]
theorem mem_node {α : Type} (x: α) (l r : BinarySearchTree α) (y : α) :
    y ∈ node x l r ↔ y ∈ l ∨ y ∈ r := by
    simp [BinarySearchTree.mem, Membership.mem]


@[grind ., simp]
def IsOrdered : BinarySearchTree α → Prop
  | leaf _ => True
  | node v l r =>
    (∀ x ∈ l, x ≤ v) ∧ (∀ x ∈ r, v ≤ x) ∧ IsOrdered l ∧ IsOrdered r ∧ (v ∈ l ∨ v ∈ r)

@[grind .]
theorem IsOrdered_leaf (x: α) :
  IsOrdered (leaf x) := by
  simp [IsOrdered]

@[grind .]
theorem IsOrdered_left_below (v: α) (l r: BinarySearchTree α) (h: IsOrdered (node v l r)) :
  ∀ x ∈ l, x ≤ v := by
  grind

@[grind .]
theorem IsOrdered_right_above (v: α) (l r: BinarySearchTree α) (h: IsOrdered (node v l r)) :
  ∀ x ∈ r, v ≤ x := by grind

@[grind .]
theorem IsOrdered_left_subtree (v: α) (l r: BinarySearchTree α) (h: IsOrdered (node v l r)) :
  IsOrdered l := by
  grind

@[grind .]
theorem IsOrdered_right_subtree (v: α) (l r: BinarySearchTree α) (h: IsOrdered (node v l r)) :
  IsOrdered r := by
  grind

@[grind .]
def BinarySearchTree.addLabel (t: BinarySearchTree α) (label: α) : BinarySearchTree α :=
  match t with
  | leaf x =>
    if label = x then
      leaf x
    else
    if label < x then
      node label (leaf label) (leaf x)
    else
      node label (leaf x) (leaf label)
  | node v l r =>
    if label ≤ v then
      node v (BinarySearchTree.addLabel l label) r
    else
      node v l (BinarySearchTree.addLabel r label)

@[grind .]
theorem mem_addLabel (t: BinarySearchTree α) (label: α) (x : α) :
    x ∈ BinarySearchTree.addLabel t label ↔ x = label ∨ x ∈ t := by
  induction t with
  | leaf v =>
    by_cases label ≤ v <;> grind
  | node v l r ihl ihr =>
    by_cases label ≤ v <;> grind


theorem ordered_addLabel (t: BinarySearchTree α) (label: α)
  (h: IsOrdered t) :
    IsOrdered (BinarySearchTree.addLabel t label) := by
  induction t with
  | leaf x =>
    by_cases label ≤ x <;> grind
  | node v l r ihl ihr =>
    by_cases label ≤ v <;> grind

def pivot : BinarySearchTree α → α
| node l .. => l
| leaf l => l

@[grind .]
theorem pivot_member (l: BinarySearchTree α) (h₀ : IsOrdered l) :
  pivot l ∈ l := by
  induction l with
  | leaf l => grind [pivot]
  | node label left right ihl ihr =>
    grind [pivot]

@[grind .]
def fastCheckMem (label : α)(l: BinarySearchTree α) : Bool := match l with
  | leaf l => l == label
  | node l left right =>
    if l == label then true
    else if label < l then fastCheckMem label left
    else fastCheckMem label right

theorem fastCheckMem_correct (label : α)(l: BinarySearchTree α)(h : IsOrdered l):
  fastCheckMem label l = true ↔ label ∈ l := by
  induction l with
  | leaf label' =>
    grind
  | node label' left right ihl ihr =>
    if p:label' = label
      then
        grind
    else
      if p':label < label'
      then
        grind
      else
        grind
