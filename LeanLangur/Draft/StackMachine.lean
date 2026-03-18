namespace stack_machine

inductive Instr
  | push (n : Nat)
  | add
  | pop
  deriving Repr

abbrev Stack := List Nat

abbrev Program := List Instr

def eval? (p: Program) (s: Stack) : Option Stack :=
  match p with
  | [] => some s
  | Instr.push n :: p' => eval? p' (n :: s)
  | Instr.add :: p' =>
      match s with
      | x :: y :: zs => eval? p' ((x + y) :: zs)
      | _ => none
  | Instr.pop :: p' =>
      match s with
      | _ :: ys => eval? p' ys
      | _ => none

/-- Validity of a program -/
inductive ValidProgram : (initStackSize : Nat) → (p : Program) → Prop
  /-- The empty program is valid with an empty stack -/
  | nil : ValidProgram n []
  /-- If the first instruction is a push and the rest of the program is valid  with stack size `s + 1` then the program is valid with stack size `s` -/
  | push  {p : Program} :
      ValidProgram (n + 1) p →
      ValidProgram n (Instr.push k :: p)
  /-- If the first instruction is an add and the rest of the program is valid with stack size `s + 2` then the program is valid with stack size `s + 1` -/
  | add {p : Program} :
      ValidProgram (n + 1) p →
      ValidProgram (n + 2) (Instr.add :: p)
  /-- If the first instruction is a pop and the rest of the program is valid with stack size `s` then the program is valid with stack size `s + 1` -/
  | pop  {p : Program} :
      ValidProgram n p →
      ValidProgram (n + 1) (Instr.pop :: p)

@[simp, grind .]
theorem valid_program_nil : ValidProgram n [] := ValidProgram.nil

@[simp, grind .]
theorem valid_program_push (n: Nat) (h : ValidProgram (n + 1) p') :
    ValidProgram n (Instr.push k :: p') :=    ValidProgram.push h

@[simp, grind .]
theorem valid_program_add (k: Nat) (h : ValidProgram (k + 1) p') :
  ValidProgram (k + 2) (Instr.add :: p') :=
  ValidProgram.add h

@[simp]
theorem valid_program_pop (h : ValidProgram n p') :
  ValidProgram (n + 1) (Instr.pop :: p') :=
  ValidProgram.pop h

example (a b: Nat) : ValidProgram 0 [Instr.push a, Instr.push b, Instr.add] := by
  grind

example (a b c : Nat) : ValidProgram 0 [Instr.push a, Instr.push b, Instr.add, Instr.push c, Instr.add] := by
  grind (ematch := 7)

@[simp]
theorem valid_program_of_push (k: Nat) (h : ValidProgram k (Instr.push a :: p')) : ValidProgram (k + 1) p' := by
  cases h
  assumption


@[simp]
theorem invalid_program_add_zero: ¬ ValidProgram 0 (Instr.add :: p')  := by
  intro h
  cases h

@[simp]
theorem invalid_program_add_one: ¬ ValidProgram 1 (Instr.add :: p')  := by
  intro h
  cases h

@[simp]
theorem valid_program_of_add {k: Nat} (h : ValidProgram (k + 2) (Instr.add :: p')) : ValidProgram (k + 1) p' := by
  cases h
  assumption

@[simp]
theorem invalid_program_pop_zero: ¬ ValidProgram 0 (Instr.pop :: p')  := by
  intro h
  cases h

@[simp]
theorem valid_program_of_pop {k: Nat} (h : ValidProgram (k +1) (Instr.pop :: p')) : ValidProgram k p' := by
  cases h
  assumption

def evaluate (p: Program) (s: Stack) (h: ValidProgram s.length p) : Stack :=
  match p with
  | [] => s
  | Instr.push n :: p' =>
      evaluate p' (n :: s) (valid_program_of_push s.length h)
  | Instr.add :: p' =>
      match s with
      | x :: y :: zs =>
        evaluate p' ((x + y) :: zs) (valid_program_of_add h)
      | [x] => by
        simp at h
  | Instr.pop :: p' =>
      match s with
      | [] => by
        simp at h
      | x :: ys => evaluate p' ys (valid_program_of_pop h)


end stack_machine
