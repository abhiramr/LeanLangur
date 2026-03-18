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
  | nil : ValidProgram 0 []
  /-- If a program is valid with a certain stack size, then it is also valid with a larger stack size -/
  | tail  {p : Program} :
      ValidProgram n p →
      ValidProgram (n + 1) p
  /-- If the first instruction is a push and the rest of the program is valid  with stack size `s + 1` then the program is valid with stack size `s` -/
  | push  {p : Program} :
      ValidProgram (n + 1) p →
      ValidProgram n (Instr.push n :: p)
  /-- If the first instruction is an add and the rest of the program is valid with stack size `s + 2` then the program is valid with stack size `s + 1` -/
  | add {s : Stack} {p : Program} :
      ValidProgram (n + 1) p →
      ValidProgram (n + 2) (Instr.add :: p)
  /-- If the first instruction is a pop and the rest of the program is valid with stack size `s` then the program is valid with stack size `s + 1` -/
  | pop {s : Stack} {p : Program} :
      ValidProgram n p →
      ValidProgram (n + 1) (Instr.pop :: p)

@[simp]
theorem valid_program_push (k: Nat) (h : ValidProgram k (Instr.push a :: p')) : ValidProgram (k + 1) p' := by
  cases h
  · rename_i k h₂
    have ih := valid_program_push k h₂
    exact .tail ih
  · assumption


@[simp]
theorem invalid_program_add_zero: ¬ ValidProgram 0 (Instr.add :: p')  := by
  intro h
  cases h

@[simp]
theorem invalid_program_add_one: ¬ ValidProgram 1 (Instr.add :: p')  := by
  intro h
  cases p:h
  · rename_i h₂
    simp at h₂



@[simp]
theorem valid_program_add (k: Nat) (h : ValidProgram (k + 2) (Instr.add :: p')) : ValidProgram (k + 1) p' := by
  cases h
  · rename_i h₂
    match k with
    | 0 =>
      simp at h₂
    | k' + 1 =>
      have ih := valid_program_add k' h₂
      exact .tail ih
  · assumption

@[simp]
theorem invalid_program_pop_zero: ¬ ValidProgram 0 (Instr.pop :: p')  := by
  intro h
  cases p:h

@[simp]
theorem valid_program_pop (k: Nat) (h : ValidProgram (k +1) (Instr.pop :: p')) : ValidProgram k p' := by
  cases p:h
  · rename_i h₂
    cases k with
    | zero =>
      simp at h₂
    | succ k' =>
       have ih := valid_program_pop k' h₂
       exact .tail ih
  · assumption

def evaluate (p: Program) (s: Stack) (h: ValidProgram s.length p) : Stack :=
  match p with
  | [] => s
  | Instr.push n :: p' =>
      evaluate p' (n :: s) (valid_program_push s.length h)
  | Instr.add :: p' =>
      match s with
      | x :: y :: zs =>
        evaluate p' ((x + y) :: zs) (by
          apply valid_program_add _ h)
      | [x] => by
        simp at h
  | Instr.pop :: p' =>
      match s with
      | [] => by
        simp at h
      | x :: ys => evaluate p' ys (by
        apply valid_program_pop _ h)


end stack_machine
