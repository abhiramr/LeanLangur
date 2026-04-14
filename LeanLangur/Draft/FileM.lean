import Lean
open IO FS System

namespace file_access

inductive FileCmd : Type → Type where
| read  : FilePath → FileCmd String
| write : FilePath → String → FileCmd Unit

inductive FileM : Type → Type _ where
| pure {α : Type} : α → FileM α
| cons : FileCmd β → (k: β → FileM α) → FileM α

def FileM.flatMap {α β : Type} (f : α → FileM β) : FileM α → FileM β
  | .pure a => f a
  | .cons cmd k => .cons cmd (fun b => (k b).flatMap f)

instance : Monad FileM where
  pure := FileM.pure
  bind x f := FileM.flatMap f x

def FileM.read (path : FilePath) : FileM String :=
    .cons (FileCmd.read path) FileM.pure

def FileM.write (path : FilePath) (contents : String) : FileM Unit :=
    .cons (FileCmd.write path contents) FileM.pure

def FileM.run : FileM α → IO α
    | FileM.pure a => return a
    | FileM.cons cmd k =>
        match cmd with
        | FileCmd.read path => do
            let contents ← IO.FS.readFile path
            FileM.run (k contents)
        | FileCmd.write path contents => do
            IO.FS.writeFile path contents
            FileM.run (k ())

abbrev FileM.map {α β : Type} (f : α → β) : FileM α → FileM β := fun x => do
    let a ← x
    return f a

inductive SafeVal : {α : Type} → α → Prop where
| nat(n) : SafeVal (n : Nat)
| strAppend (s t : String) : SafeVal s → SafeVal t → SafeVal (s ++ t)
| space : SafeVal " "
| newline : SafeVal "\n"
| semicolon : SafeVal ";"
| padLeft (s : String) : SafeVal s → SafeVal (" " ++ s)
| padRight (s : String) : SafeVal s → SafeVal (s ++ " ")

theorem blocks (s t : String) (h1 : SafeVal s) (h2 : SafeVal t) : SafeVal (s ++ "\n" ++ t) := by
    apply SafeVal.strAppend (s ++ "\n")
    apply SafeVal.strAppend s
    assumption
    apply SafeVal.newline
    assumption

inductive SafePath : FilePath → Prop where
| pub (p : FilePath) : SafePath ("public" / p)
| data (p : FilePath) : SafePath ("data" / p)

inductive SafeProg  : {α : Type} →  FileM α → Prop where
| pureSafe (a : α) (h : SafeVal a) : SafeProg (FileM.pure a)
| readSafe (p : FilePath) (h : SafePath p) : SafeProg  (FileM.read p)
| writeSafe (p : FilePath) (h : SafePath p) (s : String) (h2 : SafeVal s) : SafeProg (FileM.write p s)
| bindSafe
    (x : FileM α)
    (h : SafeProg x)
    (f : α → FileM β)
    (h2 : ∀a, SafeVal a → SafeProg  (f a)) : SafeProg  (x >>= f)

def pubToData (p : FilePath) : FileM Unit := do
    let contents ← FileM.read ("public" / p)
    FileM.write ("data" / p) contents

theorem safe_pubToData (p : FilePath) : SafeProg (pubToData p) := by
    apply SafeProg.bindSafe
    . apply SafeProg.readSafe
      apply SafePath.pub
    . intro contents hContents
      apply SafeProg.writeSafe
      · apply SafePath.data
      · assumption

def mergePubs (p1 p2 out : FilePath) : FileM Unit := do
    let c1 ← FileM.read ("public" / p1)
    let c2 ← FileM.read ("public" / p2)
    let merged := c1 ++ "\n" ++ c2
    FileM.write ("data" / out) merged

theorem safe_mergePubs (p1 p2 out : FilePath) : SafeProg (mergePubs p1 p2 out) := by
    apply SafeProg.bindSafe
    . apply SafeProg.readSafe
      apply SafePath.pub
    . intro c1 hC1
      apply SafeProg.bindSafe
      . apply SafeProg.readSafe
        apply SafePath.pub
      . intro c2 hC2
        let merged := c1 ++ "\n" ++ c2
        have hMerged : SafeVal merged := blocks c1 c2 hC1 hC2
        apply SafeProg.writeSafe
        · apply SafePath.data
        · assumption

end file_access

#check bind_pure_comp
