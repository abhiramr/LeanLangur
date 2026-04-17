inductive MyBool where
  | True
  | False

def negate(p: MyBool): MyBool :=
  match p with
  | MyBool.True => MyBool.False
  | MyBool.False => MyBool.True

inductive KannadaBool where
  | Sari
  | Tappu

def negateKan(p: KannadaBool): KannadaBool :=
  match p with
  | KannadaBool.Sari => KannadaBool.Tappu
  | KannadaBool.Tappu => KannadaBool.Sari

#eval negateKan KannadaBool.Sari -- should return KannadaBool.Tappu
#eval negateKan KannadaBool.Tappu -- should return KannadaBool.Sari

#eval negate MyBool.True -- should return MyBool.False
#eval negate MyBool.False -- should return MyBool.True

-- Need to override + for KannadaBool


-- DEMorgan Laws



inductive
