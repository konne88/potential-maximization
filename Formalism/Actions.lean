import Formalism.Focus

section Open
open FocusedUniverse

inductive Actions [FocusedUniverse] : Nat -> State -> Type where
| nil {u} : Actions 0 u
| cons {n u} a : Actions n (t u a) -> Actions (n.succ) u

instance [FocusedUniverse] n u : Fintype (Actions n u) := sorry  -- trivial

def runActions [FocusedUniverse] {n:Nat} {u:State} (as:Actions n u) : State :=
  match as with
  | .nil => u
  | .cons _ as => runActions as

-- Helpers & Lemmas

def t'' [FocusedUniverse] {n:Nat} (u:State) (as:Actions n u) : State :=
  runActions as

def run' [FocusedUniverse] {n:Nat} {u:State} (as:Actions n u) : State :=
  match as with
  | .nil => u
  | .cons _ as => run' as


end Open
