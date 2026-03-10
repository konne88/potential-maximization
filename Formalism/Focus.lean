import Formalism.Universe

section OpenUniverse
open Universe

class Focus [Universe] where
  x : Kind
  ss : OtherStrategies x

def sub [Universe] (x : Universe.Kind) (ss : OtherStrategies x) (s : Strategy x) : Strategies := by
  -- Basically: fun x' => if (x == x') then s else ss x'
  intro x'
  cases (@inferInstance (DecidableEq Universe.Kind)) x x' with
  | isTrue h => rewrite [<- h];  exact s
  | isFalse h => exact (ss x' h)

class FocusedUniverse where
  State : Type
  Action : State -> Type

  startState : State
  t u : Action u -> State  -- transition
  r : State -> ℝ           -- reward

  stepCount : State -> ℕ
  stepCountOk u a : stepCount (t u a) = 1 + stepCount u
  rewardNonNegative u : 0 ≤ r u
  actionFinite u : Fintype (@Action u)
  actionNonEmpty u : Nonempty (@Action u)

def FocusedStrategy [FocusedUniverse] := (u:FocusedUniverse.State) -> FocusedUniverse.Action u

open Focus

def focusedEvolve [Universe] (x:Kind) (ss:OtherStrategies x) (u:State) (a:Action u x) : State := by
  refine (t u (fun x' => ?_))
  -- Basically: if (x == x') then a else ss x' u
  cases (@inferInstance (DecidableEq Kind)) x x' with
  | isTrue h => rewrite [<- h]; exact a
  | isFalse h => refine (ss x' h u)

instance [Universe] [Focus] : FocusedUniverse where
  State := State
  Action u := Action u x
  startState := startState
  t := focusedEvolve x ss
  r u := r u x
  stepCount := stepCount
  stepCountOk u a := sorry -- stepCountOk u sorry
  rewardNonNegative u := rewardNonNegative u x
  actionFinite u := actionFinite u x
  actionNonEmpty u := actionNonEmpty u x

end OpenUniverse

-- Helpers & Lemmas

section OpenFocusedUniverse
open FocusedUniverse

def t' [FocusedUniverse] (s:FocusedStrategy) (n:Nat) (u:State) : State :=
  match n with
  | 0 => u
  | n + 1 => t' s n (t u (s u))

def run'' [FocusedUniverse] (s:FocusedStrategy) (n:Nat) : State :=
  match n with
  | 0 => startState
  | n + 1 => let u := run'' s n
             t u (s u)

def combine [Universe] {x} (ss:OtherStrategies x) (s:Strategy x) : Strategies :=
  sorry  -- sub x ss s

lemma runStrategyOk [Universe] [Focus] {s:FocusedStrategy} {n:Nat} :
  t' s n startState = run (combine (Focus.ss) s) n :=
by
  sorry

def cast' [Universe] {x} (ss:Strategies) : OtherStrategies x :=
  fun x _ => ss x

lemma subEq [Universe] x ss s : (sub x ss s) x = s := by
  sorry   -- trivial

lemma completeCast [Universe] ss x :(combine (cast' ss) (ss x)) = ss :=
  by sorry

lemma castComplete [Universe] x (ss:OtherStrategies x) s : (cast' (combine ss s)) = ss :=
  by sorry

end OpenFocusedUniverse
