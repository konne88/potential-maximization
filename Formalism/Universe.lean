import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.List.MinMax

class Universe where
  Kind : Type
  State : Type
  Action : State -> Kind -> Type

  startState : State
  t u : ((x:Kind) -> Action u x) -> State
  r : State -> Kind -> ℝ

  stepCount : State -> ℕ
  stepCountOk u as : stepCount (t u as) = 1 + stepCount u
  rewardNonNegative u x : 0 ≤ r u x
  kindFinite : Fintype Kind
  kindDecEq : DecidableEq Kind
  actionFinite u x : Fintype (@Action u x)
  actionNonEmpty u x : Nonempty (@Action u x)

section OpenUniverse
open Universe

instance [Universe] : Fintype (Kind) := kindFinite
instance [Universe] : DecidableEq Kind := kindDecEq
instance [Universe] u x : Fintype (Action u x) := actionFinite u x
instance [Universe] u x : Nonempty (Action u x) := actionNonEmpty u x

def Strategy [Universe] x := (u:State) -> Action u x
def Strategies [Universe] := (x:Kind) -> Strategy x
def OtherStrategies [Universe] x := (x':Kind) -> x ≠ x' -> Strategy x'

def run [Universe] (ss:Strategies) (n:Nat) : State :=
  match n with
  | 0 => startState
  | n + 1 => let u := run ss n
             t u (ss . u)

end OpenUniverse
