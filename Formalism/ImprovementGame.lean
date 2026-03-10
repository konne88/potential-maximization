import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.DeriveFintype
import Init.Data.Fin.Lemmas

import Formalism.Focus
import Formalism.Potential
import Formalism.Stability
import Formalism.GeneralTheorems

namespace Improve

inductive Game where
| improve
| reward
deriving Nonempty, Fintype

open Game

structure State where
  reward : ℝ
  rewardRate : ℝ

def Kind := Bool

def evolve (u:Kind -> State) (a:Kind -> Game) (x:Kind) : State :=
  match a x with
  | reward => { reward := (u x).reward * (u x).rewardRate,
                   rewardRate := (u x).rewardRate }
  | improve => { reward := (u x).reward,
                 rewardRate := (u x).rewardRate + 0.1 }

instance : Universe where
  Kind := Bool
  State := Kind -> State
  Action _ _ := Game
  startState _ := { reward := 1,
                    rewardRate := 2 }
  t := evolve
  stepCount u := sorry
  rewardNonNegative u x := sorry
  stepCountOk := sorry

  kindFinite := inferInstance
  kindDecEq := inferInstance
  actionFinite _ _ := inferInstance
  actionNonEmpty _ _ := inferInstance
  r u x := (u x).reward

-- theorem noBestStrategy [Focus] s : ¬(∀ n, rewardMaximizing s n) := by
--   intro h'
--   sorry

open Actions

def improvements [Focus] {u} {n} (as:Actions n u) : Nat :=
  match as with
  | nil => 0
  | cons a as => (match a with | improve => 1 | _ => 0) + improvements as

def reproductions [Focus] {u} {n} (as:Actions n u) : Nat :=
  match as with
  | nil => 0
  | cons a as => (match a with | reward => 1 | _ => 0) + reproductions as

open FocusedUniverse

lemma exponentSequence [Focus] {n u} (as:Actions n u) :
  ∃ e : Nat -> Nat,   -- it's really (Fin (improvements as) -> Nat)
    reproductions as = ∑ i ∈ Finset.range (improvements as), e i ∧
    r (run' as) =
      ∏ i ∈ Finset.range (improvements as), (2 + 0.1 * (i : ℝ)) ^ e i :=
by
  sorry

open Actions

def breakpointActions [Focus] {u} (n:Nat) (b:Nat) : Actions n u :=
  match n with
  | n+1 => let a := if b > 0 then improve else reward
           cons a (breakpointActions n (b-1))
  | 0 => nil

def maximizingBreakpoint [Focus] (n:Nat) (u:Universe.State) : Nat :=
  sorry

-- lemma maximizingBreakpointOk [Focus] n (u:Universe.State) :
--   rewardMaximizing' n u (breakpointActions n (maximizingBreakpoint n u)) :=
-- by
--   sorry

lemma breakpointsIncrease [Focus] n n' u :
  n ≤ n' -> maximizingBreakpoint n u ≤ maximizingBreakpoint n' u :=
by
  sorry

instance : Horizon := {
  horizon := sorry
  horizonNonZero := sorry
  horizonOk := sorry
  horizonMonotonicallyIncreasing := sorry
}

instance : EconomiesOfScale := {
  economiesOfScale := sorry
}

def potentialMaximizingStrategyExistsInImprovementGame :=
  potentialMaximizingStrategyExists

def potentialMaximizationIsStableInImprovementGame :=
  potentialMaximizationIsStable

end Improve
