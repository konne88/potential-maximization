import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

import Formalism.Metric
import Formalism.Stability
import Formalism.Actions

section OpenFocusedUniverse
open FocusedUniverse

noncomputable def potential [FocusedUniverse] (h:Nat) (u:State) : ℝ := by
  refine ((Finset.univ.image (fun as:Actions h u => r (run' as))).max' ?_)
  sorry

end OpenFocusedUniverse

section OpenUniverse
open Universe

noncomputable def potential' [Universe] (x:Kind) (ss:OtherStrategies x) (h:Nat) (u:State) : ℝ :=
  let _:Focus := {x := x, ss := ss}
  potential h u

end OpenUniverse


open Metric
open Actions
open FocusedUniverse

def potentialMaximizingActionProp' [FocusedUniverse] (h:Nat) (u:State) (a:Action u) : Prop :=
    ∀ a', potential h (t u a') ≤ potential h (t u a)

class Horizon [Universe] where
  horizon : Nat -> Nat
  horizonNonZero : 1 ≤ horizon
  horizonOk : ∀ x ss u a d,
    let _ : Focus := {x:=x, ss:= ss}
    let h :=  horizon (1 + stepCount u)
    potentialMaximizingActionProp' h u a ->
    potentialMaximizingActionProp' (h + d) u a
  horizonMonotonicallyIncreasing :
    ∀ n n', n ≤ n' -> horizon n ≤ horizon n'

open Horizon

class FocusedHorizon [FocusedUniverse] where
  h : Nat -> Nat
  horizonNonZero : 1 ≤ h
  horizonOk : ∀ u a d,
    let h :=  h (1 + stepCount u)
    potentialMaximizingActionProp' h u a ->
    potentialMaximizingActionProp' (h + d) u a
  horizonMonotonicallyIncreasing :
    ∀ n n', n ≤ n' -> h n ≤ h n'

open FocusedHorizon

instance [Universe] [Horizon] [Focus] : FocusedHorizon := {
  h := horizon
  horizonNonZero := horizonNonZero
  horizonOk := by
    apply Horizon.horizonOk
  horizonMonotonicallyIncreasing := by
    apply Horizon.horizonMonotonicallyIncreasing
}

noncomputable def p [FocusedUniverse] [FocusedHorizon] (u:State) : ℝ :=
by
  refine (potential (h (stepCount u)) u)

def h' [FocusedUniverse] [FocusedHorizon] (u:State): ℕ :=
   h (FocusedUniverse.stepCount u)

def h'' [FocusedUniverse] [FocusedHorizon] (n : Nat) (u:State): ℕ :=
   h (n + FocusedUniverse.stepCount u)

lemma potentialSpec [FocusedUniverse] [FocusedHorizon] :
  ∀ u (as' : Actions (h' u) u), r (runActions as') ≤ p u :=
by
  sorry

lemma potentialSpec' [FocusedUniverse] [FocusedHorizon] u :
  ∃ (as : Actions (h' u) u),
    p u  = r (t'' _ as) ∧
    ∀ (as' : Actions (h' u) u), r (t'' _ as') ≤ r (t'' _ as) :=
by
  sorry

lemma potentialSpec'' [FocusedUniverse] u h :
  ∃ (as : Actions h u),
    potential h u  = r (t'' _ as) ∧
    ∀ (as' : Actions h u), r (t'' _ as') ≤ r (t'' _ as) :=
by
  sorry

lemma simpRunActions [FocusedUniverse] s n n' u (as':Actions n' (t' s n u)) :
  ∃ as:Actions (n + n') u, t'' (t' s n u) as' = t'' u as :=
by
  sorry

lemma simpH' [FocusedUniverse] [FocusedHorizon] s n u : h' (t' s n u) = h'' n u :=
by
  sorry

lemma simpH'' [FocusedUniverse] [FocusedHorizon] u a : h' (t u a) = h'' 1 u :=
by
  sorry

def h''' [FocusedUniverse] [FocusedHorizon] n u := h'' n u

@[simp]
noncomputable def potential'' [Universe] [Horizon] x ss u :=
  let _ : Focus := {x:=x, ss:= ss}; p u

noncomputable def p' [Universe] [Horizon] (x:Universe.Kind) (ss:Strategies) (n:Nat) : ℝ :=
  potential'' x (cast' ss) (run ss n)

noncomputable instance potentialMetric [Universe] [Horizon] : Metric := {
  m := potential''
  metricNotNeg x ss u := by
    unfold potential''
    refine (let _ : Focus := {x:=x, ss:= ss}; ?_)
    have hp := (potentialSpec u)
    simp at hp
    -- TODO need proof that Actions is non-empty
    sorry
}

instance [Universe] [Horizon] : GreedilyMaximizableMetric := {
  greedilyMaximizableMetric := by
    simp
    intro x ss s hs s' n u

    unfold FocusedMetric.m at *
    unfold instFocusedMetricOfMetric at *
    simp at *
    unfold m at *
    unfold potentialMetric at *
    simp at *
    let _ : Focus := {x:=x, ss := ss}

    -- Rewrite the potentials into their definitions
    rcases (potentialSpec' (t' s n u)) with ⟨as, he, has⟩
    clear has; rewrite [he]; clear he
    rcases (potentialSpec' (t' s' n u)) with ⟨as'', he, has'⟩
    clear has'; rewrite [he]; clear he
    rcases (simpRunActions s' n _ _ as'') with ⟨as', hrw⟩
    rewrite [hrw]; clear hrw; clear as''

    -- Show that all the horizons, are the same
    refine ((fun hdone :
              ∀ (u : State),
              let h0 := h'' n u
              let h1 := h''' n u
              ∀ (as : Actions h0 (t' s n u)) (as' : Actions (n + h1) u),
                r (t'' u as') ≤ r (t'' (t' s n u) as) => ?_) ?_)
    . clear hs
      specialize (hdone u)
      have hsimp := simpH' s n u
      rewrite [<-hsimp] at hdone; clear hsimp
      specialize (hdone as)
      have hsimp := simpH' s' n u
      unfold h''' at hdone
      rewrite [<-hsimp] at hdone; clear hsimp
      specialize (hdone as')
      apply hdone
    . unfold h'''
      clear u as as'
      intro u
      show (let h := h'' n u;
            ∀ (as : Actions h (t' s n u)) (as' : Actions (n + h) u), _)
      intro h as as'

      -- Rewrite `horizonOk` assumption to be about action sequences
      have hok :
        ∀ (u:State) (n:Nat),
        let h := h'' (n + 1) u  -- the horizon, n + 1 steps from u
        ∃ as'' : Actions (n + h) (t u (s u)),
          ∀ (as':Actions (n + 1 + h) _),  -- (a': Action u)
            r (t'' u as') ≤ r (t'' (t u (s u)) as'') :=
      by {
        clear u as as' n h
        intro u n h
        -- the difference between the old and new horizon
        let d := n + h - h'' 1 u
        have hok := FocusedHorizon.horizonOk u (s u) d
        unfold potentialMaximizingActionProp' at hok
        specialize (hs u)
        unfold p at hs

        -- Adjust horizons
        have heq : ∀ a, FocusedHorizon.h (stepCount (t u a)) = h'' 1 u := by {
          intro a
          unfold h''
          rewrite [stepCountOk]
          eq_refl
        }
        conv at hs =>
          intro a
          rewrite [heq a]
          rewrite [heq (s u)]
        clear heq

        specialize (hok hs); clear hs

        rcases (potentialSpec'' (t u (s u)) (h'' 1 u + d)) with ⟨as, he, has⟩
        unfold h'' at he
        rewrite [he] at hok; clear he; clear has

        -- rewrite horizon
        unfold d at as
        let h0 := h'' 1 u + (n + h - h'' 1 u)
        change Actions h0 _ at as
        change ∀ a', _ ≤ r (t'' (n:=h0) _ _) at hok
        have hdeq : (h0 = n + h) := by {
          unfold h0
          have pos : h'' 1 u ≤ n + h := by {
            unfold h
            unfold h''
            refine ((fun mono => ?_)
              (FocusedHorizon.horizonMonotonicallyIncreasing (1 + stepCount u) (n + 1 + stepCount u) ?_)); swap
            . omega
            . omega
          }
          omega
        }
        revert as hok
        rewrite [hdeq]
        intro as hok

        exists as

        -- rewrite horizon
        intro as'
        let h1 := n + 1 + h
        change Actions h1 _ at as'
        show r (t'' (n:=h1) _ _) ≤ _
        have heq : (h1 = (n + h).succ) := by omega
        revert as'
        rewrite [heq]; clear heq
        intro as'
        cases (as') with | cons a' as' =>
        specialize (hok a')

        rcases (potentialSpec'' (t u a') (h'' 1 u + d)) with ⟨as'', he, has''⟩
        unfold h'' at he
        rewrite [he] at hok; clear he

        refine (le_trans ?_ hok); clear hok

        have heq : t'' u (cons a' as') = t'' (t u a') as' := by eq_refl
        rewrite [heq]; clear heq

        -- rewrite horizons
        let h0 := n + h
        change Actions h0 _ at as'
        show r (t'' (n:=h0) _ _) ≤ _
        revert h0 as'
        rewrite [<-hdeq]
        intro h0 as'

        apply (has'' as')
      }

      -- Induction on n
      revert as as' u h
      induction n with
      | zero =>
        sorry
      | succ n hrec =>
        intro u0 h as as'
        let u1 := t u0 (s u0)

        -- same as unfolding t', which doesn't work for some reason
        show r (t'' u0 as') ≤ r (t'' (t' s n (t u0 (s u0))) as)

        rcases (hok u0 n) with ⟨as'', hok⟩

        unfold h at as'
        specialize (hok as')
        specialize hrec u1
        have heq : h'' (n + 1) u0 = h'' n u1 := by {
          unfold u1
          unfold h''
          rewrite [stepCountOk]
          ac_rfl
        }
        rewrite [<-heq] at hrec
        specialize hrec as as''
        unfold t'' at *
        apply le_trans hok hrec
}
