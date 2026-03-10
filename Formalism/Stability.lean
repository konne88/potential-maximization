import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

import Formalism.Metric

section Open
open FocusedUniverse
open FocusedMetric
open Focus

class GreedilyMaximizableMetric [Universe] [Metric] where
  greedilyMaximizableMetric :
    ∀ x ss, let _ : Focus := {x := x, ss := ss}
      ∀ (s: FocusedStrategy),
        (∀ u a, m (t u (s u)) ≥ m (t u a)) ->
        (∀ s' n u, m (t' s n u) ≥ m (t' s' n u))

open GreedilyMaximizableMetric

class EconomiesOfScale [Universe] [Metric] where
  economiesOfScale : ∀ n, ∃ c, c > 0 ∧ ∀ x ss,
--    (∑ x, metric x ss n) > 0 ->   TODO we might need this to prove c > 0
    metricMaximizingStrategyProp' x (cast' ss) (ss x) ->
    metric' x ss n = c * metric' x ss 0

open EconomiesOfScale

noncomputable def metricMaximizingAction [FocusedUniverse] [FocusedMetric] (u:State) : Action u := by
  refine (
    let _ := actionFinite u
    let a := Finset.univ.toList.argmax (fun a : Action u => m (t u a))
    match a with
    | some a => a
    | _ => ?_
  )
  sorry

lemma metricMaximizingActionOk [FocusedUniverse] [FocusedMetric] (u:State) :
  ∀ a, m (t u a) ≤ m (t u (metricMaximizingAction u)) :=
by
  sorry

@[simp]
noncomputable def metricMaximizingStrategy [FocusedUniverse] [FocusedMetric]: FocusedStrategy :=
  metricMaximizingAction

@[simp]
lemma metricMaximizingStrategyExists [Universe] [Metric] [GreedilyMaximizableMetric] :
  ∀ x ss, ∃ s, metricMaximizingStrategyProp' x ss s :=
by
  intros x ss
  have hg := greedilyMaximizableMetric
  refine (let hf : Focus := {x := x, ss := ss}; ?_)
  exists metricMaximizingStrategy
  simp
  intro n s'
  unfold metric'
  have hn := (hg x ss metricMaximizingStrategy ?_)
  . unfold m at hn
    unfold instFocusedMetricOfMetric at hn
    simp at hn
    specialize (hn s' n startState)
    repeat rewrite [runStrategyOk] at hn
    repeat rewrite [castComplete]
    exact hn
  . simp
    intros u a
    exact (metricMaximizingActionOk u a)

lemma metricMaximizationIsStable [Universe] [Metric] [EconomiesOfScale] [GreedilyMaximizableMetric] :
  ∀ x (ss:Strategies) n,
    (metricMaximizingStrategyProp' x (cast' ss) (ss x)) ->
  --  (∑ x, metric x ss 0) > 0 ->   TODO, not sure why this isn't needed, am I not dividing by 0?
    (∑ x, metric' x ss n) > 0 ->
    (metric' x ss 0) / (∑ x, metric' x ss 0) ≤ (metric' x ss n) / (∑ x, metric' x ss n) :=
by
  intro x ss n hs nzN
  have hf := economiesOfScale
  simp at hf
  specialize (hf n)
  cases hf with | intro c hf =>
  cases hf with | intro cNotNeg hf =>
  refine ((fun hf' => ?_) hf)
  specialize (hf x ss hs)
  rewrite [hf]; clear hf
  have he : (∀ x, (metric' x ss n) ≤ (c * metric' x ss 0)) := by {
    intro x'
    cases (metricMaximizingStrategyExists x' (cast' ss)) with | intro s hs =>
    specialize (hf' x' (combine (cast' ss) s) hs)
    unfold metricMaximizingStrategyProp' at hs
    specialize (hs n (ss x'))
    rewrite [completeCast ss x'] at hs
    have hm := (metricOk x' (cast' ss) s (ss x'))
    generalize (combine (cast' ss) s) = ss' at *
    rewrite [completeCast ss x'] at hm
    rewrite [<-hm]; clear hm
    rewrite [<-hf']; clear hf'
    exact hs
  }
  simp only [div_eq_mul_inv]
  rw [mul_comm c, mul_assoc]
  apply mul_le_mul_of_nonneg_left; swap; apply metricNotNeg'
  rw [← div_le_iff₀']; swap; assumption
  rw [div_eq_mul_inv, ← mul_inv]
  apply inv_anti₀; assumption
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x' _
  rw [mul_comm]
  apply he

end Open
