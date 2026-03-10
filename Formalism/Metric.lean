import Formalism.Focus

class Metric [Universe] where
  m (x:Universe.Kind) (ss:OtherStrategies x) (u:Universe.State) : ℝ  -- metric
  metricNotNeg x ss u : 0 ≤ m x ss u

section OpenMetric
open Metric

class FocusedMetric [FocusedUniverse] where
  m : FocusedUniverse.State -> ℝ
  metricNotNeg u : 0 ≤ m u

instance [Universe] [Metric] [Focus] : FocusedMetric where
  m u := m Focus.x Focus.ss u
  metricNotNeg u := metricNotNeg Focus.x Focus.ss u

-- Helpers & Lemmas

def metric' [Universe] [Metric] (x:Universe.Kind) (ss:Strategies) (n:Nat) : ℝ :=
  m x (cast' ss) (run ss n)

lemma metricOk [Universe] [Metric] x (ss:OtherStrategies x) s s' :
    metric' x (combine ss s) 0 = metric' x (combine ss s') 0 :=
by
  unfold metric'
  unfold run
  repeat rewrite [castComplete]
  simp

lemma metricNotNeg' [Universe] [Metric] x ss n : 0 ≤ metric' x ss n :=
by
  unfold metric'
  apply metricNotNeg

@[simp]
def metricMaximizingStrategyProp' [Universe] [Metric] (x:Universe.Kind) (ss:OtherStrategies x) (s:Strategy x): Prop :=
  ∀ n s',
    metric' x (combine ss s') n ≤ metric' x (combine ss s) n

end OpenMetric
