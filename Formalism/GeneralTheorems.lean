import Formalism.Potential

section OpenUniverse
open Universe

-- TODO: should this take just ss, not s
def potentialMaximizingStrategy [Universe] [Horizon] (x:Kind) (ss:OtherStrategies x) (s:Strategy x) :=
  ∀ n s',
    p' x (combine ss s') n ≤ p' x (combine ss s) n

-- TODO: it seems having potentialIsGreedilyMaximizableMetric be a typeclass would be more uniform
theorem potentialMaximizingStrategyExists [Universe] [Horizon] :
  ∀ x ss, ∃ s, potentialMaximizingStrategy x ss s :=
by
  exact metricMaximizingStrategyExists

-- TODO: it seems having EconomiesOfScale be a typeclass would be more uniform
-- TODO: can we have real casts for ss
theorem potentialMaximizationIsStable [Universe] [Horizon] [EconomiesOfScale] :
  ∀ x (ss:Strategies) n,
    potentialMaximizingStrategy x (cast' ss) (ss x) ->
    (∑ x, p' x ss n) > 0 ->
    (p' x ss 0) / (∑ x, p' x ss 0) ≤ (p' x ss n) / (∑ x, p' x ss n) :=
by
  exact metricMaximizationIsStable




-- theorem potentialMaximizingStrategySurvives [Universe] [StabilityAssumptions] [SurvivalAssumptions] :
--   ∀ (x:Kind) (ss : OtherStrategies x) n,
--     let _:Focus := { x := x, ss := ss }
--     let u := run'' (potentialMaximizingStrategy horizon) n
--     (∑ x', reward u x') ≠ 0 -> reward u x ≠ 0 :=
-- by
--   sorry

-- def ubiquitous [Universe] (u:State) x :=
--   reward u x = ∑ x', reward u x'

-- theorem potentialMaximizingStrategyUbiquitousAfterChokepoint [Universe] [StabilityAssumptions] [SurvivalAssumptions] :
--   ∀ (x:Kind) (ss : OtherStrategies x) n,
--     let u := run (complete (potentialMaximizingStrategy' x ss horizon) ss) n
--     (∃ x', ubiquitous u x') ->    -- n is a choke point
--     ubiquitous u x :=
-- by
--   sorry
