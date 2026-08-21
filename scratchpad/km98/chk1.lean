import Mathlib

open MeasureTheory Metric Set

-- ball volume in Fin d → ℝ
example (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r) : True := by
  have := Real.volume_pi_ball a hr
  trivial

-- Besicovitch pieces
example (d : ℕ) : True := by
  have h1 := Besicovitch.multiplicity (Fin d → ℝ)
  have h2 := Besicovitch.one_lt_goodτ (Fin d → ℝ)
  have h3 := Besicovitch.isEmpty_satelliteConfig_multiplicity (Fin d → ℝ)
  have h4 := @Besicovitch.exist_disjoint_covering_families
  trivial

-- countability
example : True := by
  have := @Set.PairwiseDisjoint.countable_of_nonempty_interior
  trivial

-- measure preserving equivalences
example : True := by
  have h1 := @MeasureTheory.volume_preserving_piFinSuccAbove
  trivial

example : True := by
  have h1 := @MeasureTheory.volume_preserving_funUnique
  trivial

-- haar image linear map
example : True := by
  have := @MeasureTheory.Measure.addHaar_image_linearMap
  trivial
