import Mathlib.Topology.Instances.AddCircle.Real
import GaloisForLFunctions.HTGeometry.MetricEntropyRecurrenceAmplificationLaw

/-!
# Exact-period recurrence versus ambient complexity

An exactly one-periodic family can carry complexity controlled by the metric
entropy of its entire parameterized image, even though each individual motion
has only one clock frequency.  The clock fixes *when* the system returns; the
family parameter fixes *which* hard endpoint lies inside the cycle.

The headline theorem gives an exact quantitative recurrence bound: after every
real time, an easy point, a robustly hard point, and the easy point again occur
in strict order, with each leg no longer than one period.
-/

open Set Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- Every family obtained by reading a unit additive circle is exactly
one-periodic in real time. -/
theorem unitPeriodicFamily_period_one
    {P X : Type*} (embed : P → AddCircle (1 : ℝ) → X)
    (p : P) (t : ℝ) :
    embed p ((t + 1 : ℝ) : AddCircle (1 : ℝ)) =
      embed p (t : AddCircle (1 : ℝ)) := by
  rw [AddCircle.coe_add_period]

/-- **One-frequency/ambient-entropy separation law.** Let continuously
parameterized exactly periodic loops cover an ambient test set `A`.  If `A`
needs more radius-`ε` balls than a finite dictionary `C` contains, then one
loop contains a point farther than `ε` from every dictionary endpoint.

Moreover, after every starting time the selected loop visits an easy
neighborhood, then that hard point, then the easy neighborhood again, in
strict order.  Each leg is at most one exact period.  Thus recurrence period
and attainable circuit depth are independent invariants before a locality
constraint couples them. -/
theorem unitPeriodicFamily_coveringEntropy_easyHard_alternate
    {P X : Type*} [MetricSpace X]
    (embed : P → AddCircle (1 : ℝ) → X)
    {A C : Set X} (hcover : ∀ x ∈ A, ∃ p z, embed p z = x)
    (center : X)
    (hcenter : center ∈ C)
    (hbase : ∀ p, embed p (0 : AddCircle (1 : ℝ)) = center)
    (ε : ℝ≥0) (hε : 0 < ε)
    (hEntropy : C.encard < Metric.externalCoveringNumber ε A) :
    ∃ p : P, ∀ a : ℝ,
      ∃ tEasy ∈ Set.Icc a (a + 1),
      ∃ tHard ∈ Set.Ioc tEasy (tEasy + 1),
      ∃ tEasy' ∈ Set.Ioc tHard (tHard + 1),
        embed p (tEasy : AddCircle (1 : ℝ)) ∈
          interior (metricClosedBallTarget ε C) ∧
        (∀ c ∈ C,
          (ε : ℝ) < dist (embed p (tHard : AddCircle (1 : ℝ))) c) ∧
        embed p (tEasy' : AddCircle (1 : ℝ)) ∈
          interior (metricClosedBallTarget ε C) := by
  obtain ⟨x, hxA, hxhard⟩ :=
    exists_metricHardSeed_of_encard_lt_externalCoveringNumber hEntropy
  obtain ⟨p, seed, hpseed⟩ := hcover x hxA
  have heasy : embed p (0 : AddCircle (1 : ℝ)) ∈
      interior (metricClosedBallTarget ε C) := by
    rw [hbase p]
    exact mem_interior_metricClosedBallTarget hε hcenter
  refine ⟨p, fun a ↦ ?_⟩
  have hEasyRep : (0 : AddCircle (1 : ℝ)) ∈
      ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Icc a (a + 1) := by
    rw [AddCircle.coe_image_Icc_eq]
    exact Set.mem_univ _
  obtain ⟨tEasy, htEasy, htEasyZero⟩ := hEasyRep
  have hHardRep : seed ∈
      ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ioc tEasy (tEasy + 1) := by
    rw [AddCircle.coe_image_Ioc_eq]
    exact Set.mem_univ _
  obtain ⟨tHard, htHard, htHardSeed⟩ := hHardRep
  have hEasyRep' : (0 : AddCircle (1 : ℝ)) ∈
      ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ioc tHard (tHard + 1) := by
    rw [AddCircle.coe_image_Ioc_eq]
    exact Set.mem_univ _
  obtain ⟨tEasy', htEasy', htEasyZero'⟩ := hEasyRep'
  refine ⟨tEasy, htEasy, tHard, htHard, tEasy', htEasy', ?_, ?_, ?_⟩
  · simpa [htEasyZero] using heasy
  · intro c hc
    simpa [htHardSeed, hpseed] using hxhard c hc
  · simpa [htEasyZero'] using heasy

end GaloisForLFunctions.HTGeometry
