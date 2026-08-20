/-
# The fixed-shell coefficient law as a probability measure

Normalizing the pushforward of the sphere measure gives a probability law on the coefficient space.
It has positive finite total mass because the sphere measure of the whole sphere is the dimension
times the volume of the unit ball, and scaling commutes with pushforward, so the normalized law
inherits the signed-permutation invariance.

Main results:
* `shellCoefficientMeasure_univ_pos`, `shellCoefficientMeasure_univ_ne_top` — the total mass.
* `shellProbability` — **the fixed-shell coefficient probability law**.
* `measurePreserving_signedPerm_shellProbability` — **it is invariant under signed permutations**.
-/
import GaloisForLFunctions.HTGeometry.ShellCoefficientMeasure

open MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem shellCoefficientMeasure_univ (ι : Type*) [Fintype ι] :
    shellCoefficientMeasure ι Set.univ
      = (volume : Measure (EuclideanSpace ℝ ι)).toSphere Set.univ := by
  rw [shellCoefficientMeasure, Measure.map_apply measurable_shellCoefficientMap
    MeasurableSet.univ, Set.preimage_univ]

theorem shellCoefficientMeasure_univ_ne_top (ι : Type*) [Fintype ι] :
    shellCoefficientMeasure ι Set.univ ≠ ⊤ := by
  rw [shellCoefficientMeasure_univ, Measure.toSphere_apply_univ]
  exact (ENNReal.mul_lt_top (by simp) measure_ball_lt_top).ne

theorem shellCoefficientMeasure_univ_pos (ι : Type*) [Fintype ι] [Nonempty ι] :
    0 < shellCoefficientMeasure ι Set.univ := by
  rw [shellCoefficientMeasure_univ, Measure.toSphere_apply_univ]
  refine ENNReal.mul_pos ?_ (measure_ball_pos _ _ one_pos).ne'
  have hpos : 0 < Module.finrank ℝ (EuclideanSpace ℝ ι) := Module.finrank_pos
  exact_mod_cast hpos.ne'

/-- **The fixed-shell coefficient probability law.** -/
def shellProbability (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  (shellCoefficientMeasure ι Set.univ)⁻¹ • shellCoefficientMeasure ι

instance isProbabilityMeasure_shellProbability [Nonempty ι] :
    IsProbabilityMeasure (shellProbability ι) := by
  constructor
  rw [shellProbability, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (shellCoefficientMeasure_univ_pos ι).ne'
    (shellCoefficientMeasure_univ_ne_top ι)

/-- **The fixed-shell probability law is invariant under every signed permutation.** -/
theorem measurePreserving_signedPerm_shellProbability (π : Equiv.Perm ι) {ε : ι → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    MeasurePreserving (fun J : ι → ℝ => fun i => ε i * J (π i))
      (shellProbability ι) (shellProbability ι) := by
  have hbase := measurePreserving_signedPerm_shell π hε
  refine ⟨hbase.measurable, ?_⟩
  rw [shellProbability, Measure.map_smul, hbase.map_eq]

end

end GaloisForLFunctions.HTGeometry
