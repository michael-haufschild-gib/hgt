import GaloisForLFunctions.RHTower.ProjectiveWeightedHaarQuantileActiveSupport

/-!
# Bounded-density projective recurrence quantiles

Haar phase packets are not required for the finite-dimensional
early-recurrence estimate.  It is enough that the phase law be dominated by
a finite multiple of Haar measure.

This file proves:

* coordinatewise nonzero integer powers preserve Haar domination;
* Haar domination transfers directly to real set-measure bounds;
* the canonical weighted early-hit estimate acquires exactly the domination
  factor and no other loss.

The last theorem applies to correlated phase packets as well as independent
ones.  Independence is needed only when a concrete model is used to derive
the finite-head domination factor.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- A law on a finite torus dominated by `B` times Haar remains so after any
nonzero coordinatewise integer power map. -/
theorem map_zsmul_le_smul_volume_of_le
    {d : ℕ} (μ : Measure (Fin d → UnitAddCircle)) (B : ENNReal)
    (hμ : μ ≤ B • volume) (n : ℤ) (hn : n ≠ 0) :
    Measure.map (fun z : Fin d → UnitAddCircle => n • z) μ ≤
      B • volume := by
  have hpow := Measure.measurePreserving_zsmul
    (G := Fin d → UnitAddCircle) volume hn
  calc
    Measure.map (fun z : Fin d → UnitAddCircle => n • z) μ ≤
        Measure.map (fun z : Fin d → UnitAddCircle => n • z)
          (B • volume) :=
      Measure.map_mono hμ hpow.measurable
    _ = B • Measure.map (fun z : Fin d → UnitAddCircle => n • z)
          volume := Measure.map_smul B volume _
    _ = B • volume := by rw [hpow.map_eq]

/-- A finite Haar-domination bound transfers to the corresponding real
set-measure bound. -/
theorem measureReal_le_nnreal_mul_volumeReal_of_le
    {d : ℕ} (μ : Measure (Fin d → UnitAddCircle)) (B : NNReal)
    (hμ : μ ≤ B • volume) (s : Set (Fin d → UnitAddCircle)) :
    μ.real s ≤ (B : ℝ) * volume.real s := by
  calc
    μ.real s ≤ (B • volume).real s :=
      ENNReal.toReal_mono (by finiteness) (hμ s)
    _ = (B : ℝ) * volume.real s :=
      measureReal_nnreal_smul_apply B

/-- **Bounded-density early-recurrence quantile.**  If a finite phase law is
dominated by `B` times product Haar, then the probability of hitting the
weighted projective target during the first `N` clocks is bounded by `B`
times the exact canonical Haar water budget. -/
theorem
    measureReal_torusProjectiveWeightedCoherenceHitUnion_boundedDensity_le
    {d : ℕ} (w : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (N : ℕ) {η : ℝ} (hη1 : η ≤ 1)
    (μ : Measure (Fin d → UnitAddCircle)) (B : NNReal)
    (hμ : μ ≤ B • volume) :
    μ.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
      (B : ℝ) *
        ((N : ℝ) * projectiveCanonicalHaarWaterBudget w η) := by
  calc
    μ.real (torusProjectiveWeightedCoherenceHitUnion w N η) ≤
        (B : ℝ) * volume.real
          (torusProjectiveWeightedCoherenceHitUnion w N η) :=
      measureReal_le_nnreal_mul_volumeReal_of_le μ B hμ _
    _ ≤ (B : ℝ) *
        ((N : ℝ) * projectiveCanonicalHaarWaterBudget w η) :=
      mul_le_mul_of_nonneg_left
        (measureReal_torusProjectiveWeightedCoherenceHitUnion_canonicalHaarWater_le
          w hw hmass N hη1)
        B.2

end RHTower
