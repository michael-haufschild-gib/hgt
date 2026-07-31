import GaloisForLFunctions.RHTower.BlaschkeLocalizedSurvivalRecurrenceLaw
import GaloisForLFunctions.RHTower.SummableWeightedInfinitePhaseQuantile

/-!
# Blaschke-localized countable early-recurrence quantile

This file identifies finite-head water entropy exactly with integrated
Blaschke spectral depth and substitutes that identity into the complete
countable early-hit estimate.

Thus the probability cost of returning the infinite Blaschke-localized
packet is controlled by its exact local spectral-depth geometry.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- An active positive weight contributes exactly its excess logarithmic
water depth. -/
theorem log_max_one_exp_mul_eq_of_depth_le
    {p L : ℝ} (hp : 0 < p) (hdepth : -Real.log p ≤ L) :
    Real.log (max 1 (Real.exp L * p)) = L + Real.log p := by
  have hnonneg : 0 ≤ L + Real.log p := by linarith
  have hexp : Real.exp L * p = Real.exp (L + Real.log p) := by
    rw [Real.exp_add, Real.exp_log hp]
  rw [hexp, max_eq_right (Real.one_le_exp_iff.mpr hnonneg),
    Real.log_exp]

/-- Exact identification of active-head water entropy with integrated
Blaschke spectral depth. -/
theorem blaschkeActiveHeadWaterEntropy_eq
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {L : ℝ}
    (hLtail : blaschkeSpectralOffset a ≤ L)
    (hLzero : blaschkeSpectralSlope a ≤ L) :
    (1 / 2 : ℝ) *
        ∑ i : Fin (blaschkeActiveTailRadius a L + 2),
          Real.log (max 1
            (Real.exp L * blaschkeLocalizedWeight a i)) =
      blaschkeDepthWaterEntropy a L := by
  let R : ℕ := blaschkeActiveTailRadius a L
  have horigin :
      Real.log (max 1
          (Real.exp L * blaschkeLocalizedWeight a 0)) =
        L - blaschkeSpectralSlope a := by
    have hpositive : 0 < blaschkeLocalizedWeight a 0 := by
      rw [blaschkeLocalizedWeight_zero]
      positivity
    have hdepth :
        -Real.log (blaschkeLocalizedWeight a 0) ≤ L := by
      simpa only [blaschkeLocalizedWeight_zero,
        blaschkeSpectralSlope] using hLzero
    rw [log_max_one_exp_mul_eq_of_depth_le hpositive hdepth,
      blaschkeLocalizedWeight_zero, blaschkeSpectralSlope]
    ring
  have htail : ∀ i : Fin (R + 1),
      Real.log (max 1
          (Real.exp L * blaschkeLocalizedWeight a i.succ)) =
        L - blaschkeSpectralDepth a i := by
    intro i
    have hpositive :
        0 < blaschkeLocalizedWeight a (i + 1) :=
      blaschkeLocalizedWeight_succ_pos a ha0 ha1 i
    have hactive : (i : ℕ) ≤ blaschkeActiveTailRadius a L := by
      simpa only [R] using i.is_le
    have hdepth :
        blaschkeSpectralDepth a i ≤ L :=
      (blaschkeSpectralDepth_le_iff_le_activeTailRadius
        a ha0 ha1 hLtail i).2 hactive
    rw [show (i.succ : ℕ) = (i : ℕ) + 1 by rfl,
      log_max_one_exp_mul_eq_of_depth_le hpositive]
    · rw [blaschkeSpectralDepth]
      ring
    · simpa only [blaschkeSpectralDepth] using hdepth
  change (1 / 2 : ℝ) *
      ∑ i : Fin ((R + 1) + 1),
        Real.log (max 1
          (Real.exp L * blaschkeLocalizedWeight a i)) =
    blaschkeDepthWaterEntropy a L
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero]
  rw [horigin]
  simp_rw [htail]
  rw [Fin.sum_univ_eq_sum_range
    (fun n : ℕ => L - blaschkeSpectralDepth a n) (R + 1)]
  rw [blaschkeDepthWaterEntropy, blaschkeFiniteDepthEntropy]
  simp only [R]
  ring

/--
Exact Blaschke early-hit estimate. The full countable recurrence event pays
the exact integrated Blaschke spectral depth of the active head.
-/
theorem
    measureReal_countableTorusWeightedCoherenceHitUnion_blaschke_le
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (N : ℕ) {η L : ℝ}
    (hLtail : blaschkeSpectralOffset a ≤ L)
    (hLzero : blaschkeSpectralSlope a ≤ L)
    (hη1 :
      η / summableWeightedHeadMass
        (blaschkeLocalizedWeight a)
        (blaschkeActiveTailRadius a L + 2) ≤ 1)
    (hwater :
      1 ≤ summableWeightedHeadMass
        (blaschkeLocalizedWeight a)
        (blaschkeActiveTailRadius a L + 2) * Real.exp L)
    (ν : Measure (ℕ → UnitAddCircle)) [IsFiniteMeasure ν] (B : NNReal)
    (hhead :
      Measure.map
          (countableTorusHead (blaschkeActiveTailRadius a L + 2)) ν ≤
        B • volume) :
    ν.real
        (countableTorusWeightedCoherenceHitUnion
          (blaschkeLocalizedWeight a) N η) ≤
      (B : ℝ) * ((N : ℝ) *
        (((blaschkeActiveTailRadius a L + 2 : ℕ) : ℝ) *
          Real.exp (
            (Real.pi / 4) * (Real.exp L * η) -
              blaschkeDepthWaterEntropy a L +
              (1 / 2 : ℝ) *
                Real.log
                  (summableWeightedHeadMass
                    (blaschkeLocalizedWeight a)
                    (blaschkeActiveTailRadius a L + 2) *
                      Real.exp L)))) := by
  let M : ℕ := blaschkeActiveTailRadius a L + 2
  have hM : 1 ≤ M := by
    dsimp only [M]
    omega
  have hmass :
      0 < summableWeightedHeadMass (blaschkeLocalizedWeight a) M :=
    summableWeightedHeadMass_blaschkeLocalizedWeight_pos
      a ha0 ha1 M hM
  have hbase :=
    measureReal_countableTorusWeightedCoherenceHitUnion_originalHeadEntropy_le
      (blaschkeLocalizedWeight a)
      (fun k => sq_nonneg (blaschkeLocalizedKernel a k))
      (blaschkeLocalizedKernel_sq_summable a ha0 ha1)
      (blaschkeLocalizedWeight_tsum a ha0 ha1)
      M N hmass hη1 hwater ν B hhead
  have hentropy :=
    blaschkeActiveHeadWaterEntropy_eq
      a ha0 ha1 hLtail hLzero
  simpa only [M, hentropy] using hbase

end RHTower
