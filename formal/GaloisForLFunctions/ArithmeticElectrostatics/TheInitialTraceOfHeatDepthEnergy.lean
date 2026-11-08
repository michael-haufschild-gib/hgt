import GaloisForLFunctions.ArithmeticElectrostatics.TheGlobalHeatDepthIsContinuous
import GaloisForLFunctions.RHTower.DeBruijnNewmanEnergyUnitTime
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit

/-!
# The initial trace of heat depth energy

The upper-half squared-depth energy has an exact initial trace: the sum of
squared upper depths of the original ξ divisor, possibly infinite. Heat
majorization gives the upper bound. Compact zero sums recover every finite
initial packet and prevent energy from disappearing at time zero.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics

/-- The squared upper depth of one initial multiplicity copy. -/
def xiUpperSquaredDepth (q : XiZeroCopy) : ℝ := (max (xiSpectralPoint q).im 0) ^ 2

/-- Upper-half heat energy. Its initial trace is taken from positive times;
the real-valued `tsum` at zero is not used when the initial series diverges. -/
def heatUpperDepthEnergy (t : ℝ) : ℝ :=
  heatWeightedZeroSum (fun z => (max z.im 0) ^ 2) t

private theorem upper_weight_zero_off_nonreal {t : ℝ} (ht : 0 ≤ t)
    (z : ℂ) (hz : ¬ (riemannHeat t z = 0 ∧ z.im ≠ 0)) :
    (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2 = 0 := by
  by_cases hf : riemannHeat t z = 0
  · have hi : z.im = 0 := by simpa only [hf, true_and, not_not] using hz
    rw [hi, max_self, zero_pow two_ne_zero, mul_zero]
  · rw [zeroMult_riemannHeat_eq_zero ht hf, Nat.cast_zero, zero_mul]

private theorem summable_upper_heat_weight {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℂ => (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2) := by
  classical
  apply summable_of_ne_finset_zero (s := (riemannHeat_nonreal_zeros_finite ht).toFinset)
  intro z hz
  exact upper_weight_zero_off_nonreal ht.le z (by simpa only [Set.Finite.mem_toFinset] using hz)

private theorem heatUpperDepthEnergy_eq_sum {t : ℝ} (ht : 0 < t) :
    heatUpperDepthEnergy t = ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
      (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2 := by
  classical
  apply tsum_eq_sum
  intro z hz
  exact upper_weight_zero_off_nonreal ht.le z (by simpa only [Set.Finite.mem_toFinset] using hz)

private theorem summable_compact_heat_weight {t : ℝ} (ht : 0 ≤ t)
    (Ψ : ℂ → ℝ) (R : ℝ) (hsupp : ∀ z, R ≤ ‖z‖ → Ψ z = 0) :
    Summable (fun z : ℂ => (zeroMult (riemannHeat t) z : ℝ) * Ψ z) := by
  have hfin := finite_zeros_closedBall
    (fun z (_ : z ∈ closedBall (0 : ℂ) R) => riemannHeat_analytic ht z (mem_univ z))
    (fun z _ h => analyticOrderAt_riemannHeat_ne_top ht z (analyticOrderAt_eq_top.mpr h))
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro z hz
  change (zeroMult (riemannHeat t) z : ℝ) * Ψ z ≠ 0 at hz
  have hf : riemannHeat t z = 0 := by
    by_contra hf
    exact hz (by rw [zeroMult_riemannHeat_eq_zero ht hf, Nat.cast_zero, zero_mul])
  have hn : ‖z‖ < R := lt_of_not_ge fun h => hz (by rw [hsupp z h, mul_zero])
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hn.le, hf⟩

/-- Initial finite sums control every positive-time upper energy with the same constant. -/
theorem heatUpperDepthEnergy_le_of_initial_sums {K : ℝ}
    (hK : ∀ T : Finset XiZeroCopy, ∑ q ∈ T, xiUpperSquaredDepth q ≤ K)
    {t : ℝ} (ht : 0 < t) : heatUpperDepthEnergy t ≤ K := by
  classical
  have hK0 : 0 ≤ K := by simpa only [Finset.sum_empty] using hK ∅
  rw [heatUpperDepthEnergy_eq_sum ht]
  by_cases ht1 : t ≤ 1
  · have hb (T : Finset XiZeroCopy) :
        ∑ q ∈ T.filter (fun q => 0 < (xiSpectralPoint q).im),
          max ((xiSpectralPoint q).im ^ 2 - 2 * t - 0) 0 ≤ K := by
      apply le_trans _ (hK T)
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro q _
      by_cases hq : 0 < (xiSpectralPoint q).im
      · rw [if_pos hq, xiUpperSquaredDepth, max_eq_left hq.le]
        exact max_le (by linarith only [ht]) (sq_nonneg _)
      · rw [if_neg hq]
        exact sq_nonneg _
    have h := riemannHeat_upper_energy_le_of_le_one ht ht1 (c := 0) le_rfl hb
      (riemannHeat_nonreal_zeros_finite ht).toFinset
    simpa only [sub_zero, max_eq_left (sq_nonneg _)] using h
  · have hz : ∀ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
        (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2 = 0 := by
      intro z hz
      have hf := (Set.Finite.mem_toFinset _).mp hz
      have hi := riemannHeat_zeros_real (show 1 / 8 ≤ t by linarith only [ht1]) hf.1
      rw [hi, max_self, zero_pow two_ne_zero, mul_zero]
    rw [Finset.sum_eq_zero hz]
    exact hK0

end GaloisForLFunctions.ArithmeticElectrostatics
