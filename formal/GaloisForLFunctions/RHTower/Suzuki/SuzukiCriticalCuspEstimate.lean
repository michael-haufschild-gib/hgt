import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalArithmeticVariation
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTailSummatoryErrorTransform

/-!
# A common error bound for all signed Suzuki cusps

Krein increments control the primary atom with the source's Lévy energy.
Compact testing controls the exact growing pole. Their sum bounds every
nonnegative translate and hence the complete finite arithmetic source.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators
open GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower
noncomputable section

/-- One signed cusp error, shared by every nonnegative translate in an aperture. -/
def suzukiCriticalCuspRadius (f : ℝ → ℝ) (omega A : ℝ) : ℝ :=
  Real.sqrt (2 * autocorr f 0 * suzukiCriticalPrimaryMass omega *
    suzukiCriticalPrimaryScale omega * omega * biScaleLevyEnergy f) +
  2 * omega * suzukiCriticalPrimaryMass omega * autocorr f 0 * A * Real.exp (A / 2)

/-- The growing polar branch has a finite bound after compact testing. -/
theorem abs_suzukiCriticalPoleCusp_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {A u omega : ℝ} (hA : 0 < A) (hu : 0 ≤ u)
    (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0) (homega : 0 < omega)
    (homega5 : omega < 5 / 2) :
    |suzukiCriticalPoleCusp f omega u| ≤
      suzukiCriticalPrimaryMass omega * autocorr f 0 * A * Real.exp (A / 2) := by
  rw [suzukiCriticalPoleCusp_eq_integral_primaryCusp hf hfc hA hu hcut homega homega5]
  have hb : ∀ s ∈ Ioo (0 : ℝ) A,
      ‖Real.exp ((1 / 2 - omega) * s) * suzukiCriticalPrimaryCusp f omega (u + s)‖ ≤
        Real.exp (A / 2) * (suzukiCriticalPrimaryMass omega * autocorr f 0) := by
    intro s hs
    have he : Real.exp ((1 / 2 - omega) * s) ≤ Real.exp (A / 2) := by
      apply Real.exp_le_exp.mpr
      have hws := mul_nonneg homega.le hs.1.le
      nlinarith only [hs.2, hws]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul he (abs_suzukiCriticalPrimaryCusp_le hf hfc homega homega5 _)
      (abs_nonneg _) (Real.exp_pos _).le
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (lt_of_le_of_lt (measure_mono Ioo_subset_Icc_self) isCompact_Icc.measure_lt_top) hb
  rw [Real.norm_eq_abs, Real.volume_real_Ioo_of_le hA.le, sub_zero] at hi
  exact hi.trans_eq (by ring)

/-- The primary and pole errors stay coupled in one translation-uniform bound. -/
theorem abs_suzukiCriticalSourceCusp_sub_mass_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {A u omega : ℝ} (hA : 0 < A) (hu : 0 ≤ u)
    (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0) (homega : 0 < omega)
    (homega2 : omega ≤ 2) :
    |suzukiCriticalSourceCusp f omega u - suzukiCriticalPrimaryMass omega * autocorr f u| ≤
      suzukiCriticalCuspRadius f omega A := by
  have hsq := suzukiCriticalPrimaryCusp_sub_mass_sq_le hf hfc homega homega2 u
  have hp : |suzukiCriticalPrimaryCusp f omega u -
      suzukiCriticalPrimaryMass omega * autocorr f u| ≤
      Real.sqrt (2 * autocorr f 0 * suzukiCriticalPrimaryMass omega *
        suzukiCriticalPrimaryScale omega * omega * biScaleLevyEnergy f) := by
    have hpos := Real.le_sqrt_of_sq_le hsq
    have hneg := Real.le_sqrt_of_sq_le
      (x := -(suzukiCriticalPrimaryCusp f omega u -
        suzukiCriticalPrimaryMass omega * autocorr f u))
      (by simpa only [neg_sq] using hsq)
    exact abs_le.mpr ⟨by linarith only [hneg], hpos⟩
  have hq := abs_suzukiCriticalPoleCusp_le hf hfc hA hu hcut homega (by linarith)
  rw [suzukiCriticalSourceCusp_eq hf hfc hA hu hcut homega (by linarith)]
  calc
    _ = |(suzukiCriticalPrimaryCusp f omega u -
        suzukiCriticalPrimaryMass omega * autocorr f u) - 2 * omega *
          suzukiCriticalPoleCusp f omega u| := by congr 1; ring
    _ ≤ |suzukiCriticalPrimaryCusp f omega u -
        suzukiCriticalPrimaryMass omega * autocorr f u| +
        |2 * omega * suzukiCriticalPoleCusp f omega u| := abs_sub _ _
    _ = |suzukiCriticalPrimaryCusp f omega u -
        suzukiCriticalPrimaryMass omega * autocorr f u| +
        (2 * omega) * |suzukiCriticalPoleCusp f omega u| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * omega)]
    _ ≤ _ := (add_le_add hp (mul_le_mul_of_nonneg_left hq (by positivity))).trans_eq (by
      unfold suzukiCriticalCuspRadius
      ring)

/-- The exact finite arithmetic head inherits the common signed cusp estimate. -/
theorem abs_suzukiCriticalSourcePairing_sub_mass_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {A omega : ℝ} (hA : 0 < A)
    (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0) (homega : 0 < omega)
    (homega2 : omega ≤ 2) :
    |suzukiCriticalSourcePairing f omega - suzukiCriticalPrimaryMass omega *
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp A⌋₊,
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) * autocorr f (Real.log n)| ≤
      (∑ n ∈ Finset.Icc 1 ⌊Real.exp A⌋₊,
        suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          suzukiCriticalCuspRadius f omega A := by
  rw [suzukiCriticalSourcePairing_eq_finite hf hfc hA hcut homega (by linarith),
    Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  have hc : 0 ≤ suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2) :=
    mul_nonneg (suzukiShiftedCoefficient_nonneg homega n) (Real.exp_pos _).le
  have hu : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
  have hb := abs_suzukiCriticalSourceCusp_sub_mass_le hf hfc hA hu hcut homega homega2
  calc
    _ = |(suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
        (suzukiCriticalSourceCusp f omega (Real.log n) -
          suzukiCriticalPrimaryMass omega * autocorr f (Real.log n))| := by congr 1; ring
    _ = _ := abs_mul _ _
    _ ≤ _ := by
      rw [abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left hb hc

end
end RHTower
