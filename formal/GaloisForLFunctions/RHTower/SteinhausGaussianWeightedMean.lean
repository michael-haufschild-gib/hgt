import GaloisForLFunctions.RHTower.SteinhausUniformWeightedMean
import GaloisForLFunctions.RHTower.HighBlockCutoffMonotone

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- The real weight of the original Gaussian-smoothed subcritical Dirichlet polynomial. -/
def steinhausGaussianWeight (β r : ℝ) (N n : ℕ) : ℝ :=
  (n : ℝ) ^ (-β) * (smoothAFECutoff (r * ((n : ℝ) / N))).re

theorem steinhausGaussianWeight_nonneg (β : ℝ) {r : ℝ} (hr : 0 < r)
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n) : 0 ≤ steinhausGaussianWeight β r N n := by
  have harg : 0 < r * ((n : ℝ) / N) := mul_pos hr
    (div_pos (by exact_mod_cast hn) (by exact_mod_cast hN))
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (smoothAFECutoff_re_nonneg harg)

theorem steinhausGaussianWeight_le_rpow (β : ℝ) {r : ℝ} (hr : 0 < r)
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    steinhausGaussianWeight β r N n ≤ (n : ℝ) ^ (-β) := by
  have harg : 0 < r * ((n : ℝ) / N) := mul_pos hr
    (div_pos (by exact_mod_cast hn) (by exact_mod_cast hN))
  simpa only [steinhausGaussianWeight, mul_one] using mul_le_mul_of_nonneg_left (smoothAFECutoff_re_le_one harg)
    (Real.rpow_nonneg (Nat.cast_nonneg n) (-β))

/-- Actual Gaussian weights decrease at every positive index, uniformly over all positive scales. -/
theorem steinhausGaussianWeight_succ_le {β : ℝ} (hβ : 0 ≤ β) {r : ℝ} (hr : 0 < r)
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    steinhausGaussianWeight β r N (n + 1) ≤ steinhausGaussianWeight β r N n := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hstep : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
  have harg := mul_pos hr (div_pos hnR hNR)
  have harg1 := mul_pos hr (div_pos hn1R hNR)
  have hargle : r * ((n : ℝ) / N) ≤ r * (((n + 1 : ℕ) : ℝ) / N) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hstep hNR.le) hr.le
  exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hnR hstep (neg_nonpos.mpr hβ))
    (smoothAFECutoff_re_antitoneOn harg harg1 hargle) (smoothAFECutoff_re_nonneg harg1)
    (Real.rpow_nonneg hnR.le _)

/-- The admissible real weight is exactly the original complex Gaussian coefficient. -/
theorem steinhausGaussianWeight_coe_eq (β : ℝ) {r : ℝ} (hr : 0 < r)
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    (steinhausGaussianWeight β r N n : ℂ) =
      (n : ℂ) ^ (-(β : ℂ)) * smoothAFECutoff (r * ((n : ℝ) / N)) := by
  have harg : 0 < r * ((n : ℝ) / N) := mul_pos hr
    (div_pos (by exact_mod_cast hn) (by exact_mod_cast hN))
  have hW : ((smoothAFECutoff (r * ((n : ℝ) / N))).re : ℂ) =
      smoothAFECutoff (r * ((n : ℝ) / N)) :=
    Complex.ext rfl (smoothAFECutoff_im_eq_zero harg).symm
  rw [steinhausGaussianWeight, Complex.ofReal_mul, hW,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg, Complex.ofReal_natCast]

/-- First-mean decay for the actual Gaussian-smoothed polynomial is uniform over every positive smoothing scale. -/
theorem eventually_integral_norm_steinhausGaussianSummatory_div_rpow_le
    {β : ℝ} (hβ : 0 < β) (hβhalf : β < 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℝ, 0 < r →
      (∫ ω, ‖∑ n ∈ Finset.Icc 1 N,
        (n : ℂ) ^ (-(β : ℂ)) * smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω‖
          ∂steinhausMeasure) / (N : ℝ) ^ (1 / 2 - β) ≤ δ := by
  filter_upwards [eventually_integral_norm_steinhausWeightedSummatory_div_rpow_le hβ hβhalf hδ,
    eventually_ge_atTop (1 : ℕ)] with N hmean hN
  intro r hr
  have h := hmean (steinhausGaussianWeight β r N)
    (fun n hn => steinhausGaussianWeight_nonneg β hr hN hn)
    (fun n hn => steinhausGaussianWeight_succ_le hβ.le hr hN hn)
    (fun n hn => steinhausGaussianWeight_le_rpow β hr hN hn)
  have hsum (ω : Omega) : (∑ n ∈ Finset.Icc 1 N, (steinhausGaussianWeight β r N n : ℂ) * X n ω) =
      ∑ n ∈ Finset.Icc 1 N,
        (n : ℂ) ^ (-(β : ℂ)) * smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [steinhausGaussianWeight_coe_eq β hr hN (Finset.mem_Icc.mp hn).1]
  simpa only [hsum] using h

end RHTower
