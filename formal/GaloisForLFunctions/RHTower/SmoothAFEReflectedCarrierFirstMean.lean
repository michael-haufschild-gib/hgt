import GaloisForLFunctions.RHTower.SteinhausGaussianPhaseMean
import GaloisForLFunctions.RHTower.SmoothAFEReflectedChannelUpper

open MeasureTheory Filter Complex
open scoped Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- The literal reflected carrier has exactly the untwisted Gaussian first mean times the chi norm. -/
theorem integral_norm_reflectedPrimalCarrier_eq (d tau r : ℝ) (N : ℕ) :
    (∫ ω, ‖∑ n ∈ Finset.Icc 1 N,
      smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N n * X n ω‖
        ∂steinhausMeasure) =
      ‖zetaChi (rightDisplacedLinePt d tau)‖ *
        (∫ ω, ‖∑ n ∈ Finset.Icc 1 N,
          (n : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ)) *
            smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω‖ ∂steinhausMeasure) := by
  have he : rightDisplacedLinePt d tau - 1 =
      -((1 / 2 - d : ℝ) : ℂ) - ((-tau : ℝ) : ℂ) * I := by
    unfold rightDisplacedLinePt
    push_cast
    ring
  have hsum (ω : Omega) : (∑ n ∈ Finset.Icc 1 N,
      smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N n * X n ω) =
      zetaChi (rightDisplacedLinePt d tau) *
        ∑ n ∈ Finset.Icc 1 N,
          (n : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ) - ((-tau : ℝ) : ℂ) * I) *
            smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [reflectedPrimalPositiveCoefficient_eq_power_cutoff _ _ _ _ (Finset.mem_Icc.mp hn).1, he]
    ring
  simp_rw [hsum, norm_mul]
  rw [integral_const_mul, integral_norm_steinhausGaussianSummatory_phase_eq]

/-- The original reflected AFE carrier vanishes in first mean, uniformly above the conductor and over all positive Gaussian scales. -/
theorem eventually_integral_norm_reflectedPrimalCarrier_le
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, (N : ℝ) ≤ tau → ∀ r : ℝ, 0 < r →
      (∫ ω, ‖∑ n ∈ Finset.Icc 1 N,
        smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N n * X n ω‖
          ∂steinhausMeasure) ≤ ε := by
  obtain ⟨C, hC, hchi⟩ := exists_norm_zetaChi_fixed_right_line_le_rpow hd hdhalf
  have hC1 : 0 < C + 1 := by linarith
  have hβ : 0 < 1 / 2 - d := by linarith
  have hβhalf : 1 / 2 - d < 1 / 2 := by linarith
  have heps : 0 < ε / (C + 1) := div_pos hε hC1
  filter_upwards [eventually_integral_norm_steinhausGaussianSummatory_div_rpow_le hβ hβhalf heps,
    eventually_ge_atTop (1 : ℕ)] with N hmean hN
  intro tau htau r hr
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) ^ d := Real.rpow_pos_of_pos hNR _
  have hNmax : (N : ℝ) ≤ max 1 |tau| := htau.trans ((le_abs_self _).trans (le_max_right _ _))
  have hchiN : ‖zetaChi (rightDisplacedLinePt d tau)‖ ≤ C / (N : ℝ) ^ d :=
    (hchi tau).trans (div_le_div_of_nonneg_left hC hp
      (Real.rpow_le_rpow hNR.le hNmax hd.le))
  have he : 1 / 2 - (1 / 2 - d) = d := by ring
  have hmeanN := hmean r hr
  rw [he] at hmeanN
  rw [integral_norm_reflectedPrimalCarrier_eq]
  calc
    _ ≤ (C / (N : ℝ) ^ d) *
        (∫ ω, ‖∑ n ∈ Finset.Icc 1 N,
          (n : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ)) *
            smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω‖ ∂steinhausMeasure) :=
      mul_le_mul_of_nonneg_right hchiN (integral_nonneg (fun _ => norm_nonneg _))
    _ = C * ((∫ ω, ‖∑ n ∈ Finset.Icc 1 N,
          (n : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ)) *
            smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω‖ ∂steinhausMeasure) /
              (N : ℝ) ^ d) := by ring
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hmeanN hC
    _ ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hC1]
      nlinarith

end RHTower
