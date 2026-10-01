import GaloisForLFunctions.RHTower.SteinhausGaussianIndependentCutoffMean
import GaloisForLFunctions.RHTower.SmoothAFEReflectedCarrierFirstMean
import GaloisForLFunctions.RHTower.SteinhausSmoothCarrierProjection



open MeasureTheory Filter Complex
open scoped Topology
noncomputable section
namespace RHTower
open SteinhausModel

/-- Exact phase stationarity of the literal Gaussian Dirichlet polynomial. -/
theorem integral_norm_steinhausGaussianWindow_phase_eq (β r t : ℝ) (N L : ℕ) :
    (∫ ω, ‖∑ n ∈ Finset.Icc 1 L,
      (n : ℂ) ^ (-(β : ℂ) - (t : ℂ) * I) *
        smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω‖ ∂steinhausMeasure) =
    ∫ ω, ‖∑ n ∈ Finset.Icc 1 L,
      (n : ℂ) ^ (-(β : ℂ)) * smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω‖
        ∂steinhausMeasure := by
  have hS (n : ℕ) (hn : n ∈ Finset.Icc 1 L) : n ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  rw [← integral_norm_steinhausFiniteSum_verticalPhase
    (fun n => (n : ℂ) ^ (-(β : ℂ)) * smoothAFECutoff (r * ((n : ℝ) / N)))
    (Finset.Icc 1 L) hS t]
  apply integral_congr_ae
  filter_upwards with ω
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hS n hn
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hnC]
  congr 1
  rw [neg_mul]
  ring

/-- The literal reflected carrier has exactly the untwisted Gaussian first mean times the chi norm. -/
theorem integral_norm_reflectedPrimalWindowCarrier_eq (d tau r : ℝ) (N L : ℕ) :
    (∫ ω, ‖∑ n ∈ Finset.Icc 1 L,
      smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N n * X n ω‖
        ∂steinhausMeasure) =
      ‖zetaChi (rightDisplacedLinePt d tau)‖ *
        (∫ ω, ‖∑ n ∈ Finset.Icc 1 L,
          (n : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ)) *
            smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω‖ ∂steinhausMeasure) := by
  have he : rightDisplacedLinePt d tau - 1 =
      -((1 / 2 - d : ℝ) : ℂ) - ((-tau : ℝ) : ℂ) * I := by
    unfold rightDisplacedLinePt
    push_cast
    ring
  have hsum (ω : Omega) : (∑ n ∈ Finset.Icc 1 L,
      smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N n * X n ω) =
      zetaChi (rightDisplacedLinePt d tau) *
        ∑ n ∈ Finset.Icc 1 L,
          (n : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ) - ((-tau : ℝ) : ℂ) * I) *
            smoothAFECutoff (r * ((n : ℝ) / N)) * X n ω := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [reflectedPrimalPositiveCoefficient_eq_power_cutoff _ _ _ _ (Finset.mem_Icc.mp hn).1, he]
    ring
  simp_rw [hsum, norm_mul]
  rw [integral_const_mul, integral_norm_steinhausGaussianWindow_phase_eq]

/-- Convert the uniform real-weight estimate to the literal complex Gaussian coefficients. -/
theorem eventually_integral_norm_steinhausGaussianWindow_div_rpow_le
    {β : ℝ} (hβ : 0 < β) (hβhalf : β < 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      (∫ ω, ‖∑ n ∈ Finset.Icc 1 L, (n : ℂ) ^ (-(β : ℂ)) *
        smoothAFECutoff ((n : ℝ) / N) * X n ω‖ ∂steinhausMeasure) /
          (N : ℝ) ^ (1 / 2 - β) ≤ δ := by
  filter_upwards [eventually_integral_norm_steinhausGaussianWeight_independent_cutoff_le
    hβ hβhalf hδ, eventually_ge_atTop 1] with N hmean hN
  intro L
  have heq (ω : Omega) : (∑ n ∈ Finset.Icc 1 L,
      (steinhausGaussianWeight β 1 N n : ℂ) * X n ω) =
      ∑ n ∈ Finset.Icc 1 L, (n : ℂ) ^ (-(β : ℂ)) *
        smoothAFECutoff ((n : ℝ) / N) * X n ω := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [steinhausGaussianWeight_coe_eq β one_pos hN (Finset.mem_Icc.mp hn).1, one_mul]
  simpa only [heq] using hmean L

/-- The original reflected AFE carrier vanishes in first mean, uniformly above the conductor and over every independent polynomial cutoff. -/
theorem eventually_integral_norm_reflectedPrimalWindowCarrier_le
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ tau : ℝ, (N : ℝ) ≤ tau →
      (∫ ω, ‖∑ n ∈ Finset.Icc 1 L,
        smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau 1 N n * X n ω‖
          ∂steinhausMeasure) ≤ ε := by
  obtain ⟨C, hC, hchi⟩ := exists_norm_zetaChi_fixed_right_line_le_rpow hd hdhalf
  have hC1 : 0 < C + 1 := by linarith
  have hβ : 0 < 1 / 2 - d := by linarith
  have hβhalf : 1 / 2 - d < 1 / 2 := by linarith
  have heps : 0 < ε / (C + 1) := div_pos hε hC1
  filter_upwards [eventually_integral_norm_steinhausGaussianWindow_div_rpow_le hβ hβhalf heps,
    eventually_ge_atTop (1 : ℕ)] with N hmean hN
  intro L tau htau
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) ^ d := Real.rpow_pos_of_pos hNR _
  have hNmax : (N : ℝ) ≤ max 1 |tau| := htau.trans ((le_abs_self _).trans (le_max_right _ _))
  have hchiN : ‖zetaChi (rightDisplacedLinePt d tau)‖ ≤ C / (N : ℝ) ^ d :=
    (hchi tau).trans (div_le_div_of_nonneg_left hC hp
      (Real.rpow_le_rpow hNR.le hNmax hd.le))
  have he : 1 / 2 - (1 / 2 - d) = d := by ring
  have hmeanN := hmean L
  rw [he] at hmeanN
  rw [integral_norm_reflectedPrimalWindowCarrier_eq]
  simp only [one_mul]
  calc
    _ ≤ (C / (N : ℝ) ^ d) *
        (∫ ω, ‖∑ n ∈ Finset.Icc 1 L,
          (n : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ)) *
            smoothAFECutoff (((n : ℝ) / N)) * X n ω‖ ∂steinhausMeasure) :=
      mul_le_mul_of_nonneg_right hchiN (integral_nonneg (fun _ => norm_nonneg _))
    _ = C * ((∫ ω, ‖∑ n ∈ Finset.Icc 1 L,
          (n : ℂ) ^ (-((1 / 2 - d : ℝ) : ℂ)) *
            smoothAFECutoff (((n : ℝ) / N)) * X n ω‖ ∂steinhausMeasure) /
              (N : ℝ) ^ d) := by ring
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hmeanN hC
    _ ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hC1]
      nlinarith

/-- Averaging outside any retained prime set contracts the literal enlarged-cutoff carrier
mean. In particular, retaining primes above the free window does not lose mean decay. -/
theorem eventually_integral_norm_reflectedPrimalWindowSmooth_le
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ S : Finset ℕ, ∀ tau : ℝ, (N : ℝ) ≤ tau →
      (∫ ω, ‖∑ n ∈ Sieve.smoothUpTo S L,
        smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau 1 N n * X n ω‖
          ∂steinhausMeasure) ≤ ε := by
  filter_upwards [eventually_integral_norm_reflectedPrimalWindowCarrier_le hd hdhalf hε]
    with N hN
  intro L S tau htau
  exact (integral_norm_smoothUpTo_carrier_le
    (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau 1 N) L S).trans (hN L tau htau)

end RHTower
