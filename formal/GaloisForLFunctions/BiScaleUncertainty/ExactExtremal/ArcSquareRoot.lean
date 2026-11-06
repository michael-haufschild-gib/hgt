import GaloisForLFunctions.BiScaleUncertainty.ExactExtremal.ArcMultiplierPositiveStrip
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# A single strip-holomorphic square root of the arc mixture

The multiplier's positive real part selects its principal square root without
introducing real zeros. Xi decay pays for the square root's exponential growth.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Nat ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty.ExactExtremal

open _root_.RHTower _root_.RHTower.WeilSpectral

noncomputable section

def arcRoot (μ : ProbabilityMeasure ArcParam) (z : ℂ) : ℂ :=
  Complex.sqrt (arcSpectralMultiplier (μ : Measure ArcParam) z)

def arcSpectrum (μ : ProbabilityMeasure ArcParam) (z : ℂ) : ℂ := XiC z * arcRoot μ z

theorem arcRoot_sq (μ : ProbabilityMeasure ArcParam) {z : ℂ}
    (hz : |z.im| ≤ 501 / 1000) :
    arcRoot μ z ^ 2 = arcSpectralMultiplier (μ : Measure ArcParam) z := by
  have hn : arcSpectralMultiplier (μ : Measure ArcParam) z ≠ 0 := by
    intro h
    have hp := arcSpectralMultiplier_re_pos μ hz
    rw [h, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  rw [arcRoot, sqrt_eq_exp hn, pow_two, ← Complex.exp_add,
    show Complex.log (arcSpectralMultiplier (μ : Measure ArcParam) z) / 2 +
      Complex.log (arcSpectralMultiplier (μ : Measure ArcParam) z) / 2 =
      Complex.log (arcSpectralMultiplier (μ : Measure ArcParam) z) by ring,
    Complex.exp_log hn]

theorem differentiableAt_arcRoot (μ : ProbabilityMeasure ArcParam) {z : ℂ}
    (hz : |z.im| ≤ 501 / 1000) : DifferentiableAt ℂ (arcRoot μ) z :=
  (Complex.differentiableAt_sqrt (Or.inl (arcSpectralMultiplier_re_pos μ hz))).comp z
    (differentiableAt_arcSpectralMultiplier (μ : Measure ArcParam) (by linarith only [hz]))

theorem arcRoot_even (μ : ProbabilityMeasure ArcParam) (z : ℂ) :
    arcRoot μ (-z) = arcRoot μ z := by rw [arcRoot, arcRoot, arcSpectralMultiplier_even]

theorem arcSpectralMultiplier_ofReal (μ : ProbabilityMeasure ArcParam) (r : ℝ) :
    arcSpectralMultiplier (μ : Measure ArcParam) r =
      ((∑' j, arcSpectralWeight (μ : Measure ArcParam) j * ‖shiftedGammaPoly j r‖ ^ 2 : ℝ) : ℂ) := by
  unfold arcSpectralMultiplier
  rw [arcGammaMultiplier_criticalLine, Complex.ofReal_tsum]

theorem arcRoot_ofReal (μ : ProbabilityMeasure ArcParam) (r : ℝ) :
    arcRoot μ r = (Real.sqrt (∑' j,
      arcSpectralWeight (μ : Measure ArcParam) j * ‖shiftedGammaPoly j r‖ ^ 2) : ℂ) := by
  let a := ∑' j, arcSpectralWeight (μ : Measure ArcParam) j * ‖shiftedGammaPoly j r‖ ^ 2
  have ha : 0 ≤ a := tsum_nonneg fun j =>
    mul_nonneg (arcSpectralWeight_nonneg (μ : Measure ArcParam) j) (sq_nonneg _)
  rw [arcRoot, arcSpectralMultiplier_ofReal, Complex.sqrt_eq_real_add_ite]
  change (Real.sqrt ((‖(a : ℂ)‖ + (a : ℂ).re) / 2) : ℂ) +
    (if 0 ≤ (a : ℂ).im then 1 else -1) *
      (Real.sqrt ((‖(a : ℂ)‖ - (a : ℂ).re) / 2) : ℂ) * I = _
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
    show (a + a) / 2 = a by ring]
  rfl

theorem arcRoot_ne_zero (μ : ProbabilityMeasure ArcParam) {z : ℂ}
    (hz : |z.im| ≤ 501 / 1000) : arcRoot μ z ≠ 0 := by
  intro h
  have hs := arcRoot_sq μ hz
  rw [h, zero_pow (by decide)] at hs
  have hp := arcSpectralMultiplier_re_pos μ hz
  rw [← hs, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem arcRoot_ofReal_ne_zero (μ : ProbabilityMeasure ArcParam) (r : ℝ) : arcRoot μ r ≠ 0 :=
  arcRoot_ne_zero μ (by norm_num)

/-- The square root introduces no zeros anywhere in the proved strip. -/
theorem arcSpectrum_eq_zero_iff (μ : ProbabilityMeasure ArcParam) {z : ℂ}
    (hz : |z.im| ≤ 501 / 1000) : arcSpectrum μ z = 0 ↔ XiC z = 0 := by
  rw [arcSpectrum, mul_eq_zero]
  exact or_iff_left (arcRoot_ne_zero μ hz)

theorem arcSpectrum_neg_ofReal (μ : ProbabilityMeasure ArcParam) (r : ℝ) :
    arcSpectrum μ (-(r : ℂ)) = conj (arcSpectrum μ r) := by
  rw [arcSpectrum, arcSpectrum, XiC_even, arcRoot_even, map_mul,
    ← XiC_conj, Complex.conj_ofReal, arcRoot_ofReal, Complex.conj_ofReal]

theorem norm_arcRoot_le (μ : ProbabilityMeasure ArcParam) {z : ℂ}
    (hz : |z.im| ≤ 501 / 1000) :
    ‖arcRoot μ z‖ ≤ 3 * ((∑' j, arcSpectralWeight (μ : Measure ArcParam) j *
      ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) + 1) *
        Real.exp (Real.log 3 / 2 * |z.re|) := by
  let S := ∑' j, arcSpectralWeight (μ : Measure ArcParam) j *
    ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun j =>
    mul_nonneg (arcSpectralWeight_nonneg (μ : Measure ArcParam) j) (sq_nonneg _)
  have hsq : ‖arcRoot μ z‖ ^ 2 = ‖arcSpectralMultiplier (μ : Measure ArcParam) z‖ := by
    rw [← norm_pow, arcRoot_sq μ hz]
  have hE : Real.exp (Real.log 3 / 2 * |z.re|) ^ 2 = Real.exp (Real.log 3 * |z.re|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnorm := norm_arcSpectralMultiplier_le (μ : Measure ArcParam) (z := z)
    (by linarith only [hz])
  have hmajor : ‖arcRoot μ z‖ ^ 2 ≤
      (3 * (S + 1) * Real.exp (Real.log 3 / 2 * |z.re|)) ^ 2 := by
    calc
      ‖arcRoot μ z‖ ^ 2 = ‖arcSpectralMultiplier (μ : Measure ArcParam) z‖ := hsq
      _ ≤ 9 * S * Real.exp (Real.log 3 * |z.re|) := hnorm
      _ ≤ 9 * (S + 1) ^ 2 * Real.exp (Real.log 3 * |z.re|) := by
        gcongr
        nlinarith only [hS, sq_nonneg S]
      _ = _ := by rw [mul_pow, hE]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hmajor

/-- The single spectrum retains the positive decay rate of the shifted-Gamma family. -/
theorem exists_stripDecay_arcSpectrum (μ : ProbabilityMeasure ArcParam) :
    ∃ C : ℝ, 0 ≤ C ∧ StripDecay (arcSpectrum μ) (501 / 1000) xiShiftedGammaRate C := by
  obtain ⟨CΞ, hCΞ, hΞ⟩ := exists_norm_XiC_horizontal_le (A := 3 / 4) (δ := 3 / 4)
    (by norm_num) (by norm_num) (by linarith only [Real.pi_gt_three])
  let S := ∑' j, arcSpectralWeight (μ : Measure ArcParam) j *
    ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun j =>
    mul_nonneg (arcSpectralWeight_nonneg (μ : Measure ArcParam) j) (sq_nonneg _)
  refine ⟨3 * CΞ * (S + 1), by positivity, ⟨fun z hz => ?_, fun z hz => ?_⟩⟩
  · exact (XiC_differentiable z).mul (differentiableAt_arcRoot μ hz)
  · have hX : ‖XiC z‖ ≤ CΞ * Real.exp (-(3 / 4 * |z.re|)) := by
      have h := hΞ z.re z.im (by linarith only [hz])
      rwa [Complex.re_add_im z] at h
    rw [arcSpectrum, norm_mul]
    calc
      ‖XiC z‖ * ‖arcRoot μ z‖ ≤ (CΞ * Real.exp (-(3 / 4 * |z.re|))) *
          (3 * (S + 1) * Real.exp (Real.log 3 / 2 * |z.re|)) :=
        mul_le_mul hX (norm_arcRoot_le μ hz) (norm_nonneg _) (by positivity)
      _ = 3 * CΞ * (S + 1) * (Real.exp (-(3 / 4 * |z.re|)) *
          Real.exp (Real.log 3 / 2 * |z.re|)) := by ring
      _ = _ := by rw [← Real.exp_add]; unfold xiShiftedGammaRate; ring_nf

/-- The scalar spectrum has exactly the mixture's real spectral density. -/
theorem norm_arcSpectrum_sq (μ : ProbabilityMeasure ArcParam) (r : ℝ) :
    ‖arcSpectrum μ r‖ ^ 2 = ∑' j, arcSpectralWeight (μ : Measure ArcParam) j *
      ‖xiShiftedGamma j r‖ ^ 2 := by
  have ha : 0 ≤ ∑' j, arcSpectralWeight (μ : Measure ArcParam) j * ‖shiftedGammaPoly j r‖ ^ 2 :=
    tsum_nonneg fun j => mul_nonneg (arcSpectralWeight_nonneg (μ : Measure ArcParam) j) (sq_nonneg _)
  rw [arcSpectrum, norm_mul, mul_pow, arcRoot_ofReal, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ha,
    ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [xiShiftedGamma, norm_mul, mul_pow]
  ring

end

end GaloisForLFunctions.BiScaleUncertainty.ExactExtremal
