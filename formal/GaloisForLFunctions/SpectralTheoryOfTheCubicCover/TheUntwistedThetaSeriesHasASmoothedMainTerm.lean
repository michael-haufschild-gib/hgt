import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedContinuationHasOnlyTheCubicPole
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedThetaSeriesHasGaussianVerticalDecay
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaGaussianSmoothingIsAnArithmeticSum
import GaloisForLFunctions.HTGeometry.VerticalStripResidueShift

/-!
# A Gaussian-smoothed squarefree theta main term

The filled squarefree continuation has one simple pole at `2/3` in
`5/8<Re w<13/6`. Gaussian decay permits shifting the arithmetic Mellin contour
from `Re w=2` to any `5/8<a<2/3`. Its nonzero residue contributes
`exp(4/9) untwistedThetaResidue X^(2/3)`, with remainder bounded by `C_a X^a`.
-/

noncomputable section
open MeasureTheory Filter Topology Complex
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

/-- The Gaussian-weighted squarefree continuation. -/
def thetaGaussianContinuation (w : ℂ) : ℂ :=
  Complex.exp (w ^ 2) * regularizedUntwistedTheta w

private theorem thetaGaussianContinuation_differentiableAt (w : ℂ)
    (hw : 5 / 8 < w.re) (hB : w.re < 13 / 6) (hp : w ≠ 2 / 3) :
    DifferentiableAt ℂ thetaGaussianContinuation w :=
  (differentiableAt_id.pow 2).cexp.mul (regularizedUntwistedTheta_differentiableAt w hw hB hp)

private theorem thetaGaussianContinuation_bound (a : ℝ) (ha : 5 / 8 < a) (ha2 : a ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖thetaGaussianContinuation w‖ ≤ C * (1 + w.im ^ 2)⁻¹ := by
  obtain ⟨C, hC, hc⟩ := continuedUntwistedTheta_gaussian_vertical_bound a 2 ha ha2 (by norm_num)
  refine ⟨C, hC, fun w hwa hw2 hwi => ?_⟩
  have hi : w.im ≠ 0 := by intro he; rw [he, abs_zero] at hwi; linarith
  rw [thetaGaussianContinuation, regularizedUntwistedTheta_eq_nonreal w (ha.trans_le hwa) hi]
  exact hc w hwa hw2 hwi

/-- The nonzero coefficient of the Gaussian-smoothed `X^(2/3)` term. -/
def thetaGaussianMainCoefficient : ℂ :=
  Complex.exp ((2 / 3 : ℂ) ^ 2) * untwistedThetaResidue

theorem thetaGaussianMainCoefficient_ne_zero : thetaGaussianMainCoefficient ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) untwistedThetaResidue_ne_zero

private def thetaGaussianPerron (X : ℝ) (w : ℂ) : ℂ :=
  (X : ℂ) ^ w * thetaGaussianContinuation w

private theorem thetaGaussianPerron_residue {X : ℝ} (hX : 0 < X) :
    Tendsto (fun w => (w - 2 / 3) * thetaGaussianPerron X w) (𝓝[≠] (2 / 3 : ℂ))
      (𝓝 ((X : ℂ) ^ (2 / 3 : ℂ) * thetaGaussianMainCoefficient)) := by
  have hcont : ContinuousAt (fun w : ℂ => (X : ℂ) ^ w * Complex.exp (w ^ 2)) (2 / 3 : ℂ) :=
    (continuousAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).mul
      ((continuousAt_id.pow 2).cexp)
  have hlim := (hcont.tendsto.mono_left
    (show 𝓝[≠] (2 / 3 : ℂ) ≤ 𝓝 (2 / 3 : ℂ) from nhdsWithin_le_nhds)).mul
      regularizedUntwistedTheta_simple_pole
  have hvalue : ((X : ℂ) ^ (2 / 3 : ℂ) * Complex.exp ((2 / 3 : ℂ) ^ 2)) *
      untwistedThetaResidue = (X : ℂ) ^ (2 / 3 : ℂ) * thetaGaussianMainCoefficient := by
    rw [thetaGaussianMainCoefficient, mul_assoc]
  rw [hvalue] at hlim
  exact hlim.congr fun w => by
    dsimp only [thetaGaussianPerron, thetaGaussianContinuation]
    ring

private theorem thetaGaussianPerron_shift (a : ℝ) (ha : 5 / 8 < a) (hap : a < 2 / 3)
    {X : ℝ} (hX : 1 ≤ X) :
    (∫ t : ℝ, thetaGaussianPerron X (2 + t * I)) -
      ∫ t : ℝ, thetaGaussianPerron X ((a : ℂ) + t * I) =
        2 * Real.pi * ((X : ℂ) ^ (2 / 3 : ℂ) * thetaGaussianMainCoefficient) := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  obtain ⟨C, hC, hc⟩ := thetaGaussianContinuation_bound a ha (by linarith)
  apply HTGeometry.integral_line_sub_integral_line_eq (a := a) (b := 2) (p := (2 / 3 : ℂ))
    (T₀ := 1) (C := X ^ (2 : ℝ) * C) (by simpa using hap) (by norm_num)
  · intro w hwa hw2 hp
    exact (differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX0.ne'))).mul
      (thetaGaussianContinuation_differentiableAt w (ha.trans_le hwa) (by linarith) hp)
  · exact thetaGaussianPerron_residue hX0
  · intro w hwa hw2 hwi
    rw [thetaGaussianPerron, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
    calc
      _ ≤ X ^ (2 : ℝ) * (C * (1 + w.im ^ 2)⁻¹) :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le hX hw2) (hc w hwa hw2 hwi)
          (norm_nonneg _) (Real.rpow_nonneg hX0.le _)
      _ = _ := by ring

private theorem gaussianSmoothedUntwistedTheta_contour_identity
    (a : ℝ) (ha : 5 / 8 < a) (hap : a < 2 / 3) {X : ℝ} (hX : 1 ≤ X) :
    gaussianSmoothedUntwistedTheta X -
      (X : ℂ) ^ (2 / 3 : ℂ) * thetaGaussianMainCoefficient =
        (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, thetaGaussianPerron X ((a : ℂ) + t * I) := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hinv := gaussianSmoothedUntwistedTheta_eq_integral 2 (by norm_num) hX0
  have hright : (∫ t : ℝ, (X : ℂ) ^ ((2 : ℂ) + t * I) *
      Complex.exp (((2 : ℂ) + t * I) ^ 2) * twistedSquarefreeSeries 1 ((2 : ℂ) + t * I)) =
      ∫ t : ℝ, thetaGaussianPerron X (2 + t * I) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [thetaGaussianPerron, thetaGaussianContinuation,
      regularizedUntwistedTheta_eq_series _ (by norm_num) (by norm_num)]
    ring
  norm_num only [Complex.ofReal_ofNat] at hinv
  rw [hright, Complex.real_smul] at hinv
  rw [hinv, Complex.real_smul]
  have hshift := thetaGaussianPerron_shift a ha hap hX
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have halg (A B M : ℂ) (h : A - B = 2 * Real.pi * M) :
      (1 / (2 * Real.pi) : ℂ) * A - M = (1 / (2 * Real.pi) : ℂ) * B := by
    field_simp
    linear_combination h
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_ofNat] using halg _ _ _ hshift

/-- A signed arithmetic main term with a power-saving remainder for every `5/8<a<2/3`. -/
theorem gaussianSmoothedUntwistedTheta_main_term (a : ℝ) (ha : 5 / 8 < a) (hap : a < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ‖gaussianSmoothedUntwistedTheta X -
        (X : ℂ) ^ (2 / 3 : ℂ) * thetaGaussianMainCoefficient‖ ≤ C * X ^ a := by
  let C : ℝ := (1 / (2 * Real.pi)) * ∫ t : ℝ,
    ‖thetaGaussianContinuation ((a : ℂ) + t * I)‖
  have hκ : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  refine ⟨C, mul_nonneg hκ (integral_nonneg fun t => norm_nonneg _), ?_⟩
  intro X hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  rw [gaussianSmoothedUntwistedTheta_contour_identity a ha hap hX,
    norm_smul, Real.norm_of_nonneg hκ]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖thetaGaussianPerron X ((a : ℂ) + t * I)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hκ
    _ = (1 / (2 * Real.pi)) * (X ^ a * ∫ t : ℝ,
        ‖thetaGaussianContinuation ((a : ℂ) + t * I)‖) := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [thetaGaussianPerron, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      simp
    _ = C * X ^ a := by dsimp only [C]; ring

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
