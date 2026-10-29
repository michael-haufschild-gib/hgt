import GaloisForLFunctions.HeckeLFunctions.HeckeElementKernelsHaveExactMellinIntegrals
import GaloisForLFunctions.HeckeLFunctions.HeckeUnitOrbitsUnfoldOverTheLogSpace
import GaloisForLFunctions.HeckeLFunctions.HeckeLSeriesHaveEulerProducts
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Actual unit-averaged Mellin transforms are ideal-class Hecke series

The exact norm integral of each selected generator separates into the ideal
summand norm and one common archimedean mass. Absolute ideal-series convergence
therefore justifies the infinite Mellin exchange. Fixed-parameter unit-domain
unfolding identifies the resulting integral with the actual averaged theta.

The exact value has the torsion order, base-ideal summand, standard Gamma
product, and normalization `1/(degree * 2^unitRank)`. It agrees with the
continued unit theta transform on the full half-plane `Re s > 1`.
-/

noncomputable section
open NumberField NumberField.Units.dirichletUnitTheorem MeasureTheory
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

local instance (b : (Ideal (𝓞 K))⁰) : Countable (inverseClassIntegralIdeals b) :=
  inverseClassIntegralIdeals_countable b

/-- The actual Hecke ideal series restricted to the inverse ordinary class of `b`. -/
def heckeInverseClassL (ψ : HeckeCharacter 𝔪) (b : (Ideal (𝓞 K))⁰) (s : ℂ) : ℂ :=
  ∑' I : inverseClassIntegralIdeals b, heckeIdealTerm 𝔪 ψ s I.1

/-- The logarithmic Mellin density of the selected generator in one inverse-class ideal. -/
def heckeClassLogMellinKernel (ψ : HeckeCharacter 𝔪) (b : (Ideal (𝓞 K))⁰)
    (s : ℂ) (I : inverseClassIntegralIdeals b) (p : ℝ × logSpace K) : ℂ :=
  Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
    heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1))
      (inverseClassGenerator b I)

/-- Integrating the actual element density over all unit logarithms leaves the radial density. -/
def heckeClassRadialMellinKernel (ψ : HeckeCharacter 𝔪) (b : (Ideal (𝓞 K))⁰)
    (s : ℂ) (I : inverseClassIntegralIdeals b) (q : ℝ) : ℂ :=
  ∫ x : logSpace K, heckeClassLogMellinKernel 𝔪 ψ b s I (q, x)

/-- The selected generator supplies exactly the product of the two multiplicative ideal terms. -/
theorem inverseClassGenerator_heckeIdealTerm (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) (s : ℂ) (I : inverseClassIntegralIdeals b) :
    heckeValue 𝔪 ψ (Ideal.span {inverseClassGenerator b I}) *
      (Ideal.absNorm (Ideal.span {inverseClassGenerator b I}) : ℂ) ^ (-s) =
        heckeIdealTerm 𝔪 ψ s I.1 * heckeIdealTerm 𝔪 ψ s b := by
  rw [span_inverseClassGenerator]
  exact map_mul (heckeIdealTerm 𝔪 ψ s) I.1 b

/-- Actual inverse-class densities are jointly integrable throughout the open right half-plane. -/
theorem integrable_heckeClassLogMellinKernel (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 0 < s.re) (I : inverseClassIntegralIdeals b) :
    Integrable (heckeClassLogMellinKernel 𝔪 ψ b s I) :=
  integrable_heckeThetaKernel_logMellin 𝔪 ψ hs (inverseClassGenerator b I)
    (inverseClassGenerator_ne_zero_in_field b I)

/-- Absolute class masses are the ideal-summand norms times one common archimedean mass. -/
theorem integral_norm_heckeClassLogMellinKernel (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) (s : ℂ) (I : inverseClassIntegralIdeals b) :
    (∫ p : ℝ × logSpace K, ‖heckeClassLogMellinKernel 𝔪 ψ b s I p‖) =
      ‖heckeIdealTerm 𝔪 ψ s I.1‖ *
        (‖heckeIdealTerm 𝔪 ψ s b‖ * ∫ p : ℝ × logSpace K,
          ‖heckeArchimedeanLogKernel 𝔪 ψ s (numberFieldRadialLogParam p)‖) := by
  change (∫ p : ℝ × logSpace K,
    ‖Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1))
        (inverseClassGenerator b I)‖) = _
  rw [integral_norm_heckeThetaKernel_logMellin 𝔪 ψ s (inverseClassGenerator b I)
    (inverseClassGenerator_ne_zero_in_field b I),
    inverseClassGenerator_heckeIdealTerm, norm_mul, mul_assoc]

/-- The actual ideal-series convergence controls the sum of joint absolute Mellin masses. -/
theorem summable_integral_norm_heckeClassLogMellinKernel (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : inverseClassIntegralIdeals b =>
      ∫ p : ℝ × logSpace K, ‖heckeClassLogMellinKernel 𝔪 ψ b s I p‖) := by
  simp_rw [integral_norm_heckeClassLogMellinKernel]
  exact ((summable_norm_heckeIdealTerm 𝔪 ψ hs).comp_injective
    (i := fun I : inverseClassIntegralIdeals b => I.1) Subtype.val_injective).mul_right _

/-- Fubini gives integrability of each actual radial class density. -/
theorem integrable_heckeClassRadialMellinKernel (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 0 < s.re) (I : inverseClassIntegralIdeals b) :
    Integrable (heckeClassRadialMellinKernel 𝔪 ψ b s I) :=
  (integrable_heckeClassLogMellinKernel 𝔪 ψ b hs I).integral_prod_left

/-- The integral triangle inequality bounds radial absolute mass by joint absolute mass. -/
theorem integral_norm_heckeClassRadialMellinKernel_le (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 0 < s.re) (I : inverseClassIntegralIdeals b) :
    (∫ q : ℝ, ‖heckeClassRadialMellinKernel 𝔪 ψ b s I q‖) ≤
      ∫ p : ℝ × logSpace K, ‖heckeClassLogMellinKernel 𝔪 ψ b s I p‖ := by
  have hi := integrable_heckeClassLogMellinKernel 𝔪 ψ b hs I
  change (∫ q : ℝ, ‖heckeClassRadialMellinKernel 𝔪 ψ b s I q‖) ≤
    ∫ p : ℝ × logSpace K, ‖heckeClassLogMellinKernel 𝔪 ψ b s I p‖
      ∂(volume.prod volume)
  rw [integral_prod _ hi.norm]
  exact integral_mono (integrable_heckeClassRadialMellinKernel 𝔪 ψ b hs I).norm
    hi.norm.integral_prod_left (fun q => norm_integral_le_integral_norm _)

/-- Absolute Mellin masses remain summable after the unit-log integral. -/
theorem summable_integral_norm_heckeClassRadialMellinKernel (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : inverseClassIntegralIdeals b =>
      ∫ q : ℝ, ‖heckeClassRadialMellinKernel 𝔪 ψ b s I q‖) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (integral_norm_heckeClassRadialMellinKernel_le 𝔪 ψ b (zero_lt_one.trans hs))
    (summable_integral_norm_heckeClassLogMellinKernel 𝔪 ψ b hs)

/-- The actual radial series is integrable because its absolute masses are summable. -/
theorem integrable_tsum_heckeClassRadialMellinKernel (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun q : ℝ => ∑' I : inverseClassIntegralIdeals b,
      heckeClassRadialMellinKernel 𝔪 ψ b s I q) :=
  HTGeometry.integrable_tsum_of_summable_integral_norm
    (integrable_heckeClassRadialMellinKernel 𝔪 ψ b (zero_lt_one.trans hs))
    (summable_integral_norm_heckeClassRadialMellinKernel 𝔪 ψ b hs)

/-- Fixed-parameter unit unfolding identifies the actual logarithmic averaged Mellin density. -/
theorem heckeUnitAveragedTheta_logMellin_eq (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) (s : ℂ) (q : ℝ) :
    Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (q : ℂ)) *
      (heckeUnitAveragedTheta 𝔪 ψ (b : Ideal (𝓞 K)) (Real.exp (2 * q)) -
        (Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ) =
      (Units.torsionOrder K : ℂ) * ∑' I : inverseClassIntegralIdeals b,
        heckeClassRadialMellinKernel 𝔪 ψ b s I q := by
  rw [heckeUnitAveragedTheta_sub_constant_eq_classIntegrals 𝔪 ψ b (Real.exp_pos _),
    mul_left_comm, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro I
  simp only [heckeClassRadialMellinKernel, heckeClassLogMellinKernel, integral_const_mul]

/-- Absolute ideal-series convergence gives Mellin convergence on `Re s > 1`. -/
theorem mellinConvergent_heckeUnitAveragedTheta_classSeries (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (fun t : ℝ =>
      heckeUnitAveragedTheta 𝔪 ψ (b : Ideal (𝓞 K)) t -
        (Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ)
      (heckeThetaMellinArgument 𝔪 ψ s) := by
  apply (mellinConvergent_iff_integrable_exp_two _ _).mpr
  simp_rw [heckeUnitAveragedTheta_logMellin_eq]
  exact (integrable_tsum_heckeClassRadialMellinKernel 𝔪 ψ b hs).const_mul _

/-- Fubini and the element Mellin value evaluate each actual radial class integral. -/
theorem integral_heckeClassRadialMellinKernel (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 0 < s.re) (I : inverseClassIntegralIdeals b) :
    (2 : ℂ) * (∫ q : ℝ, heckeClassRadialMellinKernel 𝔪 ψ b s I q) =
      (heckeIdealTerm 𝔪 ψ s I.1 * heckeIdealTerm 𝔪 ψ s b) *
        (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  change (2 : ℂ) * (∫ q : ℝ, ∫ x : logSpace K,
    heckeClassLogMellinKernel 𝔪 ψ b s I (q, x)) = _
  rw [← integral_prod _ (integrable_heckeClassLogMellinKernel 𝔪 ψ b hs I)]
  change (2 : ℂ) * (∫ p : ℝ × logSpace K,
    Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1))
        (inverseClassGenerator b I)) = _
  rw [integral_heckeThetaKernel_logMellin 𝔪 ψ hs (inverseClassGenerator b I)
    (inverseClassGenerator_ne_zero_in_field b I), inverseClassGenerator_heckeIdealTerm]

/-- Actual unit-averaged Mellin unfolding gives the inverse-class Hecke ideal series. -/
theorem mellin_heckeUnitAveragedTheta_eq_inverseClassL (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t : ℝ =>
      heckeUnitAveragedTheta 𝔪 ψ (b : Ideal (𝓞 K)) t -
        (Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ)
      (heckeThetaMellinArgument 𝔪 ψ s) =
        (Units.torsionOrder K : ℂ) * heckeInverseClassL 𝔪 ψ b s *
          heckeIdealTerm 𝔪 ψ s b *
            (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  rw [RHTower.mellin_eq_integral_exp_two]
  simp_rw [heckeUnitAveragedTheta_logMellin_eq]
  rw [integral_const_mul, mul_left_comm,
    ← integral_tsum_of_summable_integral_norm
      (integrable_heckeClassRadialMellinKernel 𝔪 ψ b (zero_lt_one.trans hs))
      (summable_integral_norm_heckeClassRadialMellinKernel 𝔪 ψ b hs),
    ← tsum_mul_left]
  simp_rw [integral_heckeClassRadialMellinKernel 𝔪 ψ b (zero_lt_one.trans hs)]
  rw [tsum_mul_right, tsum_mul_right]
  simp only [heckeInverseClassL, mul_assoc]

/-- The continued actual theta transform agrees with the class ideal series on `Re s > 1`. -/
theorem heckeUnitThetaMellinContinuation_eq_inverseClassL (ψ : HeckeCharacter 𝔪)
    (b : (Ideal (𝓞 K))⁰) (hb : (b : Ideal (𝓞 K)) ⊔ 𝔪.fin = ⊤)
    {s : ℂ} (hs : 1 < s.re) :
    heckeUnitThetaMellinContinuation 𝔪 hb (nonZeroDivisors.coe_ne_zero b) ψ
      (heckeThetaMellinArgument 𝔪 ψ s) =
        (Units.torsionOrder K : ℂ) * heckeInverseClassL 𝔪 ψ b s *
          heckeIdealTerm 𝔪 ψ s b *
            (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  have hm : HasMellin (fun t : ℝ =>
      heckeUnitAveragedTheta 𝔪 ψ (b : Ideal (𝓞 K)) t -
        (Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ)
      (heckeThetaMellinArgument 𝔪 ψ s)
      (heckeUnitThetaMellinContinuation 𝔪 hb (nonZeroDivisors.coe_ne_zero b) ψ
        (heckeThetaMellinArgument 𝔪 ψ s)) := by
    by_cases hpar : HTGeometry.IntegerLatticePoisson.parityDegree (heckeCoordinateParity 𝔪 ψ) = 0
    · apply hasMellin_heckeUnitAveragedTheta 𝔪 hb (nonZeroDivisors.coe_ne_zero b) ψ
      have hn : 0 < (Module.finrank ℚ K : ℝ) := by
        rw [← numberFieldInfinitePlaceWeight_eq_finrank]
        exact numberFieldInfinitePlaceWeight_pos
      simp only [heckeThetaMellinWeight, heckeThetaMellinArgument, hpar,
        Nat.cast_zero, add_zero, Complex.div_ofNat_re, Complex.mul_re,
        Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      nlinarith [mul_pos hn (sub_pos.mpr hs)]
    · have hstrong := heckeUnitThetaMellinPair_isStrong_of_parity_ne_zero
        𝔪 hb (nonZeroDivisors.coe_ne_zero b) ψ hpar
      have hz : (Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ = 0 := by
        simpa only [heckeUnitThetaMellinPair, Complex.real_smul] using hstrong.hf₀
      simp only [hz, sub_zero]
      exact hstrong.hasMellin (heckeThetaMellinArgument 𝔪 ψ s)
  exact hm.2.symm.trans (mellin_heckeUnitAveragedTheta_eq_inverseClassL 𝔪 ψ b hs)

end GaloisForLFunctions.HeckeLFunctions
