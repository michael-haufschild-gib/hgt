import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge
import GaloisForLFunctions.ArithmeticPolarization.HeckeInvarianceOfTheCollidedPolarizationIsRH

/-!
# Translation of the actual zeta square mass and reflection defect

The positive square mass is the collided spectral form. Translation
changes this mass and its reflection defect by exactly the same amount,
because the actual Weil form is invariant. Symmetric translation has a
nonnegative second difference, identical for both energies. Consequently
translation cannot improve the missing comparison between them.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Complex
open ArithmeticPositivityTheory SquareRootThreshold ArithmeticPolarization
open _root_.Zeta23

/-- The square mass in the actual Weil comparison is precisely the collided spectral form. -/
theorem configurationSquareMass_eq_collidedForm (Z : ZeroConfig) (f : ℝ → ℂ) :
    configurationSquareMass Z f = collidedForm Z f := by
  simp only [configurationSquareMass, collidedForm, tr, Complex.normSq_eq_norm_sq]

/-- Translating a test changes the reflection defect by exactly the change in square mass. -/
theorem zeta_reflectionDefect_translate_sub (a : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    configurationReflectionDefect zetaZeroConfig (translate a f) -
        configurationReflectionDefect zetaZeroConfig f =
      configurationSquareMass zetaZeroConfig (translate a f) -
        configurationSquareMass zetaZeroConfig f := by
  have htf : ContDiff ℝ 2 (translate a f) := hf.comp (contDiff_id.sub contDiff_const)
  have htfc : HasCompactSupport (translate a f) := hfc.comp_homeomorph (Homeomorph.subRight a)
  have ht := zeta_squareMass_sub_re_W_eq_reflectionDefect htf htfc
  rw [W_translate_translate] at ht
  have h := zeta_squareMass_sub_re_W_eq_reflectionDefect hf hfc
  linarith only [ht, h]

/-- The literal von Mangoldt Weil form is invariant under translating an admissible test. -/
theorem actualZeta_weil_translate (a : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (translate a f) (translate a f)) =
    RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest f f) := by
  have htf : ContDiff ℝ 2 (translate a f) := hf.comp (contDiff_id.sub contDiff_const)
  have htfc : HasCompactSupport (translate a f) := hfc.comp_homeomorph (Homeomorph.subRight a)
  rw [← RHTower.zeta_W_eq_weilFullFunctional_mixed htf htfc htf htfc,
    ← RHTower.zeta_W_eq_weilFullFunctional_mixed hf hfc hf hfc, W_translate_translate]

/-- Translation preserves the truth of the reflection-defect comparison on each test. -/
theorem zeta_reflectionDefect_translate_le_iff (a : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    configurationReflectionDefect zetaZeroConfig (translate a f) ≤
        configurationSquareMass zetaZeroConfig (translate a f) ↔
      configurationReflectionDefect zetaZeroConfig f ≤ configurationSquareMass zetaZeroConfig f := by
  have h := zeta_reflectionDefect_translate_sub a hf hfc
  constructor <;> intro hle <;> linarith only [h, hle]

/-- Symmetric translation measures horizontal displacement by a nonnegative hyperbolic-cosine weight. -/
theorem zeta_squareMass_translate_second_difference (a : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    configurationSquareMass zetaZeroConfig (translate a f) +
      configurationSquareMass zetaZeroConfig (translate (-a) f) -
      2 * configurationSquareMass zetaZeroConfig f =
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
      (2 * Real.cosh (2 * ((ρ : ℂ).re - 1 / 2) * a) - 2) *
        ‖paperFT f (gammaOf ρ)‖ ^ 2 := by
  have hs (b : ℝ) : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (translate b f) ρ)) := by
    have htb : ContDiff ℝ 2 (translate b f) := hf.comp (contDiff_id.sub contDiff_const)
    have htbc : HasCompactSupport (translate b f) := hfc.comp_homeomorph (Homeomorph.subRight b)
    simpa only [tr, Complex.normSq_eq_norm_sq] using
      summable_squareMass_of_temperedConfig zetaZeroConfig temperedConfig_zetaZeroConfig htb htbc
  have hs0 : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f ρ)) := by
    simpa only [tr, Complex.normSq_eq_norm_sq] using
      summable_squareMass_of_temperedConfig zetaZeroConfig temperedConfig_zetaZeroConfig hf hfc
  simp only [configurationSquareMass_eq_collidedForm]
  simpa only [tr, Complex.normSq_eq_norm_sq] using
    collidedForm_second_difference (Z := zetaZeroConfig) (f := f) a hs0 (hs a) (hs (-a))

/-- Symmetric translation increases square mass and reflection defect by the same nonnegative amount. -/
theorem zeta_reflectionDefect_translate_second_difference (a : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ configurationReflectionDefect zetaZeroConfig (translate a f) +
      configurationReflectionDefect zetaZeroConfig (translate (-a) f) -
      2 * configurationReflectionDefect zetaZeroConfig f := by
  have hp := zeta_reflectionDefect_translate_sub a hf hfc
  have hm := zeta_reflectionDefect_translate_sub (-a) hf hfc
  have he := zeta_squareMass_translate_second_difference a hf hfc
  have hn : 0 ≤ ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
      (2 * Real.cosh (2 * ((ρ : ℂ).re - 1 / 2) * a) - 2) *
        ‖paperFT f (gammaOf ρ)‖ ^ 2 := by
    apply tsum_nonneg
    intro ρ
    have hc := Real.one_le_cosh (2 * ((ρ : ℂ).re - 1 / 2) * a)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith only [hc])) (sq_nonneg _)
  linarith only [hp, hm, he, hn]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
