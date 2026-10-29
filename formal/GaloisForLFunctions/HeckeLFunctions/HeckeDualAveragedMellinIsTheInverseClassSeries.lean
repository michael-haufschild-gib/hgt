import GaloisForLFunctions.HeckeLFunctions.HeckeDualClassKernelsHaveExactMellinIntegrals
import GaloisForLFunctions.HeckeLFunctions.HeckeDualUnitOrbitsUnfoldOverTheLogSpace
import GaloisForLFunctions.HeckeLFunctions.HeckeConductorsAndParitiesAreInvariantUnderInversion
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# The actual dual averaged Mellin transform is the inverse class series

Absolute inverse ideal-series convergence controls the joint Mellin masses
of all selected dual generators. Fubini bounds their radial masses and
justifies the infinite Mellin exchange. Actual unit-domain unfolding then
gives the precise Gauss, fractional-norm, torsion, and Gamma factors.
The symmetric arithmetic theta pair has this same value on all `Re s > 1`,
using its strong form when the real parity degree is nonzero.
-/

noncomputable section
open NumberField NumberField.Units.dirichletUnitTheorem MeasureTheory
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
  {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)

local instance : Countable (heckeDualClassIdeals 𝔪 hb0) :=
  fractionalInverseClassIntegralIdeals_countable (heckeDualIdealUnit 𝔪 hb0)

/-- The inverse-character ideal series on the actual dual fractional ideal's inverse class. -/
def heckeDualClassL (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  ∑' I : heckeDualClassIdeals 𝔪 hb0, heckeIdealTerm 𝔪 ψ⁻¹ s I.1

/-- Integrate the actual dual logarithmic Mellin density over all unit logarithms. -/
def heckeDualClassRadialMellinKernel (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (I : heckeDualClassIdeals 𝔪 hb0) (q : ℝ) : ℂ :=
  ∫ x : logSpace K, heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I (q, x)

/-- Fubini gives absolute integrability of each actual dual radial density. -/
theorem integrable_heckeDualClassRadialMellinKernel (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 0 < s.re)
    (I : heckeDualClassIdeals 𝔪 hb0) :
    Integrable (heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ s I) :=
  (integrable_heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ hψ hs I).integral_prod_left

/-- The integral triangle inequality bounds radial mass by the jointly integrable mass. -/
theorem integral_norm_heckeDualClassRadialMellinKernel_le (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 0 < s.re)
    (I : heckeDualClassIdeals 𝔪 hb0) :
    (∫ q : ℝ, ‖heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ s I q‖) ≤
      ∫ p : ℝ × logSpace K, ‖heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I p‖ := by
  have hi := integrable_heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ hψ hs I
  change (∫ q : ℝ, ‖heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ s I q‖) ≤
    ∫ p : ℝ × logSpace K, ‖heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I p‖
      ∂(volume.prod volume)
  rw [integral_prod _ hi.norm]
  exact integral_mono (integrable_heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ hψ hs I).norm
    hi.norm.integral_prod_left (fun q => norm_integral_le_integral_norm _)

/-- Absolute inverse ideal-series convergence controls the sum of radial Mellin masses. -/
theorem summable_integral_norm_heckeDualClassRadialMellinKernel (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : heckeDualClassIdeals 𝔪 hb0 =>
      ∫ q : ℝ, ‖heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ s I q‖) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (integral_norm_heckeDualClassRadialMellinKernel_le 𝔪 hb hb0 ψ hψ (zero_lt_one.trans hs))
    (summable_integral_norm_heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ hψ hs)

/-- Summable absolute masses make the complete actual dual radial series integrable. -/
theorem integrable_tsum_heckeDualClassRadialMellinKernel (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun q : ℝ => ∑' I : heckeDualClassIdeals 𝔪 hb0,
      heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ s I q) :=
  HTGeometry.integrable_tsum_of_summable_integral_norm
    (integrable_heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ hψ (zero_lt_one.trans hs))
    (summable_integral_norm_heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ hψ hs)

/-- Actual fixed-parameter unfolding identifies the averaged dual Mellin density. -/
theorem heckeUnitAveragedDualTheta_logMellin_eq (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (s : ℂ) (q : ℝ) :
    Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (q : ℂ)) *
      (heckeUnitAveragedDualTheta 𝔪 hb ψ (Real.exp (2 * q)) -
        (Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ) =
      (Units.torsionOrder K : ℂ) * ∑' I : heckeDualClassIdeals 𝔪 hb0,
        heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ s I q := by
  rw [heckeUnitAveragedDualTheta_sub_constant_eq_classIntegrals 𝔪 hb hb0 ψ hψ (Real.exp_pos _),
    mul_left_comm, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro I
  simp only [heckeDualClassRadialMellinKernel, heckeDualClassLogMellinKernel, integral_const_mul]

include hb0 in
/-- The dual average's actual Mellin integral converges absolutely throughout `Re s > 1`. -/
theorem mellinConvergent_heckeUnitAveragedDualTheta_classSeries (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (fun t : ℝ => heckeUnitAveragedDualTheta 𝔪 hb ψ t -
      (Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ)
      (heckeThetaMellinArgument 𝔪 ψ s) := by
  apply (mellinConvergent_iff_integrable_exp_two _ _).mpr
  simp_rw [heckeUnitAveragedDualTheta_logMellin_eq 𝔪 hb hb0 ψ hψ]
  exact (integrable_tsum_heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ hψ hs).const_mul _

/-- Fubini retains the exact dual arithmetic factor and Gamma/Jacobian value. -/
theorem integral_heckeDualClassRadialMellinKernel (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 0 < s.re)
    (I : heckeDualClassIdeals 𝔪 hb0) :
    (2 : ℂ) * (∫ q : ℝ, heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ s I q) =
      heckeIdealTerm 𝔪 ψ⁻¹ s I.1 * heckeDualMellinFactor 𝔪 hb0 ψ s *
        (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  change (2 : ℂ) * (∫ q : ℝ, ∫ x : logSpace K,
    heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I (q, x)) = _
  rw [← integral_prod _ (integrable_heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ hψ hs I)]
  exact integral_heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ hψ hs I

/-- Actual dual Mellin unfolding gives the inverse-character class series with its exact Gauss factor. -/
theorem mellin_heckeUnitAveragedDualTheta_eq_dualClassL (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t : ℝ => heckeUnitAveragedDualTheta 𝔪 hb ψ t -
      (Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ)
      (heckeThetaMellinArgument 𝔪 ψ s) =
        (Units.torsionOrder K : ℂ) * heckeDualClassL 𝔪 hb0 ψ s *
          heckeDualMellinFactor 𝔪 hb0 ψ s *
            (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  rw [RHTower.mellin_eq_integral_exp_two]
  simp_rw [heckeUnitAveragedDualTheta_logMellin_eq 𝔪 hb hb0 ψ hψ]
  rw [integral_const_mul, mul_left_comm,
    ← integral_tsum_of_summable_integral_norm
      (integrable_heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ hψ (zero_lt_one.trans hs))
      (summable_integral_norm_heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ hψ hs),
    ← tsum_mul_left]
  simp_rw [integral_heckeDualClassRadialMellinKernel 𝔪 hb hb0 ψ hψ (zero_lt_one.trans hs)]
  rw [tsum_mul_right, tsum_mul_right]
  simp only [heckeDualClassL, mul_assoc]

/-- The symmetric actual theta continuation is its inverse-character class Mellin series on `Re s > 1`. -/
theorem heckeUnitThetaMellinPair_symm_eq_dualClassL (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 1 < s.re) :
    (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).symm.Λ (heckeThetaMellinArgument 𝔪 ψ s) =
        (Units.torsionOrder K : ℂ) * heckeDualClassL 𝔪 hb0 ψ s *
          heckeDualMellinFactor 𝔪 hb0 ψ s *
            (heckeGammaFactor 𝔪 ψ⁻¹ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  have hm : HasMellin (fun t : ℝ => heckeUnitAveragedDualTheta 𝔪 hb ψ t -
      (Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ)
      (heckeThetaMellinArgument 𝔪 ψ s)
      ((heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).symm.Λ (heckeThetaMellinArgument 𝔪 ψ s)) := by
    by_cases hpar : HTGeometry.IntegerLatticePoisson.parityDegree (heckeCoordinateParity 𝔪 ψ) = 0
    · apply (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ).symm.hasMellin
      have hn : 0 < (Module.finrank ℚ K : ℝ) := by
        rw [← numberFieldInfinitePlaceWeight_eq_finrank]
        exact numberFieldInfinitePlaceWeight_pos
      change heckeThetaMellinWeight 𝔪 ψ < (heckeThetaMellinArgument 𝔪 ψ s).re
      simp only [heckeThetaMellinWeight, heckeThetaMellinArgument, hpar,
        Nat.cast_zero, add_zero, Complex.div_ofNat_re, Complex.mul_re,
        Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      nlinarith [mul_pos hn (sub_pos.mpr hs)]
    · have hstrong := (heckeUnitThetaMellinPair_isStrong_of_parity_ne_zero 𝔪 hb hb0 ψ hpar).symm
      have hz : (Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ = 0 := by
        simpa only [WeakFEPair.symm, heckeUnitThetaMellinPair, Complex.real_smul] using hstrong.hf₀
      simp only [hz, sub_zero]
      exact hstrong.hasMellin (heckeThetaMellinArgument 𝔪 ψ s)
  rw [heckeGammaFactor_inv]
  exact hm.2.symm.trans (mellin_heckeUnitAveragedDualTheta_eq_dualClassL 𝔪 hb hb0 ψ hψ hs)

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.mellin_heckeUnitAveragedDualTheta_eq_dualClassL
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeUnitThetaMellinPair_symm_eq_dualClassL
