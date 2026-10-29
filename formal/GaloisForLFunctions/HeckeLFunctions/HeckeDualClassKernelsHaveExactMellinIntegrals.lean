import GaloisForLFunctions.HeckeLFunctions.HeckeDualFrequenciesHaveClassGenerators
import GaloisForLFunctions.HeckeLFunctions.HeckeFieldElementKernelsHaveExactMellinIntegrals
import GaloisForLFunctions.HeckeLFunctions.HeckeDualThetaKernelsAreUnitCovariant
import GaloisForLFunctions.HeckeLFunctions.HeckeLSeriesHaveEulerProducts

/-!
# Exact Mellin integrals of actual dual class kernels

The selected trace-dual generator contributes its inverse Hecke ideal
term times a common Gauss, base-character, and fractional-norm factor.
Translation in archimedean logarithms gives joint integrability, the
exact Gamma integral, and an absolute-mass identity. Absolute inverse
ideal-series convergence controls the sum of all class Mellin masses.
-/

noncomputable section
open NumberField NumberField.Units.dirichletUnitTheorem MeasureTheory
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
  {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- The common arithmetic and fractional-norm factor in the actual dual class Mellin transform. -/
def heckeDualMellinFactor (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  heckeGaussConstant 𝔪 ψ * heckeValue 𝔪 ψ b *
    (FractionalIdeal.absNorm (heckeDualIdealUnit 𝔪 hb0 : FI) : ℂ) ^ (-s)

/-- The selected dual frequency contributes the exact inverse-character ideal summand. -/
theorem heckeDualClassFrequency_mellinCoefficient (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (s : ℂ) (I : heckeDualClassIdeals 𝔪 hb0) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ (heckeDualClassFrequency 𝔪 hb0 I : K) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _
          (heckeDualClassFrequency_ne_zero 𝔪 hb0 I))) : ℂ) *
        ((|(Algebra.norm ℚ (heckeDualClassFrequency 𝔪 hb0 I : K) : ℝ)| : ℝ) : ℂ) ^ (-s) =
      heckeIdealTerm 𝔪 ψ⁻¹ s I.1 * heckeDualMellinFactor 𝔪 hb0 ψ s := by
  have hn : |(Algebra.norm ℚ (heckeDualClassFrequency 𝔪 hb0 I : K) : ℝ)| =
      (Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) *
        (FractionalIdeal.absNorm (heckeDualIdealUnit 𝔪 hb0 : FI) : ℝ) := by
    have h := norm_fractionalClassGenerator (heckeDualIdealUnit 𝔪 hb0) I
    change |(Algebra.norm ℚ (fractionalClassGenerator (heckeDualIdealUnit 𝔪 hb0) I) : ℝ)| = _
    exact_mod_cast h
  have hJ : 0 ≤ (FractionalIdeal.absNorm (heckeDualIdealUnit 𝔪 hb0 : FI) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg (heckeDualIdealUnit 𝔪 hb0 : FI)
  rw [finiteHeckeFourierCoefficient_classFrequency 𝔪 hb0 hb ψ hψ I, hn,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) hJ]
  change (heckeGaussConstant 𝔪 ψ * heckeValue 𝔪 ψ b * heckeValue 𝔪 ψ⁻¹ (I.1 : Ideal (𝓞 K))) *
      (((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-s) *
        ((FractionalIdeal.absNorm (heckeDualIdealUnit 𝔪 hb0 : FI) : ℝ) : ℂ) ^ (-s)) =
    (heckeValue 𝔪 ψ⁻¹ (I.1 : Ideal (𝓞 K)) *
      (Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ) ^ (-s)) *
    (heckeGaussConstant 𝔪 ψ * heckeValue 𝔪 ψ b *
      (FractionalIdeal.absNorm (heckeDualIdealUnit 𝔪 hb0 : FI) : ℂ) ^ (-s))
  push_cast
  ring

/-- The actual logarithmic Mellin density of the selected dual class frequency. -/
def heckeDualClassLogMellinKernel (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (I : heckeDualClassIdeals 𝔪 hb0) (p : ℝ × logSpace K) : ℂ :=
  Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
    heckeDualThetaKernel 𝔪 hb ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1))
      (heckeDualClassFrequency 𝔪 hb0 I : K)

/-- The actual dual density separates its inverse ideal term from a translated place kernel. -/
theorem heckeDualClassLogMellinKernel_eq (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (s : ℂ)
    (I : heckeDualClassIdeals 𝔪 hb0) (p : ℝ × logSpace K) :
    heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I p =
      (heckeIdealTerm 𝔪 ψ⁻¹ s I.1 * heckeDualMellinFactor 𝔪 hb0 ψ s) *
        heckeArchimedeanLogKernel 𝔪 ψ s (numberFieldRadialLogParam p +
          heckeElementLogProfile (heckeDualClassFrequency 𝔪 hb0 I : K)) := by
  let a := heckeDualClassFrequency 𝔪 hb0 I
  have h := heckeParityKernel_logMellin_eq 𝔪 ψ s p (a : K)
    (heckeDualClassFrequency_ne_zero 𝔪 hb0 I)
  change Complex.exp _ * (finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
    heckeParityKernel 𝔪 ψ _ _ (a : K)) = _
  rw [mul_left_comm (Complex.exp _) (finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K)), h,
    ← mul_assoc, ← mul_assoc]
  rw [heckeDualClassFrequency_mellinCoefficient 𝔪 hb hb0 ψ hψ s I]

/-- The actual dual class density is jointly absolutely integrable on `Re s > 0`. -/
theorem integrable_heckeDualClassLogMellinKernel (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 0 < s.re)
    (I : heckeDualClassIdeals 𝔪 hb0) :
    Integrable (heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I) := by
  change Integrable (fun p : ℝ × logSpace K => heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I p)
  simp_rw [heckeDualClassLogMellinKernel_eq 𝔪 hb hb0 ψ hψ]
  exact ((integrable_numberFieldRadialLogParam_iff _).mpr
    ((integrable_heckeArchimedeanLogKernel 𝔪 ψ hs).comp_add_right
      (heckeElementLogProfile (heckeDualClassFrequency 𝔪 hb0 I : K)))).const_mul _

/-- Absolute dual class masses are ideal-summand norms times one common archimedean mass. -/
theorem integral_norm_heckeDualClassLogMellinKernel (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (s : ℂ) (I : heckeDualClassIdeals 𝔪 hb0) :
    (∫ p : ℝ × logSpace K, ‖heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I p‖) =
      ‖heckeIdealTerm 𝔪 ψ⁻¹ s I.1‖ * (‖heckeDualMellinFactor 𝔪 hb0 ψ s‖ *
        ∫ p : ℝ × logSpace K, ‖heckeArchimedeanLogKernel 𝔪 ψ s (numberFieldRadialLogParam p)‖) := by
  let a := heckeDualClassFrequency 𝔪 hb0 I
  have he (p : ℝ × logSpace K) : ‖heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I p‖ =
      ‖finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K)‖ *
        ‖Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
          heckeParityKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1)) (a : K)‖ := by
    simp only [heckeDualClassLogMellinKernel, heckeDualThetaKernel, norm_mul, a]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_norm_heckeParityKernel_logMellin 𝔪 ψ s (a : K)
    (heckeDualClassFrequency_ne_zero 𝔪 hb0 I), ← mul_assoc]
  have hc := congrArg norm (heckeDualClassFrequency_mellinCoefficient 𝔪 hb hb0 ψ hψ s I)
  simp only [norm_mul, norm_char_eq_one, mul_one] at hc
  rw [hc, mul_assoc]

/-- Absolute convergence of the actual inverse Hecke series controls all dual class Mellin masses. -/
theorem summable_integral_norm_heckeDualClassLogMellinKernel (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : heckeDualClassIdeals 𝔪 hb0 =>
      ∫ p : ℝ × logSpace K, ‖heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I p‖) := by
  simp_rw [integral_norm_heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ hψ]
  exact ((summable_norm_heckeIdealTerm 𝔪 ψ⁻¹ hs).comp_injective
    (i := fun I : heckeDualClassIdeals 𝔪 hb0 => I.1) Subtype.val_injective).mul_right _

/-- The exact dual class integral retains the common Gauss factor and radial Jacobian. -/
theorem integral_heckeDualClassLogMellinKernel (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 0 < s.re)
    (I : heckeDualClassIdeals 𝔪 hb0) :
    (2 : ℂ) * (∫ p : ℝ × logSpace K, heckeDualClassLogMellinKernel 𝔪 hb hb0 ψ s I p) =
      heckeIdealTerm 𝔪 ψ⁻¹ s I.1 * heckeDualMellinFactor 𝔪 hb0 ψ s *
        (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  have htrans : (∫ p : ℝ × logSpace K, heckeArchimedeanLogKernel 𝔪 ψ s
      (numberFieldRadialLogParam p + heckeElementLogProfile
        (heckeDualClassFrequency 𝔪 hb0 I : K))) =
        ∫ p : ℝ × logSpace K, heckeArchimedeanLogKernel 𝔪 ψ s (numberFieldRadialLogParam p) := by
    rw [integral_numberFieldRadialLogParam (fun u => heckeArchimedeanLogKernel 𝔪 ψ s
      (u + heckeElementLogProfile (heckeDualClassFrequency 𝔪 hb0 I : K))),
      integral_numberFieldRadialLogParam (heckeArchimedeanLogKernel 𝔪 ψ s), integral_add_right_eq_self]
  simp_rw [heckeDualClassLogMellinKernel_eq 𝔪 hb hb0 ψ hψ]
  rw [integral_const_mul, htrans, mul_left_comm,
    integral_heckeArchimedeanLogKernel_radial 𝔪 ψ hs]

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.heckeDualClassFrequency_mellinCoefficient
#print axioms GaloisForLFunctions.HeckeLFunctions.integrable_heckeDualClassLogMellinKernel
#print axioms GaloisForLFunctions.HeckeLFunctions.summable_integral_norm_heckeDualClassLogMellinKernel
#print axioms GaloisForLFunctions.HeckeLFunctions.integral_heckeDualClassLogMellinKernel
