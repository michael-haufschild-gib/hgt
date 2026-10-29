import GaloisForLFunctions.HeckeLFunctions.HeckeGammaFactorsAreArchimedeanMellinIntegrals
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaWeightsArePrincipalIdealCharacters
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaHasMellinContinuation

/-!
# Exact Mellin integrals of actual Hecke element kernels

For a nonzero algebraic integer, logarithmic place coordinates separate the
radial degree, unit logarithms, and principal-ideal norm. Finite weights and
real signs combine into the principal-ideal Hecke value. The actual Mellin
density is therefore its ideal summand times a translated archimedean kernel.

Translation invariance and the exact radial Jacobian prove joint absolute
integrability on `Re s > 0`. Fubini then gives the whole-unit-log Mellin value,
with Gamma factor divided by `degree * 2^unitRank`. The integral of the norm
also separates into the ideal-summand norm and one common archimedean mass.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open MeasureTheory
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- Logarithms of all archimedean absolute values of a field element. -/
def heckeElementLogProfile (a : K) (v : InfinitePlace K) : ℝ := Real.log (v a)

/-- The multiplicity-weighted logarithms recover the norm of the principal ideal. -/
theorem sum_mult_heckeElementLogProfile (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    ∑ v : InfinitePlace K, (mult v : ℝ) * heckeElementLogProfile (a : K) v =
      Real.log (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  have h := mixedEmbedding.fundamentalCone.sum_expMap_symm_apply ha
  simp only [mixedEmbedding.fundamentalCone.expMap_symm_apply,
    mixedEmbedding.normAtAllPlaces_mixedEmbedding] at h
  rw [← mixedEmbedding.norm_eq_norm, norm_mixedEmbedding_eq_absNorm] at h
  exact h

/-- The independent-place kernel is one exponential with weighted linear and Gaussian terms. -/
theorem heckeArchimedeanLogKernel_eq_exp (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (u : InfinitePlace K → ℝ) :
    heckeArchimedeanLogKernel 𝔪 ψ s u =
      Complex.exp (s * (∑ v : InfinitePlace K, (mult v : ℝ) * u v : ℝ) +
        ∑ v : InfinitePlace K, (heckePlaceParity 𝔪 ψ v : ℂ) * (u v : ℂ) -
        (Real.pi : ℂ) * (∑ v : InfinitePlace K,
          (mult v : ℝ) * Real.exp (2 * u v) : ℝ)) := by
  simp only [heckeArchimedeanLogKernel, logGaussianMellinKernel,
    Complex.ofReal_exp, ← Complex.exp_add]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- The positive part of the real monomial is an exponential of the actual place parities. -/
theorem heckeRealMonomial_eq_sign_mul_exp (ψ : HeckeCharacter 𝔪)
    (y : InfinitePlace K → ℝ) (α : Kˣ) :
    heckeRealMonomial 𝔪 ψ (numberFieldMixedPlaceScale y (mixedEmbedding K (α : K))) =
      (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 α) : ℂ) *
        Complex.exp (∑ v : InfinitePlace K, (heckePlaceParity 𝔪 ψ v : ℂ) *
          ((-y v + heckeElementLogProfile (α : K) v : ℝ) : ℂ)) := by
  rw [heckeRealMonomial_eq_sign_mul_placeProduct, sum_heckePlaceParity_mul,
    Complex.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  have hp : 0 < w.1.1 (α : K) := InfinitePlace.pos_iff.mpr α.ne_zero
  rw [Complex.exp_nat_mul, heckeElementLogProfile, ← Complex.ofReal_exp,
    Real.exp_add, Real.exp_log hp]

/-- Finite weight and real signs turn the actual theta kernel into a principal-ideal coefficient. -/
theorem heckeThetaKernel_eq_exp (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ)
    (t : ℝ) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    heckeThetaKernel 𝔪 ψ y t a = heckeValue 𝔪 ψ (Ideal.span {a}) *
      Complex.exp ((∑ v : InfinitePlace K, (heckePlaceParity 𝔪 ψ v : ℂ) *
        ((-y v + heckeElementLogProfile (a : K) v : ℝ) : ℂ)) -
          (Real.pi * t : ℂ) * (∑ v : InfinitePlace K,
            (mult v : ℝ) * (Real.exp (-y v) * v (a : K)) ^ 2 : ℝ)) := by
  rw [heckeThetaKernel, parityGaussian, parityMonomial_heckeCoordinateParity]
  rw [show (a : K) = (Units.mk0 (a : K) ha : K) by rfl,
    heckeRealMonomial_eq_sign_mul_exp]
  simp only [Units.val_mk0]
  rw [gaussianKernel, ← Complex.ofReal_pow, norm_sq_numberFieldTraceCoordinates]
  simp_rw [normAtPlace_numberFieldMixedPlaceScale, mixedEmbedding.normAtPlace_apply]
  rw [← mul_assoc, ← mul_assoc, integralHeckeWeight_mul_infiniteSign_eq_heckeValue,
    mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Weighted element coordinates split into radial degree and the principal-ideal norm. -/
theorem sum_mult_radialLogParam_add_element (p : ℝ × logSpace K)
    (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    (∑ v : InfinitePlace K, (mult v : ℝ) *
      (numberFieldRadialLogParam p + heckeElementLogProfile (a : K)) v) =
        (Module.finrank ℚ K : ℝ) * p.1 + Real.log (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  simp only [Pi.add_apply, numberFieldRadialLogParam, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_mult_numberFieldWeightedLogProfile, sub_zero,
    sum_mult_heckeElementLogProfile a ha, ← Nat.cast_sum, sum_mult_eq]

/-- Actual parity coordinates split into the Mellin degree and the scaled real monomial. -/
theorem sum_parity_radialLogParam_add_element (ψ : HeckeCharacter 𝔪)
    (p : ℝ × logSpace K) (a : K) :
    (∑ v : InfinitePlace K, (heckePlaceParity 𝔪 ψ v : ℂ) *
      ((numberFieldRadialLogParam p + heckeElementLogProfile a) v : ℂ)) =
        (parityDegree (heckeCoordinateParity 𝔪 ψ) : ℂ) * (p.1 : ℂ) +
          ∑ v : InfinitePlace K, (heckePlaceParity 𝔪 ψ v : ℂ) *
            ((-numberFieldWeightedLogProfile p.2 v + heckeElementLogProfile a v : ℝ) : ℂ) := by
  rw [← sum_heckePlaceParity]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Pi.add_apply, numberFieldRadialLogParam, Complex.ofReal_add,
    Complex.ofReal_sub]
  ring

/-- The logarithmic place Gaussian is exactly the radially scaled trace Gaussian. -/
theorem sum_gaussian_radialLogParam_add_element (p : ℝ × logSpace K)
    (a : K) (ha : a ≠ 0) :
    (∑ v : InfinitePlace K, (mult v : ℝ) *
      Real.exp (2 * (numberFieldRadialLogParam p + heckeElementLogProfile a) v)) =
        Real.exp (2 * p.1) * ∑ v : InfinitePlace K,
          (mult v : ℝ) * (Real.exp (-numberFieldWeightedLogProfile p.2 v) * v a) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hp : 0 < v a := InfinitePlace.pos_iff.mpr ha
  have htwo : Real.exp (2 * (-numberFieldWeightedLogProfile p.2 v + Real.log (v a))) =
      Real.exp (-numberFieldWeightedLogProfile p.2 v + Real.log (v a)) ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  simp only [Pi.add_apply, numberFieldRadialLogParam, heckeElementLogProfile]
  rw [show 2 * (p.1 - numberFieldWeightedLogProfile p.2 v + Real.log (v a)) =
    2 * p.1 + 2 * (-numberFieldWeightedLogProfile p.2 v + Real.log (v a)) by ring,
    Real.exp_add, htwo,
    Real.exp_add, Real.exp_log hp]
  ring

private theorem heckeThetaKernel_logMellin_eq_exp (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (p : ℝ × logSpace K) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1)) a =
        (heckeValue 𝔪 ψ (Ideal.span {a}) *
          Complex.exp (-s * (Real.log (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ))) *
            heckeArchimedeanLogKernel 𝔪 ψ s
              (numberFieldRadialLogParam p + heckeElementLogProfile (a : K)) := by
  rw [heckeThetaKernel_eq_exp 𝔪 ψ _ _ a ha, heckeArchimedeanLogKernel_eq_exp,
    sum_mult_radialLogParam_add_element p a ha,
    sum_parity_radialLogParam_add_element,
    sum_gaussian_radialLogParam_add_element p (a : K) ha]
  rw [mul_left_comm (Complex.exp _) (heckeValue 𝔪 ψ (Ideal.span {a}))]
  simp only [mul_assoc]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [heckeThetaMellinArgument]
  push_cast
  ring

private theorem exp_neg_mul_log_absNorm (s : ℂ) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    Complex.exp (-s * (Real.log (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)) =
      (Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s) := by
  have hi : Ideal.span {a} ≠ (⊥ : Ideal (𝓞 K)) := by
    intro h
    have ha0 := Ideal.span_singleton_eq_bot.mp h
    exact ha (by rw [ha0]; rfl)
  have hn : Ideal.absNorm (Ideal.span {a}) ≠ 0 :=
    Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero hi)
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), Complex.natCast_log, mul_comm]

/-- The actual logarithmic Mellin density is a translated place kernel with its ideal summand. -/
theorem heckeThetaKernel_logMellin_eq (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (p : ℝ × logSpace K) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1)) a =
        (heckeValue 𝔪 ψ (Ideal.span {a}) * (Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s)) *
          heckeArchimedeanLogKernel 𝔪 ψ s
            (numberFieldRadialLogParam p + heckeElementLogProfile (a : K)) := by
  rw [heckeThetaKernel_logMellin_eq_exp 𝔪 ψ s p a ha, exp_neg_mul_log_absNorm s a ha]

/-- The actual element Mellin density is jointly absolutely integrable on radial and unit logs. -/
theorem integrable_heckeThetaKernel_logMellin (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    Integrable (fun p : ℝ × logSpace K =>
      Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
        heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1)) a) := by
  simp_rw [heckeThetaKernel_logMellin_eq 𝔪 ψ s _ a ha]
  exact ((integrable_numberFieldRadialLogParam_iff _).mpr
    ((integrable_heckeArchimedeanLogKernel 𝔪 ψ hs).comp_add_right
      (heckeElementLogProfile (a : K)))).const_mul _

/-- The absolute Mellin mass separates into the ideal summand norm and one common place integral. -/
theorem integral_norm_heckeThetaKernel_logMellin (ψ : HeckeCharacter 𝔪)
    (s : ℂ) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    (∫ p : ℝ × logSpace K,
      ‖Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
        heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1)) a‖) =
      ‖heckeValue 𝔪 ψ (Ideal.span {a}) * (Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s)‖ *
        ∫ p : ℝ × logSpace K,
          ‖heckeArchimedeanLogKernel 𝔪 ψ s (numberFieldRadialLogParam p)‖ := by
  have hmap (f : (InfinitePlace K → ℝ) → ℝ) :
      (∫ p : ℝ × logSpace K, f (numberFieldRadialLogParam p)) =
        (ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K / Module.finrank ℚ K)).toReal •
          ∫ u, f u := by
    rw [← measurableEmbedding_numberFieldRadialLogParam.integral_map,
      map_numberFieldRadialLogParam_volume, integral_smul_measure]
  simp_rw [heckeThetaKernel_logMellin_eq 𝔪 ψ s _ a ha, norm_mul]
  rw [integral_const_mul,
    hmap (fun u => ‖heckeArchimedeanLogKernel 𝔪 ψ s (u + heckeElementLogProfile (a : K))‖),
    hmap (fun u => ‖heckeArchimedeanLogKernel 𝔪 ψ s u‖),
    integral_add_right_eq_self (fun u => ‖heckeArchimedeanLogKernel 𝔪 ψ s u‖)
      (heckeElementLogProfile (a : K))]

/-- Haar translation removes the element logarithms from the archimedean integral. -/
theorem integral_heckeThetaKernel_logMellin (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    (2 : ℂ) * (∫ p : ℝ × logSpace K,
      Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
        heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1)) a) =
      (heckeValue 𝔪 ψ (Ideal.span {a}) * (Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s)) *
          (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  have htrans : (∫ p : ℝ × logSpace K, heckeArchimedeanLogKernel 𝔪 ψ s
      (numberFieldRadialLogParam p + heckeElementLogProfile (a : K))) =
        ∫ p : ℝ × logSpace K, heckeArchimedeanLogKernel 𝔪 ψ s
          (numberFieldRadialLogParam p) := by
    rw [integral_numberFieldRadialLogParam (fun u => heckeArchimedeanLogKernel 𝔪 ψ s
      (u + heckeElementLogProfile (a : K))),
      integral_numberFieldRadialLogParam (heckeArchimedeanLogKernel 𝔪 ψ s),
      integral_add_right_eq_self]
  simp_rw [heckeThetaKernel_logMellin_eq 𝔪 ψ s _ a ha]
  rw [integral_const_mul, htrans, mul_left_comm,
    integral_heckeArchimedeanLogKernel_radial 𝔪 ψ hs]

/-- Fubini gives absolute Mellin convergence of the actual whole-unit-log element integral. -/
theorem mellinConvergent_integral_heckeThetaKernel (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    MellinConvergent (fun t : ℝ => ∫ x : logSpace K,
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a)
        (heckeThetaMellinArgument 𝔪 ψ s) := by
  apply (mellinConvergent_iff_integrable_exp_two _ _).mpr
  have h := (integrable_heckeThetaKernel_logMellin 𝔪 ψ hs a ha).integral_prod_left
  simpa only [integral_const_mul] using h

/-- The whole-unit-log element integral has the exact archimedean Mellin value. -/
theorem mellin_integral_heckeThetaKernel (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (a : 𝓞 K) (ha : (a : K) ≠ 0) :
    mellin (fun t : ℝ => ∫ x : logSpace K,
      heckeThetaKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a)
        (heckeThetaMellinArgument 𝔪 ψ s) =
      (heckeValue 𝔪 ψ (Ideal.span {a}) * (Ideal.absNorm (Ideal.span {a}) : ℂ) ^ (-s)) *
          (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  rw [RHTower.mellin_eq_integral_exp_two]
  have hF := integral_prod _ (integrable_heckeThetaKernel_logMellin 𝔪 ψ hs a ha)
  simp only [integral_const_mul] at hF
  rw [← hF]
  exact integral_heckeThetaKernel_logMellin 𝔪 ψ hs a ha

end GaloisForLFunctions.HeckeLFunctions
