import GaloisForLFunctions.HeckeLFunctions.HeckeElementKernelsHaveExactMellinIntegrals

/-!
# Exact Mellin integrals for nonzero field elements

The parity kernel of any nonzero field element has Mellin coefficient equal to its
infinite sign character times its absolute norm to the power `-s`. Translation in
archimedean logarithms gives joint absolute integrability, the exact Gamma factor,
and an absolute-mass formula uniform in the element. Haar negation also covers
the negative logarithmic profile occurring in dual theta averages.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem MeasureTheory
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- Weighted logarithms recover the absolute field norm also for nonintegral field elements. -/
theorem sum_mult_heckeElementLogProfile_field (a : K) (ha : a ≠ 0) :
    ∑ v : InfinitePlace K, (mult v : ℝ) * heckeElementLogProfile a v =
      Real.log |(Algebra.norm ℚ a : ℝ)| := by
  simpa only [heckeElementLogProfile, mixedEmbedding.fundamentalCone.expMap_symm_apply,
    mixedEmbedding.normAtAllPlaces_mixedEmbedding, Rat.cast_abs] using
      mixedEmbedding.fundamentalCone.sum_expMap_symm_apply ha

/-- The parity kernel separates the actual sign character from its positive Gaussian factor. -/
theorem heckeParityKernel_eq_exp (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ)
    (t : ℝ) (a : K) (ha : a ≠ 0) :
    heckeParityKernel 𝔪 ψ y t a =
      (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 a ha)) : ℂ) *
        Complex.exp ((∑ v : InfinitePlace K, (heckePlaceParity 𝔪 ψ v : ℂ) *
          ((-y v + heckeElementLogProfile a v : ℝ) : ℂ)) -
            (Real.pi * t : ℂ) * (∑ v : InfinitePlace K,
              (mult v : ℝ) * (Real.exp (-y v) * v a) ^ 2 : ℝ)) := by
  rw [heckeParityKernel, parityGaussian, parityMonomial_heckeCoordinateParity]
  have hm := heckeRealMonomial_eq_sign_mul_exp 𝔪 ψ y (Units.mk0 a ha)
  simp only [Units.val_mk0] at hm
  rw [hm]
  rw [gaussianKernel, ← Complex.ofReal_pow, norm_sq_numberFieldTraceCoordinates]
  simp_rw [normAtPlace_numberFieldMixedPlaceScale, mixedEmbedding.normAtPlace_apply]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A field element contributes its exact absolute norm to radial logarithmic coordinates. -/
theorem sum_mult_radialLogParam_add_fieldElement (p : ℝ × logSpace K)
    (a : K) (ha : a ≠ 0) :
    (∑ v : InfinitePlace K, (mult v : ℝ) *
      (numberFieldRadialLogParam p + heckeElementLogProfile a) v) =
        (Module.finrank ℚ K : ℝ) * p.1 + Real.log |(Algebra.norm ℚ a : ℝ)| := by
  simp only [Pi.add_apply, numberFieldRadialLogParam, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_mult_numberFieldWeightedLogProfile, sub_zero,
    sum_mult_heckeElementLogProfile_field a ha, ← Nat.cast_sum, sum_mult_eq]

private theorem exp_neg_mul_log_fieldNorm (s : ℂ) (a : K) (ha : a ≠ 0) :
    Complex.exp (-s * (Real.log |(Algebra.norm ℚ a : ℝ)| : ℂ)) =
      ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  have hn : (Algebra.norm ℚ a : ℝ) ≠ 0 := by
    have hq : Algebra.norm ℚ a ≠ 0 := Algebra.norm_eq_zero_iff.not.mpr ha
    exact_mod_cast hq
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hn)),
    Complex.ofReal_log (abs_nonneg _), mul_comm]

/-- The actual field-element Mellin density is a translated archimedean kernel with sign and norm. -/
theorem heckeParityKernel_logMellin_eq (ψ : HeckeCharacter 𝔪) (s : ℂ)
    (p : ℝ × logSpace K) (a : K) (ha : a ≠ 0) :
    Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
      heckeParityKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1)) a =
        ((infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 a ha)) : ℂ) *
          ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ) ^ (-s)) *
            heckeArchimedeanLogKernel 𝔪 ψ s
              (numberFieldRadialLogParam p + heckeElementLogProfile a) := by
  rw [← exp_neg_mul_log_fieldNorm s a ha]
  rw [heckeParityKernel_eq_exp 𝔪 ψ _ _ a ha, heckeArchimedeanLogKernel_eq_exp,
    sum_mult_radialLogParam_add_fieldElement p a ha,
    sum_parity_radialLogParam_add_element,
    sum_gaussian_radialLogParam_add_element p a ha]
  rw [mul_left_comm (Complex.exp _) (infiniteSignCharacter 𝔪 ψ _ : ℂ)]
  simp only [mul_assoc]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [heckeThetaMellinArgument]
  push_cast
  ring

/-- Actual field-element densities are jointly absolutely integrable throughout `Re s > 0`. -/
theorem integrable_heckeParityKernel_logMellin (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (a : K) (ha : a ≠ 0) :
    Integrable (fun p : ℝ × logSpace K =>
      Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
        heckeParityKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1)) a) := by
  simp_rw [heckeParityKernel_logMellin_eq 𝔪 ψ s _ a ha]
  exact ((integrable_numberFieldRadialLogParam_iff _).mpr
    ((integrable_heckeArchimedeanLogKernel 𝔪 ψ hs).comp_add_right
      (heckeElementLogProfile a))).const_mul _

/-- Absolute Mellin mass separates into the field norm factor and one common place integral. -/
theorem integral_norm_heckeParityKernel_logMellin (ψ : HeckeCharacter 𝔪)
    (s : ℂ) (a : K) (ha : a ≠ 0) :
    (∫ p : ℝ × logSpace K,
      ‖Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
        heckeParityKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1)) a‖) =
      ‖((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ) ^ (-s)‖ *
        ∫ p : ℝ × logSpace K,
          ‖heckeArchimedeanLogKernel 𝔪 ψ s (numberFieldRadialLogParam p)‖ := by
  have hmap (f : (InfinitePlace K → ℝ) → ℝ) :
      (∫ p : ℝ × logSpace K, f (numberFieldRadialLogParam p)) =
        (ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K / Module.finrank ℚ K)).toReal •
          ∫ u, f u := by
    rw [← measurableEmbedding_numberFieldRadialLogParam.integral_map,
      map_numberFieldRadialLogParam_volume, integral_smul_measure]
  simp_rw [heckeParityKernel_logMellin_eq 𝔪 ψ s _ a ha, norm_mul,
    norm_char_eq_one, one_mul]
  rw [integral_const_mul,
    hmap (fun u => ‖heckeArchimedeanLogKernel 𝔪 ψ s (u + heckeElementLogProfile a)‖),
    hmap (fun u => ‖heckeArchimedeanLogKernel 𝔪 ψ s u‖),
    integral_add_right_eq_self (fun u => ‖heckeArchimedeanLogKernel 𝔪 ψ s u‖)
      (heckeElementLogProfile a)]

/-- Translation removes the field-element logarithms with the exact radial Jacobian. -/
theorem integral_heckeParityKernel_logMellin (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (a : K) (ha : a ≠ 0) :
    (2 : ℂ) * (∫ p : ℝ × logSpace K,
      Complex.exp (2 * heckeThetaMellinArgument 𝔪 ψ s * (p.1 : ℂ)) *
        heckeParityKernel 𝔪 ψ (numberFieldWeightedLogProfile p.2) (Real.exp (2 * p.1)) a) =
      ((infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 a ha)) : ℂ) *
          ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ) ^ (-s)) *
        (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  have htrans : (∫ p : ℝ × logSpace K, heckeArchimedeanLogKernel 𝔪 ψ s
      (numberFieldRadialLogParam p + heckeElementLogProfile a)) =
        ∫ p : ℝ × logSpace K, heckeArchimedeanLogKernel 𝔪 ψ s (numberFieldRadialLogParam p) := by
    rw [integral_numberFieldRadialLogParam (fun u => heckeArchimedeanLogKernel 𝔪 ψ s
      (u + heckeElementLogProfile a)),
      integral_numberFieldRadialLogParam (heckeArchimedeanLogKernel 𝔪 ψ s),
      integral_add_right_eq_self]
  simp_rw [heckeParityKernel_logMellin_eq 𝔪 ψ s _ a ha]
  rw [integral_const_mul, htrans, mul_left_comm,
    integral_heckeArchimedeanLogKernel_radial 𝔪 ψ hs]

/-- Fubini gives absolute Mellin convergence after integrating over all unit logarithms. -/
theorem mellinConvergent_integral_heckeParityKernel (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (a : K) (ha : a ≠ 0) :
    MellinConvergent (fun t : ℝ => ∫ x : logSpace K,
      heckeParityKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a)
        (heckeThetaMellinArgument 𝔪 ψ s) := by
  apply (mellinConvergent_iff_integrable_exp_two _ _).mpr
  have h := (integrable_heckeParityKernel_logMellin 𝔪 ψ hs a ha).integral_prod_left
  simpa only [integral_const_mul] using h

/-- The whole-unit-log field-element integral has the exact sign, norm, and Gamma factors. -/
theorem mellin_integral_heckeParityKernel (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (a : K) (ha : a ≠ 0) :
    mellin (fun t : ℝ => ∫ x : logSpace K,
      heckeParityKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a)
        (heckeThetaMellinArgument 𝔪 ψ s) =
      ((infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 a ha)) : ℂ) *
          ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ) ^ (-s)) *
        (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  rw [RHTower.mellin_eq_integral_exp_two]
  have hF := integral_prod _ (integrable_heckeParityKernel_logMellin 𝔪 ψ hs a ha)
  simp only [integral_const_mul] at hF
  rw [← hF]
  exact integral_heckeParityKernel_logMellin 𝔪 ψ hs a ha

/-- Negation preserves Haar measure on the full unit-log space. -/
theorem integral_heckeParityKernel_negativeLogProfile (ψ : HeckeCharacter 𝔪)
    (t : ℝ) (a : K) :
    (∫ x : logSpace K, heckeParityKernel 𝔪 ψ (-numberFieldWeightedLogProfile x) t a) =
      ∫ x : logSpace K, heckeParityKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a := by
  simpa only [map_neg] using integral_neg_eq_self
    (fun x : logSpace K => heckeParityKernel 𝔪 ψ (numberFieldWeightedLogProfile x) t a) volume

/-- The negative profile used by dual theta has the same whole-log Mellin convergence. -/
theorem mellinConvergent_integral_heckeParityKernel_negative (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (a : K) (ha : a ≠ 0) :
    MellinConvergent (fun t : ℝ => ∫ x : logSpace K,
      heckeParityKernel 𝔪 ψ (-numberFieldWeightedLogProfile x) t a)
        (heckeThetaMellinArgument 𝔪 ψ s) := by
  simpa only [integral_heckeParityKernel_negativeLogProfile] using
    mellinConvergent_integral_heckeParityKernel 𝔪 ψ hs a ha

/-- Dual negative-profile integration retains the exact sign, absolute norm, and Gamma factors. -/
theorem mellin_integral_heckeParityKernel_negative (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (a : K) (ha : a ≠ 0) :
    mellin (fun t : ℝ => ∫ x : logSpace K,
      heckeParityKernel 𝔪 ψ (-numberFieldWeightedLogProfile x) t a)
        (heckeThetaMellinArgument 𝔪 ψ s) =
      ((infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 a ha)) : ℂ) *
          ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ) ^ (-s)) *
        (heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K)) := by
  simpa only [integral_heckeParityKernel_negativeLogProfile] using
    mellin_integral_heckeParityKernel 𝔪 ψ hs a ha

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.heckeParityKernel_logMellin_eq
#print axioms GaloisForLFunctions.HeckeLFunctions.integrable_heckeParityKernel_logMellin
#print axioms GaloisForLFunctions.HeckeLFunctions.integral_norm_heckeParityKernel_logMellin
#print axioms GaloisForLFunctions.HeckeLFunctions.mellin_integral_heckeParityKernel
#print axioms GaloisForLFunctions.HeckeLFunctions.mellin_integral_heckeParityKernel_negative
