import GaloisForLFunctions.BiarithmeticGeometry.CriticalCoefficientDomain
import GaloisForLFunctions.BiarithmeticGeometry.ComplexCriticalWienerLift

/-!
# Actual Wiener realization of the normalized critical coefficient domain

The complex coefficient lift is a linear isometry. Its range is exactly
the actual Wiener kernels supported on powers of five, with inverse
given by normalized coefficients. Actual critical golden payment pulls
back to the square-partial-sum domain without an additional hypothesis.
-/

noncomputable section
open HTGeometry.ConstraintMotiveRelativity
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The normalized coefficient space as an isometric complex subspace of the actual Wiener algebra. -/
def criticalCoefficientLift : CriticalCoefficientSpace →ₗᵢ[ℂ] WienerAlgebraAt (1 / 2) where
  toFun g := fiveComplexCriticalWienerLift g (summable_norm_lp_one g)
  map_add' g h := by
    have hgh : Summable (fun r => ‖g r + (1 : ℂ) * h r‖) := by
      simpa only [one_mul, lp.coeFn_add, Pi.add_apply] using summable_norm_lp_one (g + h)
    simpa only [one_mul, one_smul, lp.coeFn_add, Pi.add_apply, Pi.add_def] using
      fiveComplexCriticalWienerLift_linear g h (summable_norm_lp_one g)
        (summable_norm_lp_one h) 1 hgh
  map_smul' z g := by
    apply WienerAlgebraAt.ext
    intro n
    change (fiveComplexCriticalWienerLift (z • g : CriticalCoefficientSpace) _).toFn n =
      z * (fiveComplexCriticalWienerLift g _).toFn n
    by_cases hn : n ∈ Set.range (fun r : ℕ => 5 ^ r)
    · obtain ⟨r, rfl⟩ := hn
      rw [fiveComplexCriticalWienerLift_pow, fiveComplexCriticalWienerLift_pow]
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [fiveComplexCriticalWienerLift_off_support _ _ n hn,
        fiveComplexCriticalWienerLift_off_support _ _ n hn, mul_zero]
  norm_map' g := by
    change ‖fiveComplexCriticalWienerLift g (summable_norm_lp_one g)‖ = ‖g‖
    rw [norm_fiveComplexCriticalWienerLift, norm_eq_tsum_one]

theorem criticalCoefficientLift_pow (g : CriticalCoefficientSpace) (r : ℕ) :
    (criticalCoefficientLift g).toFn (5 ^ r) = (Real.sqrt 5 : ℂ) ^ r * g r :=
  fiveComplexCriticalWienerLift_pow g (summable_norm_lp_one g) r

theorem criticalCoefficientLift_off_support (g : CriticalCoefficientSpace) (n : ℕ)
    (hn : n ∉ Set.range (fun r : ℕ => 5 ^ r)) : (criticalCoefficientLift g).toFn n = 0 :=
  fiveComplexCriticalWienerLift_off_support g (summable_norm_lp_one g) n hn

private theorem normalizedCoefficient_norm_eq_term (k : WienerAlgebraAt (1 / 2)) (r : ℕ) :
    ‖k.toFn (5 ^ r) / (Real.sqrt 5 : ℂ) ^ r‖ =
      ‖LSeries.term (⇑k.toFn) ((1 / 2 : ℝ) : ℂ) (5 ^ r)‖ := by
  have hs0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  have hs : Real.sqrt 5 ^ r ≠ 0 := (pow_pos hs0 r).ne'
  have hw : ((5 ^ r : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt 5 ^ r := by
    apply (eq_div_iff hs).mpr
    simpa only [mul_comm] using fiveCritical_weight_cancel r
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
    LSeries.norm_term_eq, if_neg (pow_ne_zero r (by omega : (5 : ℕ) ≠ 0)), Complex.ofReal_re]
  have hweight : ((5 ^ r : ℕ) : ℝ) ^ (-(1 * 2⁻¹ : ℝ)) = (Real.sqrt 5 ^ r)⁻¹ := by
    simpa only [div_eq_mul_inv, one_mul] using hw
  simp only [div_eq_mul_inv]
  rw [← Real.rpow_neg (Nat.cast_nonneg (5 ^ r)), hweight]

/-- Restricting any actual Wiener kernel to normalized five-power coordinates gives `ell1`. -/
theorem summable_norm_criticalNormalizedCoefficients (k : WienerAlgebraAt (1 / 2)) :
    Summable (fun r : ℕ => ‖k.toFn (5 ^ r) / (Real.sqrt 5 : ℂ) ^ r‖) := by
  have h := Summable.comp_injective
    (f := fun n : ℕ => ‖LSeries.term (⇑k.toFn) ((1 / 2 : ℝ) : ℂ) n‖)
    (i := fun r : ℕ => 5 ^ r) k.summable_norm (Nat.pow_right_injective (by omega : 2 ≤ 5))
  simpa only [normalizedCoefficient_norm_eq_term, Function.comp_def] using h

/-- The actual normalized coefficient restriction, with its summability discharged by the Wiener norm. -/
def criticalNormalizedCoefficients (k : WienerAlgebraAt (1 / 2)) : CriticalCoefficientSpace :=
  ⟨fun r => k.toFn (5 ^ r) / (Real.sqrt 5 : ℂ) ^ r, memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      summable_norm_criticalNormalizedCoefficients k)⟩

/-- Normalized restriction inverts the coefficient lift exactly. -/
theorem criticalNormalizedCoefficients_lift (g : CriticalCoefficientSpace) :
    criticalNormalizedCoefficients (criticalCoefficientLift g) = g := by
  apply lp.ext
  funext r
  change (criticalCoefficientLift g).toFn (5 ^ r) / (Real.sqrt 5 : ℂ) ^ r = g r
  rw [criticalCoefficientLift_pow]
  have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  field_simp [hs]

/-- Every actual one-prime supported kernel is recovered from its normalized coefficients. -/
theorem criticalCoefficientLift_normalizedCoefficients (k : WienerAlgebraAt (1 / 2))
    (hk : ∀ n : ℕ, n ∉ Set.range (fun r : ℕ => 5 ^ r) → k.toFn n = 0) :
    criticalCoefficientLift (criticalNormalizedCoefficients k) = k := by
  apply WienerAlgebraAt.ext
  intro n
  by_cases hn : n ∈ Set.range (fun r : ℕ => 5 ^ r)
  · obtain ⟨r, rfl⟩ := hn
    rw [criticalCoefficientLift_pow]
    change (Real.sqrt 5 : ℂ) ^ r * (k.toFn (5 ^ r) / (Real.sqrt 5 : ℂ) ^ r) = _
    have hs : (Real.sqrt 5 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
    field_simp [hs]
  · rw [criticalCoefficientLift_off_support _ n hn, hk n hn]

/-- The image of the linear isometry is exactly the actual prime-five subspace. -/
theorem mem_range_criticalCoefficientLift_iff (k : WienerAlgebraAt (1 / 2)) :
    k ∈ Set.range criticalCoefficientLift ↔
      ∀ n : ℕ, n ∉ Set.range (fun r : ℕ => 5 ^ r) → k.toFn n = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact criticalCoefficientLift_off_support g
  · intro hk
    exact ⟨criticalNormalizedCoefficients k, criticalCoefficientLift_normalizedCoefficients k hk⟩

/-- Actual critical golden payment is exactly the normalized coefficient domain. -/
theorem criticalCoefficientLift_mem_golden_paidIdeal_iff (g : CriticalCoefficientSpace) :
    criticalCoefficientLift g ∈ paidIdeal (goldenArithmeticSource goldenCriticalParameter)
      (summable_abs_goldenArithmeticSource_div _ goldenCriticalParameter_bounds.1.le
        goldenCriticalParameter_bounds.2.le) ↔ g ∈ criticalCoefficientDomain :=
  mem_golden_critical_fiveComplexCriticalWienerLift_iff g (summable_norm_lp_one g)

end GaloisForLFunctions.BiarithmeticGeometry

