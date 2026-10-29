import GaloisForLFunctions.HeckeLFunctions.HeckeIdealThetaIsUnitPeriodic
import GaloisForLFunctions.HTGeometry.LogarithmicGaussianMellin
import GaloisForLFunctions.HTGeometry.NumberFieldRadialLogarithmicJacobian

/-!
# Hecke Gamma factors from actual archimedean Mellin integrals

Extend the character's real parities by zero at complex places. The resulting
place Gaussian product integrates to the standard Gamma product with a factor
`1/2` per real place and `1/4` per complex place. The radial/unit-log Jacobian
therefore gives the exact Mellin normalization `1/(degree * 2^unitRank)`.

Absolute convergence holds on `Re s > 0`. The Gamma product is nonzero there,
and its reciprocal is entire.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open MeasureTheory
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- The actual real-character parity, extended by zero to complex places. -/
def heckePlaceParity (ψ : HeckeCharacter 𝔪) (v : InfinitePlace K) : ℕ :=
  if h : v.IsReal then (heckeCoordinateParity 𝔪 ψ (Sum.inl ⟨v, h⟩)).toNat else 0

theorem heckePlaceParity_real (ψ : HeckeCharacter 𝔪) (v : {v : InfinitePlace K // v.IsReal}) :
    heckePlaceParity 𝔪 ψ v.1 = (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat := by
  simp only [heckePlaceParity, dif_pos v.2]

theorem heckePlaceParity_complex (ψ : HeckeCharacter 𝔪) (v : {v : InfinitePlace K // v.IsComplex}) :
    heckePlaceParity 𝔪 ψ v.1 = 0 := by
  simp only [heckePlaceParity, dif_neg (not_isReal_iff_isComplex.mpr v.2)]

/-- Place parities have the same total degree as the actual trace-coordinate monomial. -/
theorem sum_heckePlaceParity (ψ : HeckeCharacter 𝔪) :
    ∑ v : InfinitePlace K, heckePlaceParity 𝔪 ψ v = parityDegree (heckeCoordinateParity 𝔪 ψ) := by
  rw [sum_eq_sum_add_sum, parityDegree, Fintype.sum_sum_type]
  simp only [heckePlaceParity_real, heckePlaceParity_complex, Finset.sum_const_zero,
    heckeCoordinateParity, Bool.toNat_false, add_zero]

/-- Place-parity sums retain exactly the real places selected by the modulus. -/
theorem sum_heckePlaceParity_mul (ψ : HeckeCharacter 𝔪) (f : InfinitePlace K → ℂ) :
    ∑ v : InfinitePlace K, (heckePlaceParity 𝔪 ψ v : ℂ) * f v =
      ∑ w : 𝔪.inf, (heckeParity 𝔪 ψ w : ℂ) * f w.1.1 := by
  rw [sum_eq_sum_add_sum]
  simp only [heckePlaceParity_real, heckePlaceParity_complex, Nat.cast_zero,
    zero_mul, Finset.sum_const_zero, add_zero]
  have h (v : {v : InfinitePlace K // v.IsReal}) :
      ((heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat : ℂ) * f v.1 =
        if hv : v ∈ 𝔪.inf then (heckeParity 𝔪 ψ ⟨v, hv⟩ : ℂ) * f v.1 else 0 := by
    simp only [heckeCoordinateParity]
    split_ifs with hv
    · rw [heckeParity_decide]
    · simp only [Bool.toNat_false, Nat.cast_zero, zero_mul]
  simp_rw [h]
  simp only [Finset.sum_dite, Finset.sum_const_zero, add_zero]
  exact (Equiv.subtypeEquivRight <| by simp).sum_comp
    (fun w : 𝔪.inf => (heckeParity 𝔪 ψ w : ℂ) * f w.1.1)

/-- Standard real and complex Gamma factors attached to the actual Hecke character. -/
def heckeGammaFactor (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  (∏ v : {v : InfinitePlace K // v.IsReal},
    Complex.Gammaℝ (s + (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat)) *
      Complex.Gammaℂ s ^ nrComplexPlaces K

/-- The actual Gamma product is nonzero in the open right half-plane. -/
theorem heckeGammaFactor_ne_zero (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 0 < s.re) :
    heckeGammaFactor 𝔪 ψ s ≠ 0 := by
  have hr (e : ℕ) : 0 < (s + (e : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    exact add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg e)
  have hc : Complex.Gammaℂ s ≠ 0 := by
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs)
      (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hr 1))
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun v _ => Complex.Gammaℝ_ne_zero_of_re_pos (hr _)))
    (pow_ne_zero _ hc)

/-- The reciprocal of the actual Gamma product is entire, including its trivial-zero factors. -/
theorem differentiable_heckeGammaFactor_inv (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (fun s => (heckeGammaFactor 𝔪 ψ s)⁻¹) := by
  have heq : (fun s => (heckeGammaFactor 𝔪 ψ s)⁻¹) =
      (fun s => (∏ v : {v : InfinitePlace K // v.IsReal},
        (Complex.Gammaℝ (s + (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat))⁻¹) *
          ((Complex.Gammaℝ s)⁻¹ * (Complex.Gammaℝ (s + 1))⁻¹) ^ nrComplexPlaces K) := by
    funext s
    simp only [heckeGammaFactor, ← Complex.Gammaℝ_mul_Gammaℝ_add_one, mul_inv,
      ← Finset.prod_inv_distrib, ← inv_pow]
  rw [heq]
  apply Differentiable.mul
  · exact Differentiable.fun_finsetProd fun v _ =>
      Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const _)
  · exact (Complex.differentiable_Gammaℝ_inv.mul
      (Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1))).pow _

/-- Independent place-logarithmic Gaussian factors with the actual multiplicities and parities. -/
def heckeArchimedeanLogKernel (ψ : HeckeCharacter 𝔪) (s : ℂ) (u : InfinitePlace K → ℝ) : ℂ :=
  ∏ v : InfinitePlace K, logGaussianMellinKernel (Real.pi * (mult v : ℝ))
    (((mult v : ℂ) * s + heckePlaceParity 𝔪 ψ v) / 2) (u v)

private theorem heckePlaceMellinExponent_re_pos (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) (v : InfinitePlace K) :
    0 < (((mult v : ℂ) * s + heckePlaceParity 𝔪 ψ v) / 2).re := by
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  exact div_pos (add_pos_of_pos_of_nonneg
    (mul_pos (Nat.cast_pos.mpr mult_pos) hs) (Nat.cast_nonneg _)) zero_lt_two

/-- The actual archimedean product is absolutely integrable throughout `Re s > 0`. -/
theorem integrable_heckeArchimedeanLogKernel (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) : Integrable (heckeArchimedeanLogKernel 𝔪 ψ s) :=
  integrable_logGaussianMellinProduct _ _
    (fun _ => mul_pos Real.pi_pos (Nat.cast_pos.mpr mult_pos))
    (heckePlaceMellinExponent_re_pos 𝔪 ψ hs)

/-- Real places contribute `GammaR/2`, and complex places contribute `GammaC/4`. -/
theorem integral_heckeArchimedeanLogKernel (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ u : InfinitePlace K → ℝ, heckeArchimedeanLogKernel 𝔪 ψ s u) =
      heckeGammaFactor 𝔪 ψ s / ((2 : ℂ) ^ nrRealPlaces K * (4 : ℂ) ^ nrComplexPlaces K) := by
  have hr (v : {v : InfinitePlace K // v.IsReal}) :
      (∫ u : ℝ, logGaussianMellinKernel (Real.pi * (mult v.1 : ℝ))
        (((mult v.1 : ℂ) * s + heckePlaceParity 𝔪 ψ v.1) / 2) u) =
      Complex.Gammaℝ (s + (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat) / 2 := by
    simp only [mult_isReal, Nat.cast_one, mul_one, one_mul, heckePlaceParity_real]
    exact integral_logGaussianMellinKernel_real hs _
  have hc (v : {v : InfinitePlace K // v.IsComplex}) :
      (∫ u : ℝ, logGaussianMellinKernel (Real.pi * (mult v.1 : ℝ))
        (((mult v.1 : ℂ) * s + heckePlaceParity 𝔪 ψ v.1) / 2) u) =
      Complex.Gammaℂ s / 4 := by
    simp only [mult_isComplex, Nat.cast_ofNat, heckePlaceParity_complex, Nat.cast_zero, add_zero]
    rw [show (2 * s) / 2 = s by ring, mul_comm Real.pi 2]
    exact integral_logGaussianMellinKernel_complex hs
  simp only [heckeArchimedeanLogKernel]
  rw [integral_fintype_prod_volume_eq_prod, prod_eq_prod_mul_prod]
  simp_rw [hr, hc]
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  rw [div_mul_div_comm]
  rfl

/-- The radial/unit-log kernel inherits absolute integrability from independent place coordinates. -/
theorem integrable_heckeArchimedeanLogKernel_radial (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun p : ℝ × logSpace K =>
      heckeArchimedeanLogKernel 𝔪 ψ s (numberFieldRadialLogParam p)) :=
  (integrable_numberFieldRadialLogParam_iff _).mpr
    (integrable_heckeArchimedeanLogKernel 𝔪 ψ hs)

/-- The exact archimedean Mellin normalization is `1 / (degree * 2^unitRank)`. -/
theorem integral_heckeArchimedeanLogKernel_radial (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 0 < s.re) :
    (2 : ℂ) * (∫ p : ℝ × logSpace K,
      heckeArchimedeanLogKernel 𝔪 ψ s (numberFieldRadialLogParam p)) =
      heckeGammaFactor 𝔪 ψ s / ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K) := by
  have hr : Units.rank K + 1 = nrRealPlaces K + nrComplexPlaces K := by
    have hp : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    rw [Units.rank, ← card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  have hd : (2 : ℂ) ^ nrRealPlaces K * (4 : ℂ) ^ nrComplexPlaces K =
      2 ^ Units.rank K * 2 ^ nrComplexPlaces K * 2 := by
    rw [show (4 : ℂ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_add,
      ← pow_add, ← pow_succ]
    congr 1
    omega
  have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := by
    have hp : 0 < (Module.finrank ℚ K : ℝ) := by
      rw [← numberFieldInfinitePlaceWeight_eq_finrank]
      exact numberFieldInfinitePlaceWeight_pos
    exact_mod_cast hp.ne'
  rw [integral_numberFieldRadialLogParam, integral_heckeArchimedeanLogKernel 𝔪 ψ hs, hd]
  push_cast
  field_simp

end GaloisForLFunctions.HeckeLFunctions
