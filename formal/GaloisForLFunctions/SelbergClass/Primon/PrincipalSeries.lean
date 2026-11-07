import GaloisForLFunctions.RHTower.RealSphericalHarishChandra

/-!
# The conformal principal series on the spherical weight lattice

Hartnoll–Yang, arXiv:2502.02661v2, (28)–(29), use conformal weight
`1/2 + iε` and positive Laplacian scalar `1/4 + ε²`. These are realized in
the existing spherical Harish-Chandra module at parameter `2iε`.
The raising and lowering coefficients never vanish on the integer weight
lattice; explicit inverse shifts rule out highest and lowest weight vectors.
-/

open GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The imaginary Harish-Chandra parameter of the conformal principal series. -/
def principalParameter (ε : ℝ) : ℂ := 2 * (ε : ℂ) * Complex.I

/-- Conformal dimension on the unitary principal line. -/
def principalConformalWeight (ε : ℝ) : ℂ := 1 / 2 + (ε : ℂ) * Complex.I

/-- Positive hyperbolic Laplacian scalar. -/
def principalEnergy (ε : ℝ) : ℝ := 1 / 4 + ε ^ 2

theorem principalParameter_sq (ε : ℝ) :
    principalParameter ε ^ 2 = -4 * (ε : ℂ) ^ 2 := by
  unfold principalParameter
  rw [mul_pow, mul_pow, Complex.I_sq]
  ring

/-- The conformal Casimir has the negative of the hyperbolic Laplacian scalar. -/
theorem principalConformalWeight_casimir (ε : ℝ) :
    principalConformalWeight ε * (principalConformalWeight ε - 1) =
      -(principalEnergy ε : ℂ) := by
  calc principalConformalWeight ε * (principalConformalWeight ε - 1) =
      -1 / 4 + (ε : ℂ) ^ 2 * Complex.I ^ 2 := by
        unfold principalConformalWeight
        ring
    _ = -(principalEnergy ε : ℂ) := by
      rw [Complex.I_sq]
      unfold principalEnergy
      push_cast
      ring

/-- The concrete spherical Laplacian realizes the principal-series energy. -/
theorem sphericalPrincipalLaplacian_principalParameter (ε : ℝ) :
    sphericalPrincipalLaplacian (principalParameter ε) =
      (principalEnergy ε : ℂ) • LinearMap.id := by
  rw [sphericalPrincipalLaplacian_eq_smul_id, principalParameter_sq]
  congr 1
  unfold principalEnergy
  push_cast
  ring

theorem principalEnergy_ge_quarter (ε : ℝ) : 1 / 4 ≤ principalEnergy ε := by
  unfold principalEnergy
  exact le_add_of_nonneg_right (sq_nonneg ε)

/-- Coefficient from weight `m` to weight `m+1`. -/
def principalRaiseCoefficient (ε : ℝ) (m : ℤ) : ℂ := ⟨-(m : ℝ) - 1 / 2, ε⟩

/-- Coefficient from weight `m` to weight `m-1`. -/
def principalLowerCoefficient (ε : ℝ) (m : ℤ) : ℂ := ⟨(m : ℝ) - 1 / 2, ε⟩

private theorem raiseCoefficient_eq (ε : ℝ) (m : ℤ) :
    principalRaiseCoefficient ε m = (principalParameter ε - 1 - 2 * (m : ℂ)) / 2 := by
  apply Complex.ext <;>
    norm_num [principalRaiseCoefficient, principalParameter, Complex.div_re, Complex.div_im]
  ring

private theorem lowerCoefficient_eq (ε : ℝ) (m : ℤ) :
    principalLowerCoefficient ε m = (principalParameter ε - 1 + 2 * (m : ℂ)) / 2 := by
  apply Complex.ext <;>
    norm_num [principalLowerCoefficient, principalParameter, Complex.div_re, Complex.div_im]
  ring

/-- Squared raising amplitude at every integer weight. -/
theorem normSq_principalRaiseCoefficient (ε : ℝ) (m : ℤ) :
    Complex.normSq (principalRaiseCoefficient ε m) = ((m : ℝ) + 1 / 2) ^ 2 + ε ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [principalRaiseCoefficient]
  ring

/-- Squared lowering amplitude at every integer weight. -/
theorem normSq_principalLowerCoefficient (ε : ℝ) (m : ℤ) :
    Complex.normSq (principalLowerCoefficient ε m) = ((m : ℝ) - 1 / 2) ^ 2 + ε ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [principalLowerCoefficient]
  ring

/-- The Laplacian energy is a uniform lower bound for squared raising amplitudes. -/
theorem normSq_principalRaiseCoefficient_ge_energy (ε : ℝ) (m : ℤ) :
    principalEnergy ε ≤ Complex.normSq (principalRaiseCoefficient ε m) := by
  rw [normSq_principalRaiseCoefficient]
  unfold principalEnergy
  rcases (show 0 ≤ m ∨ m ≤ -1 by omega) with hm | hm
  · have hr : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith only [hr, sq_nonneg (m : ℝ)]
  · have hr : (m : ℝ) ≤ -1 := by exact_mod_cast hm
    nlinarith only [hr, sq_nonneg ((m : ℝ) + 1)]

/-- The Laplacian energy is a uniform lower bound for squared lowering amplitudes. -/
theorem normSq_principalLowerCoefficient_ge_energy (ε : ℝ) (m : ℤ) :
    principalEnergy ε ≤ Complex.normSq (principalLowerCoefficient ε m) := by
  rw [normSq_principalLowerCoefficient]
  unfold principalEnergy
  rcases (show m ≤ 0 ∨ 1 ≤ m by omega) with hm | hm
  · have hr : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    nlinarith only [hr, sq_nonneg (m : ℝ)]
  · have hr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith only [hr, sq_nonneg ((m : ℝ) - 1)]

/-- Both amplitude bounds are attained at spherical weight zero. -/
theorem principal_ladder_ground_energy (ε : ℝ) :
    Complex.normSq (principalRaiseCoefficient ε 0) = principalEnergy ε ∧
      Complex.normSq (principalLowerCoefficient ε 0) = principalEnergy ε := by
  rw [normSq_principalRaiseCoefficient, normSq_principalLowerCoefficient]
  norm_num [principalEnergy]

/-- Half-integral offset keeps the raising amplitude uniformly away from zero. -/
theorem normSq_principalRaiseCoefficient_ge_quarter (ε : ℝ) (m : ℤ) :
    1 / 4 ≤ Complex.normSq (principalRaiseCoefficient ε m) :=
  (principalEnergy_ge_quarter ε).trans (normSq_principalRaiseCoefficient_ge_energy ε m)

/-- Half-integral offset keeps the lowering amplitude uniformly away from zero. -/
theorem normSq_principalLowerCoefficient_ge_quarter (ε : ℝ) (m : ℤ) :
    1 / 4 ≤ Complex.normSq (principalLowerCoefficient ε m) :=
  (principalEnergy_ge_quarter ε).trans (normSq_principalLowerCoefficient_ge_energy ε m)

theorem principalRaiseCoefficient_ne_zero (ε : ℝ) (m : ℤ) :
    principalRaiseCoefficient ε m ≠ 0 := by
  intro h
  have hb := normSq_principalRaiseCoefficient_ge_quarter ε m
  norm_num [h] at hb

theorem principalLowerCoefficient_ne_zero (ε : ℝ) (m : ℤ) :
    principalLowerCoefficient ε m ≠ 0 := by
  intro h
  have hb := normSq_principalLowerCoefficient_ge_quarter ε m
  norm_num [h] at hb

/-- Raising in the existing spherical model at imaginary parameter. -/
def principalRaising (ε : ℝ) := sphericalPrincipalE (principalParameter ε)

/-- Lowering in the existing spherical model at imaginary parameter. -/
def principalLowering (ε : ℝ) := sphericalPrincipalF (principalParameter ε)

@[simp] theorem principalRaising_single (ε : ℝ) (m : ℤ) (z : ℂ) :
    principalRaising ε (Finsupp.single m z) =
      Finsupp.single (m + 1) (principalRaiseCoefficient ε m * z) := by
  rw [principalRaising, sphericalPrincipalE_single, ← raiseCoefficient_eq]

@[simp] theorem principalLowering_single (ε : ℝ) (m : ℤ) (z : ℂ) :
    principalLowering ε (Finsupp.single m z) =
      Finsupp.single (m - 1) (principalLowerCoefficient ε m * z) := by
  rw [principalLowering, sphericalPrincipalF_single, ← lowerCoefficient_eq]

/-- Inverse raising shift, with reciprocal coefficient at the source weight. -/
def principalRaisingInverse (ε : ℝ) : SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel :=
  weightedShift (-1) (fun m => (principalRaiseCoefficient ε (m - 1))⁻¹)

/-- Inverse lowering shift, with reciprocal coefficient at the source weight. -/
def principalLoweringInverse (ε : ℝ) : SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel :=
  weightedShift 1 (fun m => (principalLowerCoefficient ε (m + 1))⁻¹)

/-- Raising followed by its explicit inverse is the identity. -/
theorem principalRaisingInverse_comp (ε : ℝ) :
    (principalRaisingInverse ε).comp (principalRaising ε) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro m z
  simp [principalRaisingInverse, principalRaiseCoefficient_ne_zero]

/-- The inverse raising shift is also a right inverse. -/
theorem principalRaising_comp_inverse (ε : ℝ) :
    (principalRaising ε).comp (principalRaisingInverse ε) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro m z
  simp [principalRaisingInverse, ← sub_eq_add_neg,
    principalRaiseCoefficient_ne_zero]

/-- Lowering followed by its explicit inverse is the identity. -/
theorem principalLoweringInverse_comp (ε : ℝ) :
    (principalLoweringInverse ε).comp (principalLowering ε) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro m z
  simp [principalLoweringInverse, principalLowerCoefficient_ne_zero]

/-- The inverse lowering shift is also a right inverse. -/
theorem principalLowering_comp_inverse (ε : ℝ) :
    (principalLowering ε).comp (principalLoweringInverse ε) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro m z
  simp [principalLoweringInverse, principalLowerCoefficient_ne_zero]

/-- Raising is an actual linear automorphism of the algebraic principal series. -/
def principalRaisingEquiv (ε : ℝ) : SphericalKFiniteModel ≃ₗ[ℂ] SphericalKFiniteModel :=
  LinearEquiv.ofLinear (principalRaising ε) (principalRaisingInverse ε)
    (principalRaising_comp_inverse ε) (principalRaisingInverse_comp ε)

/-- Lowering is an actual linear automorphism of the algebraic principal series. -/
def principalLoweringEquiv (ε : ℝ) : SphericalKFiniteModel ≃ₗ[ℂ] SphericalKFiniteModel :=
  LinearEquiv.ofLinear (principalLowering ε) (principalLoweringInverse ε)
    (principalLowering_comp_inverse ε) (principalLoweringInverse_comp ε)

theorem principalRaising_bijective (ε : ℝ) : Function.Bijective (principalRaising ε) :=
  (principalRaisingEquiv ε).bijective

theorem principalLowering_bijective (ε : ℝ) : Function.Bijective (principalLowering ε) :=
  (principalLoweringEquiv ε).bijective

/-- No nonzero finite principal-series vector is a highest weight vector. -/
theorem principalRaising_eq_zero_iff (ε : ℝ) (v : SphericalKFiniteModel) :
    principalRaising ε v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply (principalRaising_bijective ε).injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

/-- No nonzero finite principal-series vector is a lowest weight vector. -/
theorem principalLowering_eq_zero_iff (ε : ℝ) (v : SphericalKFiniteModel) :
    principalLowering ε v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply (principalLowering_bijective ε).injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

end
end GaloisForLFunctions.SelbergClass.Primon
