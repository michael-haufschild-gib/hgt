import GaloisForLFunctions.HTGeometry.PolynomialScaleVariable
import GaloisForLFunctions.HTGeometry.TailCoefficientLinearSolve

/-!
# The scaling that fixes every tail coefficient

Scaling the `i`-th parameter by the `(i+1)`-st power of a scalar rescales the tail polynomial by
that scalar and rescales its variable by the same amount.  Raising to the power `n - j` and reading
the `j`-th coefficient therefore multiplies the `j`-th tail coefficient by the scalar to the power
`(n - j) + j = n`.

So when the scalar is an `n`-th root of unity every tail coefficient is fixed, while the first
parameter is multiplied by the scalar.  That is the deck transformation of the Kummer covering: it
fixes the coefficient field and moves the first parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- Scaling the `i`-th parameter by the `(i+1)`-st power of a scalar. -/
noncomputable def varScaleHom (K : Type*) [Field K] (n : ℕ) (ζ : K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (fun i : Fin n => MvPolynomial.C (ζ ^ ((i : ℕ) + 1)) * MvPolynomial.X i)

theorem varScaleHom_C (ζ a : K) :
    varScaleHom K n ζ (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [varScaleHom, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem varScaleHom_X (ζ : K) (i : Fin n) :
    varScaleHom K n ζ (MvPolynomial.X i) =
      MvPolynomial.C (ζ ^ ((i : ℕ) + 1)) * MvPolynomial.X i := by
  rw [varScaleHom, MvPolynomial.aeval_X]

/-- **The scaling is an automorphism when the scalar is nonzero.** -/
noncomputable def varScale (K : Type*) [Field K] (n : ℕ) {ζ : K} (hζ : ζ ≠ 0) :
    MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K :=
  AlgEquiv.ofAlgHom (varScaleHom K n ζ) (varScaleHom K n ζ⁻¹)
    (by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, varScaleHom_X, map_mul, varScaleHom_X, varScaleHom_C,
        ← mul_assoc, ← map_mul, ← mul_pow, inv_mul_cancel₀ hζ, one_pow, map_one, one_mul]
      rfl)
    (by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, varScaleHom_X, map_mul, varScaleHom_X, varScaleHom_C,
        ← mul_assoc, ← map_mul, ← mul_pow, mul_inv_cancel₀ hζ, one_pow, map_one, one_mul]
      rfl)

theorem varScale_apply {ζ : K} (hζ : ζ ≠ 0) (p : MvPolynomial (Fin n) K) :
    varScale K n hζ p = varScaleHom K n ζ p := rfl

/-- **The scaling rescales the tail polynomial and its variable together.** -/
theorem map_varScaleHom_tailPoly (ζ : K) :
    Polynomial.map (varScaleHom K n ζ).toRingHom (tailPoly K n) =
      Polynomial.C (MvPolynomial.C ζ) *
        scaleVar (MvPolynomial.C ζ : MvPolynomial (Fin n) K) (tailPoly K n) := by
  refine Polynomial.ext fun j => ?_
  rw [Polynomial.coeff_map, coeff_tailPoly, Polynomial.coeff_C_mul, coeff_scaleVar, coeff_tailPoly]
  by_cases hj : j < n
  · simp only [dif_pos hj]
    have h : (varScaleHom K n ζ).toRingHom (MvPolynomial.X (⟨j, hj⟩ : Fin n)) =
        MvPolynomial.C (ζ ^ (j + 1)) * MvPolynomial.X (⟨j, hj⟩ : Fin n) := varScaleHom_X ζ _
    rw [h, ← map_pow, ← mul_assoc, ← map_mul, ← pow_succ']
  · simp only [dif_neg hj, map_zero, mul_zero]

theorem map_varScaleHom_tailPoly_pow (ζ : K) (m : ℕ) :
    Polynomial.map (varScaleHom K n ζ).toRingHom ((tailPoly K n) ^ m) =
      Polynomial.C (MvPolynomial.C (ζ ^ m)) *
        scaleVar (MvPolynomial.C ζ : MvPolynomial (Fin n) K) ((tailPoly K n) ^ m) := by
  rw [Polynomial.map_pow, map_varScaleHom_tailPoly, mul_pow]
  congr 1
  · rw [← Polynomial.C_pow, ← map_pow]
  · rw [← map_pow]

/-- **The scaling multiplies every tail coefficient by the `n`-th power of the scalar.** -/
theorem varScaleHom_tailCoeff (ζ : K) (j : Fin n) :
    varScaleHom K n ζ (tailCoeff K n j) =
      MvPolynomial.C (ζ ^ n) * tailCoeff K n j := by
  have hj : (j : ℕ) < n := j.2
  rw [tailCoeff]
  have hmap : (varScaleHom K n ζ) (((tailPoly K n) ^ (n - (j : ℕ))).coeff (j : ℕ)) =
      (Polynomial.map (varScaleHom K n ζ).toRingHom ((tailPoly K n) ^ (n - (j : ℕ)))).coeff
        (j : ℕ) := (Polynomial.coeff_map _ _).symm
  rw [hmap, map_varScaleHom_tailPoly_pow, Polynomial.coeff_C_mul, coeff_scaleVar, ← mul_assoc,
    ← map_pow, ← map_mul, ← pow_add]
  congr 3
  omega

/-- **An `n`-th root of unity fixes every tail coefficient.** -/
theorem varScaleHom_tailCoeff_of_pow_eq_one {ζ : K} (hζ : ζ ^ n = 1) (j : Fin n) :
    varScaleHom K n ζ (tailCoeff K n j) = tailCoeff K n j := by
  rw [varScaleHom_tailCoeff, hζ, map_one, one_mul]

/-- **The scaling moves the first parameter by the scalar.** -/
theorem varScaleHom_X_zero {j : Fin n} (hj : (j : ℕ) = 0) (ζ : K) :
    varScaleHom K n ζ (MvPolynomial.X j) = MvPolynomial.C ζ * MvPolynomial.X j := by
  rw [varScaleHom_X, hj, zero_add, pow_one]

end GaloisForLFunctions.HTGeometry
