import Mathlib

/-!
# Extending the coefficient field keeps a proper ideal proper

A functional on the extension that sends one to one, applied to every coefficient, is a retraction
of the coefficient extension compatible with multiplication by polynomials over the base.  A
relation exhibiting one in the extended ideal is therefore pushed back to a relation exhibiting one
in the original ideal.

This is the consistency transfer a differential closure needs: a system that is consistent over the
base stays consistent over any extension.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F E σ : Type*} [Field F] [CommRing E] [Algebra F E]

/-- Applying an `F`-linear functional to every coefficient. -/
def coeffProject (π : E →ₗ[F] F) : MvPolynomial σ E →ₗ[ℤ] MvPolynomial σ F :=
  (AddMonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp <|
    (Finsupp.mapRange.linearMap π.toAddMonoidHom.toIntLinearMap).comp <|
      (AddMonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem coeffProject_coeff (π : E →ₗ[F] F) (c : MvPolynomial σ E) (u : σ →₀ ℕ) :
    (coeffProject (σ := σ) π c).coeff u = π (c.coeff u) := rfl

theorem coeffProject_map_mul (π : E →ₗ[F] F) (s : MvPolynomial σ F) (c : MvPolynomial σ E) :
    coeffProject π (MvPolynomial.map (algebraMap F E) s * c) = s * coeffProject π c := by
  classical
  refine MvPolynomial.ext _ _ fun u => ?_
  rw [coeffProject_coeff, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MvPolynomial.coeff_map, coeffProject_coeff, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, map_smul, smul_eq_mul]

theorem coeffProject_one (π : E →ₗ[F] F) (hπ : π 1 = 1) :
    coeffProject (σ := σ) π (1 : MvPolynomial σ E) = 1 := by
  classical
  refine MvPolynomial.ext _ _ fun u => ?_
  rw [coeffProject_coeff, MvPolynomial.coeff_one, MvPolynomial.coeff_one]
  by_cases h : (0 : σ →₀ ℕ) = u
  · rw [if_pos h, if_pos h, hπ]
  · rw [if_neg h, if_neg h, map_zero]

/-- **A proper ideal stays proper after extending the coefficient field.** -/
theorem map_ne_top_of_ne_top [Nontrivial E] {I : Ideal (MvPolynomial σ F)} (hI : I ≠ ⊤) :
    I.map (MvPolynomial.map (algebraMap F E) : MvPolynomial σ F →+* MvPolynomial σ E) ≠ ⊤ := by
  classical
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one (V := E) F (x := (1 : E)) one_ne_zero
  intro htop
  have hone : (1 : MvPolynomial σ E) ∈
      I.map (MvPolynomial.map (algebraMap F E) : MvPolynomial σ F →+* MvPolynomial σ E) := by
    rw [htop]
    trivial
  have hmem : ∀ z ∈ I.map (MvPolynomial.map (algebraMap F E) :
      MvPolynomial σ F →+* MvPolynomial σ E),
      ∀ a : MvPolynomial σ E, coeffProject π (a * z) ∈ I := by
    intro z hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro y ⟨x, hx, rfl⟩ a
      rw [mul_comm, coeffProject_map_mul]
      exact Ideal.mul_mem_right _ _ hx
    · intro a
      rw [mul_zero]
      have hzero : coeffProject (σ := σ) π (0 : MvPolynomial σ E) = 0 := map_zero _
      rw [hzero]
      exact Ideal.zero_mem I
    · intro y z _ _ hy hz a
      rw [mul_add, map_add]
      exact Ideal.add_mem I (hy a) (hz a)
    · intro b y _ hy a
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (a * b)
  have hfinal := hmem 1 hone 1
  rw [one_mul, coeffProject_one π hπ] at hfinal
  exact hI (Ideal.eq_top_of_isUnit_mem I hfinal isUnit_one)

end

end GaloisForLFunctions.HTGeometry
