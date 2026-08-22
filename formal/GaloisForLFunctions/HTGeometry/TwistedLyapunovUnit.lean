import GaloisForLFunctions.HTGeometry.CFCSqrtDerivative

/-!
# The twisted Lyapunov unit

The Fréchet derivative of the continuous functional calculus square root is described by the
invertible operator `Λ_{√c} ∘ P + (1 - P)` on the whole algebra, where `P` is the self-adjoint
projection `saProj`.  On self-adjoint elements this operator is the Lyapunov operator itself, and
it commutes with the star involution; consequently its inverse maps self-adjoint elements to
self-adjoint elements, and the value of the inverse at a self-adjoint `q` is the unique
self-adjoint solution of the Lyapunov equation `√c y + y √c = q`.
-/

open scoped Ring

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The self-adjoint projection is star-invariant. -/
lemma saProj_star (x : A) : saProj (star x) = saProj x := by
  rw [saProj_apply, saProj_apply, star_star, add_comm]

omit [PartialOrder A] [StarOrderedRing A] in
/-- A unit of the algebra of operators is a left inverse of itself. -/
lemma unit_inv_apply_apply (u : (A →L[ℝ] A)ˣ) (z : A) :
    (↑u⁻¹ : A →L[ℝ] A) ((↑u : A →L[ℝ] A) z) = z := by
  have h : ((↑u⁻¹ : A →L[ℝ] A) * (↑u : A →L[ℝ] A)) = 1 := u.inv_mul
  calc (↑u⁻¹ : A →L[ℝ] A) ((↑u : A →L[ℝ] A) z)
      = ((↑u⁻¹ : A →L[ℝ] A) * (↑u : A →L[ℝ] A)) z := rfl
    _ = z := by rw [h]; rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- A unit of the algebra of operators is a right inverse of itself. -/
lemma unit_apply_inv_apply (u : (A →L[ℝ] A)ˣ) (z : A) :
    (↑u : A →L[ℝ] A) ((↑u⁻¹ : A →L[ℝ] A) z) = z := by
  have h : ((↑u : A →L[ℝ] A) * (↑u⁻¹ : A →L[ℝ] A)) = 1 := u.mul_inv
  calc (↑u : A →L[ℝ] A) ((↑u⁻¹ : A →L[ℝ] A) z)
      = ((↑u : A →L[ℝ] A) * (↑u⁻¹ : A →L[ℝ] A)) z := rfl
    _ = z := by rw [h]; rfl

variable {c : A} {u : (A →L[ℝ] A)ˣ}

/-- The value of the twisted Lyapunov unit. -/
lemma twisted_unit_apply
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt c)).comp (saProj : A →L[ℝ] A) + ((1 : A →L[ℝ] A) - saProj))
    (x : A) :
    (↑u : A →L[ℝ] A) x
      = (CFC.sqrt c * saProj x + saProj x * CFC.sqrt c) + (x - saProj x) := by
  rw [hu]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, lyapunov_apply,
    sub_apply, one_apply_eq_self]

/-- On self-adjoint elements the twisted Lyapunov unit is the Lyapunov operator. -/
lemma twisted_unit_apply_of_isSelfAdjoint
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt c)).comp (saProj : A →L[ℝ] A) + ((1 : A →L[ℝ] A) - saProj))
    {x : A} (hx : IsSelfAdjoint x) :
    (↑u : A →L[ℝ] A) x = CFC.sqrt c * x + x * CFC.sqrt c := by
  rw [twisted_unit_apply hu, saProj_of_isSelfAdjoint hx, sub_self, add_zero]

/-- The twisted Lyapunov unit commutes with the star involution. -/
lemma star_twisted_unit_apply
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt c)).comp (saProj : A →L[ℝ] A) + ((1 : A →L[ℝ] A) - saProj))
    (x : A) :
    star ((↑u : A →L[ℝ] A) x) = (↑u : A →L[ℝ] A) (star x) := by
  have hsa : IsSelfAdjoint (CFC.sqrt c) := (CFC.sqrt_nonneg c).isSelfAdjoint
  have hP : IsSelfAdjoint (saProj x) := isSelfAdjoint_saProj x
  rw [twisted_unit_apply hu, twisted_unit_apply hu, saProj_star, star_add, star_add,
    star_sub, star_mul, star_mul, hsa.star_eq, hP.star_eq]
  abel

/-- The inverse of the twisted Lyapunov unit preserves self-adjointness. -/
lemma isSelfAdjoint_twisted_unit_inv
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt c)).comp (saProj : A →L[ℝ] A) + ((1 : A →L[ℝ] A) - saProj))
    {q : A} (hq : IsSelfAdjoint q) :
    IsSelfAdjoint ((↑u⁻¹ : A →L[ℝ] A) q) := by
  have huy : (↑u : A →L[ℝ] A) ((↑u⁻¹ : A →L[ℝ] A) q) = q := unit_apply_inv_apply u q
  have h1 : (↑u : A →L[ℝ] A) (star ((↑u⁻¹ : A →L[ℝ] A) q)) = q := by
    rw [← star_twisted_unit_apply hu, huy, hq.star_eq]
  have h2 := congrArg (fun z => (↑u⁻¹ : A →L[ℝ] A) z) h1
  simp only [unit_inv_apply_apply] at h2
  exact h2

/-- **The inverse of the twisted Lyapunov unit solves the Lyapunov equation.** -/
lemma lyapunov_twisted_unit_inv
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt c)).comp (saProj : A →L[ℝ] A) + ((1 : A →L[ℝ] A) - saProj))
    {q : A} (hq : IsSelfAdjoint q) :
    CFC.sqrt c * ((↑u⁻¹ : A →L[ℝ] A) q) + ((↑u⁻¹ : A →L[ℝ] A) q) * CFC.sqrt c = q := by
  rw [← twisted_unit_apply_of_isSelfAdjoint hu (isSelfAdjoint_twisted_unit_inv hu hq),
    unit_apply_inv_apply]

end

end GaloisForLFunctions.HTGeometry
