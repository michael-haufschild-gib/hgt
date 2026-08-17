import GaloisForLFunctions.HTGeometry.ContextOrderTransverseAction
import GaloisForLFunctions.HTGeometry.ConstitutiveVisibleKernelPurificationGauge

/-!
# Gram realizations and the dimension firewall

A finite kernel realized as the Gram matrix of a family of vectors in *any* complex inner product
space is positive semidefinite: the quadratic form is the squared norm of a finite linear
combination, and no finiteness of the ambient space enters.  Conversely a positive semidefinite
kernel is the Gram matrix of the conjugated rows of any of its square factorizations, so the two
notions coincide already in the canonical space of the kernel's own size.

Consequently an indefinite finite kernel has no Gram realization at all, in any dimension; and when a
diagonal block of a Gram kernel is the identity, the corresponding subfamily is orthonormal.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

section GramRealization

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Gram kernel of a finite family of vectors. -/
def innerGramMatrix (v : B → E) : Matrix B B ℂ := Matrix.of fun i j => (inner ℂ (v i) (v j) : ℂ)

@[simp] theorem innerGramMatrix_apply (v : B → E) (i j : B) :
    innerGramMatrix v i j = (inner ℂ (v i) (v j) : ℂ) := rfl

theorem isHermitian_innerGramMatrix (v : B → E) : (innerGramMatrix v).IsHermitian := by
  ext i j
  show (starRingEnd ℂ) (innerGramMatrix v j i) = innerGramMatrix v i j
  rw [innerGramMatrix_apply, innerGramMatrix_apply, inner_conj_symm]

/-- **Every Gram kernel is positive semidefinite**, in any complex inner product space and with no
finiteness assumption on it. -/
theorem posSemidef_innerGramMatrix (v : B → E) : (innerGramMatrix v).PosSemidef := by
  refine ⟨isHermitian_innerGramMatrix v, fun x => ?_⟩
  have hquad : (x.sum fun i xi => x.sum fun j xj => star xi * innerGramMatrix v i j * xj)
      = (inner ℂ (∑ i ∈ x.support, x i • v i) (∑ j ∈ x.support, x j • v j) : ℂ) := by
    rw [sum_inner]
    simp only [Finsupp.sum, inner_sum, inner_smul_left, inner_smul_right,
      innerGramMatrix_apply, RCLike.star_def]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hquad]
  exact CStarModule.inner_self_nonneg

/-- **Every positive semidefinite kernel is a Gram kernel** of a family in the canonical space of its
own size. -/
theorem exists_innerGramMatrix_of_posSemidef {K : Matrix B B ℂ} (hK : K.PosSemidef) :
    ∃ v : B → EuclideanSpace ℂ B, K = innerGramMatrix v := by
  obtain ⟨V, hV⟩ := exists_gram_factorization hK
  refine ⟨fun i => WithLp.toLp 2 fun k => (starRingEnd ℂ) (V i k), ?_⟩
  ext i j
  have hL : (V * Vᴴ) i j = ∑ k, V i k * (starRingEnd ℂ) (V j k) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  have hR : innerGramMatrix (fun i => (WithLp.toLp 2 fun k => (starRingEnd ℂ) (V i k)
        : EuclideanSpace ℂ B)) i j = ∑ k, V i k * (starRingEnd ℂ) (V j k) := by
    rw [innerGramMatrix_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [RCLike.inner_apply, mul_comm]
  rw [hV, hL, hR]

/-- **The dimension firewall.**  Gram realizability in any complex inner product space is exactly
positive semidefiniteness, hence exactly Gram realizability in the canonical space of the kernel's
own size. -/
theorem posSemidef_iff_exists_innerGramMatrix {K : Matrix B B ℂ} :
    K.PosSemidef ↔ ∃ v : B → EuclideanSpace ℂ B, K = innerGramMatrix v := by
  refine ⟨exists_innerGramMatrix_of_posSemidef, ?_⟩
  rintro ⟨v, rfl⟩
  exact posSemidef_innerGramMatrix v

/-- An identity diagonal block of a Gram kernel is an orthonormal frame. -/
theorem orthonormal_of_innerGramMatrix {κ : Type*} [DecidableEq κ] (v : B → E) (e : κ → B)
    (h : (innerGramMatrix v).submatrix e e = 1) : Orthonormal ℂ (v ∘ e) := by
  refine orthonormal_iff_ite.mpr fun a b => ?_
  have hab := congrFun (congrFun h a) b
  rw [Matrix.submatrix_apply, innerGramMatrix_apply] at hab
  rw [Function.comp_apply, Function.comp_apply, hab, Matrix.one_apply]

end GramRealization

section Firewall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The balanced context kernel has no Gram realization in any complex inner product space.**
Increasing the ambient dimension cannot repair an indefinite finite kernel. -/
theorem balancedContext_ne_innerGramMatrix (r : ℕ) (v : Fin (r + 3) → E) :
    contextOrderKernel (ι := Fin (r + 3)) (balancedContextScale r) ≠ innerGramMatrix v := by
  intro h
  refine balancedContext_global_not_posSemidef r ?_
  rw [h]
  exact posSemidef_innerGramMatrix v

end Firewall

end

end GaloisForLFunctions.HTGeometry
