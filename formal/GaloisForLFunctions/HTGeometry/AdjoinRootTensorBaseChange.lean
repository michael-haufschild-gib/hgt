import GaloisForLFunctions.HTGeometry.SeparableAdjoinRootReduced

/-!
# Base change of `AdjoinRoot` along a tensor product

`AdjoinRoot f ⊗[k] A ≅ AdjoinRoot (f.map (algebraMap k A))`.  Combined with
`isReduced_adjoinRoot_of_separable` this says that a reduced algebra stays reduced after base change
to a finite separable extension of the ground field — the finite step of geometric reducedness in
characteristic zero.

The identification of `k[X] ⊗[k] A` with `A[X]` is `polyEquivTensor` after commuting the factors,
and the two algebra maps `k[X] → A[X]` agree because they agree on `X`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial TensorProduct

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

/-- The polynomial ring over `A` as the base change of the polynomial ring over `k`. -/
noncomputable def tensorPolyEquiv : k[X] ⊗[k] A ≃ₐ[k] A[X] :=
  (Algebra.TensorProduct.comm k k[X] A).trans (polyEquivTensor k A).symm

variable {k A}

theorem tensorPolyEquiv_includeLeft (p : k[X]) :
    tensorPolyEquiv k A (p ⊗ₜ[k] 1) = p.map (algebraMap k A) := by
  have hX : tensorPolyEquiv k A ((X : k[X]) ⊗ₜ[k] 1) = (X : A[X]) := by
    have h1 : (Algebra.TensorProduct.comm k k[X] A) ((X : k[X]) ⊗ₜ[k] 1)
        = (1 : A) ⊗ₜ[k] (X : k[X]) := rfl
    have h2 : (polyEquivTensor k A) (X : A[X]) = (1 : A) ⊗ₜ[k] (X : k[X]) := by
      rw [polyEquivTensor_apply]
      simp
    simp only [tensorPolyEquiv, AlgEquiv.trans_apply, h1, ← h2, AlgEquiv.symm_apply_apply]
  have hcomp : (tensorPolyEquiv k A).toAlgHom.comp
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := k[X]) (B := A))
      = Polynomial.mapAlgHom (Algebra.ofId k A) := by
    refine Polynomial.algHom_ext ?_
    simpa using hX
  have := AlgHom.congr_fun hcomp p
  simpa using this

/-- **Base change of `AdjoinRoot`.** -/
noncomputable def adjoinRootTensorRingEquiv (f : k[X]) :
    (AdjoinRoot f ⊗[k] A) ≃+* AdjoinRoot (f.map (algebraMap k A)) := by
  classical
  refine RingEquiv.trans
    (Algebra.TensorProduct.quotientTensorEquiv (R := k) k A k[X] (Ideal.span {f})).toRingEquiv ?_
  refine Ideal.quotientEquiv _ _ (tensorPolyEquiv k A).toRingEquiv ?_
  symm
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  congr 1
  have hval : (tensorPolyEquiv k A) ((algebraMap k[X] (k[X] ⊗[k] A)) f)
      = f.map (algebraMap k A) := by
    have halg : (algebraMap k[X] (k[X] ⊗[k] A)) f = f ⊗ₜ[k] (1 : A) := rfl
    rw [halg, tensorPolyEquiv_includeLeft]
  congr 1
  exact hval

/-- **A reduced algebra stays reduced after base change along a monic separable polynomial.** -/
theorem isReduced_adjoinRoot_tensor_of_separable [IsReduced A] {f : k[X]}
    (hm : f.Monic) (hsep : f.Separable) :
    IsReduced (AdjoinRoot f ⊗[k] A) := by
  haveI : IsReduced (AdjoinRoot (f.map (algebraMap k A))) :=
    isReduced_adjoinRoot_of_separable (hm.map _) (hsep.map (f := algebraMap k A))
  exact isReduced_of_injective (adjoinRootTensorRingEquiv f).toRingHom
    (adjoinRootTensorRingEquiv f).injective

end GaloisForLFunctions.HTGeometry
