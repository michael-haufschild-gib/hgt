import GaloisForLFunctions.HTGeometry.ABHN.IntegralNormUnits

/-!
# Quotient fibres of adjoin-root presentations

An algebra equivalence `AdjoinRoot p ≃ B` descends after quotienting the base by any ideal.  The
closed fibre is canonically the root algebra of the coefficientwise-reduced polynomial.  The
equivalence also sends the reduced distinguished root to the residue of the original generator.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **An adjoin-root presentation descends to every quotient fibre.** -/
noncomputable def adjoinRootQuotientFibreEquiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (p : Polynomial A) (e : AdjoinRoot p ≃ₐ[A] B) :
    AdjoinRoot (p.map (algebraMap A (A ⧸ I))) ≃ₐ[A ⧸ I]
      (B ⧸ I.map (algebraMap A B)) :=
  (ABHN.adjoinRootScalarExtensionEquiv A (A ⧸ I) p).symm |>.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl) e) |>.trans
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm

/-- The quotient-fibre equivalence sends the reduced distinguished root to the residue of the
original generator. -/
theorem adjoinRootQuotientFibreEquiv_root
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (p : Polynomial A) (e : AdjoinRoot p ≃ₐ[A] B) :
    adjoinRootQuotientFibreEquiv I p e
        (AdjoinRoot.root (p.map (algebraMap A (A ⧸ I)))) =
      Ideal.Quotient.mk (I.map (algebraMap A B)) (e (AdjoinRoot.root p)) := by
  unfold adjoinRootQuotientFibreEquiv
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have hroot : (ABHN.adjoinRootScalarExtensionEquiv A (A ⧸ I) p).symm
      (AdjoinRoot.root (p.map (algebraMap A (A ⧸ I)))) =
        (1 : A ⧸ I) ⊗ₜ[A] AdjoinRoot.root p := by
    apply (ABHN.adjoinRootScalarExtensionEquiv A (A ⧸ I) p).injective
    rw [AlgEquiv.apply_symm_apply]
    symm
    unfold ABHN.adjoinRootScalarExtensionEquiv
    dsimp only
    rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root]
    let q' : Polynomial (TensorProduct A (A ⧸ I) A) :=
      p.map Algebra.TensorProduct.includeRight.toRingHom
    have hq : q'.map (Algebra.TensorProduct.rid A (A ⧸ I) (A ⧸ I)) =
        p.map (algebraMap A (A ⧸ I)) := by
      ext i
      simp [q', Algebra.smul_def]
    change AdjoinRoot.map (Algebra.TensorProduct.rid A (A ⧸ I) (A ⧸ I)).toRingHom q'
      (p.map (algebraMap A (A ⧸ I))) hq.symm.dvd (AdjoinRoot.root q') =
        AdjoinRoot.root (p.map (algebraMap A (A ⧸ I)))
    rw [AdjoinRoot.map_root]
  rw [hroot]
  have hcongr : (Algebra.TensorProduct.congr
      (AlgEquiv.refl : (A ⧸ I) ≃ₐ[A ⧸ I] (A ⧸ I)) e)
      ((1 : A ⧸ I) ⊗ₜ[A] AdjoinRoot.root p) =
        (1 : A ⧸ I) ⊗ₜ[A] e (AdjoinRoot.root p) := by
    change (Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) e.toAlgHom)
      ((1 : A ⧸ I) ⊗ₜ[A] AdjoinRoot.root p) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).injective
  rw [AlgEquiv.apply_symm_apply]
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  exact hcongr

end GaloisForLFunctions.HTGeometry
