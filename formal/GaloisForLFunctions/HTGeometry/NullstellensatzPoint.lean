import GaloisForLFunctions.HTGeometry.SigmaIdealConstantCoefficients

/-!
# A nontrivial finite-type algebra over an algebraically closed field has a point

The Galois correspondence turns the ideal correspondence into actual automorphisms by specialising
the comparison matrix at a point of the Galois group.  Points exist because the constants form an
algebraically closed field: a nontrivial finitely generated algebra over an algebraically closed
field admits a homomorphism to that field.

This is the weak Nullstellensatz.  Take a maximal ideal; the quotient is a field of finite type over
the base, hence finite over it by Zariski's lemma, hence equal to the base because the base is
algebraically closed.

The matrix form is what the torsor argument uses: an invertible matrix over such an algebra
specialises to an invertible matrix over the constants, so the Galois group really has points.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The weak Nullstellensatz.**  A nontrivial finitely generated algebra over an algebraically
closed field admits an algebra homomorphism to that field. -/
theorem exists_algHom_of_finiteType_of_isAlgClosed
    {C E : Type*} [Field C] [IsAlgClosed C] [CommRing E] [Nontrivial E] [Algebra C E]
    [Algebra.FiniteType C E] : Nonempty (E →ₐ[C] C) := by
  classical
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal E) bot_ne_top
  haveI : m.IsMaximal := hm
  haveI : Algebra.FiniteType C (E ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ C m) Ideal.Quotient.mk_surjective
  letI : Field (E ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite C (E ⧸ m) := finite_of_finite_type_of_isJacobsonRing C (E ⧸ m)
  haveI : Algebra.IsIntegral C (E ⧸ m) := Algebra.IsIntegral.of_finite C (E ⧸ m)
  have hbij : Function.Bijective (algebraMap C (E ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : C ≃ₐ[C] (E ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId C (E ⧸ m)) hbij
  exact ⟨(e.symm.toAlgHom).comp (Ideal.Quotient.mkₐ C m)⟩

/-- **The Galois group has points.**  An invertible matrix over a nontrivial finitely generated
algebra over an algebraically closed field specialises to an invertible matrix over the field. -/
theorem exists_matrix_point_of_finiteType
    {C A : Type*} [Field C] [IsAlgClosed C] [CommRing A] [Nontrivial A] [Algebra C A]
    [Algebra.FiniteType C A] {n : ℕ} (Z : Matrix (Fin n) (Fin n) A) (w : A)
    (hw : Z.det * w = 1) :
    ∃ χ : A →ₐ[C] C, IsUnit (Z.map (χ : A → C)).det := by
  obtain ⟨χ⟩ := exists_algHom_of_finiteType_of_isAlgClosed (C := C) (E := A)
  refine ⟨χ, ?_⟩
  have hdet : (Z.map (χ : A → C)).det = χ Z.det := by
    have h := RingHom.map_det (χ.toRingHom) Z
    rw [RingHom.mapMatrix_apply] at h
    exact h.symm
  rw [hdet, isUnit_iff_ne_zero]
  intro h0
  have hone : (1 : C) = 0 := by
    rw [← map_one χ, ← hw, map_mul, h0, zero_mul]
  exact one_ne_zero hone

end

end GaloisForLFunctions.HTGeometry
