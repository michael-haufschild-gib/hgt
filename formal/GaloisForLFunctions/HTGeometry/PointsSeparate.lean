import GaloisForLFunctions.HTGeometry.NullstellensatzPoint

/-!
# Points separate on a reduced finite-type algebra over an algebraically closed field

The Galois correspondence needs more than the existence of one point of the group: it needs the
points to separate, so that an element of the Picard--Vessiot ring fixed by every automorphism
really is in the base.  That is the statement that the intersection of the kernels of all
`C`-algebra homomorphisms to `C` is zero, and for a finitely generated algebra over an algebraically
closed field it is the Nullstellensatz together with the Jacobson property: the intersection of the
maximal ideals is the nilradical, which vanishes when the algebra is reduced.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every maximal ideal of a finite-type algebra over an algebraically closed field is the kernel of
a point. -/
theorem exists_algHom_ker_eq_of_isMaximal
    {C E : Type*} [Field C] [IsAlgClosed C] [CommRing E] [Algebra C E]
    [Algebra.FiniteType C E] (m : Ideal E) [m.IsMaximal] :
    ∃ χ : E →ₐ[C] C, ∀ y : E, χ y = 0 ↔ y ∈ m := by
  classical
  haveI : Algebra.FiniteType C (E ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ C m) Ideal.Quotient.mk_surjective
  letI : Field (E ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite C (E ⧸ m) := finite_of_finite_type_of_isJacobsonRing C (E ⧸ m)
  haveI : Algebra.IsIntegral C (E ⧸ m) := Algebra.IsIntegral.of_finite C (E ⧸ m)
  have hbij : Function.Bijective (algebraMap C (E ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : C ≃ₐ[C] (E ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId C (E ⧸ m)) hbij
  refine ⟨(e.symm.toAlgHom).comp (Ideal.Quotient.mkₐ C m), fun y => ?_⟩
  constructor
  · intro hy
    have hmk : (Ideal.Quotient.mk m) y = 0 := by
      have : e.symm ((Ideal.Quotient.mk m) y) = 0 := hy
      have h2 := congrArg e this
      rw [AlgEquiv.apply_symm_apply, map_zero] at h2
      exact h2
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hmk
  · intro hy
    have hmk : (Ideal.Quotient.mk m) y = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hy
    show e.symm ((Ideal.Quotient.mk m) y) = 0
    rw [hmk, map_zero]

/-- **Points separate.**  On a reduced finitely generated algebra over an algebraically closed
field, an element killed by every point is zero. -/
theorem eq_zero_of_forall_algHom_eq_zero
    {C E : Type*} [Field C] [IsAlgClosed C] [CommRing E] [IsReduced E] [Algebra C E]
    [Algebra.FiniteType C E] {x : E} (h : ∀ χ : E →ₐ[C] C, χ x = 0) : x = 0 := by
  classical
  haveI : IsJacobsonRing E := isJacobsonRing_of_finiteType (A := C) (B := E)
  have hbotrad : (⊥ : Ideal E).IsRadical := by
    intro y hy
    obtain ⟨n, hn⟩ := hy
    rw [Ideal.mem_bot] at hn ⊢
    exact IsReduced.eq_zero y ⟨n, hn⟩
  have hjac : (⊥ : Ideal E).jacobson = ⊥ := ‹IsJacobsonRing E›.out hbotrad
  have hmem : x ∈ (⊥ : Ideal E).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    intro J hJ
    haveI hJmax : Ideal.IsMaximal J := hJ.2
    obtain ⟨χ, hχ⟩ := exists_algHom_ker_eq_of_isMaximal (C := C) J
    exact (hχ x).mp (h χ)
  rw [hjac, Ideal.mem_bot] at hmem
  exact hmem

end

end GaloisForLFunctions.HTGeometry
