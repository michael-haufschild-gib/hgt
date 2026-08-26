import GaloisForLFunctions.HTGeometry.AdjoinRootQuotientFibre
import GaloisForLFunctions.HTGeometry.SplitResidueAdjoinRootPresentation
import GaloisForLFunctions.HTGeometry.MonicDistinctRootFactorization

/-!
# Separable adjoin-root presentations from split fibres

A monic root algebra equivalent to a finite product of copies of a field has exactly
degree-many distinct coordinate roots, so its defining polynomial is separable.  Combining this
with local split-fibre monogenicity gives a single producer of an exact `AdjoinRoot` presentation
whose closed-fibre polynomial is separable.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsLocalRing

/-- **A monic root algebra which is a split finite field algebra has separable defining
polynomial.** -/
theorem separable_of_adjoinRoot_algEquiv_pi
    {k ι : Type*} [Field k] [Fintype ι]
    (q : Polynomial k) (hq : q.Monic)
    (e : AdjoinRoot q ≃ₐ[k] (ι → k)) : q.Separable := by
  classical
  let r : ι → k := fun i => e (AdjoinRoot.root q) i
  let χ : ι → (AdjoinRoot q →ₐ[k] k) := fun i =>
    (Pi.evalAlgHom k (fun _ : ι => k) i).comp e.toAlgHom
  have hroot : ∀ i, q.IsRoot (r i) := by
    intro i
    have hr := (AdjoinRoot.isRoot_root q).map (f := (χ i).toRingHom)
    have hcomm : (χ i).toRingHom.comp (AdjoinRoot.of q) = RingHom.id k := by
      ext x
      change e (algebraMap k (AdjoinRoot q) x) i = x
      rw [e.commutes]
      simp
    rw [Polynomial.map_map, hcomm, Polynomial.map_id] at hr
    simpa [χ, r] using hr
  have hinj : Function.Injective r := by
    intro i j hij
    have hχ : χ i = χ j := by
      apply AdjoinRoot.algHom_ext
      exact hij
    by_contra hij'
    have hval := DFunLike.congr_fun hχ (e.symm (Pi.single i 1))
    simp [χ, hij'] at hval
  have hdeg : q.natDegree = Fintype.card ι := by
    calc
      q.natDegree = (AdjoinRoot.powerBasis hq.ne_zero).dim :=
        (AdjoinRoot.powerBasis_dim hq.ne_zero).symm
      _ = Module.finrank k (AdjoinRoot q) :=
        (AdjoinRoot.powerBasis hq.ne_zero).finrank.symm
      _ = Module.finrank k (ι → k) := e.toLinearEquiv.finrank_eq
      _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card k
  have hfac : q = ∏ i : ι, (X - C (r i)) := by
    let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    have hfacFin := eq_prod_X_sub_C_of_monic_of_injective_roots hq hdeg
      (hinj.comp σ.symm.injective) (fun i => hroot (σ.symm i))
    rw [hfacFin]
    exact Fintype.prod_equiv σ.symm _ _ fun i => rfl
  rw [hfac]
  exact Polynomial.separable_prod (Polynomial.pairwise_coprime_X_sub_C hinj)
    fun _ => Polynomial.separable_X_sub_C

/-- **A split quotient fibre makes the reduced defining polynomial separable.** -/
theorem separable_map_of_adjoinRoot_equiv_of_split_quotient
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.IsMaximal) (p : Polynomial A) (hp : p.Monic)
    (e : AdjoinRoot p ≃ₐ[A] B) {ι : Type*} [Fintype ι]
    (hsplit : Nonempty ((B ⧸ I.map (algebraMap A B)) ≃ₐ[A ⧸ I] (ι → A ⧸ I))) :
    (p.map (algebraMap A (A ⧸ I))).Separable := by
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  obtain ⟨s⟩ := hsplit
  exact separable_of_adjoinRoot_algEquiv_pi _ (hp.map _)
    ((adjoinRootQuotientFibreEquiv I p e).trans s)

/-- **Split closed fibre produces a separable local adjoin-root presentation.** -/
theorem exists_adjoinRoot_equiv_and_separable_residue_of_split_residue_fibre
    {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Module.Finite A B] [CharZero (ResidueField A)]
    {ι : Type*} [Fintype ι]
    (hsplit : Nonempty ((B ⧸ maxExt A B) ≃ₐ[ResidueField A] (ι → ResidueField A))) :
    ∃ θ : B, IsIntegral A θ ∧
      Nonempty (AdjoinRoot (minpoly A θ) ≃ₐ[A] B) ∧
        ((minpoly A θ).map (algebraMap A (ResidueField A))).Separable := by
  obtain ⟨θ, hθ, ⟨e⟩⟩ := exists_adjoinRoot_equiv_of_split_residue_fibre hsplit
  refine ⟨θ, hθ, ⟨e⟩, ?_⟩
  obtain ⟨s⟩ := hsplit
  let oldAlg : Algebra (ResidueField A) (B ⧸ maxExt A B) :=
    residueAlgebraQuotient A B
  let sr : (B ⧸ maxExt A B) ≃+* (ι → ResidueField A) := s.toRingEquiv
  have hscomm (x : ResidueField A) :
      sr (@algebraMap (ResidueField A) (B ⧸ maxExt A B) _ _ oldAlg x) =
        algebraMap (ResidueField A) (ι → ResidueField A) x := s.commutes x
  let stdAlg : Algebra (ResidueField A) (B ⧸ maxExt A B) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (ResidueField A) (B ⧸ maxExt A B) := stdAlg
  have hsplit' : Nonempty
      ((B ⧸ maxExt A B) ≃ₐ[ResidueField A] (ι → ResidueField A)) := by
    refine ⟨{ sr with commutes' := ?_ }⟩
    intro x
    rw [show algebraMap (ResidueField A) (B ⧸ maxExt A B) x =
        @algebraMap (ResidueField A) (B ⧸ maxExt A B) _ _ oldAlg x by rfl]
    exact hscomm x
  exact separable_map_of_adjoinRoot_equiv_of_split_quotient
    (maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A) (minpoly A θ)
    (minpoly.monic hθ) e hsplit'

/-- **Nondegenerate closed-fibre trace produces a separable local adjoin-root presentation.** -/
theorem exists_adjoinRoot_equiv_and_separable_residue_of_residue_traceForm_nondegenerate
    {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Module.Finite A B] [CharZero (ResidueField A)] [IsAlgClosed (ResidueField A)]
    (h : (Algebra.traceForm (ResidueField A) (B ⧸ maxExt A B)).Nondegenerate) :
    ∃ θ : B, IsIntegral A θ ∧
      Nonempty (AdjoinRoot (minpoly A θ) ≃ₐ[A] B) ∧
        ((minpoly A θ).map (algebraMap A (ResidueField A))).Separable := by
  letI : Module.Finite A (B ⧸ maxExt A B) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (maxExt A B)).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : Module.Finite (ResidueField A) (B ⧸ maxExt A B) :=
    Module.Finite.of_restrictScalars_finite A _ _
  letI : IsArtinianRing (B ⧸ maxExt A B) :=
    isArtinian_of_tower (ResidueField A) inferInstance
  letI : Fintype (MaximalSpectrum (B ⧸ maxExt A B)) := Fintype.ofFinite _
  exact exists_adjoinRoot_equiv_and_separable_residue_of_split_residue_fibre
    (nonempty_algEquiv_pi_of_traceForm_nondegenerate h)

end GaloisForLFunctions.HTGeometry
