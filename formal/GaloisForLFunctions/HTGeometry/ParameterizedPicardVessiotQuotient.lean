import GaloisForLFunctions.HTGeometry.QuotientDerivation

/-!
# Parameterized Picard--Vessiot quotients

The quotient of a `σ`-`δ` ring by a maximal doubly stable ideal carries both operators and is doubly
simple.  This is the parameterized analogue of `DifferencePicardVessiotQuotient`: the difference
operator descends because maximality forces two-sided stability, the derivation descends because the
ideal is a `δ`-ideal, and the two descended operators still commute.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

/-- A maximal doubly stable ideal is stable under the inverse difference operator. -/
theorem isSigmaIdeal_symm_of_maximal_sigmaDelta {σ : R ≃+* R} (hσ : CommutesDeriv σ)
    {M : Ideal R} (hM : IsSigmaDeltaIdeal σ M) (hne : M ≠ ⊤)
    (hmax : ∀ J : Ideal R, IsSigmaDeltaIdeal σ J → J ≠ ⊤ → M ≤ J → J = M) :
    IsSigmaIdeal σ.symm M := by
  have hcomapDelta : IsSigmaDeltaIdeal σ (Ideal.comap (σ : R →+* R) M) := by
    refine ⟨isSigmaIdeal_comap hM.1, ?_⟩
    intro x hx
    show σ (Differential.deriv x) ∈ M
    rw [hσ x]
    exact hM.2 _ hx
  have hcomap : Ideal.comap (σ : R →+* R) M = M :=
    hmax _ hcomapDelta (comap_ne_top_of_ne_top hne) (le_comap_of_isSigmaIdeal hM.1)
  intro x hx
  have hmem : σ (σ.symm x) ∈ M := by rw [σ.apply_symm_apply]; exact hx
  exact hcomap ▸ hmem

/-- **The quotient by a maximal doubly stable ideal is doubly simple.** -/
theorem isSigmaDeltaSimple_quotient_of_maximal {σ : R ≃+* R} (hσ : CommutesDeriv σ)
    {M : Ideal R} (hM : IsSigmaDeltaIdeal σ M) (hne : M ≠ ⊤)
    (hmax : ∀ J : Ideal R, IsSigmaDeltaIdeal σ J → J ≠ ⊤ → M ≤ J → J = M) :
    @IsSigmaDeltaSimple (R ⧸ M) _ (quotientDifferential M hM.2)
      (sigmaQuotientEquiv σ M hM.1 (isSigmaIdeal_symm_of_maximal_sigmaDelta hσ hM hne hmax)) := by
  classical
  set hM' := isSigmaIdeal_symm_of_maximal_sigmaDelta hσ hM hne hmax with hM'def
  letI : Differential (R ⧸ M) := quotientDifferential M hM.2
  intro J hJ
  by_cases htop : J = ⊤
  · exact Or.inr htop
  refine Or.inl ?_
  set f : R →+* R ⧸ M := Ideal.Quotient.mk M with hf
  set J' : Ideal R := Ideal.comap f J with hJ'
  have hMJ' : M ≤ J' := by
    intro x hx
    have hzero : f x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    show f x ∈ J
    rw [hzero]
    exact J.zero_mem
  have hJ'sigma : IsSigmaIdeal σ J' := by
    intro x hx
    show f (σ x) ∈ J
    have hmk : f (σ x) = sigmaQuotientEquiv σ M hM.1 hM' (f x) := rfl
    rw [hmk]
    exact hJ.1 _ hx
  have hJ'delta : ∀ x ∈ J', Differential.deriv x ∈ J' := by
    intro x hx
    show f (Differential.deriv x) ∈ J
    have hmk : f (Differential.deriv x)
        = @Differential.deriv _ _ (quotientDifferential M hM.2) (f x) := rfl
    rw [hmk]
    exact hJ.2 _ hx
  have hJ'top : J' ≠ ⊤ := by
    intro h1
    apply htop
    have hone : (1 : R) ∈ J' := by rw [h1]; trivial
    have h1J : (1 : R ⧸ M) ∈ J := by simpa [hJ', hf] using hone
    exact Ideal.eq_top_of_isUnit_mem J h1J isUnit_one
  have hJ'eq : J' = M := hmax J' ⟨hJ'sigma, hJ'delta⟩ hJ'top hMJ'
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  calc J = Ideal.map f J' := (Ideal.map_comap_of_surjective f hsurj J).symm
    _ = Ideal.map f M := by rw [hJ'eq]
    _ = ⊥ := Ideal.map_quotient_self M

/-- **Existence of a parameterized Picard--Vessiot quotient.**  Every proper doubly stable ideal is
contained in one whose quotient carries both operators, is doubly simple, and on which the descended
operators commute. -/
theorem exists_sigmaDeltaSimple_quotient (σ : R ≃+* R) (hσ : CommutesDeriv σ)
    (I : Ideal R) (hI : IsSigmaDeltaIdeal σ I) (hne : I ≠ ⊤) :
    ∃ (M : Ideal R) (hM : IsSigmaDeltaIdeal σ M) (_ : M ≠ ⊤)
      (hM' : IsSigmaIdeal σ.symm M),
      I ≤ M ∧
      @IsSigmaDeltaSimple (R ⧸ M) _ (quotientDifferential M hM.2)
        (sigmaQuotientEquiv σ M hM.1 hM') ∧
      @CommutesDeriv (R ⧸ M) _ (quotientDifferential M hM.2)
        (sigmaQuotientEquiv σ M hM.1 hM') := by
  obtain ⟨M, hIM, hM, hMne, hmax⟩ := exists_maximal_isSigmaDeltaIdeal σ I hI hne
  refine ⟨M, hM, hMne, isSigmaIdeal_symm_of_maximal_sigmaDelta hσ hM hMne hmax, hIM, ?_, ?_⟩
  · exact isSigmaDeltaSimple_quotient_of_maximal hσ hM hMne hmax
  · exact quotientDifferential_commutesDeriv hσ M hM
      (isSigmaIdeal_symm_of_maximal_sigmaDelta hσ hM hMne hmax)

end

end GaloisForLFunctions.HTGeometry
