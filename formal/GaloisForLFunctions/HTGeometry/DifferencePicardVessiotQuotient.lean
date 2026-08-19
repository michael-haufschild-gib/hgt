import GaloisForLFunctions.HTGeometry.DifferenceCoordinateRing

/-!
# Picard--Vessiot quotients: the `σ`-simple difference ring of a maximal `σ`-ideal

A Picard--Vessiot ring for a linear difference system is the quotient of the coordinate ring of a
fundamental matrix by a maximal `σ`-ideal.  This file proves that such a quotient is a difference
ring in its own right — the automorphism descends because maximality forces the ideal to be stable
under `σ` in *both* directions — that it is `σ`-simple, and hence that its constants form a field
and it is reduced.

The last two conclusions are the defining properties of a Picard--Vessiot ring: the solution space
of the system inside it is a vector space over a field of constants, of dimension exactly the rank
of the system.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R]

/-! ### Two-sided stability of a maximal `σ`-ideal -/

/-- The preimage of a `σ`-ideal is a `σ`-ideal. -/
theorem isSigmaIdeal_comap {σ : R ≃+* R} {I : Ideal R} (hI : IsSigmaIdeal σ I) :
    IsSigmaIdeal σ (Ideal.comap (σ : R →+* R) I) := by
  intro x hx
  exact hI _ hx

theorem le_comap_of_isSigmaIdeal {σ : R ≃+* R} {I : Ideal R} (hI : IsSigmaIdeal σ I) :
    I ≤ Ideal.comap (σ : R →+* R) I := fun x hx => hI x hx

theorem comap_ne_top_of_ne_top {σ : R ≃+* R} {I : Ideal R} (h : I ≠ ⊤) :
    Ideal.comap (σ : R →+* R) I ≠ ⊤ := by
  intro htop
  apply h
  have h1 : (1 : R) ∈ Ideal.comap (σ : R →+* R) I := by rw [htop]; trivial
  have : (1 : R) ∈ I := by simpa using h1
  exact Ideal.eq_top_of_isUnit_mem I this isUnit_one

/-- **A maximal `σ`-ideal is stable under the inverse automorphism.**  Its preimage is again a
proper `σ`-ideal containing it, so maximality forces equality. -/
theorem isSigmaIdeal_symm_of_maximal {σ : R ≃+* R} {M : Ideal R}
    (hM : IsSigmaIdeal σ M) (hne : M ≠ ⊤)
    (hmax : ∀ J : Ideal R, IsSigmaIdeal σ J → J ≠ ⊤ → M ≤ J → J = M) :
    IsSigmaIdeal σ.symm M := by
  have hcomap : Ideal.comap (σ : R →+* R) M = M :=
    hmax _ (isSigmaIdeal_comap hM) (comap_ne_top_of_ne_top hne) (le_comap_of_isSigmaIdeal hM)
  intro x hx
  have : σ (σ.symm x) ∈ M := by rw [σ.apply_symm_apply]; exact hx
  exact hcomap ▸ this

/-- A `σ`-ideal stable in both directions is carried onto itself. -/
theorem map_eq_self_of_isSigmaIdeal {σ : R ≃+* R} {I : Ideal R}
    (hI : IsSigmaIdeal σ I) (hI' : IsSigmaIdeal σ.symm I) :
    I = Ideal.map (σ : R →+* R) I := by
  refine le_antisymm (fun x hx => ?_) (Ideal.map_le_iff_le_comap.mpr (le_comap_of_isSigmaIdeal hI))
  have hpre : σ.symm x ∈ I := hI' x hx
  have hmem := Ideal.mem_map_of_mem (σ : R →+* R) hpre
  have heq : (σ : R →+* R) (σ.symm x) = x := σ.apply_symm_apply x
  rwa [heq] at hmem

/-! ### The induced automorphism on the quotient -/

/-- The automorphism induced on the quotient by a two-sided stable `σ`-ideal. -/
def sigmaQuotientEquiv (σ : R ≃+* R) (I : Ideal R)
    (hI : IsSigmaIdeal σ I) (hI' : IsSigmaIdeal σ.symm I) :
    (R ⧸ I) ≃+* (R ⧸ I) :=
  Ideal.quotientEquiv I I σ (map_eq_self_of_isSigmaIdeal hI hI')

@[simp] theorem sigmaQuotientEquiv_mk (σ : R ≃+* R) (I : Ideal R)
    (hI : IsSigmaIdeal σ I) (hI' : IsSigmaIdeal σ.symm I) (x : R) :
    sigmaQuotientEquiv σ I hI hI' (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (σ x) := rfl

/-! ### `σ`-simplicity of the quotient by a maximal `σ`-ideal -/

/-- **The quotient by a maximal `σ`-ideal is `σ`-simple.**  This is the defining property of a
Picard--Vessiot ring. -/
theorem isSigmaSimple_quotient_of_maximal {σ : R ≃+* R} {M : Ideal R}
    (hM : IsSigmaIdeal σ M) (hne : M ≠ ⊤)
    (hmax : ∀ J : Ideal R, IsSigmaIdeal σ J → J ≠ ⊤ → M ≤ J → J = M) :
    IsSigmaSimple (sigmaQuotientEquiv σ M hM (isSigmaIdeal_symm_of_maximal hM hne hmax)) := by
  classical
  set hM' := isSigmaIdeal_symm_of_maximal hM hne hmax with hM'def
  intro J hJ
  by_cases htop : J = ⊤
  · exact Or.inr htop
  refine Or.inl ?_
  set f : R →+* R ⧸ M := Ideal.Quotient.mk M with hf
  set J' : Ideal R := Ideal.comap f J with hJ'
  have hMJ' : M ≤ J' := by
    intro x hx
    have : f x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    show f x ∈ J
    rw [this]
    exact J.zero_mem
  have hJ'sigma : IsSigmaIdeal σ J' := by
    intro x hx
    show f (σ x) ∈ J
    have hmk : f (σ x) = sigmaQuotientEquiv σ M hM hM' (f x) := rfl
    rw [hmk]
    exact hJ _ hx
  have hJ'top : J' ≠ ⊤ := by
    intro h1
    apply htop
    have : (1 : R) ∈ J' := by rw [h1]; trivial
    have h1J : (1 : R ⧸ M) ∈ J := by simpa [hJ', hf] using this
    exact Ideal.eq_top_of_isUnit_mem J h1J isUnit_one
  have hJ'eq : J' = M := hmax J' hJ'sigma hJ'top hMJ'
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  calc J = Ideal.map f J' := (Ideal.map_comap_of_surjective f hsurj J).symm
    _ = Ideal.map f M := by rw [hJ'eq]
    _ = ⊥ := Ideal.map_quotient_self M

/-! ### Consequences for the Picard--Vessiot ring -/

/-- A Picard--Vessiot quotient is reduced. -/
theorem isReduced_quotient_of_maximal {σ : R ≃+* R} {M : Ideal R}
    (hM : IsSigmaIdeal σ M) (hne : M ≠ ⊤)
    (hmax : ∀ J : Ideal R, IsSigmaIdeal σ J → J ≠ ⊤ → M ≤ J → J = M) :
    IsReduced (R ⧸ M) := by
  haveI : Nontrivial (R ⧸ M) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact hne
  exact isReduced_of_isSigmaSimple (isSigmaSimple_quotient_of_maximal hM hne hmax)

/-- **The constants of a Picard--Vessiot ring form a field.** -/
theorem isField_constants_quotient_of_maximal {σ : R ≃+* R} {M : Ideal R}
    (hM : IsSigmaIdeal σ M) (hne : M ≠ ⊤)
    (hmax : ∀ J : Ideal R, IsSigmaIdeal σ J → J ≠ ⊤ → M ≤ J → J = M) :
    IsField (sigmaConstantsSubring
      (sigmaQuotientEquiv σ M hM (isSigmaIdeal_symm_of_maximal hM hne hmax))) := by
  haveI : Nontrivial (R ⧸ M) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact hne
  exact isField_sigmaConstantsSubring_of_isSigmaSimple
    (isSigmaSimple_quotient_of_maximal hM hne hmax)

/-- **Existence of a Picard--Vessiot quotient.**  Any proper `σ`-ideal of a difference ring is
contained in one whose quotient is `σ`-simple, reduced, and has a field of constants. -/
theorem exists_sigmaSimple_quotient (σ : R ≃+* R) (I : Ideal R)
    (hI : IsSigmaIdeal σ I) (hne : I ≠ ⊤) :
    ∃ (M : Ideal R) (hM : IsSigmaIdeal σ M) (_ : M ≠ ⊤)
      (hM' : IsSigmaIdeal σ.symm M),
      I ≤ M ∧ IsSigmaSimple (sigmaQuotientEquiv σ M hM hM') := by
  obtain ⟨M, hIM, hM, hMne, hmax⟩ := exists_maximal_isSigmaIdeal σ I hI hne
  exact ⟨M, hM, hMne, isSigmaIdeal_symm_of_maximal hM hMne hmax, hIM,
    isSigmaSimple_quotient_of_maximal hM hMne hmax⟩

end

end GaloisForLFunctions.HTGeometry
