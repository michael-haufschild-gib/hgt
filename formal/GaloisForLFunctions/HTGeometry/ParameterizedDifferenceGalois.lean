import GaloisForLFunctions.HTGeometry.DifferenceGaloisRepresentation

/-!
# The parameterized layer: difference rings carrying a commuting derivation

Dreyfus's classification is a theorem of *parameterized* difference Galois theory: the difference
equation is studied together with a derivation in the same variable, and the Galois group becomes a
linear differential algebraic group over the differential field of constants.  This file builds the
ring-theoretic layer of that setting.

The two facts that make the parameterized theory possible are here: ideals stable under both
operators admit maximal ones, so parameterized Picard--Vessiot quotients exist; and the constants
of the difference operator are stable under the derivation, so they form a *differential* field
rather than a bare field.  The Galois matrix of a parameterized automorphism therefore has entries
in a differential field, which is what makes its image a differential algebraic group.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

/-- A difference operator commuting with the derivation. -/
def CommutesDeriv (σ : R ≃+* R) : Prop :=
  ∀ x : R, σ (Differential.deriv x) = Differential.deriv (σ x)

/-! ### Ideals stable under both operators -/

/-- An ideal stable under both the difference operator and the derivation. -/
def IsSigmaDeltaIdeal (σ : R ≃+* R) (I : Ideal R) : Prop :=
  IsSigmaIdeal σ I ∧ ∀ x ∈ I, Differential.deriv x ∈ I

theorem isSigmaDeltaIdeal_bot (σ : R ≃+* R) : IsSigmaDeltaIdeal σ (⊥ : Ideal R) := by
  refine ⟨isSigmaIdeal_bot σ, fun x hx => ?_⟩
  have hx0 : x = 0 := by simpa using hx
  simp [hx0]

theorem isSigmaDeltaIdeal_top (σ : R ≃+* R) : IsSigmaDeltaIdeal σ (⊤ : Ideal R) :=
  ⟨isSigmaIdeal_top σ, fun _ _ => trivial⟩

/-- **Maximal doubly stable ideals exist.**  Every proper ideal stable under both operators lies in
one maximal among the proper such ideals. -/
theorem exists_maximal_isSigmaDeltaIdeal (σ : R ≃+* R) (I : Ideal R)
    (hI : IsSigmaDeltaIdeal σ I) (hne : I ≠ ⊤) :
    ∃ M : Ideal R, I ≤ M ∧ IsSigmaDeltaIdeal σ M ∧ M ≠ ⊤ ∧
      ∀ J : Ideal R, IsSigmaDeltaIdeal σ J → J ≠ ⊤ → M ≤ J → J = M := by
  classical
  set S : Set (Ideal R) := {J | I ≤ J ∧ IsSigmaDeltaIdeal σ J ∧ J ≠ ⊤} with hS
  have hIS : I ∈ S := ⟨le_rfl, hI, hne⟩
  have hchain : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hne'
    · exact ⟨I, hIS, by simp⟩
    · refine ⟨sSup c, ⟨?_, ⟨?_, ?_⟩, ?_⟩, fun z hz => le_sSup hz⟩
      · obtain ⟨J, hJ⟩ := hne'
        exact le_trans (hcS hJ).1 (le_sSup hJ)
      · intro x hx
        rw [Submodule.mem_sSup_of_directed hne' hc.directedOn] at hx ⊢
        obtain ⟨J, hJc, hxJ⟩ := hx
        exact ⟨J, hJc, (hcS hJc).2.1.1 x hxJ⟩
      · intro x hx
        rw [Submodule.mem_sSup_of_directed hne' hc.directedOn] at hx ⊢
        obtain ⟨J, hJc, hxJ⟩ := hx
        exact ⟨J, hJc, (hcS hJc).2.1.2 x hxJ⟩
      · intro htop
        have h1 : (1 : R) ∈ sSup c := by rw [htop]; trivial
        rw [Submodule.mem_sSup_of_directed hne' hc.directedOn] at h1
        obtain ⟨J, hJc, h1J⟩ := h1
        exact (hcS hJc).2.2 (Ideal.eq_top_of_isUnit_mem J h1J isUnit_one)
  obtain ⟨M, hMS, hmax⟩ := zorn_le₀ S hchain
  exact ⟨M, hMS.1, hMS.2.1, hMS.2.2, fun J hJ hJtop hle =>
    le_antisymm (hmax ⟨le_trans hMS.1 hle, hJ, hJtop⟩ hle) hle⟩

/-- A difference ring with a commuting derivation is doubly simple when its only ideals stable
under both operators are the trivial ones. -/
def IsSigmaDeltaSimple (σ : R ≃+* R) : Prop :=
  ∀ I : Ideal R, IsSigmaDeltaIdeal σ I → I = ⊥ ∨ I = ⊤

theorem isSigmaDeltaSimple_of_isSigmaSimple {σ : R ≃+* R} (h : IsSigmaSimple σ) :
    IsSigmaDeltaSimple σ := fun I hI => h I hI.1

/-! ### The constants form a differential ring -/

/-- **The constants are stable under the derivation.**  This is what makes the field of constants
of a parameterized difference ring a *differential* field. -/
theorem deriv_mem_sigmaConstantsSubring {σ : R ≃+* R} (hσ : CommutesDeriv σ)
    {x : R} (hx : x ∈ sigmaConstantsSubring σ) :
    Differential.deriv x ∈ sigmaConstantsSubring σ := by
  have hx' : σ x = x := hx
  show σ (Differential.deriv x) = Differential.deriv x
  rw [hσ x, hx']

/-- **The constants of a `σ`-simple parameterized difference ring form a differential field.** -/
theorem isField_and_derivClosed_sigmaConstantsSubring [Nontrivial R] {σ : R ≃+* R}
    (hsimple : IsSigmaSimple σ) (hσ : CommutesDeriv σ) :
    IsField (sigmaConstantsSubring σ) ∧
      ∀ x ∈ sigmaConstantsSubring σ, Differential.deriv x ∈ sigmaConstantsSubring σ :=
  ⟨isField_sigmaConstantsSubring_of_isSigmaSimple hsimple,
    fun _ hx => deriv_mem_sigmaConstantsSubring hσ hx⟩

/-! ### The parameterized automorphism group -/

variable {K : Type*} [Field K] [Algebra K R]

/-- The group of `K`-algebra automorphisms commuting with both the difference operator and the
derivation: the parameterized difference Galois group. -/
def parameterizedAut (σR : R ≃+* R) : Subgroup (R ≃ₐ[K] R) where
  carrier := {φ | (∀ x : R, φ (σR x) = σR (φ x)) ∧
    ∀ x : R, φ (Differential.deriv x) = Differential.deriv (φ x)}
  one_mem' := ⟨fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro φ ψ ⟨hφσ, hφδ⟩ ⟨hψσ, hψδ⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hψσ, hφσ]
    · rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hψδ, hφδ]
  inv_mem' := by
    rintro φ ⟨hφσ, hφδ⟩
    have hsymm : ∀ y : R, (φ⁻¹ : R ≃ₐ[K] R) y = φ.symm y := fun _ => rfl
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hsymm, hsymm]
      apply φ.injective
      rw [φ.apply_symm_apply, hφσ, φ.apply_symm_apply]
    · rw [hsymm, hsymm]
      apply φ.injective
      rw [φ.apply_symm_apply, hφδ, φ.apply_symm_apply]

@[simp] theorem mem_parameterizedAut {σR : R ≃+* R} {φ : R ≃ₐ[K] R} :
    φ ∈ parameterizedAut (K := K) σR ↔
      (∀ x : R, φ (σR x) = σR (φ x)) ∧
        (∀ x : R, φ (Differential.deriv x) = Differential.deriv (φ x)) := Iff.rfl

theorem parameterizedAut_le_differenceAut (σR : R ≃+* R) :
    parameterizedAut (K := K) σR ≤ differenceAut (K := K) σR :=
  fun _ hφ => hφ.1

/-- **The parameterized Galois matrix lives over a differential field.**  For a parameterized
automorphism the Galois matrix has entries in the constants, and the constants are closed under the
derivation, so the parameterized Galois group is a subgroup of the invertible matrices over a
differential field. -/
theorem galoisMatrix_deriv_mem_sigmaConstants {n : ℕ} (σR : R ≃+* R)
    (hσ : CommutesDeriv σR)
    (B : Matrix (Fin n) (Fin n) K) (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y)
    (φ : R ≃ₐ[K] R) (hφ : φ ∈ parameterizedAut (K := K) σR) (i j : Fin n) :
    galoisMatrix Y φ i j ∈ sigmaConstantsSubring σR ∧
      Differential.deriv (galoisMatrix Y φ i j) ∈ sigmaConstantsSubring σR := by
  have hconst : (galoisMatrix Y φ).map (σR : R → R) = galoisMatrix Y φ :=
    galoisMatrix_map_eq_self σR B Y hY φ hφ.1
  have hij : σR (galoisMatrix Y φ i j) = galoisMatrix Y φ i j :=
    congrFun (congrFun hconst i) j
  exact ⟨hij, deriv_mem_sigmaConstantsSubring hσ hij⟩

end

end GaloisForLFunctions.HTGeometry
