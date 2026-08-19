import GaloisForLFunctions.HTGeometry.SigmaIdealConstantCoefficients

/-!
# Constants are linearly disjoint from a `σ`-simple base

The torsor isomorphism `R ⊗_K R ≅ R ⊗_C C[G]` needs the constants of the big ring to stay linearly
independent after extending scalars from the constants of the base to the base itself.  That is the
zero-ideal case of the `σ`-ideal theorem: a nontrivial `R`-relation among constants produces, by the
same minimal-support argument, a nontrivial relation with *constant* coefficients.

So linear disjointness of the constants is not an extra hypothesis: it is a consequence of
`σ`-simplicity of the base.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Constants linearly independent over the base constants are linearly independent over the
base.** -/
theorem basisIndependentOver_of_constants [Nontrivial R]
    (σR : R ≃+* R) (σA : A ≃+* A)
    (hcompat : ∀ r : R, σA (algebraMap R A r) = algebraMap R A (σR r))
    (hsimple : IsSigmaSimple σR)
    {ι : Type*} [DecidableEq ι] (b : ι → A) (hb : ∀ j, σA (b j) = b j)
    (hCindep : ∀ (t : Finset ι) (d : ι → R), (∀ j ∈ t, σR (d j) = d j) →
        (∑ j ∈ t, algebraMap R A (d j) * b j) = 0 → ∀ j ∈ t, d j = 0) :
    BasisIndependentOver R b := by
  classical
  intro s r hsum j hj
  by_contra hrj
  obtain ⟨t, d, htne, hconst, hnz, hdI⟩ :=
    exists_constant_coeff_mem_sigmaIdeal σR σA hcompat hsimple b hb
      (⊥ : Ideal A) (isSigmaIdeal_bot σA) s.card s r rfl ⟨j, hj, hrj⟩
      (by rw [hsum]; exact Ideal.zero_mem ⊥)
  obtain ⟨j', hj'⟩ := htne
  refine hnz j' hj' (hCindep t d hconst ?_ j' hj')
  simpa using hdI

/-- **A nonzero `σ`-ideal meets the constant span nontrivially.**  The contraction of a nonzero
`σ`-ideal to the constant span of a family of constants is nonzero, which is what makes the ideal
correspondence with the coordinate ring of the Galois group faithful. -/
theorem exists_nonzero_constant_span_mem_of_sigmaIdeal [Nontrivial R]
    (σR : R ≃+* R) (σA : A ≃+* A)
    (hcompat : ∀ r : R, σA (algebraMap R A r) = algebraMap R A (σR r))
    (hsimple : IsSigmaSimple σR)
    {ι : Type*} [DecidableEq ι] (b : ι → A) (hb : ∀ j, σA (b j) = b j)
    (hli : BasisIndependentOver R b)
    (I : Ideal A) (hI : IsSigmaIdeal σA I)
    (s : Finset ι) (r : ι → R) (hne : ∃ j ∈ s, r j ≠ 0)
    (hmem : (∑ j ∈ s, algebraMap R A (r j) * b j) ∈ I) :
    ∃ (t : Finset ι) (d : ι → R), t.Nonempty ∧ (∀ j ∈ t, σR (d j) = d j) ∧
      (∀ j ∈ t, d j ≠ 0) ∧ (∑ j ∈ t, algebraMap R A (d j) * b j) ∈ I ∧
      (∑ j ∈ t, algebraMap R A (d j) * b j) ≠ 0 := by
  obtain ⟨t, d, htne, hconst, hnz, hdI⟩ :=
    exists_constant_coeff_mem_sigmaIdeal σR σA hcompat hsimple b hb I hI
      s.card s r rfl hne hmem
  refine ⟨t, d, htne, hconst, hnz, hdI, ?_⟩
  intro hzero
  obtain ⟨j, hj⟩ := htne
  exact hnz j hj (hli t d hzero j hj)

end

end GaloisForLFunctions.HTGeometry
