import GaloisForLFunctions.HTGeometry.ParameterizedPicardVessiotQuotient

/-!
# Existence of a parameterized Picard--Vessiot ring

The parameterized analogue of `exists_picardVessiot_of_fundamentalMatrix`: a nontrivial
`σ`-`δ` ring carrying an invertible fundamental solution matrix has a doubly simple quotient in
which the matrix is still an invertible fundamental solution and on which the two descended
operators commute.

This is the ring in which the parameterized difference Galois group lives.  Its Galois matrix has
entries in the constants of the difference operator, and those constants are closed under the
derivation, so the group is a *differential* algebraic group -- the structure Cassidy's
classification acts on.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {S : Type*} [CommRing S] [Differential S]

/-- **Existence of a parameterized Picard--Vessiot quotient of a `σ`-`δ` ring with a fundamental
matrix.** -/
theorem exists_parameterizedPicardVessiot_of_fundamentalMatrix [Nontrivial S]
    (τ : S ≃+* S) (hτ : CommutesDeriv τ) {n : ℕ} (B Y : Matrix (Fin n) (Fin n) S)
    (hY : ∀ i j, τ (Y i j) = (B * Y) i j) (hdet : IsUnit Y.det) :
    ∃ (M : Ideal S) (hM : IsSigmaDeltaIdeal τ M) (_ : M ≠ ⊤) (hM' : IsSigmaIdeal τ.symm M),
      @IsSigmaDeltaSimple (S ⧸ M) _ (quotientDifferential M hM.2)
        (sigmaQuotientEquiv τ M hM.1 hM') ∧
      @CommutesDeriv (S ⧸ M) _ (quotientDifferential M hM.2)
        (sigmaQuotientEquiv τ M hM.1 hM') ∧
      (∀ i j, sigmaQuotientEquiv τ M hM.1 hM' (Ideal.Quotient.mk M (Y i j))
        = ((B.map (Ideal.Quotient.mk M)) * (Y.map (Ideal.Quotient.mk M))) i j) ∧
      IsUnit ((Y.map (Ideal.Quotient.mk M)).det) := by
  classical
  obtain ⟨M, hM, hMne, hM', -, hsimple, hcomm⟩ :=
    exists_sigmaDeltaSimple_quotient τ hτ (⊥ : Ideal S) (isSigmaDeltaIdeal_bot τ) bot_ne_top
  refine ⟨M, hM, hMne, hM', hsimple, hcomm, ?_, ?_⟩
  · intro i j
    have hmk : sigmaQuotientEquiv τ M hM.1 hM' (Ideal.Quotient.mk M (Y i j))
        = Ideal.Quotient.mk M (τ (Y i j)) := rfl
    rw [hmk, hY i j]
    simp [Matrix.mul_apply, Matrix.map_apply, map_sum]
  · have hmap : (Y.map (Ideal.Quotient.mk M)).det = Ideal.Quotient.mk M Y.det := by
      rw [RingHom.map_det (Ideal.Quotient.mk M) Y, RingHom.mapMatrix_apply]
    rw [hmap]
    exact hdet.map (Ideal.Quotient.mk M)

end

end GaloisForLFunctions.HTGeometry
