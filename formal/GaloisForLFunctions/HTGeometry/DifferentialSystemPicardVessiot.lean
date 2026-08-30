import GaloisForLFunctions.HTGeometry.DifferentialDeltaQuotient

/-!
# Existence of a Picard--Vessiot ring for a linear differential system

A nontrivial differential ring carrying an invertible fundamental solution matrix of a linear
system `δ Y = A Y` has a `δ`-simple quotient in which that matrix is still an invertible
fundamental solution, and whose constants form a field.  This is the differential analogue of the
difference construction, and it is the ring-theoretic foundation of differential Galois theory.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Existence of a Picard--Vessiot quotient of a differential ring with a fundamental matrix.**
A nontrivial differential ring carrying an invertible fundamental solution matrix of a linear
system has a `δ`-simple quotient in which the matrix is still an invertible fundamental solution,
and the constants of that quotient form a field. -/
theorem exists_deltaPicardVessiot_of_fundamentalMatrix
    {S : Type*} [CommRing S] [Nontrivial S] [Differential S]
    {N : ℕ} (B Y : Matrix (Fin N) (Fin N) S)
    (hY : ∀ i j, (Y i j)′ = (B * Y) i j) (hdet : IsUnit Y.det) :
    ∃ (M : Ideal S) (hM : IsDeltaIdeal M) (_ : M ≠ ⊤),
      @IsDeltaSimple (S ⧸ M) _ (quotientDifferential M hM) ∧
      IsField (@deltaConstantsSubring (S ⧸ M) _ (quotientDifferential M hM)) ∧
      (∀ i j, @Differential.deriv (S ⧸ M) _ (quotientDifferential M hM)
          (Ideal.Quotient.mk M (Y i j))
        = ((B.map (Ideal.Quotient.mk M)) * (Y.map (Ideal.Quotient.mk M))) i j) ∧
      IsUnit (Y.map (Ideal.Quotient.mk M)).det := by
  classical
  obtain ⟨M, _, hM, hMne, hmax⟩ :=
    exists_maximal_isDeltaIdeal (R := S) (⊥ : Ideal S) isDeltaIdeal_bot bot_ne_top
  have hsimple : @IsDeltaSimple (S ⧸ M) _ (quotientDifferential M hM) :=
    isDeltaSimple_quotient_of_maximal hM hmax
  haveI : Nontrivial (S ⧸ M) := nontrivial_quotient_of_ne_top hMne
  refine ⟨M, hM, hMne, hsimple,
    @isField_deltaConstantsSubring_of_isDeltaSimple _ _ (quotientDifferential M hM) _ hsimple,
    ?_, ?_⟩
  · intro i j
    rw [quotientDifferential_deriv_mk, hY i j]
    simp [Matrix.mul_apply, Matrix.map_apply, map_sum]
  · have hmap : (Y.map (Ideal.Quotient.mk M)).det = Ideal.Quotient.mk M Y.det := by
      rw [RingHom.map_det (Ideal.Quotient.mk M) Y, RingHom.mapMatrix_apply]
    rw [hmap]
    exact hdet.map (Ideal.Quotient.mk M)

end

end GaloisForLFunctions.HTGeometry
