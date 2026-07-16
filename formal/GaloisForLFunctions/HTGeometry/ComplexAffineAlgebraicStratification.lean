import GaloisForLFunctions.HTGeometry.ComplexAffineAlgebraicRegularPeel
import GaloisForLFunctions.HTGeometry.NoetherianRegularStratification

/-!
# Finite regular stratification of complex affine algebraic sets
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- A local regular-level-set codimension bound can be weakened. -/
theorem IsLocalRegularLevelSetOfCodimAtLeast.mono
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {S : Set Y} {c d : ℕ} (hdc : d ≤ c)
    (hS : IsLocalRegularLevelSetOfCodimAtLeast S c) :
    IsLocalRegularLevelSetOfCodimAtLeast S d := by
  intro y hy
  obtain ⟨m, hcm, U, hU, hyU, g, hg, hzero, hsurj⟩ := hS y hy
  exact ⟨m, hdc.trans hcm, U, hU, hyU, g, hg, hzero, hsurj⟩

set_option maxHeartbeats 2000000 in
/-- Every complex affine algebraic set admits a finite disjoint stratification by local regular
level sets.  The universal codimension bound is zero; stronger bounds require geometric input
excluding components of smaller codimension. -/
theorem complexAffineAlgebraic_finiteRegularStratification_zero
    {n : ℕ} (S : Set (Fin n → ℂ))
    (hS : IsComplexAffineAlgebraic S) :
    Nonempty (FiniteRegularStratification S 0) := by
  refine finiteRegularStratification_of_wellFounded_peel
    IsComplexAffineAlgebraic wellFounded_ssubset_complexAffineAlgebraic
    ?_ S hS
  intro T hT hTne
  let I : Ideal (MvPolynomial (Fin n) ℂ) :=
    MvPolynomial.vanishingIdeal ℂ T
  have hzero : MvPolynomial.zeroLocus ℂ I = T :=
    hT.zeroLocus_vanishingIdeal_eq
  have hI : I ≠ ⊤ := by
    intro htop
    have hTempty : T = ∅ := by
      apply not_nonempty_iff_eq_empty.mp
      rintro ⟨y, hy⟩
      have hyI : y ∈ MvPolynomial.zeroLocus ℂ I := by
        rw [hzero]
        exact hy
      have h1 := hyI 1 (by rw [htop]; trivial)
      rw [map_one] at h1
      exact one_ne_zero h1
    exact hTne.ne_empty hTempty
  have hrad : I.IsRadical := by
    rw [← Ideal.radical_eq_iff]
    calc
      I.radical = MvPolynomial.vanishingIdeal ℂ
          (MvPolynomial.zeroLocus ℂ I) :=
        (MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I).symm
      _ = MvPolynomial.vanishingIdeal ℂ T := by rw [hzero]
      _ = I := rfl
  obtain ⟨m, R, hRne, hRsub, hRreg, hrem⟩ :=
    exists_regularPeel_complex_zeroLocus_of_proper_radical I hI hrad
  refine ⟨R, hRne, ?_, ?_, ?_⟩
  · simpa [hzero] using hRsub
  · exact hRreg.mono (Nat.zero_le (2 * m))
  · simpa [hzero] using hrem

end

end GaloisForLFunctions.HTGeometry
