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

/-- A complex affine algebraic set has complex codimension at least `c` when the Krull dimension
of its reduced coordinate ring is at most the ambient dimension minus `c`. -/
def IsComplexAffineAlgebraicOfCodimAtLeast {n : ℕ}
    (S : Set (Fin n → ℂ)) (c : ℕ) : Prop :=
  IsComplexAffineAlgebraic S ∧
    ringKrullDim ((MvPolynomial (Fin n) ℂ) ⧸ MvPolynomial.vanishingIdeal ℂ S) + c ≤
      (n : WithBot ℕ∞)

/-- Algebraic subsets inherit a global Krull-codimension lower bound. -/
theorem IsComplexAffineAlgebraicOfCodimAtLeast.mono
    {n c : ℕ} {S T : Set (Fin n → ℂ)}
    (hS : IsComplexAffineAlgebraicOfCodimAtLeast S c)
    (hTalg : IsComplexAffineAlgebraic T) (hTS : T ⊆ S) :
    IsComplexAffineAlgebraicOfCodimAtLeast T c := by
  refine ⟨hTalg, ?_⟩
  have hideal : MvPolynomial.vanishingIdeal ℂ S ≤
      MvPolynomial.vanishingIdeal ℂ T :=
    MvPolynomial.vanishingIdeal_anti_mono hTS
  have hdim : ringKrullDim
      ((MvPolynomial (Fin n) ℂ) ⧸ MvPolynomial.vanishingIdeal ℂ T) ≤
      ringKrullDim
        ((MvPolynomial (Fin n) ℂ) ⧸ MvPolynomial.vanishingIdeal ℂ S) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hideal)
      (Ideal.Quotient.factor_surjective hideal)
  have hadd := add_le_add_right hdim (c : WithBot ℕ∞)
  have hadd' : ringKrullDim
        ((MvPolynomial (Fin n) ℂ) ⧸ MvPolynomial.vanishingIdeal ℂ T) + c ≤
      ringKrullDim
        ((MvPolynomial (Fin n) ℂ) ⧸ MvPolynomial.vanishingIdeal ℂ S) + c := by
    simpa [add_comm] using hadd
  exact hadd'.trans hS.2

theorem wellFounded_ssubset_complexAffineAlgebraicOfCodimAtLeast
    {n c : ℕ} :
    WellFounded (fun T S :
      {Z : Set (Fin n → ℂ) // IsComplexAffineAlgebraicOfCodimAtLeast Z c} =>
        T.1 ⊂ S.1) := by
  let f : {Z : Set (Fin n → ℂ) // IsComplexAffineAlgebraicOfCodimAtLeast Z c} →
      {Z : Set (Fin n → ℂ) // IsComplexAffineAlgebraic Z} :=
    fun Z ↦ ⟨Z.1, Z.2.1⟩
  simpa [f] using!
    (wellFounded_ssubset_complexAffineAlgebraic (n := n)).onFun (f := f)

set_option maxHeartbeats 4000000 in
/-- Every complex affine algebraic set of complex codimension at least `c` has a finite
stratification by real regular level sets of codimension at least `2 * c`. -/
theorem complexAffineAlgebraic_finiteRegularStratification_of_krullDim
    {n c : ℕ} (S : Set (Fin n → ℂ))
    (hS : IsComplexAffineAlgebraic S)
    (hdim : ringKrullDim
        ((MvPolynomial (Fin n) ℂ) ⧸ MvPolynomial.vanishingIdeal ℂ S) + c ≤
      (n : WithBot ℕ∞)) :
    Nonempty (FiniteRegularStratification S (2 * c)) := by
  refine finiteRegularStratification_of_wellFounded_peel
    (fun T ↦ IsComplexAffineAlgebraicOfCodimAtLeast T c)
    wellFounded_ssubset_complexAffineAlgebraicOfCodimAtLeast ?_ S ⟨hS, hdim⟩
  intro T hT hTne
  let I : Ideal (MvPolynomial (Fin n) ℂ) := MvPolynomial.vanishingIdeal ℂ T
  have hzero : MvPolynomial.zeroLocus ℂ I = T := hT.1.zeroLocus_vanishingIdeal_eq
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
      I.radical = MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) :=
        (MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I).symm
      _ = MvPolynomial.vanishingIdeal ℂ T := by rw [hzero]
      _ = I := rfl
  obtain ⟨m, R, hcm, hRne, hRsub, hRreg, hrem⟩ :=
    exists_regularPeel_complex_zeroLocus_of_proper_radical_with_codim
      I hI hrad hT.2
  refine ⟨R, hRne, ?_, hRreg, ?_⟩
  · simpa [hzero] using hRsub
  · have hrem' : IsComplexAffineAlgebraic (T \ R) := by
      simpa [hzero] using hrem
    exact IsComplexAffineAlgebraicOfCodimAtLeast.mono hT hrem' diff_subset

end

end GaloisForLFunctions.HTGeometry
