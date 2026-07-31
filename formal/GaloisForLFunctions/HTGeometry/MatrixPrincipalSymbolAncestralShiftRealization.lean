import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolDerivationLawHorizon

/-!
# Ancestral shift realization of hyperplane phase diagrams

This file identifies the exact law required of the external source.  An ancestrally free grid
`x i n` is acted on by each selected derivation as a character-weighted unilateral shift.  Its
complete selected-law jet packet is then obtained by a diagonal principal symbol, and its actual
differential-algebraic dependence spectrum is exactly the union of the character kernels.

The theorem is a conditional realization statement.  Constructing a universal differential field
carrying such a free shift grid is isolated as the remaining existence problem; no existence is
silently assumed or claimed here.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {K L h ι : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup h] [Module K h] [Fintype ι] [DecidableEq ι]

/-- The diagonal symbol of a character-weighted ancestral shift at layer `n`. -/
def ancestralShiftPrincipalSymbol
    (characters : ι → h →ₗ[K] K) (A : h) (n : ℕ) : Matrix ι ι K :=
  Matrix.diagonal fun i ↦ (characters i A) ^ n

omit [Fintype ι] [DecidableEq ι] in
/-- Iterating a character-weighted shift produces the corresponding character power. -/
theorem selectedDerivationJet_ancestralShift
    (ancestor : ℕ → ι → L)
    (law : h → Derivation K L L)
    (characters : ι → h →ₗ[K] K)
    (hshift : ∀ A n i,
      law A (ancestor n i) = characters i A • ancestor (n + 1) i)
    (A : h) (i : ι) :
    ∀ n, selectedDerivationJet (law A) n (ancestor 0 i) =
      (characters i A) ^ n • ancestor n i := by
  intro n
  induction n with
  | zero => simp [selectedDerivationJet]
  | succ n ih =>
      simp only [selectedDerivationJet, Function.iterate_succ_apply']
      change law A (selectedDerivationJet (law A) n (ancestor 0 i)) =
        (characters i A) ^ (n + 1) • ancestor (n + 1) i
      rw [ih, (law A).map_smul, hshift A n i]
      simp [pow_succ, smul_smul, mul_comm]

/-- The weighted ancestral shift is an explicit diagonal principal lower law. -/
theorem ancestralShift_principalLowerLaw
    (ancestor : ℕ → ι → L)
    (law : h → Derivation K L L)
    (characters : ι → h →ₗ[K] K)
    (hshift : ∀ A n i,
      law A (ancestor n i) = characters i A • ancestor (n + 1) i)
    (A : h) :
    MatrixPrincipalLowerLaw ancestor
      (fun n i ↦ selectedDerivationJet (law A) n (ancestor 0 i))
      (fun n ↦ ancestralShiftPrincipalSymbol characters A n) := by
  intro N
  refine ⟨0, ?_, ?_⟩
  · simp
  · funext p
    change selectedDerivationJet (law A) (p.1 : ℕ) (ancestor 0 p.2) = _
    rw [selectedDerivationJet_ancestralShift ancestor law characters hshift A p.2 p.1]
    simp only [zero_add, matrixLinearForms, matrixPrincipalBlockDiagonal,
      ancestralShiftPrincipalSymbol]
    rw [Finset.sum_eq_single p]
    · simp [Algebra.smul_def]
    · intro q _ hqp
      by_cases hlevel : p.1 = q.1
      · have hindex : p.2 ≠ q.2 := by
          intro h
          exact hqp (Prod.ext hlevel.symm h.symm)
        simp [hlevel, hindex]
      · simp [hlevel]
    · simp

/-- **Ancestral shift phase theorem.**  A finite observable family in a free ancestral shift
sector is differentially algebraically independent for the selected law `A` exactly when all of
the sector characters are nonzero at `A`. -/
theorem derivationIndependentOver_ancestralShift_iff
    (ancestor : ℕ → ι → L)
    (law : h → Derivation K L L)
    (characters : ι → h →ₗ[K] K)
    (hshift : ∀ A n i,
      law A (ancestor n i) = characters i A • ancestor (n + 1) i)
    (hancestor : AlgebraicIndependent K
      (fun p : ℕ × ι ↦ ancestor p.1 p.2))
    (A : h) :
    DerivationIndependentOver K (law A) (ancestor 0) ↔
      ∀ i, characters i A ≠ 0 := by
  rw [derivationPrincipalLowerLaw_independent_iff
    ancestor (ancestor 0) (law A)
    (fun n ↦ ancestralShiftPrincipalSymbol characters A n)
    (ancestralShift_principalLowerLaw ancestor law characters hshift A)
    hancestor]
  constructor
  · intro hsymbols i hi
    have hdet := hsymbols 1
    apply hdet
    rw [ancestralShiftPrincipalSymbol, Matrix.det_diagonal]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa using hi
  · intro hall n
    rw [ancestralShiftPrincipalSymbol, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero n (hall i)

/-- **Exact hyperplane-spectrum realization.**  Under the ancestral shift law, the actual
varying-derivation dependence set is precisely the finite union of character kernels. -/
theorem derivationLawDependentSet_ancestralShift_eq_hyperplaneArrangement
    (ancestor : ℕ → ι → L)
    (law : h → Derivation K L L)
    (characters : ι → h →ₗ[K] K)
    (hshift : ∀ A n i,
      law A (ancestor n i) = characters i A • ancestor (n + 1) i)
    (hancestor : AlgebraicIndependent K
      (fun p : ℕ × ι ↦ ancestor p.1 p.2)) :
    derivationLawDependentSet (K := K) law (ancestor 0) =
      {A | ∃ i, characters i A = 0} := by
  classical
  ext A
  change (¬ DerivationIndependentOver K (law A) (ancestor 0)) ↔ _
  rw [derivationIndependentOver_ancestralShift_iff
    ancestor law characters hshift hancestor A]
  push Not
  rfl

end

end GaloisForLFunctions.HTGeometry
