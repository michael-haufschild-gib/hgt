import GaloisForLFunctions.HTGeometry.FiniteUnitaryHaarMeasureLaw

/-!
# Restricted-control ergotropy in finite dimension

This module formalizes the exact compact-group argument behind Eq. (16) of
Formicola--Di Bello--de Candia--De Filippis--Perroni,
*Discrete time crystals in disordered anisotropic Heisenberg chains*, arXiv:2609.04037.

A compact subgroup models the closure of finite accessible control sequences.  The restricted
ergotropy is the supremum of extractable work over that subgroup.  Compactness makes the supremum
a maximum, and the group inverse of an accessible evolution exactly returns its evolved state to
the initial state.  This gives the paper's energy-gain lower bound without assuming an exact
finite-time return protocol.
-/

open scoped Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Compact subgroup of finite-dimensional unitary controls. -/
structure CompactUnitaryControl
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  subgroup : Subgroup (Matrix.unitaryGroup ι ℂ)
  isCompact : IsCompact (subgroup : Set (Matrix.unitaryGroup ι ℂ))

/-- The full finite-dimensional unitary group as a compact control group. -/
def fullCompactUnitaryControl
    (ι : Type*) [Fintype ι] [DecidableEq ι] : CompactUnitaryControl ι where
  subgroup := ⊤
  isCompact := by
    letI := finiteUnitaryCompactSpace ι
    simpa using (isCompact_univ : IsCompact (Set.univ : Set (Matrix.unitaryGroup ι ℂ)))

/-- Energy expectation represented by the real part of `Tr(Hρ)`. -/
def finiteMatrixEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H ρ : Matrix ι ι ℂ) : ℝ :=
  ((H * ρ).trace).re

/-- Work extracted by conjugating the state with one allowed control. -/
def restrictedControlWork
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ)
    (V : C.subgroup) : ℝ :=
  finiteMatrixEnergy H ρ -
    finiteMatrixEnergy H (V.1.1 * ρ * V.1.1ᴴ)

/-- Work is continuous in the finite-dimensional unitary control. -/
theorem continuous_restrictedControlWork
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ) :
    Continuous (fun V : C.subgroup => restrictedControlWork C H ρ V) := by
  unfold restrictedControlWork finiteMatrixEnergy
  fun_prop

/-- Restricted-control ergotropy as supremum over the compact accessible group. -/
def restrictedControlErgotropy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ) : ℝ :=
  sSup (Set.range fun V : C.subgroup => restrictedControlWork C H ρ V)

/-- Every accessible control gives a lower bound on restricted ergotropy. -/
theorem restrictedControlWork_le_ergotropy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ)
    (V : C.subgroup) :
    restrictedControlWork C H ρ V ≤ restrictedControlErgotropy C H ρ := by
  letI : CompactSpace C.subgroup := isCompact_iff_compactSpace.mp C.isCompact
  apply le_csSup
    (isCompact_range (continuous_restrictedControlWork C H ρ)).bddAbove
  exact ⟨V, rfl⟩

/-- Doing nothing extracts zero work. -/
theorem restrictedControlWork_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ) :
    restrictedControlWork C H ρ (1 : C.subgroup) = 0 := by
  simp [restrictedControlWork]

/-- Restricted-control ergotropy is nonnegative because the identity control is accessible. -/
theorem restrictedControlErgotropy_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ) :
    0 ≤ restrictedControlErgotropy C H ρ := by
  rw [← restrictedControlWork_one C H ρ]
  exact restrictedControlWork_le_ergotropy C H ρ 1

/-- Compactness upgrades the restricted-control supremum to an attained maximum. -/
theorem exists_restrictedControlWork_eq_ergotropy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ) :
    ∃ V : C.subgroup,
      restrictedControlErgotropy C H ρ = restrictedControlWork C H ρ V := by
  letI : CompactSpace C.subgroup := isCompact_iff_compactSpace.mp C.isCompact
  rcases (isCompact_range (continuous_restrictedControlWork C H ρ)).sSup_mem
      (Set.range_nonempty _) with ⟨V, hV⟩
  exact ⟨V, hV.symm⟩

/-- State reached by an accessible unitary. -/
def restrictedControlEvolvedState
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : CompactUnitaryControl ι} (ρ : Matrix ι ι ℂ)
    (U : C.subgroup) : Matrix ι ι ℂ :=
  U.1.1 * ρ * U.1.1ᴴ

/-- Successive accessible evolutions compose in the same compact control subgroup. -/
theorem restrictedControlEvolvedState_comp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : CompactUnitaryControl ι} (ρ : Matrix ι ι ℂ)
    (U V : C.subgroup) :
    restrictedControlEvolvedState (restrictedControlEvolvedState ρ U) V =
      restrictedControlEvolvedState ρ (V * U) := by
  simp [restrictedControlEvolvedState, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

/-- Work from an already evolved state is original-orbit work plus the intervening energy gain. -/
theorem restrictedControlWork_evolvedState
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ)
    (U V : C.subgroup) :
    restrictedControlWork C H (restrictedControlEvolvedState ρ U) V =
    restrictedControlWork C H ρ (V * U) +
        (finiteMatrixEnergy H (restrictedControlEvolvedState ρ U) -
          finiteMatrixEnergy H ρ) := by
  change finiteMatrixEnergy H (restrictedControlEvolvedState ρ U) -
      finiteMatrixEnergy H
        (restrictedControlEvolvedState (restrictedControlEvolvedState ρ U) V) =
    (finiteMatrixEnergy H ρ -
      finiteMatrixEnergy H (restrictedControlEvolvedState ρ (V * U))) +
        (finiteMatrixEnergy H (restrictedControlEvolvedState ρ U) -
          finiteMatrixEnergy H ρ)
  rw [restrictedControlEvolvedState_comp]
  ring

/-- Exact compact-orbit law: accessible evolution shifts restricted ergotropy by exactly its
energy gain. -/
theorem restrictedControlErgotropy_evolvedState
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ)
    (U : C.subgroup) :
    restrictedControlErgotropy C H (restrictedControlEvolvedState ρ U) =
      restrictedControlErgotropy C H ρ +
        (finiteMatrixEnergy H (restrictedControlEvolvedState ρ U) -
          finiteMatrixEnergy H ρ) := by
  rcases exists_restrictedControlWork_eq_ergotropy C H
      (restrictedControlEvolvedState ρ U) with ⟨V, hV⟩
  rcases exists_restrictedControlWork_eq_ergotropy C H ρ with ⟨W, hW⟩
  apply le_antisymm
  · rw [hV, restrictedControlWork_evolvedState]
    linarith [restrictedControlWork_le_ergotropy C H ρ (V * U)]
  · have hcandidate := restrictedControlWork_le_ergotropy C H
        (restrictedControlEvolvedState ρ U) (W * U⁻¹)
    rw [restrictedControlWork_evolvedState] at hcandidate
    simp [mul_assoc] at hcandidate
    rw [hW]
    exact hcandidate

/-- The inverse element in the compact control group exactly recovers the initial state. -/
theorem restrictedControl_inverse_recovers
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : CompactUnitaryControl ι} (ρ : Matrix ι ι ℂ)
    (U : C.subgroup) :
    ((U⁻¹ : C.subgroup).1.1) * restrictedControlEvolvedState ρ U *
        ((U⁻¹ : C.subgroup).1.1)ᴴ = ρ := by
  have hunit : U.1.1ᴴ * U.1.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.1.2
  change U.1.1ᴴ * (U.1.1 * ρ * U.1.1ᴴ) * (U.1.1ᴴ)ᴴ = ρ
  rw [Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc,
    Matrix.mul_assoc (U.1.1 * ρ) U.1.1ᴴ U.1.1,
    hunit, Matrix.mul_one,
    ← Matrix.mul_assoc, hunit, Matrix.one_mul]

/-- Restricted ergotropy dominates energy gained along any accessible unitary evolution. -/
theorem restrictedControlErgotropy_ge_energyGain
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ)
    (U : C.subgroup) :
    finiteMatrixEnergy H (restrictedControlEvolvedState ρ U) -
        finiteMatrixEnergy H ρ ≤
      restrictedControlErgotropy C H (restrictedControlEvolvedState ρ U) := by
  calc
    finiteMatrixEnergy H (restrictedControlEvolvedState ρ U) - finiteMatrixEnergy H ρ =
        restrictedControlWork C H (restrictedControlEvolvedState ρ U) (U⁻¹) := by
      unfold restrictedControlWork
      rw [restrictedControl_inverse_recovers]
    _ ≤ restrictedControlErgotropy C H (restrictedControlEvolvedState ρ U) :=
      restrictedControlWork_le_ergotropy C H _ _

/-- Difference of matrix energies is the real trace pairing with the state difference. -/
theorem finiteMatrixEnergy_sub_eq_trace_stateSub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H ρ σ : Matrix ι ι ℂ) :
    finiteMatrixEnergy H ρ - finiteMatrixEnergy H σ =
      ((H * (ρ - σ)).trace).re := by
  simp [finiteMatrixEnergy, Matrix.mul_sub, Matrix.trace_sub]

/-- Trace form of the paper's restricted-control ergotropy bound. -/
theorem restrictedControlErgotropy_ge_trace_energyGain
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : CompactUnitaryControl ι) (H ρ : Matrix ι ι ℂ)
    (U : C.subgroup) :
    ((H * (restrictedControlEvolvedState ρ U - ρ)).trace).re ≤
      restrictedControlErgotropy C H (restrictedControlEvolvedState ρ U) := by
  rw [← finiteMatrixEnergy_sub_eq_trace_stateSub]
  exact restrictedControlErgotropy_ge_energyGain C H ρ U

end

end GaloisForLFunctions.HTGeometry
