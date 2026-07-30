import GaloisForLFunctions.HTGeometry.SpectralCharacterDimensionBridgeLaw
import Mathlib.RingTheory.Artinian.Module

/-!
# Finite temporal cascades terminate

For every finite spectral label set, the descending rational relation
filtration is a chain of subspaces in a finite-dimensional vector space.
It therefore stabilizes after one finite order. Integer projective
constraints stabilize at the same order.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The rational spectral-constraint filtration as an increasing map into
the order dual of the submodule lattice. -/
def rationalSpectralConstraintOrderHom
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) :
    ℕ →o
      (Submodule ℚ (ProjectiveRationalCharacter I))ᵒᵈ where
  toFun r := rationalSpectralConstraintSpace jet r
  monotone' := by
    intro r s hrs
    exact rationalSpectralConstraintSpace_antitone jet hrs

/-- **Finite termination of the rational temporal cascade.** Every finite
spectrum has one finite resolution after which no further independent
rational spectral relation can be lost. -/
theorem exists_rationalSpectralConstraintSpace_stabilization
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) :
    ∃ R : ℕ, ∀ s, R ≤ s →
      rationalSpectralConstraintSpace jet s =
        rationalSpectralConstraintSpace jet R := by
  let chain := rationalSpectralConstraintOrderHom jet
  obtain ⟨R, hR⟩ :=
    IsArtinian.monotone_stabilizes chain
  exact ⟨R, fun s hs => (hR s hs).symm⟩

/-- The integral projective-character filtration stabilizes at the same
finite resolution. -/
theorem exists_spectralConstraintFiltration_stabilization
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) :
    ∃ R : ℕ, ∀ s, R ≤ s →
      spectralConstraintFiltration jet s =
        spectralConstraintFiltration jet R := by
  obtain ⟨R, hR⟩ :=
    exists_rationalSpectralConstraintSpace_stabilization jet
  refine ⟨R, fun s hs => ?_⟩
  ext k
  rw [← mem_rationalConstraint_toRational_iff,
    ← mem_rationalConstraint_toRational_iff,
    hR s hs]

/-- At any stabilized layer, membership is equivalent to being an exact
relation at every order. -/
theorem mem_stabilizedConstraint_iff_not_active
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) (R : ℕ)
    (hR : ∀ s, R ≤ s →
      spectralConstraintFiltration jet s =
        spectralConstraintFiltration jet R)
    (k : ProjectiveCharacter I) :
    k ∈ spectralConstraintFiltration jet R ↔
      ¬ SpectralCharacterActive jet k := by
  constructor
  · intro hk hactive
    let b := spectralCharacterBirthOrder jet k hactive
    let s := max R (b + 1)
    have hRs : R ≤ s := le_max_left _ _
    have hks :
        k ∈ spectralConstraintFiltration jet s := by
      rw [hR s hRs]
      exact hk
    exact spectralRelationJet_birthOrder_ne_zero hactive
      (hks b (lt_of_lt_of_le (Nat.lt_succ_self b)
        (le_max_right R (b + 1))))
  · intro hinactive
    exact
      (not_spectralCharacterActive_iff_forall_mem.mp hinactive) R

/-- Temporal dimension of every finite spectrum is eventually constant. -/
theorem exists_temporalDimension_stabilization
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) :
    ∃ R : ℕ, ∀ s, R ≤ s →
      temporalDimension jet s = temporalDimension jet R := by
  obtain ⟨R, hR⟩ :=
    exists_rationalSpectralConstraintSpace_stabilization jet
  refine ⟨R, fun s hs => ?_⟩
  have hr :=
    temporalDimension_add_constraintFinrank jet R
  have hs' :=
    temporalDimension_add_constraintFinrank jet s
  rw [hR s hs] at hs'
  omega

end

end GaloisForLFunctions.HTGeometry
