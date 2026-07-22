import Mathlib

/-!
# Exposed coefficient constraint capacity

A finite energy face can carry no more independent coefficient directions than it has source
points.  The theorem is stated for the coefficient evaluation matrix itself, independently of any
choice of positive weights.
-/

open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

/-- The source points lying on one exposed energy level. -/
abbrev FiniteExposedSource
    {P : Type*} (energy : P → ℝ) (radius : ℝ) :=
  {p : P // energy p = radius}

/-- Coefficient evaluation matrix restricted to one exposed source level. -/
def finiteExposedCoefficientMatrix
    {J P : Type*}
    (c : J → P → ℂ) (energy : P → ℝ) (radius : ℝ) :
    Matrix (FiniteExposedSource energy radius) J ℂ :=
  fun p j => c j p.1

/-- Rank of the coefficient geometry visible on an exposed source level. -/
def finiteExposedConstraintRank
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (energy : P → ℝ) (radius : ℝ) : ℕ :=
  (finiteExposedCoefficientMatrix c energy radius).rank

/-- Cardinality of an exposed source level. -/
def finiteExposedSourceCard
    {P : Type*} [Fintype P] (energy : P → ℝ) (radius : ℝ) : ℕ :=
  Fintype.card (FiniteExposedSource energy radius)

/-- The visible coefficient rank is bounded by the number of exposed source points. -/
theorem finiteExposedConstraintRank_le_sourceCard
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (energy : P → ℝ) (radius : ℝ) :
    finiteExposedConstraintRank c energy radius ≤
      finiteExposedSourceCard energy radius := by
  exact Matrix.rank_le_card_height (finiteExposedCoefficientMatrix c energy radius)

/-- The visible coefficient rank is bounded by the number of probes. -/
theorem finiteExposedConstraintRank_le_probeCard
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (energy : P → ℝ) (radius : ℝ) :
    finiteExposedConstraintRank c energy radius ≤ Fintype.card J := by
  exact Matrix.rank_le_card_width (finiteExposedCoefficientMatrix c energy radius)

/-- Linear evaluation of a coefficient packet on one exposed source level. -/
def finiteExposedCoefficientEvaluation
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (energy : P → ℝ) (radius : ℝ) :
    (J → ℂ) →ₗ[ℂ] (FiniteExposedSource energy radius → ℂ) :=
  (finiteExposedCoefficientMatrix c energy radius).mulVecLin

/-- Evaluation on an exposed point is the corresponding coefficient linear form. -/
theorem finiteExposedCoefficientEvaluation_apply
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (energy : P → ℝ) (radius : ℝ)
    (q : J → ℂ) (p : FiniteExposedSource energy radius) :
    finiteExposedCoefficientEvaluation c energy radius q p =
      ∑ j, q j * c j p.1 := by
  simp [finiteExposedCoefficientEvaluation, finiteExposedCoefficientMatrix,
    Matrix.mulVecLin, Matrix.mulVec, dotProduct, mul_comm]

/-- If the exposed coefficient evaluations separate every probe combination, then the exposed
face has at least as many points as there are probes. -/
theorem probeCard_le_finiteExposedSourceCard_of_separating
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (energy : P → ℝ) (radius : ℝ)
    (hseparating : ∀ q : J → ℂ,
      (∀ p, energy p = radius → ∑ j, q j * c j p = 0) → q = 0) :
    Fintype.card J ≤ finiteExposedSourceCard energy radius := by
  have hinjective : Function.Injective
      (finiteExposedCoefficientEvaluation c energy radius) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro q hq
    apply hseparating q
    intro p hp
    have hpzero := congrFun hq (⟨p, hp⟩ : FiniteExposedSource energy radius)
    simpa [finiteExposedCoefficientEvaluation_apply] using hpzero
  have hdim := LinearMap.finrank_le_finrank_of_injective hinjective
  simpa [finiteExposedSourceCard, Module.finrank_fin_fun] using hdim

/-- A one-point exposed face carries at most one independent coefficient direction. -/
theorem finiteExposedConstraintRank_le_one_of_sourceCard_eq_one
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (energy : P → ℝ) (radius : ℝ)
    (hcard : finiteExposedSourceCard energy radius = 1) :
    finiteExposedConstraintRank c energy radius ≤ 1 := by
  simpa [hcard] using finiteExposedConstraintRank_le_sourceCard c energy radius

end

end HTGeometry
