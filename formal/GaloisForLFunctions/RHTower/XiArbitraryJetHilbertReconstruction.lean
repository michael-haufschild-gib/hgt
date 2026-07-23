import GaloisForLFunctions.RHTower.XiJetFreeness

/-!
# Arbitrary finite completed-Xi jet Hilbert reconstruction

The completed-Xi corpus supplies algebraic independence of every derivative function, while the
existing Hilbert reconstruction is stated for initial jet segments. This module removes that
ordering restriction. An arbitrary finite dictionary of derivative orders admits a pairwise
distinct unisolvent sample packet, exact dual recovery, a positive-definite evaluation Gram, and
positive Hilbert volume exactly when no derivative order is repeated.
-/

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder BigOperators

noncomputable section

/-- Completed-Xi derivative functions selected by an arbitrary finite order dictionary. -/
def xiDerivativeOrderFamily {d : ℕ} (order : Fin d → ℕ) :
    Fin d → ℂ → ℂ :=
  fun j => iteratedDeriv (order j) xi

/-- Evaluation Gram of an arbitrary finite completed-Xi derivative-order dictionary. -/
def xiDerivativeOrderEvaluationGram {d : ℕ}
    (order : Fin d → ℕ) (points : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  finiteEvaluationGram (xiDerivativeOrderFamily order) points

/-- Arbitrary selected completed-Xi derivatives are algebraically independent exactly when their
orders are distinct. -/
theorem algebraicIndependent_xiDerivativeOrderFamily_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    AlgebraicIndependent ℂ (xiDerivativeOrderFamily order) ↔
      Function.Injective order := by
  constructor
  · intro h i j hij
    apply h.injective
    simp [xiDerivativeOrderFamily, hij]
  · intro h
    exact algebraicIndependent_xi_iteratedDeriv.comp order h

/-- The same exact collision classification holds at the linear level. -/
theorem linearIndependent_xiDerivativeOrderFamily_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    LinearIndependent ℂ (xiDerivativeOrderFamily order) ↔
      Function.Injective order := by
  constructor
  · intro h i j hij
    apply h.injective
    simp only [xiDerivativeOrderFamily, hij]
  · intro h
    exact
      ((algebraicIndependent_xiDerivativeOrderFamily_iff_injective order).2 h).linearIndependent

/-- **Arbitrary-jet completed-Xi Hilbert reconstruction.** Every collision-free finite dictionary
of derivative orders admits distinct sample points and dual weights giving exact coefficient
recovery, a positive-definite literal evaluation Gram, and positive determinant. -/
theorem exists_injective_xiDerivativeOrderEvaluationHilbertReconstruction
    {d : ℕ} (order : Fin d → ℕ) (horder : Function.Injective order) :
    ∃ (points : Fin d → ℂ) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * iteratedDeriv (order r) xi (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * iteratedDeriv (order r) xi (points i)) = a q) ∧
      (xiDerivativeOrderEvaluationGram order points).PosDef ∧
      0 < (xiDerivativeOrderEvaluationGram order points).det := by
  simpa [xiDerivativeOrderFamily, xiDerivativeOrderEvaluationGram] using
    exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent
      (xiDerivativeOrderFamily order)
      ((linearIndependent_xiDerivativeOrderFamily_iff_injective order).2 horder)

/-- **Exact arbitrary-jet Gram classification.** A positive-definite evaluation realization exists
exactly for a collision-free derivative-order dictionary. -/
theorem exists_injective_xiDerivativeOrderEvaluationGram_posDef_iff
    {d : ℕ} (order : Fin d → ℕ) :
    (∃ points : Fin d → ℂ, Function.Injective points ∧
      (xiDerivativeOrderEvaluationGram order points).PosDef) ↔
      Function.Injective order := by
  constructor
  · rintro ⟨points, _hpoints, hgram⟩
    have hcols : LinearIndependent ℂ
        (finiteEvaluationColumn (xiDerivativeOrderFamily order) points) :=
      Matrix.posDef_gram_iff_linearIndependent.mp hgram
    intro i j hij
    apply hcols.injective
    ext row
    simp [finiteEvaluationColumn, xiDerivativeOrderFamily, hij]
  · intro horder
    obtain ⟨points, _dual, hpoints, _hdelta, _hrecovery, hgram, _hdet⟩ :=
      exists_injective_xiDerivativeOrderEvaluationHilbertReconstruction order horder
    exact ⟨points, hpoints, hgram⟩

/-- Full unisolvent Hilbert reconstruction exists exactly when the derivative-order dictionary is
injective; no separate algebraic-independence or positivity certificate remains in the interface. -/
theorem exists_injective_xiDerivativeOrderEvaluationHilbertReconstruction_iff
    {d : ℕ} (order : Fin d → ℕ) :
    (∃ (points : Fin d → ℂ) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * iteratedDeriv (order r) xi (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * iteratedDeriv (order r) xi (points i)) = a q) ∧
      (xiDerivativeOrderEvaluationGram order points).PosDef ∧
      0 < (xiDerivativeOrderEvaluationGram order points).det) ↔
      Function.Injective order := by
  change
    FiniteEvaluationHilbertReconstruction (xiDerivativeOrderFamily order) ↔
      Function.Injective order
  calc
    _ ↔ LinearIndependent ℂ (xiDerivativeOrderFamily order) :=
      finiteEvaluationHilbertReconstruction_iff_linearIndependent
        (xiDerivativeOrderFamily order)
    _ ↔ _ := linearIndependent_xiDerivativeOrderFamily_iff_injective order

end

end RHTower
