import GaloisForLFunctions.HTGeometry.CofiniteTailGramPolarization
import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain

/-!
# Cofinite Hilbert reconstruction from coefficient tails

For a finite complex function family on an arbitrary domain, coefficient independence modulo
finite support is exactly the condition that complete square Hilbert reconstruction survives every
finite deletion.  This topology-free phase law packages distinct nodes, exact dual coefficient
recovery, strict Hermitian Gram geometry, and positive volume into one reusable interface.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ComplexOrder

noncomputable section

/-- Complete cofinite complex evaluation phase: every finite deletion leaves a square packet with
distinct nodes, exact dual recovery, a positive-definite Hermitian Gram, and positive volume. -/
def CofiniteEvaluationHilbertReconstruction
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ) : Prop :=
  ∀ F : Set X, F.Finite →
    ∃ (points : J → {x : X // x ∉ F}) (dual : J → J → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * u r (points i) = if q = r then 1 else 0) ∧
      (∀ (a : J → ℂ) q,
        ∑ i, dual q i * (∑ r, a r * u r (points i)) = a q) ∧
      (cofiniteEvaluationGram u F points).PosDef ∧
      0 < (cofiniteEvaluationGram u F points).det

/-- Tail-independent complex functions admit complete Hilbert reconstruction after every finite
deletion, without topology or continuity assumptions. -/
theorem
    exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ)
    (htail : TailCoefficientIndependent u)
    (F : Set X) (hF : F.Finite) :
    ∃ (points : J → {x : X // x ∉ F}) (dual : J → J → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * u r (points i) = if q = r then 1 else 0) ∧
      (∀ (a : J → ℂ) q,
        ∑ i, dual q i * (∑ r, a r * u r (points i)) = a q) ∧
      (cofiniteEvaluationGram u F points).PosDef ∧
      0 < (cofiniteEvaluationGram u F points).det := by
  have hlin := htail.linearIndependent_on_compl u F hF
  simpa only [cofiniteEvaluationGram, cofiniteEvaluationColumn,
    finiteEvaluationGram, finiteEvaluationColumn] using
    exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent
      (fun j => fun x : {x : X // x ∉ F} => u j x) hlin

/-- **Universal cofinite complex Hilbert reconstruction law.** Complete reconstruction survives
every finite deletion exactly when no nonzero coefficient combination has finite support. -/
theorem cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ) :
    CofiniteEvaluationHilbertReconstruction u ↔
      TailCoefficientIndependent u := by
  constructor
  · intro hphase
    apply (tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram u).2
    intro F hF
    obtain ⟨points, _dual, _hinj, _hdelta, _hrecovery, hgram, _hdet⟩ :=
      hphase F hF
    exact ⟨points, hgram⟩
  · intro htail F hF
    exact
      exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
        u htail F hF

/-- Complete reconstruction after every finite deletion always supplies one finite reconstruction
packet.  No topology or continuity is needed for this direction. -/
theorem cofiniteEvaluationHilbertReconstruction_imp_finite
    {J X : Type*} [Fintype J] [DecidableEq J] (u : J → X → ℂ) :
    CofiniteEvaluationHilbertReconstruction u →
      FiniteEvaluationHilbertReconstruction u := by
  intro hcofinite
  apply (finiteEvaluationHilbertReconstruction_iff_linearIndependent u).2
  exact
    ((cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent
      u).1 hcofinite).linearIndependent u

end

end GaloisForLFunctions.HTGeometry
