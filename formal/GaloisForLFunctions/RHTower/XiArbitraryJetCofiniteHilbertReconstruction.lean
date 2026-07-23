import GaloisForLFunctions.HTGeometry.ContinuousFiniteSupportTailIndependence
import GaloisForLFunctions.RHTower.XiArbitraryJetHilbertReconstruction

/-!
# Cofinite arbitrary-jet completed-Xi Hilbert reconstruction

Completed Xi is entire, so every selected derivative is continuous.  The continuous finite-support
HTGeometry bridge therefore upgrades ordinary independence of an arbitrary derivative-order
dictionary to independence after every finite deletion of the complex domain.

Since the existing arbitrary-jet theorem classifies ordinary independence and finite Hilbert
reconstruction by injectivity of the derivative-order map, the same collision law now classifies
cofinite positive Grams and cofinite exact reconstruction.  In particular, one finite exact
reconstruction packet exists exactly when such a packet exists after every finite deletion.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Arbitrary completed-Xi derivative dictionaries are independent modulo finite complex support
exactly when their derivative orders are distinct. -/
theorem tailCoefficientIndependent_xiDerivativeOrderFamily_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    TailCoefficientIndependent (xiDerivativeOrderFamily order) ↔
      Function.Injective order := by
  calc
    _ ↔ LinearIndependent ℂ (xiDerivativeOrderFamily order) :=
      tailCoefficientIndependent_iff_linearIndependent_of_continuous
        (xiDerivativeOrderFamily order) (fun j =>
          (differentiable_iteratedDeriv_of_entire
            xi_differentiable (order j)).continuous)
    _ ↔ _ := linearIndependent_xiDerivativeOrderFamily_iff_injective order

/-- For completed-Xi derivative dictionaries, ordinary linear independence is already equivalent
to coefficient independence after every finite complex deletion. -/
theorem linearIndependent_xiDerivativeOrderFamily_iff_tailCoefficientIndependent
    {d : ℕ} (order : Fin d → ℕ) :
    LinearIndependent ℂ (xiDerivativeOrderFamily order) ↔
      TailCoefficientIndependent (xiDerivativeOrderFamily order) := by
  rw [linearIndependent_xiDerivativeOrderFamily_iff_injective,
    tailCoefficientIndependent_xiDerivativeOrderFamily_iff_injective]

/-- Strict square evaluation Grams survive every finite complex deletion exactly when the selected
completed-Xi derivative orders are distinct. -/
theorem xiDerivativeOrderCofiniteEvaluationGram_posDef_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    (∀ F : Set ℂ, F.Finite →
      ∃ points : Fin d → {z : ℂ // z ∉ F},
        (cofiniteEvaluationGram
          (xiDerivativeOrderFamily order) F points).PosDef) ↔
      Function.Injective order := by
  calc
    _ ↔ TailCoefficientIndependent (xiDerivativeOrderFamily order) :=
      (tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram
        (xiDerivativeOrderFamily order)).symm
    _ ↔ _ :=
      tailCoefficientIndependent_xiDerivativeOrderFamily_iff_injective order

/-- After an arbitrary finite complex deletion, every collision-free completed-Xi derivative
dictionary admits distinct surviving samples, exact dual recovery, a strict evaluation Gram, and
positive Hilbert volume. -/
theorem exists_injective_xiDerivativeOrderCofiniteHilbertReconstruction
    {d : ℕ} (order : Fin d → ℕ) (horder : Function.Injective order)
    (F : Set ℂ) (hF : F.Finite) :
    ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * iteratedDeriv (order r) xi (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * iteratedDeriv (order r) xi (points i)) = a q) ∧
      (cofiniteEvaluationGram
        (xiDerivativeOrderFamily order) F points).PosDef ∧
      0 < (cofiniteEvaluationGram
        (xiDerivativeOrderFamily order) F points).det := by
  simpa only [xiDerivativeOrderFamily] using
    exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
      (xiDerivativeOrderFamily order)
      ((tailCoefficientIndependent_xiDerivativeOrderFamily_iff_injective
        order).2 horder)
      F hF

/-- **Cofinite arbitrary-jet completed-Xi reconstruction classification.**  Exact dual recovery,
strict Gram positivity, and positive volume survive every finite complex deletion exactly when the
derivative-order dictionary is injective. -/
theorem xiDerivativeOrderCofiniteHilbertReconstruction_iff_injective
    {d : ℕ} (order : Fin d → ℕ) :
    (∀ F : Set ℂ, F.Finite →
      ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
        Function.Injective points ∧
        (∀ q r, ∑ i, dual q i * iteratedDeriv (order r) xi (points i) =
          if q = r then 1 else 0) ∧
        (∀ (a : Fin d → ℂ) q,
          ∑ i, dual q i *
            (∑ r, a r * iteratedDeriv (order r) xi (points i)) = a q) ∧
        (cofiniteEvaluationGram
          (xiDerivativeOrderFamily order) F points).PosDef ∧
        0 < (cofiniteEvaluationGram
          (xiDerivativeOrderFamily order) F points).det) ↔
      Function.Injective order := by
  change
    CofiniteEvaluationHilbertReconstruction (xiDerivativeOrderFamily order) ↔
      Function.Injective order
  calc
    _ ↔ TailCoefficientIndependent (xiDerivativeOrderFamily order) :=
      cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent
        (xiDerivativeOrderFamily order)
    _ ↔ _ := tailCoefficientIndependent_xiDerivativeOrderFamily_iff_injective order

/-- One finite strict completed-Xi derivative evaluation Gram exists exactly when strict square
Grams can be chosen after every finite deletion. -/
theorem exists_injective_xiDerivativeOrderEvaluationGram_posDef_iff_cofinite
    {d : ℕ} (order : Fin d → ℕ) :
    (∃ points : Fin d → ℂ, Function.Injective points ∧
      (xiDerivativeOrderEvaluationGram order points).PosDef) ↔
    (∀ F : Set ℂ, F.Finite →
      ∃ points : Fin d → {z : ℂ // z ∉ F},
        (cofiniteEvaluationGram
          (xiDerivativeOrderFamily order) F points).PosDef) := by
  calc
    _ ↔ Function.Injective order :=
      exists_injective_xiDerivativeOrderEvaluationGram_posDef_iff order
    _ ↔ _ :=
      (xiDerivativeOrderCofiniteEvaluationGram_posDef_iff_injective order).symm

/-- **Finite/cofinite arbitrary-jet completed-Xi connector.**  One finite exact Hilbert
reconstruction packet exists exactly when exact reconstruction survives every finite deletion of
the complex evaluation domain. -/
theorem exists_injective_xiDerivativeOrderEvaluationHilbertReconstruction_iff_cofinite
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
    (∀ F : Set ℂ, F.Finite →
      ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
        Function.Injective points ∧
        (∀ q r, ∑ i, dual q i * iteratedDeriv (order r) xi (points i) =
          if q = r then 1 else 0) ∧
        (∀ (a : Fin d → ℂ) q,
          ∑ i, dual q i *
            (∑ r, a r * iteratedDeriv (order r) xi (points i)) = a q) ∧
        (cofiniteEvaluationGram
          (xiDerivativeOrderFamily order) F points).PosDef ∧
        0 < (cofiniteEvaluationGram
          (xiDerivativeOrderFamily order) F points).det) := by
  change
    FiniteEvaluationHilbertReconstruction (xiDerivativeOrderFamily order) ↔
      CofiniteEvaluationHilbertReconstruction (xiDerivativeOrderFamily order)
  exact
    finiteEvaluationHilbertReconstruction_iff_cofinite_of_continuous
      (xiDerivativeOrderFamily order)
      (fun j => (differentiable_iteratedDeriv_of_entire
        xi_differentiable (order j)).continuous)

end

end RHTower
