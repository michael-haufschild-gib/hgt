import GaloisForLFunctions.HTGeometry.UpperEndLiteralTailIndependence
import GaloisForLFunctions.HTGeometry.CofiniteTailHilbertReconstruction
import GaloisForLFunctions.RHTower.XiZeroHurwitzJetHilbertReconstruction

/-!
# Cofinite Xi-zero Hurwitz jet Hilbert reconstruction

Upper-end independence rules out more than global literal relations: a nonzero coefficient
combination cannot be supported on finitely many complex points.  For an arbitrary finite
Xi-zero Hurwitz jet dictionary, this tail property is equivalent to absence of collisions in the
intrinsic `(support point, derivative order)` labels.

Therefore every finite deletion of the complex sampling domain still admits pairwise distinct
sample points, exact dual coefficient recovery, a positive-definite evaluation Gram, and positive
volume.  The collision-free label condition is also necessary, giving an exact unconditional
classification rather than a tail-independence or Gram hypothesis.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open Complex Filter
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HurwitzJointLadder

noncomputable section

local instance xiZeroHurwitzJetCofiniteUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiZeroHurwitzJetCofiniteUpperEndComplexAlgebra :
    Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

/-- **Exact Xi-zero Hurwitz jet tail law.** A finite literal jet dictionary remains independent
after every finite deletion of the complex evaluation domain exactly when its intrinsic
support/order labels do not collide. -/
theorem tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    TailCoefficientIndependent (xiZeroHurwitzJetFamily ρ order) ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  constructor
  · intro htail
    exact (linearIndependent_xiZeroHurwitzJetFamily_iff_injective ρ order).1
      (htail.linearIndependent (xiZeroHurwitzJetFamily ρ order))
  · intro hindex
    apply tailCoefficientIndependent_literal_of_upperEndMero
      (xiZeroHurwitzJetFamily ρ order)
      (fun i => continuedHzetaUpperEndAnalyticJet
        ((ρ i : XiDivisorSupport) : ℂ) (order i))
    · intro i
      rfl
    · exact
        (linearIndependent_xiZeroHurwitzJetUpperEndAnalytic_iff_injective
          ρ order).2 hindex

/-- Strict square evaluation Grams exist after every finite complex deletion exactly when the
selected Xi-zero Hurwitz support/order labels are collision-free. -/
theorem xiZeroHurwitzJetCofiniteEvaluationGram_posDef_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∀ F : Set ℂ, F.Finite →
      ∃ points : Fin d → {z : ℂ // z ∉ F},
        (cofiniteEvaluationGram (xiZeroHurwitzJetFamily ρ order) F points).PosDef) ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  calc
    _ ↔ TailCoefficientIndependent (xiZeroHurwitzJetFamily ρ order) :=
      (tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram
        (xiZeroHurwitzJetFamily ρ order)).symm
    _ ↔ _ :=
      tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_injective ρ order

/-- After an arbitrary finite deletion, every collision-free Xi-zero Hurwitz jet dictionary has
pairwise distinct surviving samples with exact dual reconstruction and a strict Hilbert Gram. -/
theorem exists_injective_xiZeroHurwitzJetCofiniteHilbertReconstruction
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (hindex : Function.Injective (xiZeroHurwitzJetIndex ρ order))
    (F : Set ℂ) (hF : F.Finite) :
    ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetFamily ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiZeroHurwitzJetFamily ρ order r (points i)) = a q) ∧
      (cofiniteEvaluationGram
        (xiZeroHurwitzJetFamily ρ order) F points).PosDef ∧
      0 < (cofiniteEvaluationGram
        (xiZeroHurwitzJetFamily ρ order) F points).det := by
  exact
    exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
      (xiZeroHurwitzJetFamily ρ order)
      ((tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_injective
        ρ order).2 hindex) F hF

/-- **Cofinite Xi-zero Hurwitz jet reconstruction classification.** Exact dual reconstruction,
strict Gram positivity, and positive volume survive every finite complex deletion iff the finite
support/order dictionary is collision-free. No tail-independence, differential-independence, or
positivity hypothesis remains in the interface. -/
theorem xiZeroHurwitzJetCofiniteHilbertReconstruction_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∀ F : Set ℂ, F.Finite →
      ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
        Function.Injective points ∧
        (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetFamily ρ order r (points i) =
          if q = r then 1 else 0) ∧
        (∀ (a : Fin d → ℂ) q,
          ∑ i, dual q i *
            (∑ r, a r * xiZeroHurwitzJetFamily ρ order r (points i)) = a q) ∧
        (cofiniteEvaluationGram
          (xiZeroHurwitzJetFamily ρ order) F points).PosDef ∧
        0 < (cofiniteEvaluationGram
          (xiZeroHurwitzJetFamily ρ order) F points).det) ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  change
    CofiniteEvaluationHilbertReconstruction
      (xiZeroHurwitzJetFamily ρ order) ↔
        Function.Injective (xiZeroHurwitzJetIndex ρ order)
  calc
    _ ↔ TailCoefficientIndependent (xiZeroHurwitzJetFamily ρ order) :=
      cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent
        (xiZeroHurwitzJetFamily ρ order)
    _ ↔ _ :=
      tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_injective ρ order

end

end RHTower
