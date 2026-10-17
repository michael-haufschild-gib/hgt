import GaloisForLFunctions.RHTower.PrimeBurnolGeneratorMeasure
import GaloisForLFunctions.RHTower.PrimeBurnolJumpEvolution

/-! Complete finite-jump classification of bounded generators on the actual critical-prime space. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ComplexOrder NNReal
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

/-- A natural bounded generator class, with the physical cone and literal prime columns. -/
def BurnolPrimePositiveContractionGenerator
    (A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) : Prop :=
  (∀ p : Nat.Primes, ∃ a : ℂ, A (primeLogCriticalLaplaceFeatureL2 p) =
    a • primeLogCriticalLaplaceFeatureL2 p) ∧
  ∀ t : ℝ, 0 ≤ t → BurnolPreservesNonnegativity (burnolEvolution A t) ∧
    ‖burnolEvolution A t‖ ≤ 1

/-- Every canonical jump datum is realized, including the zero measure and pure killing. -/
theorem BurnolJumpData.generator_admission (D : BurnolJumpData) :
    BurnolPrimePositiveContractionGenerator D.generator := by
  refine ⟨fun p => ⟨(D.rate (Real.log (p : ℝ)) : ℂ), D.generator_prime p⟩, ?_⟩
  intro t ht
  exact ⟨D.evolution_positive ht, D.evolution_contraction ht⟩

/-- **Exact bounded-generator classification.** All positive contractive actual-prime dynamics
have unique finite jump and nonnegative killing coordinates, and every such datum occurs. -/
theorem primeBurnol_positive_contraction_generator_iff_unique_jump
    (A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) :
    BurnolPrimePositiveContractionGenerator A ↔
      ∃! D : BurnolJumpData, A = D.generator := by
  constructor
  · rintro ⟨hline, hflow⟩
    choose a ha using hline
    obtain ⟨D, hD⟩ := primeBurnol_positive_contraction_generator_exists A a ha
      (fun t ht => (hflow t ht).1) (hflow 1 zero_le_one).2
    refine ⟨D, hD, ?_⟩
    intro E hE
    exact BurnolJumpData.generator_injective (hE.symm.trans hD)
  · rintro ⟨D, hD, _⟩
    rw [hD]
    exact D.generator_admission

/-- Within the positive prime-preserving class, contractivity at time one forces it at every time. -/
theorem primeBurnol_positive_generator_contractivity_at_one
    (A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2)
    (hline : ∀ p : Nat.Primes, ∃ a : ℂ, A (primeLogCriticalLaplaceFeatureL2 p) =
      a • primeLogCriticalLaplaceFeatureL2 p)
    (hpos : ∀ t : ℝ, 0 ≤ t → BurnolPreservesNonnegativity (burnolEvolution A t)) :
    (‖burnolEvolution A 1‖ ≤ 1) ↔ ∀ t : ℝ, 0 ≤ t → ‖burnolEvolution A t‖ ≤ 1 := by
  constructor
  · intro h1
    choose a ha using hline
    obtain ⟨D, hD⟩ := primeBurnol_positive_contraction_generator_exists A a ha hpos h1
    rw [hD]
    exact fun _ ht => D.evolution_contraction ht
  · exact fun h => h 1 zero_le_one

/-- A concrete nonzero jump channel, with every measure admission discharged. -/
def burnolUnitJumpData : BurnolJumpData where
  measure := Measure.dirac 1
  finite := inferInstance
  zero_atom := by simp
  killing := 0

lemma burnolUnitJumpData_generator : burnolUnitJumpData.generator = burnolWeightedShift 1 - 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change (∫ h, burnolWeightedShift h f ∂Measure.dirac 1) -
    (((0 : ℝ) + ((Measure.dirac (1 : ℝ≥0)) univ).toReal : ℝ) : ℂ) • f = _
  simp

/-- The literal unit-shift jump generator has a positive contractive evolution of norm one. -/
theorem primeBurnol_unitJump_evolution :
    BurnolPrimePositiveContractionGenerator (burnolWeightedShift 1 - 1) ∧
      ∀ t : ℝ, 0 ≤ t → ‖burnolEvolution (burnolWeightedShift 1 - 1) t‖ = 1 := by
  rw [← burnolUnitJumpData_generator]
  refine ⟨burnolUnitJumpData.generator_admission, fun t ht => ?_⟩
  simpa [burnolUnitJumpData] using burnolUnitJumpData.evolution_norm ht

end RHTower
