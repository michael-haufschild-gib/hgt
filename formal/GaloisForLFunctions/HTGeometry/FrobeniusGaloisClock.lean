import GaloisForLFunctions.HTGeometry.ClockProlongationAdjunction

/-!
# The clock instance of the adjoint lattice laws

The adjunction portion of arXiv:2609.09529, Lemma 3.14, applies to
finite differential prolongation and erosion. These are preservation laws
for the existing clock adjunction; they do not assert the stronger
Frobenius compatibility of a residuated lattice.
-/
namespace GaloisForLFunctions.HTGeometry
open scoped Differential
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
  [Algebra F E] [DifferentialAlgebra F E]

/-- Erosion distributes over intersections of observation fields. -/
theorem clockCore_inf (A B : IntermediateField F E) (r : ℕ) :
    clockCore (A ⊓ B) r = clockCore A r ⊓ clockCore B r :=
  (clockGaloisConnection r).u_inf

/-- Prolongation distributes over field composita. -/
theorem clockProlongation_sup (A B : IntermediateField F E) (r : ℕ) :
    clockProlongation (A ⊔ B) r = clockProlongation A r ⊔ clockProlongation B r :=
  (clockGaloisConnection r).l_sup

/-- Arbitrary intersections of field constraints can be eroded componentwise. -/
theorem clockCore_iInf {ι : Sort*} (A : ι → IntermediateField F E) (r : ℕ) :
    clockCore (⨅ i, A i) r = ⨅ i, clockCore (A i) r :=
  (clockGaloisConnection r).u_iInf

/-- Arbitrary source families can be prolonged before taking their compositum. -/
theorem clockProlongation_iSup {ι : Sort*} (A : ι → IntermediateField F E) (r : ℕ) :
    clockProlongation (⨆ i, A i) r = ⨆ i, clockProlongation (A i) r :=
  (clockGaloisConnection r).l_iSup

/-- No clocks are generated from the scalar base field. -/
theorem clockProlongation_bot (r : ℕ) :
    clockProlongation (⊥ : IntermediateField F E) r = ⊥ :=
  (clockGaloisConnection r).l_bot

/-- The full ambient field survives erosion at every finite resolution. -/
theorem clockCore_top (r : ℕ) : clockCore (⊤ : IntermediateField F E) r = ⊤ :=
  (clockGaloisConnection r).u_top

/-- Both composites of the clock adjunction stabilize after one application. -/
theorem clockAdjunction_composites_idempotent (A : IntermediateField F E) (r : ℕ) :
    clockCore (clockProlongation (clockCore (clockProlongation A r) r) r) r =
      clockCore (clockProlongation A r) r ∧
    clockProlongation (clockCore (clockProlongation (clockCore A r) r) r) r =
      clockProlongation (clockCore A r) r := by
  constructor
  · rw [clockCore_clockProlongation_clockCore]
  · rw [clockProlongation_clockCore_clockProlongation]
end
end GaloisForLFunctions.HTGeometry
