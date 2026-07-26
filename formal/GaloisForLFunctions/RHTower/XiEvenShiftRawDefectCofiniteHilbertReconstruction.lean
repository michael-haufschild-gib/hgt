import GaloisForLFunctions.HTGeometry.CofiniteTailHilbertReconstruction
import GaloisForLFunctions.RHTower.XiEvenShiftRawDefectDifferentialRank
import GaloisForLFunctions.RHTower.XiTransverseShiftDefectCofiniteHilbertReconstruction
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances

/-!
# Cofinite Hilbert reconstruction of raw even-shift Xi defects

The actual uncorrected differences

`logDeriv xi (s + 2m) - logDeriv xi s`

inherit the exact pointed-collision phase of the corrected transverse prime-source carriers.
Existing RHTower results identify these literal values with upper-end analytic representatives and
prove that the rational archimedean correction preserves their differential matroid.  The
HTGeometry upper-end tail bridge and Hilbert evaluation machinery then show that every finite
deletion of the complex sampling domain still permits distinct nodes, exact dual coefficient
recovery, a positive-definite Gram, and positive Gram determinant.

This raw-value reconstruction phase is equivalent to absence of zero or repeated grades, to the
corrected even-shift reconstruction phase, and to raw-carrier differential independence both over
the rational coordinate field and after adjoining all scalar valuation layers.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open Complex Filter
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

open scoped UpperEndDifferentialInstances

/-- Literal upper-end rotation of the actual raw even-shift completed-Xi defects. -/
def xiEvenShiftRawLogDerivDefectRotatedFamily
    {d : ℕ} (grade : Fin d → ℕ) : Fin d → ℂ → ℂ :=
  fun i z => logDeriv xi (-Complex.I * z + (2 * grade i : ℕ)) -
    logDeriv xi (-Complex.I * z)

/-- Full-family specialization of the existing raw pointed-collision differential law. -/
theorem xiEvenShiftRawLogDerivDefectUpperEndCarrier_full_differentialIndependent_iff
    {d : ℕ} (grade : Fin d → ℕ) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) ↔
      Function.Injective grade ∧ ∀ i, grade i ≠ 0 := by
  constructor
  · intro hdiff
    have hsub := hdiff.comp
      (fun i : (Set.univ : Set (Fin d)) => i.1) Subtype.val_injective
    have hcondition :=
      (xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialIndependent_iff
        grade Set.univ).1 hsub
    exact ⟨
      fun i j hij => hcondition.1 (Set.mem_univ i) (Set.mem_univ j) hij,
      fun i => hcondition.2 i (Set.mem_univ i)⟩
  · rintro ⟨hinj, hne⟩
    have hsub :=
      (xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialIndependent_iff
        grade Set.univ).2 ⟨
          fun i _ j _ hij => hinj hij,
          fun i _ => hne i⟩
    exact hsub.comp
      (fun i => ⟨i, Set.mem_univ i⟩)
      (fun _ _ hij => congrArg Subtype.val hij)

/-- The same full raw packet has the identical collision classification after adjoining every
scalar valuation layer. -/
theorem
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_full_differentialIndependent_iff
    {d : ℕ} (grade : Fin d → ℕ) :
    DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) ↔
      Function.Injective grade ∧ ∀ i, grade i ≠ 0 := by
  constructor
  · intro hdiff
    have hsub := hdiff.comp
      (fun i : (Set.univ : Set (Fin d)) => i.1) Subtype.val_injective
    have hcondition :=
      (xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialIndependent_iff
        grade Set.univ).1 hsub
    exact ⟨
      fun i j hij => hcondition.1 (Set.mem_univ i) (Set.mem_univ j) hij,
      fun i => hcondition.2 i (Set.mem_univ i)⟩
  · rintro ⟨hinj, hne⟩
    have hsub :=
      (xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialIndependent_iff
        grade Set.univ).2 ⟨
          fun i _ j _ hij => hinj hij,
          fun i _ => hne i⟩
    exact hsub.comp
      (fun i => ⟨i, Set.mem_univ i⟩)
      (fun _ _ hij => congrArg Subtype.val hij)

/-- Differential independence of raw upper-end carriers supplies ordinary complex linear
independence of their analytic representatives. -/
theorem linearIndependent_xiEvenShiftRawLogDerivDefectUpperEndAnalytic_of_injective_ne_zero
    {d : ℕ} (grade : Fin d → ℕ)
    (hinj : Function.Injective grade) (hne : ∀ i, grade i ≠ 0) :
    LinearIndependent ℂ
      (fun i => algebraMap upperEndAnalyticSubring upperEndMeroField
        (xiEvenShiftRawLogDerivDefectUpperEndAnalytic (grade i))) := by
  have hdiff : DifferentialIndependent upperEndRationalCoordinateField
      (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) :=
    (xiEvenShiftRawLogDerivDefectUpperEndCarrier_full_differentialIndependent_iff
      grade).2 ⟨hinj, hne⟩
  have hdiffC : DifferentialIndependent ℂ
      (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) :=
    GaloisForLFunctions.HTGeometry.DifferentialIndependent.restrictScalars hdiff
  have hlinear := hdiffC.algebraicIndependent.linearIndependent
  simpa only [xiEvenShiftRawLogDerivDefectUpperEndCarrier_eq_algebraMap] using hlinear

/-- **Literal raw-Xi independence law.** Actual uncorrected even-shift logarithmic-derivative
defects are linearly independent exactly when their grades are distinct and nonzero. -/
theorem linearIndependent_xiEvenShiftRawLogDerivDefectRotatedFamily_iff
    {d : ℕ} (grade : Fin d → ℕ) :
    LinearIndependent ℂ (xiEvenShiftRawLogDerivDefectRotatedFamily grade) ↔
      Function.Injective grade ∧ ∀ i, grade i ≠ 0 := by
  constructor
  · intro hlin
    constructor
    · intro i j hij
      apply hlin.injective
      funext z
      simp only [xiEvenShiftRawLogDerivDefectRotatedFamily, hij]
    · intro i hi
      apply hlin.ne_zero i
      funext z
      simp [xiEvenShiftRawLogDerivDefectRotatedFamily, hi]
  · rintro ⟨hinj, hne⟩
    apply linearIndependent_literal_of_upperEndMero
      (xiEvenShiftRawLogDerivDefectRotatedFamily grade)
      (fun i => xiEvenShiftRawLogDerivDefectUpperEndAnalytic (grade i))
    · intro i
      change ((xiEvenShiftRawLogDerivDefectUpperEndAnalytic (grade i) :
          upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
        xiEvenShiftRawLogDerivDefectUpperEndGerm (grade i)
      exact xiEvenShiftRawLogDerivDefectUpperEndCarrier_germ_eq (grade i)
    · exact
        linearIndependent_xiEvenShiftRawLogDerivDefectUpperEndAnalytic_of_injective_ne_zero
          grade hinj hne

/-- **Deletion-robust raw-Xi independence law.** Removing any finite set of complex samples
preserves independence exactly off the zero and collision locus of the even-shift grades. -/
theorem tailCoefficientIndependent_xiEvenShiftRawLogDerivDefectRotatedFamily_iff
    {d : ℕ} (grade : Fin d → ℕ) :
    TailCoefficientIndependent (xiEvenShiftRawLogDerivDefectRotatedFamily grade) ↔
      Function.Injective grade ∧ ∀ i, grade i ≠ 0 := by
  constructor
  · intro htail
    exact (linearIndependent_xiEvenShiftRawLogDerivDefectRotatedFamily_iff grade).1
      (htail.linearIndependent (xiEvenShiftRawLogDerivDefectRotatedFamily grade))
  · rintro ⟨hinj, hne⟩
    apply tailCoefficientIndependent_literal_of_upperEndMero
      (xiEvenShiftRawLogDerivDefectRotatedFamily grade)
      (fun i => xiEvenShiftRawLogDerivDefectUpperEndAnalytic (grade i))
    · intro i
      change ((xiEvenShiftRawLogDerivDefectUpperEndAnalytic (grade i) :
          upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
        xiEvenShiftRawLogDerivDefectUpperEndGerm (grade i)
      exact xiEvenShiftRawLogDerivDefectUpperEndCarrier_germ_eq (grade i)
    · exact
        linearIndependent_xiEvenShiftRawLogDerivDefectUpperEndAnalytic_of_injective_ne_zero
          grade hinj hne

/-- Strict square evaluation Grams for actual raw Xi defects survive every finite complex
deletion exactly when all grades are distinct and positive. -/
theorem xiEvenShiftRawLogDerivDefectCofiniteEvaluationGram_posDef_iff
    {d : ℕ} (grade : Fin d → ℕ) :
    (∀ F : Set ℂ, F.Finite →
      ∃ points : Fin d → {z : ℂ // z ∉ F},
        (cofiniteEvaluationGram
          (xiEvenShiftRawLogDerivDefectRotatedFamily grade) F points).PosDef) ↔
      Function.Injective grade ∧ ∀ i, grade i ≠ 0 := by
  calc
    _ ↔ TailCoefficientIndependent
        (xiEvenShiftRawLogDerivDefectRotatedFamily grade) :=
      (tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram
        (xiEvenShiftRawLogDerivDefectRotatedFamily grade)).symm
    _ ↔ _ :=
      tailCoefficientIndependent_xiEvenShiftRawLogDerivDefectRotatedFamily_iff grade

/-- After any finite deletion, a collision-free raw Xi packet has distinct surviving nodes,
exact dual coefficient recovery, a positive-definite Gram, and positive volume. -/
theorem exists_injective_xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction
    {d : ℕ} (grade : Fin d → ℕ)
    (hinj : Function.Injective grade) (hne : ∀ i, grade i ≠ 0)
    (F : Set ℂ) (hF : F.Finite) :
    ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
        xiEvenShiftRawLogDerivDefectRotatedFamily grade r (points i) =
          if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiEvenShiftRawLogDerivDefectRotatedFamily grade r (points i)) = a q) ∧
      (cofiniteEvaluationGram
        (xiEvenShiftRawLogDerivDefectRotatedFamily grade) F points).PosDef ∧
      0 < (cofiniteEvaluationGram
        (xiEvenShiftRawLogDerivDefectRotatedFamily grade) F points).det := by
  exact
    exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
      (xiEvenShiftRawLogDerivDefectRotatedFamily grade)
      ((tailCoefficientIndependent_xiEvenShiftRawLogDerivDefectRotatedFamily_iff
        grade).2 ⟨hinj, hne⟩) F hF

/-- Complete cofinite Hilbert reconstruction phase for actual raw even-shift Xi defects. -/
def XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction
    {d : ℕ} (grade : Fin d → ℕ) : Prop :=
  CofiniteEvaluationHilbertReconstruction
    (xiEvenShiftRawLogDerivDefectRotatedFamily grade)

/-- **Unconditional raw-Xi reconstruction classification.** The complete cofinite Hilbert phase
is exactly the complement of the pointed collision locus. -/
theorem xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff
    {d : ℕ} (grade : Fin d → ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      Function.Injective grade ∧ ∀ i, grade i ≠ 0 := by
  calc
    _ ↔ TailCoefficientIndependent
        (xiEvenShiftRawLogDerivDefectRotatedFamily grade) :=
      cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent
        (xiEvenShiftRawLogDerivDefectRotatedFamily grade)
    _ ↔ _ :=
      tailCoefficientIndependent_xiEvenShiftRawLogDerivDefectRotatedFamily_iff
        grade

/-- Doubling all grades preserves exactly the zero/collision phase. -/
theorem injective_two_mul_and_ne_zero_iff
    {d : ℕ} (grade : Fin d → ℕ) :
    (Function.Injective (fun i => 2 * grade i) ∧ ∀ i, 2 * grade i ≠ 0) ↔
      Function.Injective grade ∧ ∀ i, grade i ≠ 0 := by
  constructor
  · rintro ⟨hinj, hne⟩
    exact ⟨
      fun i j hij => hinj (congrArg (fun n => 2 * n) hij),
      fun i hi => hne i (by simp [hi])⟩
  · rintro ⟨hinj, hne⟩
    constructor
    · intro i j hij
      exact hinj (Nat.mul_left_cancel (Nat.zero_lt_succ 1) hij)
    · intro i hi
      apply hne i
      exact (mul_eq_zero.mp hi).resolve_left (Nat.succ_ne_zero 1)

/-- **Raw/corrected Hilbert-phase invariance.** The rational archimedean correction changes
literal values but not deletion-robust exact recoverability of the corresponding even shifts. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedEvenShiftReconstruction
    {d : ℕ} (grade : Fin d → ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction
        (fun i => 2 * grade i) := by
  rw [xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff,
    xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff,
    injective_two_mul_and_ne_zero_iff]

/-- Raw literal cofinite recovery is equivalent to canonical finite-depth valuation recovery for
the corresponding corrected even shifts at any prime. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
    {d : ℕ} (grade : Fin d → ℕ) (p : Nat.Primes) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      XiTransversePrimeValuationCanonicalReconstruction (fun i => 2 * grade i) p := by
  calc
    _ ↔ XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction
        (fun i => 2 * grade i) :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedEvenShiftReconstruction
        grade
    _ ↔ _ :=
      xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
        (fun i => 2 * grade i) p

/-- Raw literal cofinite Hilbert recovery is equivalent to differential independence of the raw
upper-end carriers over the rational coordinate field. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_differentialIndependent
    {d : ℕ} (grade : Fin d → ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      DifferentialIndependent upperEndRationalCoordinateField
        (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) := by
  rw [xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_full_differentialIndependent_iff]

/-- The same literal Hilbert phase detects raw-carrier differential independence after adjoining
all scalar valuation layers. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_allValuation_differentialIndependent
    {d : ℕ} (grade : Fin d → ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      DifferentialIndependent analyticScalarValuationLayerDifferentialField
        (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) := by
  rw [xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff,
    xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_full_differentialIndependent_iff]

/-- **Universal raw-Xi Hilbert phase law.** One unconditional interface simultaneously supplies
corrected even-shift reconstruction and raw differential independence over both coefficient
fields. -/
theorem xiEvenShiftRawLogDerivDefectCofiniteHilbertPhase_iff
    {d : ℕ} (grade : Fin d → ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction
          (fun i => 2 * grade i) ∧
        DifferentialIndependent upperEndRationalCoordinateField
          (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) ∧
        DifferentialIndependent analyticScalarValuationLayerDifferentialField
          (fun i => xiEvenShiftRawLogDerivDefectUpperEndCarrier (grade i)) := by
  constructor
  · intro hraw
    exact ⟨
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedEvenShiftReconstruction
        grade).1 hraw,
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_differentialIndependent
        grade).1 hraw,
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_allValuation_differentialIndependent
        grade).1 hraw⟩
  · rintro ⟨hcorrected, _hrational, _hallValuation⟩
    exact
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedEvenShiftReconstruction
        grade).2 hcorrected

end

end RHTower
