import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicBaseChange
import GaloisForLFunctions.HTGeometry.CofiniteTailHilbertReconstruction
import GaloisForLFunctions.HTGeometry.UpperEndLiteralTailIndependence
import GaloisForLFunctions.RHTower.XiTransverseShiftPrimeDefectValueReflection
import GaloisForLFunctions.RHTower.XiTransverseValuationCanonicalReconstruction

/-!
# Cofinite Hilbert reconstruction of actual transverse Xi shift defects

The differential pointed-collision law for transverse Xi carriers has a literal analytic
realization.  A finite family of corrected completed-Xi logarithmic-derivative shift defects,
rotated to the upper-end coordinate, remains linearly independent after deleting any finite set
of complex sample points exactly when its integral shifts are distinct and nonzero.

Consequently every such deletion admits distinct surviving nodes, exact dual coefficient
recovery, a positive-definite evaluation Gram, and positive Gram determinant.  This phase is
equivalent both to canonical finite-depth recovery from one prime's valuation coordinates and to
differential independence of the upper-end carriers.  No linear-independence, positivity, tail,
or reconstruction hypothesis remains in the final interfaces.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open Complex Filter
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

local instance xiTransverseDefectReconstructionUpperEndDomain :
    IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiTransverseDefectReconstructionUpperEndComplexAlgebra :
    Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiTransverseDefectReconstructionUpperEndCharZero :
    CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiTransverseDefectReconstructionUpperEndDifferential :
    Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiTransverseDefectReconstructionCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiTransverseDefectReconstructionCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

/-- Literal upper-end rotation of the actual corrected completed-Xi shift defects. -/
def xiTransverseShiftPrimeDefectRotatedFamily
    {d : ℕ} (shift : Fin d → ℕ) : Fin d → ℂ → ℂ :=
  fun i z => xiTransverseShiftPrimeDefect (shift i) (-Complex.I * z)

/-- Differential independence over the rational coordinate field supplies ordinary complex
linear independence of the analytic upper-end representatives. -/
theorem linearIndependent_xiTransverseShiftUpperEndAnalytic_of_injective_ne_zero
    {d : ℕ} (shift : Fin d → ℕ)
    (hinj : Function.Injective shift) (hne : ∀ i, shift i ≠ 0) :
    LinearIndependent ℂ
      (fun i => algebraMap upperEndAnalyticSubring upperEndMeroField
        (finiteAbscissaLSeriesToUpperEndAnalytic
          (xiTransverseShiftFiniteAbscissaSource (shift i)))) := by
  have hdiff :=
    xiTransverseShiftUpperEndCarrier_differentialIndependent
      shift (fun i => Nat.pos_of_ne_zero (hne i)) hinj
  have hdiffC : DifferentialIndependent ℂ
      (fun i => xiTransverseShiftUpperEndCarrier (shift i)) :=
    GaloisForLFunctions.HTGeometry.DifferentialIndependent.restrictScalars hdiff
  have hlinear := hdiffC.algebraicIndependent.linearIndependent
  simpa [xiTransverseShiftUpperEndCarrier,
    finiteAbscissaLSeriesToUpperEndMero_eq_algebraMap] using hlinear

/-- **Literal corrected-Xi independence law.** The actual rotated logarithmic-derivative shift
defects are linearly independent exactly when zero shifts and repeated shifts are absent. -/
theorem linearIndependent_xiTransverseShiftPrimeDefectRotatedFamily_iff
    {d : ℕ} (shift : Fin d → ℕ) :
    LinearIndependent ℂ (xiTransverseShiftPrimeDefectRotatedFamily shift) ↔
      Function.Injective shift ∧ ∀ i, shift i ≠ 0 := by
  constructor
  · intro hlin
    constructor
    · intro i j hij
      apply hlin.injective
      funext z
      simp only [xiTransverseShiftPrimeDefectRotatedFamily, hij]
    · intro i hi
      apply hlin.ne_zero i
      funext z
      simp [xiTransverseShiftPrimeDefectRotatedFamily, hi,
        xiTransverseShiftPrimeDefect, xiTransverseShiftRawLogDerivDefect,
        xiTransverseShiftArchimedeanCorrection]
  · rintro ⟨hinj, hne⟩
    apply linearIndependent_literal_of_upperEndMero
      (xiTransverseShiftPrimeDefectRotatedFamily shift)
      (fun i => finiteAbscissaLSeriesToUpperEndAnalytic
        (xiTransverseShiftFiniteAbscissaSource (shift i)))
    · intro i
      change finiteAbscissaLSeriesToUpperEndGerm
          (xiTransverseShiftFiniteAbscissaSource (shift i)) =
        xiTransverseShiftPrimeDefectUpperEndGerm (shift i)
      exact xiTransverseShiftUpperEndGerm_eq_xiTransverseShiftPrimeDefect (shift i)
    · exact linearIndependent_xiTransverseShiftUpperEndAnalytic_of_injective_ne_zero
        shift hinj hne

/-- **Deletion-robust corrected-Xi independence law.** The literal defect family remains
independent modulo every finite subset of the complex domain exactly off the intrinsic pointed
collision locus of its integral shift labels. -/
theorem tailCoefficientIndependent_xiTransverseShiftPrimeDefectRotatedFamily_iff
    {d : ℕ} (shift : Fin d → ℕ) :
    TailCoefficientIndependent (xiTransverseShiftPrimeDefectRotatedFamily shift) ↔
      Function.Injective shift ∧ ∀ i, shift i ≠ 0 := by
  constructor
  · intro htail
    exact (linearIndependent_xiTransverseShiftPrimeDefectRotatedFamily_iff shift).1
      (htail.linearIndependent (xiTransverseShiftPrimeDefectRotatedFamily shift))
  · rintro ⟨hinj, hne⟩
    apply tailCoefficientIndependent_literal_of_upperEndMero
      (xiTransverseShiftPrimeDefectRotatedFamily shift)
      (fun i => finiteAbscissaLSeriesToUpperEndAnalytic
        (xiTransverseShiftFiniteAbscissaSource (shift i)))
    · intro i
      change finiteAbscissaLSeriesToUpperEndGerm
          (xiTransverseShiftFiniteAbscissaSource (shift i)) =
        xiTransverseShiftPrimeDefectUpperEndGerm (shift i)
      exact xiTransverseShiftUpperEndGerm_eq_xiTransverseShiftPrimeDefect (shift i)
    · exact linearIndependent_xiTransverseShiftUpperEndAnalytic_of_injective_ne_zero
        shift hinj hne

/-- Strict square evaluation Grams survive every finite complex deletion exactly when the shift
labels are distinct and nonzero. -/
theorem xiTransverseShiftPrimeDefectCofiniteEvaluationGram_posDef_iff
    {d : ℕ} (shift : Fin d → ℕ) :
    (∀ F : Set ℂ, F.Finite →
      ∃ points : Fin d → {z : ℂ // z ∉ F},
        (cofiniteEvaluationGram
          (xiTransverseShiftPrimeDefectRotatedFamily shift) F points).PosDef) ↔
      Function.Injective shift ∧ ∀ i, shift i ≠ 0 := by
  calc
    _ ↔ TailCoefficientIndependent
        (xiTransverseShiftPrimeDefectRotatedFamily shift) :=
      (tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram
        (xiTransverseShiftPrimeDefectRotatedFamily shift)).symm
    _ ↔ _ :=
      tailCoefficientIndependent_xiTransverseShiftPrimeDefectRotatedFamily_iff shift

/-- After any finite deletion, a collision-free corrected-Xi defect packet has distinct surviving
nodes, exact dual coefficient recovery, positive-definite Gram, and positive volume. -/
theorem exists_injective_xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction
    {d : ℕ} (shift : Fin d → ℕ)
    (hinj : Function.Injective shift) (hne : ∀ i, shift i ≠ 0)
    (F : Set ℂ) (hF : F.Finite) :
    ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i *
        xiTransverseShiftPrimeDefectRotatedFamily shift r (points i) =
          if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r *
            xiTransverseShiftPrimeDefectRotatedFamily shift r (points i)) = a q) ∧
      (cofiniteEvaluationGram
        (xiTransverseShiftPrimeDefectRotatedFamily shift) F points).PosDef ∧
      0 < (cofiniteEvaluationGram
        (xiTransverseShiftPrimeDefectRotatedFamily shift) F points).det := by
  exact
    exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
      (xiTransverseShiftPrimeDefectRotatedFamily shift)
      ((tailCoefficientIndependent_xiTransverseShiftPrimeDefectRotatedFamily_iff
        shift).2 ⟨hinj, hne⟩) F hF

/-- Exact dual reconstruction, strict Gram positivity, and positive volume survive every finite
complex deletion iff zero and repeated integral shifts are absent. -/
def XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction
    {d : ℕ} (shift : Fin d → ℕ) : Prop :=
  CofiniteEvaluationHilbertReconstruction
    (xiTransverseShiftPrimeDefectRotatedFamily shift)

/-- **Unconditional corrected-Xi reconstruction classification.** The complete cofinite Hilbert
reconstruction phase is exactly the complement of the pointed collision locus. -/
theorem xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff
    {d : ℕ} (shift : Fin d → ℕ) :
    XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction shift ↔
      Function.Injective shift ∧ ∀ i, shift i ≠ 0 := by
  calc
    _ ↔ TailCoefficientIndependent
        (xiTransverseShiftPrimeDefectRotatedFamily shift) :=
      cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent
        (xiTransverseShiftPrimeDefectRotatedFamily shift)
    _ ↔ _ :=
      tailCoefficientIndependent_xiTransverseShiftPrimeDefectRotatedFamily_iff
        shift

/-- Literal cofinite reconstruction of actual corrected-Xi values and canonical reconstruction
from the first valuation coordinates of any one prime have exactly the same strict phase. -/
theorem
    xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
    {d : ℕ} (shift : Fin d → ℕ) (p : Nat.Primes) :
    XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction shift ↔
      XiTransversePrimeValuationCanonicalReconstruction shift p := by
  rw [xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff,
    xiTransversePrimeValuationCanonicalReconstruction_iff_injective_ne_zero]

/-- **Analytic-Hilbert/differential-matroid connector.** Deletion-robust exact recovery from
literal values of the actual corrected completed-Xi defects is equivalent to differential
independence of their upper-end carriers over the rational coordinate field. -/
theorem
    xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_differentialIndependent
    {d : ℕ} (shift : Fin d → ℕ) :
    XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction shift ↔
      DifferentialIndependent upperEndRationalCoordinateField
        (fun i => xiTransverseShiftUpperEndCarrier (shift i)) := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  calc
    _ ↔ XiTransversePrimeValuationCanonicalReconstruction shift p :=
      xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_canonicalValuationReconstruction
        shift p
    _ ↔ _ :=
      (xiTransverseShiftUpperEndCarrier_differentialIndependent_iff_canonicalValuationReconstruction
        shift p).symm

end

end RHTower
