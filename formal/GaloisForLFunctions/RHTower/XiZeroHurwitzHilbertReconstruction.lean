import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import GaloisForLFunctions.HTGeometry.UpperEndConstantField
import GaloisForLFunctions.HTGeometry.UpperEndLiteralLinearIndependence
import GaloisForLFunctions.RHTower.XiZeroHurwitzDifferentialIndependence

/-!
# Literal Hilbert reconstruction of Xi-zero-indexed Hurwitz families

Xi-zero-indexed continued Hurwitz carriers are already known to be differentially independent in
the upper-end meromorphic field.  This module transports that theorem back to the literal
continued functions: a global linear relation would induce the same relation among analytic germs
and hence among their meromorphic images.

The general finite evaluation theorem then gives pairwise distinct complex sample points, exact
dual coefficient recovery, a positive-definite evaluation Gram, and positive Hilbert volume.  The
construction exists exactly when the selected Xi-divisor support points have no repetitions.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open Complex Filter
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HurwitzJointLadder HurwitzZetaContinuation

noncomputable section

local instance xiZeroHurwitzHilbertUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiZeroHurwitzHilbertUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiZeroHurwitzHilbertUpperEndRatfuncAlgebra :
    Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance xiZeroHurwitzHilbertUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- Literal continued Hurwitz functions indexed by a finite Xi-divisor packet. -/
def xiZeroHurwitzFunction {N : ℕ} (ρ : Fin N → XiDivisorSupport) :
    Fin N → ℂ → ℂ :=
  fun i => continuedHzeta ((ρ i : XiDivisorSupport) : ℂ)

/-- Evaluation Gram of a finite Xi-zero-indexed continued Hurwitz family. -/
def xiZeroHurwitzEvaluationGram {N : ℕ} (ρ : Fin N → XiDivisorSupport)
    (points : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  finiteEvaluationGram (xiZeroHurwitzFunction ρ) points

/-- Distinct Xi-divisor support points index linearly independent literal continued Hurwitz
functions, not merely independent abstract meromorphic germs. -/
theorem linearIndependent_xiZeroHurwitzFunction
    {N : ℕ} (ρ : Fin N → XiDivisorSupport) (hρ : Function.Injective ρ) :
    LinearIndependent ℂ (xiZeroHurwitzFunction ρ) := by
  classical
  have hmeroDI : DifferentialIndependent ℂ
      (fun i => continuedHzetaUpperEndMero
        ((ρ i : XiDivisorSupport) : ℂ)) :=
    differentialIndependent_upperEnd_restrictComplex _
      (xi_zero_hurwitz_differentialIndependent ρ hρ)
  have hmeroLI : LinearIndependent ℂ
      (fun i => continuedHzetaUpperEndMero
        ((ρ i : XiDivisorSupport) : ℂ)) :=
    hmeroDI.algebraicIndependent.linearIndependent
  apply linearIndependent_literal_of_upperEndMero
    (xiZeroHurwitzFunction ρ)
    (fun i => continuedHzetaUpperEndAnalytic
      ((ρ i : XiDivisorSupport) : ℂ))
  · intro i
    rfl
  · simpa [continuedHzetaUpperEndMero] using hmeroLI

/-- **Xi-zero Hurwitz Hilbert reconstruction.**  Every finite injective Xi-divisor packet admits
distinct complex sampling points and dual weights which isolate every continued Hurwitz function,
recover every coefficient vector, and carry a strict evaluation Gram with positive volume. -/
theorem exists_injective_xiZeroHurwitzEvaluationHilbertReconstruction
    {N : ℕ} (ρ : Fin N → XiDivisorSupport) (hρ : Function.Injective ρ) :
    ∃ (points : Fin N → ℂ) (dual : Fin N → Fin N → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiZeroHurwitzFunction ρ r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin N → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiZeroHurwitzFunction ρ r (points i)) = a q) ∧
      (xiZeroHurwitzEvaluationGram ρ points).PosDef ∧
      0 < (xiZeroHurwitzEvaluationGram ρ points).det := by
  simpa [xiZeroHurwitzEvaluationGram] using
    exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent
      (xiZeroHurwitzFunction ρ)
      (linearIndependent_xiZeroHurwitzFunction ρ hρ)

/-- A positive-definite literal evaluation realization exists exactly when the Xi-divisor packet
has no repeated support point. -/
theorem exists_injective_xiZeroHurwitzEvaluationGram_posDef_iff
    {N : ℕ} (ρ : Fin N → XiDivisorSupport) :
    (∃ points : Fin N → ℂ, Function.Injective points ∧
      (xiZeroHurwitzEvaluationGram ρ points).PosDef) ↔
      Function.Injective ρ := by
  constructor
  · rintro ⟨points, _hpoints, hgram⟩
    have hcols : LinearIndependent ℂ
        (finiteEvaluationColumn (xiZeroHurwitzFunction ρ) points) :=
      Matrix.posDef_gram_iff_linearIndependent.mp hgram
    intro i j hij
    apply hcols.injective
    ext row
    simp [finiteEvaluationColumn, xiZeroHurwitzFunction, hij]
  · intro hρ
    obtain ⟨points, _dual, hpoints, _hdelta, _hrecovery, hgram, _hdet⟩ :=
      exists_injective_xiZeroHurwitzEvaluationHilbertReconstruction ρ hρ
    exact ⟨points, hpoints, hgram⟩

/-- Full dual reconstruction, strict Gram positivity, and positive volume exist exactly for an
injective Xi-divisor packet; no differential-independence hypothesis remains in the interface. -/
theorem exists_injective_xiZeroHurwitzEvaluationHilbertReconstruction_iff
    {N : ℕ} (ρ : Fin N → XiDivisorSupport) :
    (∃ (points : Fin N → ℂ) (dual : Fin N → Fin N → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiZeroHurwitzFunction ρ r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin N → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiZeroHurwitzFunction ρ r (points i)) = a q) ∧
      (xiZeroHurwitzEvaluationGram ρ points).PosDef ∧
      0 < (xiZeroHurwitzEvaluationGram ρ points).det) ↔
      Function.Injective ρ := by
  constructor
  · rintro ⟨points, _dual, hpoints, _hdelta, _hrecovery, hgram, _hdet⟩
    exact (exists_injective_xiZeroHurwitzEvaluationGram_posDef_iff ρ).1
      ⟨points, hpoints, hgram⟩
  · exact exists_injective_xiZeroHurwitzEvaluationHilbertReconstruction ρ

end

end RHTower
