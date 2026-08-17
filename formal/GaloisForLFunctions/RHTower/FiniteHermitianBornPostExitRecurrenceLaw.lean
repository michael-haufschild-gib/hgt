import GaloisForLFunctions.RHTower.FiniteHermitianExpectationPostExitRecurrenceLaw
import GaloisForLFunctions.HTGeometry.FiniteQuantumOperationalMemoryLaw
import GaloisForLFunctions.HTGeometry.FiniteBuresKrausDataProcessingLaw

/-!
# Born-probability post-exit recurrence for finite Hermitian dynamics

This module specializes the trace-expectation recurrence law to genuine
density matrices and quantum effects.  Unitary conjugation is proved to
preserve positivity and trace one, and positivity proves that every trace
pairing used below is the real Born probability.  Thus no physicality premise
is left implicit in the final theorem.
-/

open scoped BigOperators ComplexOrder Matrix MatrixOrder
open Matrix

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Schrödinger evolution under a finite Hermitian Hamiltonian preserves the
density-matrix axioms. -/
def finiteHermitianEvolvedDensityMatrix
    {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (t : ℝ) (rho : DensityMatrix d) : DensityMatrix d where
  val := unitaryEvolution H t * rho.1 * star (unitaryEvolution H t)
  property := by
    constructor
    · simpa only [Matrix.star_eq_conjTranspose] using
        rho.property.1.mul_mul_conjTranspose_same (unitaryEvolution H t)
    · have hunitary := unitaryEvolution_mem_unitary hH.isSelfAdjoint t
      have hleft : star (unitaryEvolution H t) * unitaryEvolution H t = 1 :=
        (Unitary.mem_iff.mp hunitary).1
      calc
        (unitaryEvolution H t * rho.1 *
            star (unitaryEvolution H t)).trace =
            (star (unitaryEvolution H t) * unitaryEvolution H t * rho.1).trace :=
          Matrix.trace_mul_cycle _ _ _
        _ = rho.1.trace := by rw [hleft, Matrix.one_mul]
        _ = 1 := rho.property.2

/-- Weighted displacement of a finite family of Born probabilities. -/
def finiteHermitianBornTotalDeviation
    {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    {J : Type*} [Fintype J] (lam : J → ℝ)
    (rho : J → DensityMatrix d) (effect : J → QuantumEffect d)
    (t : ℝ) : ℝ :=
  ∑ a, lam a *
    |quantumProbability (effect a)
        (finiteHermitianEvolvedDensityMatrix hH t (rho a)) -
      quantumProbability (effect a) (rho a)|

/-- For physical states and effects, complex trace deviation is exactly
absolute Born-probability deviation. -/
theorem finiteHermitian_traceExpectationNorm_eq_bornAbs
    {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (rho : DensityMatrix d) (effect : QuantumEffect d) (t : ℝ) :
    ‖(unitaryEvolution H t * rho.1 * star (unitaryEvolution H t) *
          effect.1).trace -
        (rho.1 * effect.1).trace‖ =
      |quantumProbability effect
          (finiteHermitianEvolvedDensityMatrix hH t rho) -
        quantumProbability effect rho| := by
  let rhoT : DensityMatrix d := finiteHermitianEvolvedDensityMatrix hH t rho
  have hevolved :
      unitaryEvolution H t * rho.1 * star (unitaryEvolution H t) = rhoT.1 := by
    rfl
  have htraceT :
      (rhoT.1 * effect.1).trace =
        ((quantumProbability effect rhoT : ℝ) : ℂ) := by
    calc
      (rhoT.1 * effect.1).trace =
          (((rhoT.1 * effect.1).trace.re : ℝ) : ℂ) :=
        finiteMatrix_trace_mul_eq_ofReal_re_of_posSemidef
          rhoT.property.1 effect.property.1
      _ = ((quantumProbability effect rhoT : ℝ) : ℂ) := by
        unfold quantumProbability
        rw [Matrix.trace_mul_comm rhoT.1 effect.1]
  have htrace0 :
      (rho.1 * effect.1).trace =
        ((quantumProbability effect rho : ℝ) : ℂ) := by
    calc
      (rho.1 * effect.1).trace =
          (((rho.1 * effect.1).trace.re : ℝ) : ℂ) :=
        finiteMatrix_trace_mul_eq_ofReal_re_of_posSemidef
          rho.property.1 effect.property.1
      _ = ((quantumProbability effect rho : ℝ) : ℂ) := by
        unfold quantumProbability
        rw [Matrix.trace_mul_comm rho.1 effect.1]
  rw [hevolved, htraceT, htrace0, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]

/-- The physical Born deviation and the matrix trace-expectation deviation
coincide exactly. -/
theorem finiteHermitianBornTotalDeviation_eq_expectation
    {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    {J : Type*} [Fintype J] (lam : J → ℝ)
    (rho : J → DensityMatrix d) (effect : J → QuantumEffect d)
    (t : ℝ) :
    finiteHermitianBornTotalDeviation hH lam rho effect t =
      finiteHermitianQuantumExpectationTotalDeviation hH lam
        (fun a => (rho a).1) (fun a => (effect a).1) t := by
  classical
  unfold finiteHermitianBornTotalDeviation
    finiteHermitianQuantumExpectationTotalDeviation
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  exact (finiteHermitian_traceExpectationNorm_eq_bornAbs
    hH (rho a) (effect a) t).symm

/-- **Finite Hermitian Born escape--return law.** For every finite family of
physical states and effects and every positive target, either every
nonnegative-time Born record stays within the target or a witnessed exit is
followed strictly later by a return.  The deadline is the least certified
graph--resolution clock visible to those state--effect pairs. -/
theorem finiteHermitianBorn_positiveTarget_optimal_neverExits_or_postExit
    {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    {J : Type*} [Fintype J] (lam : J → ℝ)
    (rho : J → DensityMatrix d) (effect : J → QuantumEffect d)
    (hlam : ∀ a, 0 ≤ lam a)
    {ε : ℝ} (hε : 0 < ε)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      finiteHermitianBornTotalDeviation hH lam rho effect t ≤ ε) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧
      n ≤ finiteQuantumExpectationSectorOptimalCertifiedDeadline lam
        (finiteHermitianQuantumExpectationCoefficient hH
          (fun a => (rho a).1) (fun a => (effect a).1)) ε ∧
      ε < finiteHermitianBornTotalDeviation hH lam rho effect exitTime ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (finiteQuantumExpectationSectorOptimalCertifiedDeadline lam
          (finiteHermitianQuantumExpectationCoefficient hH
            (fun a => (rho a).1) (fun a => (effect a).1)) ε : ℝ) *
          (exitTime + guardTime) ∧
      finiteHermitianBornTotalDeviation hH lam rho effect
        ((n : ℝ) * (exitTime + guardTime)) ≤ ε := by
  simpa only [finiteHermitianBornTotalDeviation_eq_expectation] using
    finiteHermitianQuantumExpectation_positiveTarget_optimal_neverExits_or_postExit
      hH lam (fun a => (rho a).1) (fun a => (effect a).1) hlam hε
      guardTime hguard

end RHTower
