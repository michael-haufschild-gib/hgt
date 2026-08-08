import GaloisForLFunctions.HTGeometry.UniversalOperationalMemoryFloor
import Mathlib.Analysis.Matrix.Order

/-!
# Universal operational memory law for finite quantum channels

A finite quantum channel is presented by a normalized Kraus family.  It
maps density matrices to density matrices and pulls quantum effects back to
quantum effects.  Exact trace cyclicity proves Schrödinger--Heisenberg
duality, so the universal operational memory-floor law applies without
unitality, detailed balance, Hilbert--Schmidt contractivity, or closed-system
dynamics.

The distinguishability used here is defined operationally as the supremum
probability gap over all quantum effects.  Thus no auxiliary probe norm
enters the statement.
-/

open Filter
open scoped BigOperators ComplexOrder ENNReal MatrixOrder Topology

noncomputable section

namespace RHTower

/-- Complex square matrices on a `d`-level quantum system. -/
abbrev QuantumMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Finite-dimensional density matrices. -/
def DensityMatrix (d : ℕ) :=
  {ρ : QuantumMatrix d // ρ.PosSemidef ∧ ρ.trace = 1}

/-- Finite-dimensional quantum effects, characterized by `0 ≤ E ≤ 1`. -/
def QuantumEffect (d : ℕ) :=
  {E : QuantumMatrix d // E.PosSemidef ∧ (1 - E).PosSemidef}

/-- The real trace pairing of two positive semidefinite matrices is
nonnegative. -/
theorem re_trace_mul_nonneg_of_posSemidef
    {d : ℕ} {A B : QuantumMatrix d}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨C, hC⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have hBfactor : B = C.conjTranspose * C := by
    simpa only [Matrix.star_eq_conjTranspose] using hC
  have hPSD : (C * A * C.conjTranspose).PosSemidef :=
    hA.mul_mul_conjTranspose_same C
  have htrace : 0 ≤ Matrix.trace (C * A * C.conjTranspose) :=
    hPSD.trace_nonneg
  have hre : 0 ≤ (Matrix.trace (C * A * C.conjTranspose)).re :=
    (RCLike.nonneg_iff.mp htrace).1
  rw [hBfactor]
  have heq :
      Matrix.trace (A * (C.conjTranspose * C)) =
        Matrix.trace (C * A * C.conjTranspose) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [heq]
  exact hre

/-- Born probability of a quantum effect in a density matrix. -/
def quantumProbability {d : ℕ}
    (E : QuantumEffect d) (ρ : DensityMatrix d) : ℝ :=
  (Matrix.trace (E.1 * ρ.1)).re

theorem quantumProbability_nonneg {d : ℕ}
    (E : QuantumEffect d) (ρ : DensityMatrix d) :
    0 ≤ quantumProbability E ρ :=
  re_trace_mul_nonneg_of_posSemidef E.property.1 ρ.property.1

theorem quantumProbability_le_one {d : ℕ}
    (E : QuantumEffect d) (ρ : DensityMatrix d) :
    quantumProbability E ρ ≤ 1 := by
  have hcomp :
      0 ≤ (Matrix.trace (((1 : QuantumMatrix d) - E.1) * ρ.1)).re :=
    re_trace_mul_nonneg_of_posSemidef E.property.2 ρ.property.1
  have htrace : (Matrix.trace ρ.1).re = 1 := by
    rw [ρ.property.2]
    norm_num
  simp only [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re] at hcomp
  dsimp only [quantumProbability]
  linarith

/-- Standard finite quantum theory as an operational theory. -/
def finiteQuantumOperationalTheory (d : ℕ) : OperationalTheory where
  State := DensityMatrix d
  Effect := QuantumEffect d
  probability := quantumProbability
  probability_nonneg := quantumProbability_nonneg
  probability_le_one := quantumProbability_le_one

/-- A finite normalized Kraus family.  This is the operator-sum
presentation of a finite quantum channel. -/
structure FiniteKrausChannel (d k : ℕ) where
  operator : Fin k → QuantumMatrix d
  completeness :
    ∑ a, (operator a).conjTranspose * operator a = 1

/-- Schrödinger action of a Kraus channel on matrices. -/
def FiniteKrausChannel.evolveMatrix {d k : ℕ}
    (Φ : FiniteKrausChannel d k) (ρ : QuantumMatrix d) :
    QuantumMatrix d :=
  ∑ a, Φ.operator a * ρ * (Φ.operator a).conjTranspose

/-- Heisenberg action of a Kraus channel on effect matrices. -/
def FiniteKrausChannel.pullbackMatrix {d k : ℕ}
    (Φ : FiniteKrausChannel d k) (E : QuantumMatrix d) :
    QuantumMatrix d :=
  ∑ a, (Φ.operator a).conjTranspose * E * Φ.operator a

theorem FiniteKrausChannel.evolveMatrix_posSemidef {d k : ℕ}
    (Φ : FiniteKrausChannel d k) {ρ : QuantumMatrix d}
    (hρ : ρ.PosSemidef) :
    (Φ.evolveMatrix ρ).PosSemidef := by
  apply Matrix.posSemidef_sum Finset.univ
  intro a _ha
  exact hρ.mul_mul_conjTranspose_same (Φ.operator a)

theorem FiniteKrausChannel.trace_evolveMatrix {d k : ℕ}
    (Φ : FiniteKrausChannel d k) (ρ : QuantumMatrix d) :
    Matrix.trace (Φ.evolveMatrix ρ) = Matrix.trace ρ := by
  rw [FiniteKrausChannel.evolveMatrix]
  change Matrix.trace
    (∑ a ∈ Finset.univ,
      Φ.operator a * ρ * (Φ.operator a).conjTranspose) =
        Matrix.trace ρ
  rw [Matrix.trace_sum]
  calc
    ∑ a, Matrix.trace
        (Φ.operator a * ρ * (Φ.operator a).conjTranspose) =
        ∑ a, Matrix.trace
          ((Φ.operator a).conjTranspose * Φ.operator a * ρ) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace
        ((∑ a, (Φ.operator a).conjTranspose * Φ.operator a) * ρ) := by
      rw [Finset.sum_mul]
      exact
        (Matrix.trace_sum Finset.univ
          (fun a => (Φ.operator a).conjTranspose * Φ.operator a * ρ)).symm
    _ = Matrix.trace ρ := by
      rw [Φ.completeness, one_mul]

/-- A normalized Kraus family maps density matrices to density matrices. -/
def FiniteKrausChannel.evolve {d k : ℕ}
    (Φ : FiniteKrausChannel d k) (ρ : DensityMatrix d) :
    DensityMatrix d :=
  ⟨Φ.evolveMatrix ρ.1,
    Φ.evolveMatrix_posSemidef ρ.property.1,
    (Φ.trace_evolveMatrix ρ.1).trans ρ.property.2⟩

theorem FiniteKrausChannel.pullbackMatrix_posSemidef {d k : ℕ}
    (Φ : FiniteKrausChannel d k) {E : QuantumMatrix d}
    (hE : E.PosSemidef) :
    (Φ.pullbackMatrix E).PosSemidef := by
  apply Matrix.posSemidef_sum Finset.univ
  intro a _ha
  exact hE.conjTranspose_mul_mul_same (Φ.operator a)

theorem FiniteKrausChannel.one_sub_pullbackMatrix {d k : ℕ}
    (Φ : FiniteKrausChannel d k) (E : QuantumMatrix d) :
    1 - Φ.pullbackMatrix E = Φ.pullbackMatrix (1 - E) := by
  rw [FiniteKrausChannel.pullbackMatrix,
    FiniteKrausChannel.pullbackMatrix]
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
    Finset.sum_sub_distrib]
  rw [Φ.completeness]

/-- A normalized Kraus family pulls quantum effects back to quantum
effects. -/
def FiniteKrausChannel.pullback {d k : ℕ}
    (Φ : FiniteKrausChannel d k) (E : QuantumEffect d) :
    QuantumEffect d :=
  ⟨Φ.pullbackMatrix E.1,
    Φ.pullbackMatrix_posSemidef E.property.1,
    Φ.one_sub_pullbackMatrix E.1 ▸
      Φ.pullbackMatrix_posSemidef E.property.2⟩

/-- Exact Born-probability duality between Schrödinger evolution and
Heisenberg pullback for every normalized Kraus family. -/
theorem FiniteKrausChannel.quantumProbability_after {d k : ℕ}
    (Φ : FiniteKrausChannel d k) (E : QuantumEffect d)
    (ρ : DensityMatrix d) :
    quantumProbability E (Φ.evolve ρ) =
      quantumProbability (Φ.pullback E) ρ := by
  apply congrArg Complex.re
  dsimp only [quantumProbability, FiniteKrausChannel.evolve,
    FiniteKrausChannel.pullback]
  rw [FiniteKrausChannel.evolveMatrix,
    FiniteKrausChannel.pullbackMatrix]
  change Matrix.trace
      (E.1 * ∑ a ∈ Finset.univ,
        Φ.operator a * ρ.1 * (Φ.operator a).conjTranspose) =
    Matrix.trace
      ((∑ a ∈ Finset.univ,
        (Φ.operator a).conjTranspose * E.1 * Φ.operator a) * ρ.1)
  rw [Matrix.mul_sum, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_cycle E.1
      (Φ.operator a * ρ.1) (Φ.operator a).conjTranspose

/-- Every finite normalized Kraus family is an operational channel. -/
def FiniteKrausChannel.toOperationalChannel {d k : ℕ}
    (Φ : FiniteKrausChannel d k) :
    (finiteQuantumOperationalTheory d).Channel where
  evolve := Φ.evolve
  pullback := Φ.pullback
  probability_after := Φ.quantumProbability_after

/-- Every finite Kraus channel has one exact asymptotic operational
distinguishability floor for every pair of initial density matrices. -/
theorem FiniteKrausChannel.tendsto_operationalDistance_memoryFloor
    {d k : ℕ} (Φ : FiniteKrausChannel d k)
    (ρ σ : DensityMatrix d) :
    Tendsto
      (Φ.toOperationalChannel.distanceAt ρ σ) atTop
      (𝓝 (Φ.toOperationalChannel.memoryFloor ρ σ)) :=
  Φ.toOperationalChannel.tendsto_distanceAt_memoryFloor ρ σ

/-- Exact open-quantum dichotomy: every pair is either forgotten
operationally or retains a strictly positive effect-probability distinction
at every future time. -/
theorem FiniteKrausChannel.forgetting_or_persistent_memory
    {d k : ℕ} (Φ : FiniteKrausChannel d k)
    (ρ σ : DensityMatrix d) :
    Tendsto (Φ.toOperationalChannel.distanceAt ρ σ) atTop (𝓝 0) ∨
      ∃ ε : ℝ≥0∞, 0 < ε ∧
        ∀ n, ε ≤ Φ.toOperationalChannel.distanceAt ρ σ n :=
  Φ.toOperationalChannel.forgetting_or_persistent_memory ρ σ

/-- Operational information loss under every finite Kraus channel is
monotone. -/
theorem FiniteKrausChannel.operationalInformationLoss_monotone
    {d k : ℕ} (Φ : FiniteKrausChannel d k)
    (ρ σ : DensityMatrix d) :
    Monotone (Φ.toOperationalChannel.informationLossAt ρ σ) :=
  Φ.toOperationalChannel.informationLossAt_monotone ρ σ

end RHTower
