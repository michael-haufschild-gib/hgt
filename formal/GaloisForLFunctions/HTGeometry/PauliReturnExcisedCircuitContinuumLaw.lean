import GaloisForLFunctions.HTGeometry.PauliHighIncidenceCircuitContinuumLaw

/-!
# Return-excised occupied-image circuit continuum law

Compress a finite circuit dictionary to its actual unitary endpoint image,
remove the low-incidence carrier and an exact normalized-trace return tube,
and retain the complete surviving endpoint image.  The exact two-local Pauli
incidence law charges every survivor by at least `(6n-4)δ`.  Consequently a
continuous polynomial laboratory window pays one energy-cap tail and the
cardinality of the occupied return-excised image, never circuit-word
multiplicity.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Distinct circuit endpoints surviving both low-incidence excision and the
normalized-trace return tube of deficit `δ`. -/
noncomputable def twoLocalPauliReturnExcisedCircuitImage
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (δ : ℝ) :
    Finset (Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) := by
  classical
  exact (twoLocalPauliOccupiedCircuitImage U).filter fun V =>
    2 / gaussianIntervalActivationMass ≤
        twoLocalPauliUnitaryAnticommutingIncidenceMass V ∧
      δ ≤ 1 - ‖pauliCoeff
        (V : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)
        pauliCharacterZero‖ ^ 2

/-- Inclusion of the return-excised occupied endpoint image. -/
def twoLocalPauliReturnExcisedCircuitTarget
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (δ : ℝ) :
    ↥(twoLocalPauliReturnExcisedCircuitImage U δ) →
      Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ :=
  fun V => V.1

/-- Complete continuous polynomial-window return event to the surviving
occupied circuit image. -/
def twoLocalPauliReturnExcisedCircuitPolynomialWindowReturnEvent
    (k n : ℕ) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (δ A : ℝ) :
    Set (TwoLocalPauliCoefficientSpace n) :=
  twoLocalPauliHighIncidenceCircuitPolynomialWindowReturnEvent k n
    (twoLocalPauliReturnExcisedCircuitTarget U δ) A

/-- **Return-excised occupied-image continuum law.**  For one ordinary static
Gaussian two-local Hamiltonian, complete continuous polynomial-window return
mass to a finite circuit family is controlled by the energy tail and the
number of distinct return-excised endpoints, each charged by the sharp
worst-sector incidence exponent `(6n-4)δ`. -/
theorem stdGaussian_twoLocalPauli_measure_returnExcisedCircuitPolynomialWindowReturnEvent_le
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (δ A : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliReturnExcisedCircuitPolynomialWindowReturnEvent
          k n U δ A) ≤
      (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
          (twoLocalPauliCoefficientBox n)ᶜ +
        (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          (Fintype.card ↥(twoLocalPauliReturnExcisedCircuitImage U δ) : ℝ) *
          Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
            ((6 * n - 4 : ℕ) : ℝ) * δ) := by
  let V := twoLocalPauliReturnExcisedCircuitTarget U δ
  have hbase :=
    stdGaussian_twoLocalPauli_measure_highIncidenceCircuitPolynomialWindowReturnEvent_le
      k hn V A
  rw [twoLocalPauliReturnExcisedCircuitPolynomialWindowReturnEvent]
  have hsum :
      (∑ c : ↥(twoLocalPauliHighIncidenceCircuitTargets V),
          Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
            twoLocalPauliUnitaryAnticommutingIncidenceMass (V c.1))) ≤
        (Fintype.card ↥(twoLocalPauliReturnExcisedCircuitImage U δ) : ℝ) *
          Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
            ((6 * n - 4 : ℕ) : ℝ) * δ) := by
    calc
      ∑ c : ↥(twoLocalPauliHighIncidenceCircuitTargets V),
          Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
            twoLocalPauliUnitaryAnticommutingIncidenceMass (V c.1)) ≤
        ∑ _c : ↥(twoLocalPauliHighIncidenceCircuitTargets V),
          Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
            (((6 * n - 4 : ℕ) : ℝ) * δ)) := by
        apply Finset.sum_le_sum
        intro c _
        apply Real.exp_le_exp.mpr
        have hcδ : δ ≤ 1 - ‖pauliCoeff
            (V c.1 : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)
            pauliCharacterZero‖ ^ 2 := by
          exact (Finset.mem_filter.mp c.1.2).2.2
        have hcoef : (0 : ℝ) ≤ ((6 * n - 4 : ℕ) : ℝ) := by positivity
        have hinc :=
          twoLocalPauliUnitaryAnticommutingIncidenceMass_ge_sixNSubFour_traceDeficit
            (V c.1)
        have hδinc : ((6 * n - 4 : ℕ) : ℝ) * δ ≤
            twoLocalPauliUnitaryAnticommutingIncidenceMass (V c.1) :=
          (mul_le_mul_of_nonneg_left hcδ hcoef).trans hinc
        have ha : 0 < gaussianIntervalActivationMass ^ 2 / 2 := by
          have hg := gaussianIntervalActivationMass_pos
          nlinarith [sq_pos_of_pos hg]
        nlinarith
      _ = (Fintype.card ↥(twoLocalPauliHighIncidenceCircuitTargets V) : ℝ) *
          Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
            ((6 * n - 4 : ℕ) : ℝ) * δ) := by
        simp [mul_assoc]
      _ ≤ (Fintype.card ↥(twoLocalPauliReturnExcisedCircuitImage U δ) : ℝ) *
          Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
            ((6 * n - 4 : ℕ) : ℝ) * δ) := by
        gcongr
        simpa only [Fintype.card_coe] using
          Finset.card_le_univ (twoLocalPauliHighIncidenceCircuitTargets V)
  have hmul :
      (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          (∑ c : ↥(twoLocalPauliHighIncidenceCircuitTargets V),
            Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
              twoLocalPauliUnitaryAnticommutingIncidenceMass (V c.1))) ≤
        (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          (Fintype.card ↥(twoLocalPauliReturnExcisedCircuitImage U δ) : ℝ) *
          Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
            ((6 * n - 4 : ℕ) : ℝ) * δ) := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hP : (0 : ℝ) ≤ 649 * (n : ℝ) ^ (k + 7) :=
      mul_nonneg (by norm_num) (pow_nonneg hn0 _)
    calc
      (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          (∑ c : ↥(twoLocalPauliHighIncidenceCircuitTargets V),
            Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
              twoLocalPauliUnitaryAnticommutingIncidenceMass (V c.1))) ≤
        (649 * (n : ℝ) ^ (k + 7)) *
          ((Fintype.card ↥(twoLocalPauliReturnExcisedCircuitImage U δ) : ℝ) *
            Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
              ((6 * n - 4 : ℕ) : ℝ) * δ)) :=
        mul_le_mul_of_nonneg_left hsum hP
      _ = (649 : ℝ) * (n : ℝ) ^ (k + 7) *
          (Fintype.card ↥(twoLocalPauliReturnExcisedCircuitImage U δ) : ℝ) *
          Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
            ((6 * n - 4 : ℕ) : ℝ) * δ) := by ring
  exact hbase.trans (add_le_add_right hmul _)

end

end GaloisForLFunctions.HTGeometry
