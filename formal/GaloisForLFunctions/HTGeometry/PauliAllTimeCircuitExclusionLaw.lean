import GaloisForLFunctions.HTGeometry.PauliReturnExcisedCircuitContinuumLaw

/-!
# Horizon-free circuit exclusion from static commutator incidence

One Gaussian two-local Hamiltonian draw is retained across all real times.
Every circuit return belongs to a single static commutator exception set, so
its Gaussian estimate needs neither a time grid nor an energy-cap tail.
Distinct occupied endpoints and their individual incidence costs are retained.
The resulting tubes are energy-normalized; the estimate does not assert
fixed-error complexity growth or suppression of the weak-centralizer sector.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section


/-- Entry at any real time into a target-specific energy-normalized tube.
The Hamiltonian draw is shared by the time choice and every circuit target. -/
def twoLocalPauliCircuitAllTimeReturnEvent
    {n : ℕ} {C : Type*}
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    Set (TwoLocalPauliCoefficientSpace n) :=
  {x | ∃ t : ℝ, ∃ c : C,
    twoLocalCircuitScaledReturnDistance x t (U c) ^ (2 : ℕ) ≤
      (gaussianIntervalActivationMass / 2) *
        (4 * (2 : ℝ) ^ n *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))}

/-- All possible hitting times use one static commutator exception set.
No time discretization, energy cap, or independence between times is used. -/
theorem twoLocalPauliCircuitAllTimeReturnEvent_subset_commutatorTube
    {n : ℕ} {C : Type*}
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliCircuitAllTimeReturnEvent U ⊆
      ⋃ c, {x |
        ‖twoLocalPauliUnitaryCommutatorMap (U c) x‖ ^ (2 : ℕ) ≤
          (gaussianIntervalActivationMass / 2) *
            (4 * (2 : ℝ) ^ n *
              twoLocalPauliUnitaryAnticommutingIncidenceMass (U c))} := by
  rintro x ⟨t, c, hc⟩
  exact Set.mem_iUnion.mpr ⟨c,
    (norm_twoLocalPauliUnitaryCommutatorMap_sq_le_returnDefect (U c) x t).trans hc⟩

/-- Complete finite-family exclusion for all real times.  A target is charged
once, not once per time sample, including when time is chosen after the draw. -/
theorem stdGaussian_twoLocalPauli_measure_circuitAllTimeReturnEvent_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliCircuitAllTimeReturnEvent U) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)) := by
  exact (measureReal_mono
    (twoLocalPauliCircuitAllTimeReturnEvent_subset_commutatorTube U)
    (measure_ne_top _ _)).trans
      (stdGaussian_twoLocalPauli_measure_iUnion_incidenceCommutatorTube_le U)

/-- All-time entry depends on the occupied endpoint image, not on the number
of circuit descriptions of the same endpoint. -/
theorem twoLocalPauliCircuitAllTimeReturnEvent_eq_occupiedImage
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliCircuitAllTimeReturnEvent U =
      twoLocalPauliCircuitAllTimeReturnEvent
        (twoLocalPauliOccupiedCircuitTarget U) := by
  classical
  ext x
  constructor
  · rintro ⟨t, c, hc⟩
    exact ⟨t, ⟨U c, Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩⟩, hc⟩
  · rintro ⟨t, V, hV⟩
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp V.2
    exact ⟨t, c, by simpa only [twoLocalPauliOccupiedCircuitTarget, hc] using hV⟩

/-- Occupied-image all-time bound, with exact target-specific incidence. -/
theorem stdGaussian_twoLocalPauli_measure_circuitAllTimeReturnEvent_le_occupiedImage
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliCircuitAllTimeReturnEvent U) ≤
      ∑ V : ↥(twoLocalPauliOccupiedCircuitImage U), Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass V.1) := by
  rw [twoLocalPauliCircuitAllTimeReturnEvent_eq_occupiedImage U]
  exact stdGaussian_twoLocalPauli_measure_circuitAllTimeReturnEvent_le
    (twoLocalPauliOccupiedCircuitTarget U)

/-- Return-excised occupied circuit images obey the incidence bound for all
real times, without an energy-cap tail or a polynomial time-grid factor. -/
theorem stdGaussian_twoLocalPauli_measure_returnExcisedCircuitAllTimeReturnEvent_le
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (δ : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliCircuitAllTimeReturnEvent
          (twoLocalPauliReturnExcisedCircuitTarget U δ)) ≤
      (Fintype.card ↥(twoLocalPauliReturnExcisedCircuitImage U δ) : ℝ) *
        Real.exp (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          ((6 * n - 4 : ℕ) : ℝ) * δ) := by
  refine (stdGaussian_twoLocalPauli_measure_circuitAllTimeReturnEvent_le
    (twoLocalPauliReturnExcisedCircuitTarget U δ)).trans ?_
  calc
    ∑ V : ↥(twoLocalPauliReturnExcisedCircuitImage U δ),
        Real.exp (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass V.1) ≤
      ∑ _V : ↥(twoLocalPauliReturnExcisedCircuitImage U δ),
        Real.exp (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          (((6 * n - 4 : ℕ) : ℝ) * δ)) := by
      apply Finset.sum_le_sum
      intro V _
      apply Real.exp_le_exp.mpr
      have hδ := (Finset.mem_filter.mp V.2).2.2
      have hinc :=
        (mul_le_mul_of_nonneg_left hδ
          (show (0 : ℝ) ≤ ((6 * n - 4 : ℕ) : ℝ) by positivity)).trans
            (twoLocalPauliUnitaryAnticommutingIncidenceMass_ge_sixNSubFour_traceDeficit
              V.1)
      exact mul_le_mul_of_nonpos_left hinc (neg_nonpos.mpr (by positivity))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- The former polynomial-window event satisfies the stronger horizon-free
bound for every qubit count. -/
theorem stdGaussian_twoLocalPauli_measure_returnExcisedCircuitPolynomialWindowReturnEvent_le_noGrid
    (k n : ℕ) {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) (δ A : ℝ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliReturnExcisedCircuitPolynomialWindowReturnEvent k n U δ A) ≤
      (Fintype.card ↥(twoLocalPauliReturnExcisedCircuitImage U δ) : ℝ) *
        Real.exp (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          ((6 * n - 4 : ℕ) : ℝ) * δ) := by
  apply le_trans _
    (stdGaussian_twoLocalPauli_measure_returnExcisedCircuitAllTimeReturnEvent_le U δ)
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro x ⟨t, _, hx⟩
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
  refine ⟨t, c.1, hc.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (by linarith only [gaussianIntervalActivationMass_pos] :
      gaussianIntervalActivationMass / 8 ≤ gaussianIntervalActivationMass / 2)
    (mul_nonneg (by positivity)
      (twoLocalPauliUnitaryAnticommutingIncidenceMass_nonneg _))

/-- Entry at any real time into any nonidentity Pauli tube, with its exact
weight-dependent radius. -/
def twoLocalPauliAllPauliAllTimeReturnEvent (n : ℕ) :
    Set (TwoLocalPauliCoefficientSpace n) :=
  {x | ∃ t : ℝ, x ∈ twoLocalPauliAllPauliReturnTubeEvent n t}

/-- Complete Pauli-dictionary entropy compensation holds over the entire
real time axis, with the same bound as at a single fixed time. -/
theorem stdGaussian_twoLocalPauli_measure_allPauliAllTimeReturnEvent_le_binomial
    (n : ℕ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliAllPauliAllTimeReturnEvent n) ≤
      (1 + 3 * Real.exp
        (-2 * (gaussianIntervalActivationMass ^ (2 : ℕ) / 2) * n)) ^ n - 1 := by
  apply le_trans _
    (stdGaussian_twoLocalPauli_measure_iUnion_allPauliCommutatorTube_le_binomial
      (n := n))
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro x ⟨t, hx⟩
  obtain ⟨P, hP⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨P,
    (norm_twoLocalPauliUnitaryCommutatorMap_sq_le_returnDefect
      (finitePauliUnitary P.1) x t).trans hP⟩

/-- One Gaussian two-local draw avoids every nonidentity Pauli tube for all
real times with probability tending to one as the qubit count grows. -/
theorem tendsto_stdGaussian_twoLocalPauli_allPauliAllTimeReturnProbability_atTop :
    Tendsto
      (fun n => (stdGaussian (TwoLocalPauliCoefficientSpace n)).real
        (twoLocalPauliAllPauliAllTimeReturnEvent n)) atTop (nhds 0) := by
  exact squeeze_zero (fun _ => measureReal_nonneg)
    stdGaussian_twoLocalPauli_measure_allPauliAllTimeReturnEvent_le_binomial
    (tendsto_pauliIncidenceCompensatedBinomial_atTop
      (div_pos (sq_pos_of_pos gaussianIntervalActivationMass_pos) (by positivity)))


/-- Every target's anticommuting incidence is bounded by the number of
ordinary two-local Pauli directions, irrespective of circuit complexity. -/
theorem twoLocalPauliUnitaryAnticommutingIncidenceMass_le_localDirections
    {n : ℕ}
    (U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ) :
    twoLocalPauliUnitaryAnticommutingIncidenceMass U ≤
      Fintype.card (boundedLocalPauliLabel n 2) := by
  rw [twoLocalPauliUnitaryAnticommutingIncidenceMass]
  calc
    _ ≤ ∑ _Q : boundedLocalPauliLabel n 2,
        (1 - ‖pauliCoeff
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
          pauliCharacterZero‖ ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro Q _
      rw [← unitary_nonzero_pauliCoeff_mass_eq_traceDeficit U]
      unfold pauliAnticommutingIncidenceMass
      apply Finset.sum_le_sum
      intro P _
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _
    _ ≤ ∑ _Q : boundedLocalPauliLabel n 2, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro Q _
      exact sub_le_self _ (sq_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The static incidence partition function cannot decay faster than its
cardinality times the coefficient-dimension exponential.  This is a lower
bound on the certificate, not on the return probability. -/
theorem card_mul_exp_neg_localDirections_le_incidencePartition
    {n : ℕ} {C : Type*} [Fintype C]
    (U : C → Matrix.unitaryGroup
      (FiniteQubitConfiguration (Fin n)) ℂ) :
    (Fintype.card C : ℝ) * Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          Fintype.card (boundedLocalPauliLabel n 2)) ≤
      ∑ c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          twoLocalPauliUnitaryAnticommutingIncidenceMass (U c)) := by
  calc
    _ = ∑ _c : C, Real.exp
        (-(gaussianIntervalActivationMass ^ (2 : ℕ) / 2) *
          Fintype.card (boundedLocalPauliLabel n 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c _
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
        (twoLocalPauliUnitaryAnticommutingIncidenceMass_le_localDirections (U c))
        (neg_nonpos.mpr (by positivity)))

end

end GaloisForLFunctions.HTGeometry
