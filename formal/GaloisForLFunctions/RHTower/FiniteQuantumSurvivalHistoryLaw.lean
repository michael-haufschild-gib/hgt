import GaloisForLFunctions.RHTower.FiniteQuantumExpectationGraphRateDistortionLaw

/-!
# Finite quantum survival-history law

A normalized local spectral packet with weights `pᵢ` has survival amplitude
`∑ᵢ pᵢ zᵢ`.  Its survival probability is therefore a scalar expectation
history whose ordered-pair coefficients are exactly `pᵢpⱼ`.

This identity is the algebraic bridge from observer-graph rate--distortion
to local return probabilities.  It does not assume nondegenerate energies,
distinct gaps, or absence of cancellation.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Survival amplitude of a finite normalized spectral-weight packet under
arbitrary vertex phases. -/
def finiteSpectralSurvivalAmplitude
    {d : ℕ} (p : Fin d → ℝ) (z : Fin d → ℂ) : ℂ :=
  ∑ i, (p i : ℂ) * z i

/-- Born survival probability associated with a finite spectral-weight
packet. -/
def finiteSpectralSurvivalProbability
    {d : ℕ} (p : Fin d → ℝ) (z : Fin d → ℂ) : ℝ :=
  Complex.normSq (finiteSpectralSurvivalAmplitude p z)

/-- Survival probability is nonnegative for every spectral packet. -/
theorem finiteSpectralSurvivalProbability_nonneg
    {d : ℕ} (p : Fin d → ℝ) (z : Fin d → ℂ) :
    0 ≤ finiteSpectralSurvivalProbability p z :=
  Complex.normSq_nonneg _

/--
A normalized nonnegative spectral packet evolved by unit phases has survival
probability at most one.
-/
theorem finiteSpectralSurvivalProbability_le_one
    {d : ℕ} (p : Fin d → ℝ) (z : Fin d → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hz : ∀ i, ‖z i‖ = 1) :
    finiteSpectralSurvivalProbability p z ≤ 1 := by
  rw [finiteSpectralSurvivalProbability, Complex.normSq_eq_norm_sq]
  have hnorm :
      ‖finiteSpectralSurvivalAmplitude p z‖ ≤ 1 := by
    calc
      ‖finiteSpectralSurvivalAmplitude p z‖ =
          ‖∑ i, (p i : ℂ) * z i‖ := rfl
      _ ≤ ∑ i, ‖(p i : ℂ) * z i‖ := norm_sum_le _ _
      _ = ∑ i, p i := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hp i), hz i, mul_one]
      _ = 1 := hsum
  nlinarith [norm_nonneg (finiteSpectralSurvivalAmplitude p z)]

/-- Ordered-pair coefficient packet of a survival-probability history. -/
def finiteSpectralSurvivalCoefficient
    {d : ℕ} (p : Fin d → ℝ) :
    Unit → Fin d → Fin d → ℂ :=
  fun _ i j => ((p i * p j : ℝ) : ℂ)

/--
The scalar history with coefficients `pᵢpⱼ` is exactly survival-probability
displacement from the squared total spectral mass.
-/
theorem finiteQuantumExpectationDisplacement_survivalCoefficient
    {d : ℕ} (p : Fin d → ℝ) (z : Fin d → ℂ) :
    finiteQuantumExpectationDisplacement z
        (finiteSpectralSurvivalCoefficient p) () =
      (finiteSpectralSurvivalProbability p z : ℂ) -
        (((∑ i, p i) ^ (2 : ℕ) : ℝ) : ℂ) := by
  classical
  unfold finiteQuantumExpectationDisplacement
    finiteSpectralSurvivalCoefficient
    finiteSpectralSurvivalProbability
    finiteSpectralSurvivalAmplitude
    finiteQuantumObserverPhase
  rw [← Complex.mul_conj]
  simp_rw [map_sum, map_mul, Complex.conj_ofReal]
  push_cast
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hsum :
      (∑ i, (p i : ℂ)) ^ (2 : ℕ) =
        ∑ i, ∑ j, (p i : ℂ) * (p j : ℂ) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
  rw [hsum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [starRingEnd_apply]
  ring

/--
For normalized spectral weights, the same scalar history is exactly the
change of survival probability from its initial value one.
-/
theorem finiteQuantumExpectationDisplacement_survivalCoefficient_normalized
    {d : ℕ} (p : Fin d → ℝ) (z : Fin d → ℂ)
    (hp : ∑ i, p i = 1) :
    finiteQuantumExpectationDisplacement z
        (finiteSpectralSurvivalCoefficient p) () =
      (finiteSpectralSurvivalProbability p z : ℂ) - 1 := by
  rw [finiteQuantumExpectationDisplacement_survivalCoefficient, hp]
  norm_num

/-- Absolute change of a normalized survival probability from one. -/
def finiteSpectralSurvivalDeviation
    {d : ℕ} (p : Fin d → ℝ) (z : Fin d → ℂ) : ℝ :=
  |finiteSpectralSurvivalProbability p z - 1|

/--
For normalized nonnegative weights and unit phases, survival deviation is
exactly loss of survival probability.
-/
theorem finiteSpectralSurvivalDeviation_eq_one_sub
    {d : ℕ} (p : Fin d → ℝ) (z : Fin d → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hz : ∀ i, ‖z i‖ = 1) :
    finiteSpectralSurvivalDeviation p z =
      1 - finiteSpectralSurvivalProbability p z := by
  rw [finiteSpectralSurvivalDeviation,
    abs_of_nonpos (sub_nonpos.mpr
      (finiteSpectralSurvivalProbability_le_one p z hp hsum hz))]
  ring

/--
The scalar rate--distortion metric for a single normalized survival history
is exactly its absolute survival-probability deviation.
-/
theorem finiteQuantumExpectationTotalDeviation_survivalCoefficient_normalized
    {d : ℕ} (p : Fin d → ℝ) (z : Fin d → ℂ)
    (hp : ∑ i, p i = 1) :
    finiteQuantumExpectationTotalDeviation (fun _ : Unit => 1) z
        (finiteSpectralSurvivalCoefficient p) =
      finiteSpectralSurvivalDeviation p z := by
  classical
  unfold finiteQuantumExpectationTotalDeviation
    finiteSpectralSurvivalDeviation
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
  rw [finiteQuantumExpectationDisplacement_survivalCoefficient_normalized p z hp]
  have hcast :
      (finiteSpectralSurvivalProbability p z : ℂ) - 1 =
        ((finiteSpectralSurvivalProbability p z - 1 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]

end RHTower
