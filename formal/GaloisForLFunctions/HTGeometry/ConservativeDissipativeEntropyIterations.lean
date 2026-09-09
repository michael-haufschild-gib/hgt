import GaloisForLFunctions.HTGeometry.ConservativeDissipativeImplicitEntropy
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-!
# Adaptive implicit entropy trajectories

The Schaffer–Exl energy construction (arXiv:2609.04530) yields actual
positive discrete trajectories with unrestricted time- and state-dependent
transport networks and nonnegative step schedules. Population conservation,
initial extremum bounds, and a global lower bound on relative Boltzmann
energy imply a finite total physical-plus-temporal entropy loss. Finite
energy budgets telescope to an exact limiting entropy and vanishing per-step
loss. No convergence of the state is assumed or asserted here.
-/
open scoped BigOperators NNReal
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Iterated actual implicit transport with arbitrary changes in network and step size. -/
def implicitEntropyOrbit (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) : ℕ → ι → ℝ
  | 0 => x
  | n + 1 => let y := implicitEntropyOrbit a r t x n
    implicitEntropyLog (a n y) r y (t n y)

/-- Physical edge dissipation plus temporal Boltzmann remainder at each actual step. -/
def implicitEntropyOrbitLoss (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) (n : ℕ) : ℝ :=
  let y := implicitEntropyOrbit a r t x n
  let z := implicitEntropyOrbit a r t x (n + 1)
  (t n y : ℝ) * (2 : ℝ)⁻¹ * ∑ i, ∑ j, entropyConductance (a n y) i j *
    entropyProductionValue (Real.exp (z i)) (Real.exp (z j)) + relativeEntropyRemainder r y z

/-- Positive-reference Boltzmann energy has an unconditional finite lower bound. -/
theorem relativeEntropyEnergy_lower_bound (r x : ι → ℝ) :
    -(∑ i, Real.exp (r i)) ≤ relativeEntropyEnergy r x := by
  have h := relativeEntropyEnergy_decomposition r x 0
  have he : relativeEntropyEnergy r 0 = -(∑ i, Real.exp (r i)) := by
    simp [relativeEntropyEnergy, Finset.sum_neg_distrib]
  rw [he] at h
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at h
  linarith [relativeEntropyRemainder_nonneg r x 0]

/-- The full implicit entropy loss is nonnegative for every coefficient schedule. -/
theorem implicitEntropyOrbitLoss_nonneg (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) (n : ℕ) :
    0 ≤ implicitEntropyOrbitLoss a r t x n := by
  unfold implicitEntropyOrbitLoss
  exact add_nonneg (mul_nonneg (mul_nonneg (t n _).coe_nonneg (by positivity))
    (entropyProduction_nonneg _ _)) (relativeEntropyRemainder_nonneg _ _ _)

/-- Exact stepwise entropy conservation after including both physical and temporal loss. -/
theorem implicitEntropyOrbit_step_energy (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) (n : ℕ) :
    relativeEntropyEnergy r (implicitEntropyOrbit a r t x (n + 1)) +
      implicitEntropyOrbitLoss a r t x n = relativeEntropyEnergy r (implicitEntropyOrbit a r t x n) := by
  dsimp only [implicitEntropyOrbitLoss, implicitEntropyOrbit]
  linarith [implicitEntropyLog_energy_balance (a n (implicitEntropyOrbit a r t x n)) r
    (implicitEntropyOrbit a r t x n) (t n (implicitEntropyOrbit a r t x n))]

/-- Exact finite entropy budget for arbitrary nonlinear network adaptation. -/
theorem implicitEntropyOrbit_energy_balance (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) (n : ℕ) :
    relativeEntropyEnergy r (implicitEntropyOrbit a r t x n) +
      ∑ k ∈ Finset.range n, implicitEntropyOrbitLoss a r t x k = relativeEntropyEnergy r x := by
  induction n with
  | zero => simp [implicitEntropyOrbit]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [implicitEntropyOrbit_step_energy a r t x n]

/-- Relative population is conserved along every adaptive implicit trajectory. -/
theorem implicitEntropyOrbit_mass (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) (n : ℕ) :
    ∑ i, Real.exp (r i + implicitEntropyOrbit a r t x n i) = ∑ i, Real.exp (r i + x i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ∑ i, Real.exp (r i + implicitEntropyLog _ r _ _ i) = _
    rw [implicitEntropyLog_mass]
    exact ih

/-- Every logarithmic state remains between extrema of its original input. -/
theorem implicitEntropyOrbit_extrema (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) (n : ℕ) (i : ι) :
    ∃ j k, x j ≤ implicitEntropyOrbit a r t x n i ∧ implicitEntropyOrbit a r t x n i ≤ x k := by
  induction n generalizing i with
  | zero => exact ⟨i, i, le_rfl, le_rfl⟩
  | succ n ih =>
    obtain ⟨j, k, hj, hk⟩ := implicitEntropyLog_extrema
      (a n (implicitEntropyOrbit a r t x n)) r (implicitEntropyOrbit a r t x n)
      (t n (implicitEntropyOrbit a r t x n)) i
    obtain ⟨j₀, _, hj₀, _⟩ := ih j
    obtain ⟨_, k₀, _, hk₀⟩ := ih k
    exact ⟨j₀, k₀, hj₀.trans hj, hk.trans hk₀⟩

/-- Arbitrary state-dependent network changes cannot increase entropy along the actual orbit. -/
theorem implicitEntropyOrbit_energy_antitone (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) :
    Antitone (fun n => relativeEntropyEnergy r (implicitEntropyOrbit a r t x n)) := by
  apply antitone_nat_of_succ_le
  intro n
  linarith [implicitEntropyOrbit_step_energy a r t x n, implicitEntropyOrbitLoss_nonneg a r t x n]

/-- Infinite adaptive evolution has finite total physical-plus-temporal entropy loss. -/
theorem implicitEntropyOrbitLoss_summable (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) : Summable (implicitEntropyOrbitLoss a r t x) := by
  apply summable_of_sum_range_le (fun n => implicitEntropyOrbitLoss_nonneg a r t x n)
    (c := relativeEntropyEnergy r x + ∑ i, Real.exp (r i))
  intro n
  linarith [implicitEntropyOrbit_energy_balance a r t x n,
    relativeEntropyEnergy_lower_bound r (implicitEntropyOrbit a r t x n)]

/-- The initial energy above the universal lower bound limits all future entropy loss. -/
theorem implicitEntropyOrbitLoss_tsum_le (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) :
    ∑' n, implicitEntropyOrbitLoss a r t x n ≤ relativeEntropyEnergy r x + ∑ i, Real.exp (r i) := by
  apply (implicitEntropyOrbitLoss_summable a r t x).tsum_le_of_sum_range_le
  intro n
  linarith [implicitEntropyOrbit_energy_balance a r t x n,
    relativeEntropyEnergy_lower_bound r (implicitEntropyOrbit a r t x n)]

/-- Exact limiting entropy for every unrestricted adaptive implicit trajectory. -/
theorem implicitEntropyOrbit_energy_tendsto (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) :
    Filter.Tendsto (fun n => relativeEntropyEnergy r (implicitEntropyOrbit a r t x n)) Filter.atTop
      (nhds (relativeEntropyEnergy r x - ∑' n, implicitEntropyOrbitLoss a r t x n)) := by
  have h : Filter.Tendsto
      (fun n => relativeEntropyEnergy r x - ∑ k ∈ Finset.range n, implicitEntropyOrbitLoss a r t x k)
      Filter.atTop (nhds (relativeEntropyEnergy r x - ∑' n, implicitEntropyOrbitLoss a r t x n)) :=
    tendsto_const_nhds.sub (implicitEntropyOrbitLoss_summable a r t x).hasSum.tendsto_sum_nat
  convert h using 1
  funext n
  linarith [implicitEntropyOrbit_energy_balance a r t x n]

/-- Physical-plus-temporal entropy loss tends to zero along the actual adaptive orbit. -/
theorem implicitEntropyOrbitLoss_tendsto_zero (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (t : ℕ → (ι → ℝ) → ℝ≥0) (x : ι → ℝ) :
    Filter.Tendsto (implicitEntropyOrbitLoss a r t x) Filter.atTop (nhds 0) :=
  (implicitEntropyOrbitLoss_summable a r t x).tendsto_atTop_zero

end
end GaloisForLFunctions.HTGeometry.SchafferExl
