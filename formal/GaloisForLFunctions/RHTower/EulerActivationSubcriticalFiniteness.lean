import GaloisForLFunctions.RHTower.EulerActivationSubcriticalOccupancy
import GaloisForLFunctions.RHTower.EulerActivationSquarefreeProbability

/-!
# Above the Euler edge the source is an honest random finite integer

The occupancy probabilities of the diagonal activation law are summable above the Euler edge, so
the first Borel--Cantelli lemma puts full mass on the configurations with only finitely many
occupied primes.  The source there is a random finite integer, and its radical is a finite
squarefree number.

This is the exact complement of the critical statement: at the Euler edge the same Kolmogorov
product is supported on configurations occupying infinitely many primes, so the finite-integer
carrier disappears precisely at the edge.
-/

open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

/-! ### The subcritical product law -/

/-- Subcritical Euler parameter `q_p = p ^ (-σ)`. -/
def subcriticalEulerParameter {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) : unitInterval :=
  ⟨((p : ℕ) : ℝ) ^ (-σ), by
    have hp : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    refine ⟨Real.rpow_nonneg (by linarith) _, ?_⟩
    exact Real.rpow_le_one_of_one_le_of_nonpos hp (by linarith)⟩

theorem subcriticalEulerParameter_coe {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) :
    (subcriticalEulerParameter hσ p : ℝ) = ((p : ℕ) : ℝ) ^ (-σ) := rfl

/-- Kolmogorov product of the subcritical local activation laws. -/
def subcriticalEulerProductMeasure {σ : ℝ} (hσ : 1 < σ) :
    MeasureTheory.Measure CriticalEulerConfiguration :=
  MeasureTheory.Measure.infinitePi fun p : Nat.Primes ↦
    diagonalActivationMeasure (subcriticalEulerParameter hσ p)

instance subcriticalEulerProductMeasure_isProbabilityMeasure {σ : ℝ} (hσ : 1 < σ) :
    MeasureTheory.IsProbabilityMeasure (subcriticalEulerProductMeasure hσ) := by
  rw [subcriticalEulerProductMeasure]
  infer_instance

/-! ### Occupancy masses -/

set_option maxHeartbeats 1000000 in
/-- The subcritical occupancy cylinder mass. -/
theorem subcriticalEulerProductMeasure_criticalPrimeOccupied {σ : ℝ} (hσ : 1 < σ)
    (p : Nat.Primes) :
    subcriticalEulerProductMeasure hσ (criticalPrimeOccupied p) =
      ENNReal.ofReal
        (diagonalActivationOccupancyProbability (((p : ℕ) : ℝ) ^ (-σ))) := by
  let μp : Nat.Primes → MeasureTheory.Measure ℕ :=
    fun r ↦ diagonalActivationMeasure (subcriticalEulerParameter hσ r)
  have hmap := MeasureTheory.Measure.infinitePi_map_eval μp p
  have hq : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_nonneg (by positivity) _
  have hcoe : ((unitIntervalToNNReal (subcriticalEulerParameter hσ p) : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal (((p : ℕ) : ℝ) ^ (-σ)) := by
    rw [ENNReal.ofReal_eq_coe_nnreal hq]
    rfl
  have hstep :
      diagonalActivationMeasure (subcriticalEulerParameter hσ p) {k : ℕ | 0 < k} =
        ENNReal.ofReal
          (diagonalActivationOccupancyProbability (((p : ℕ) : ℝ) ^ (-σ))) := by
    rw [diagonalActivationMeasure_positive, hcoe, diagonalActivationOccupancyProbability,
      ENNReal.ofReal_div_of_pos (by linarith), ENNReal.ofReal_add (by norm_num) hq,
      ENNReal.ofReal_one]
  calc
    subcriticalEulerProductMeasure hσ (criticalPrimeOccupied p) =
        ((subcriticalEulerProductMeasure hσ).map (fun K ↦ K p)) {k : ℕ | 0 < k} := by
      rw [MeasureTheory.Measure.map_apply (by fun_prop) (by measurability)]
      rfl
    _ = diagonalActivationMeasure (subcriticalEulerParameter hσ p) {k : ℕ | 0 < k} := by
      rw [show subcriticalEulerProductMeasure hσ =
          MeasureTheory.Measure.infinitePi μp by rfl, hmap]
    _ = _ := hstep

/-- **Equation `(25)` in measure form.**  The enumerated subcritical occupancy masses have finite
sum. -/
theorem tsum_subcriticalPrimeOccupiedSequence_ne_top {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, subcriticalEulerProductMeasure hσ
      (criticalPrimeOccupiedSequence n)) ≠ ∞ := by
  have hnonneg : ∀ p : Nat.Primes,
      0 ≤ diagonalActivationOccupancyProbability (((p : ℕ) : ℝ) ^ (-σ)) := by
    intro p
    have hq : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
    exact div_nonneg hq (by linarith)
  have hsum : Summable fun n : ℕ =>
      diagonalActivationOccupancyProbability
        ((((natEquivPrimes n : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) :=
    natEquivPrimes.summable_iff.mpr (summable_subcritical_activationOccupancy hσ)
  rw [show (fun n : ℕ ↦ subcriticalEulerProductMeasure hσ
      (criticalPrimeOccupiedSequence n)) =
      fun n ↦ ENNReal.ofReal (diagonalActivationOccupancyProbability
        ((((natEquivPrimes n : Nat.Primes) : ℕ) : ℝ) ^ (-σ))) by
    funext n
    exact subcriticalEulerProductMeasure_criticalPrimeOccupied hσ _]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hnonneg _) hsum]
  exact ENNReal.ofReal_ne_top

/-! ### The finite-integer carrier -/

/-- **Above the Euler edge the source is an honest random finite integer.**  Only finitely many
primes are occupied almost surely, so the configuration is the valuation vector of a genuine
integer and its radical is a genuine squarefree number. -/
theorem subcriticalEulerProductMeasure_finite_occupancy {σ : ℝ} (hσ : 1 < σ) :
    subcriticalEulerProductMeasure hσ
        {K : CriticalEulerConfiguration |
          Set.Finite {p : Nat.Primes | 0 < K p}} = 1 := by
  have hzero : subcriticalEulerProductMeasure hσ
      (Filter.limsup criticalPrimeOccupiedSequence Filter.atTop) = 0 :=
    MeasureTheory.measure_limsup_atTop_eq_zero (tsum_subcriticalPrimeOccupiedSequence_ne_top hσ)
  rw [limsup_criticalPrimeOccupiedSequence] at hzero
  have hcompl : {K : CriticalEulerConfiguration |
      Set.Finite {p : Nat.Primes | 0 < K p}} =
      {K : CriticalEulerConfiguration |
        Set.Infinite {p : Nat.Primes | 0 < K p}}ᶜ := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.not_infinite]
  rw [hcompl, MeasureTheory.prob_compl_eq_one_iff]
  · exact hzero
  · rw [← limsup_criticalPrimeOccupiedSequence]
    exact MeasurableSet.measurableSet_limsup measurableSet_criticalPrimeOccupiedSequence

end

end RHTower
