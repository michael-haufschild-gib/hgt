import GaloisForLFunctions.RHTower.EulerActivationSubcriticalFiniteness
import GaloisForLFunctions.HTGeometry.ProductOccupancyDichotomy

/-!
# The Euler edge is the occupancy phase transition of the activation product

The diagonal activation product is defined for every exponent `σ ≥ 0`: the local law at `p` occupies
that prime with probability `q_p / (1 + q_p)` for `q_p = p^{-σ}`.  The occupancy dichotomy of a
product of laws on `ℕ` therefore decides the size of the occupied set from the single scalar
`∑_p q_p / (1 + q_p)`, and that series converges exactly when `σ > 1`.

So the source is almost surely a finite integer exactly above the Euler edge, and almost surely
occupies infinitely many primes on the whole closed segment `0 ≤ σ ≤ 1`.  The abscissa of the Euler
product is not merely where the analytic formulas stop converging: it is the measure-theoretic phase
boundary of the activation model, and the transition is sharp.
-/

open MeasureTheory ProbabilityTheory Filter Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## The local occupancy mass -/

/-- **The local activation law occupies its coordinate with the Gibbs occupancy probability.** -/
theorem diagonalActivationMeasure_compl_zero (q : unitInterval) :
    diagonalActivationMeasure q {0}ᶜ =
      ENNReal.ofReal (diagonalActivationOccupancyProbability (q : ℝ)) := by
  have hq : (0 : ℝ) ≤ (q : ℝ) := q.2.1
  have hcoe : ((unitIntervalToNNReal q : NNReal) : ENNReal) =
      ENNReal.ofReal (q : ℝ) := by
    rw [ENNReal.ofReal_eq_coe_nnreal hq]
    rfl
  have hset : ({0}ᶜ : Set ℕ) = {k : ℕ | 0 < k} := by
    ext k
    simp [Nat.pos_iff_ne_zero]
  rw [hset, diagonalActivationMeasure_positive, hcoe,
    diagonalActivationOccupancyProbability,
    ENNReal.ofReal_div_of_pos (by linarith), ENNReal.ofReal_add (by norm_num) hq,
    ENNReal.ofReal_one]

/-- **The occupancy mass of an activation product is the local Gibbs probability.**  One appeal to
the universal locality of occupancy masses replaces the pushforward computation. -/
theorem infinitePi_diagonalActivation_occupiedEvent
    (q : Nat.Primes → unitInterval) (p : Nat.Primes) :
    Measure.infinitePi (fun r => diagonalActivationMeasure (q r)) (occupiedEvent p) =
      ENNReal.ofReal (diagonalActivationOccupancyProbability (q p : ℝ)) := by
  rw [infinitePi_occupiedEvent (fun r => diagonalActivationMeasure (q r)) p]
  exact diagonalActivationMeasure_compl_zero (q p)

/-! ## The activation product at an arbitrary exponent -/

/-- Activation parameter `q_p = p^{-σ}` at an arbitrary nonnegative exponent. -/
def eulerActivationParameter {σ : ℝ} (hσ : 0 ≤ σ) (p : Nat.Primes) : unitInterval :=
  ⟨((p : ℕ) : ℝ) ^ (-σ), by
    have hp : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    refine ⟨Real.rpow_nonneg (by linarith) _, ?_⟩
    exact Real.rpow_le_one_of_one_le_of_nonpos hp (by linarith)⟩

theorem eulerActivationParameter_coe {σ : ℝ} (hσ : 0 ≤ σ) (p : Nat.Primes) :
    (eulerActivationParameter hσ p : ℝ) = ((p : ℕ) : ℝ) ^ (-σ) := rfl

/-- Kolmogorov product of the local activation laws at exponent `σ`. -/
def eulerActivationProductMeasure {σ : ℝ} (hσ : 0 ≤ σ) :
    Measure CriticalEulerConfiguration :=
  Measure.infinitePi fun p : Nat.Primes =>
    diagonalActivationMeasure (eulerActivationParameter hσ p)

instance eulerActivationProductMeasure_isProbabilityMeasure {σ : ℝ} (hσ : 0 ≤ σ) :
    IsProbabilityMeasure (eulerActivationProductMeasure hσ) := by
  rw [eulerActivationProductMeasure]
  infer_instance

/-- At the Euler edge the exponent family is the critical activation product. -/
theorem eulerActivationProductMeasure_one :
    eulerActivationProductMeasure (le_of_lt one_pos : (0 : ℝ) ≤ 1) =
      criticalEulerProductMeasure := by
  have hparam : ∀ p : Nat.Primes,
      eulerActivationParameter (le_of_lt one_pos : (0 : ℝ) ≤ 1) p =
        criticalEulerParameter p := by
    intro p
    refine Subtype.ext ?_
    rw [eulerActivationParameter_coe]
    have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [Real.rpow_neg_one, ← one_div]
    rfl
  rw [eulerActivationProductMeasure, criticalEulerProductMeasure]
  exact congrArg Measure.infinitePi (funext fun p => by rw [hparam p])

/-- Above the Euler edge the exponent family is the subcritical activation product. -/
theorem eulerActivationProductMeasure_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    eulerActivationProductMeasure (le_of_lt (lt_trans one_pos hσ)) =
      subcriticalEulerProductMeasure hσ := by
  rw [eulerActivationProductMeasure, subcriticalEulerProductMeasure]
  exact congrArg Measure.infinitePi (funext fun p => by
    refine congrArg diagonalActivationMeasure (Subtype.ext ?_)
    rw [eulerActivationParameter_coe, subcriticalEulerParameter_coe])

/-! ## The threshold -/

/-- **The occupancy series converges exactly above the Euler edge.**  Below and at the edge the
occupancy probability is bounded below by half a prime reciprocal, so the series diverges with
`∑_p 1/p`; above the edge it is bounded by `p^{-σ}`. -/
theorem summable_diagonalActivationOccupancy_iff {σ : ℝ} (hσ : 0 ≤ σ) :
    Summable (fun p : Nat.Primes =>
        diagonalActivationOccupancyProbability
          ((eulerActivationParameter hσ p : ℝ))) ↔ 1 < σ := by
  have hocc : ∀ p : Nat.Primes,
      diagonalActivationOccupancyProbability ((eulerActivationParameter hσ p : ℝ)) =
        ((p : ℝ) ^ (-σ)) / (1 + (p : ℝ) ^ (-σ)) := fun _ => rfl
  constructor
  · intro h
    by_contra hσ1
    have hσle : σ ≤ 1 := not_lt.mp hσ1
    refine Nat.Primes.not_summable_one_div ?_
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (h.mul_left 2)
    · have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
      positivity
    · have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
      have hq0 : (0 : ℝ) < (p : ℝ) ^ (-σ) :=
        Real.rpow_pos_of_pos (by linarith) _
      have hq1 : (p : ℝ) ^ (-σ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)
      have hd : (0 : ℝ) < 1 + (p : ℝ) ^ (-σ) := by linarith
      have hinv : 1 / (p : ℝ) ≤ (p : ℝ) ^ (-σ) := by
        rw [one_div, ← Real.rpow_neg_one]
        exact (Real.rpow_le_rpow_left_iff hp1).mpr (by linarith)
      have hhalf : (p : ℝ) ^ (-σ) ≤
          2 * ((p : ℝ) ^ (-σ) / (1 + (p : ℝ) ^ (-σ))) := by
        have hid : 2 * ((p : ℝ) ^ (-σ) / (1 + (p : ℝ) ^ (-σ))) - (p : ℝ) ^ (-σ) =
            (p : ℝ) ^ (-σ) * (1 - (p : ℝ) ^ (-σ)) / (1 + (p : ℝ) ^ (-σ)) := by
          field_simp
          ring
        have hnn : (0 : ℝ) ≤
            (p : ℝ) ^ (-σ) * (1 - (p : ℝ) ^ (-σ)) / (1 + (p : ℝ) ^ (-σ)) :=
          div_nonneg (mul_nonneg hq0.le (by linarith)) hd.le
        linarith
      rw [hocc p]
      linarith
  · intro h1
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      (Nat.Primes.summable_rpow.mpr (show -σ < -1 by linarith))
    · have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
      have hq0 : (0 : ℝ) < (p : ℝ) ^ (-σ) :=
        Real.rpow_pos_of_pos (by linarith) _
      rw [hocc p]
      positivity
    · have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
      have hq0 : (0 : ℝ) < (p : ℝ) ^ (-σ) :=
        Real.rpow_pos_of_pos (by linarith) _
      rw [hocc p, div_le_iff₀ (by linarith)]
      nlinarith

/-- The total local occupancy mass of the activation product at exponent `σ`. -/
theorem tsum_eulerActivation_localMass_ne_top_iff {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑' p : Nat.Primes,
        diagonalActivationMeasure (eulerActivationParameter hσ p) {0}ᶜ) ≠ ∞ ↔ 1 < σ := by
  have hlocal : ∀ p : Nat.Primes,
      diagonalActivationMeasure (eulerActivationParameter hσ p) {0}ᶜ =
        ENNReal.ofReal (diagonalActivationOccupancyProbability
          ((eulerActivationParameter hσ p : ℝ))) :=
    fun p => diagonalActivationMeasure_compl_zero _
  rw [tsum_congr hlocal]
  rw [tsum_ofReal_ne_top_iff_summable _ (fun p => ?_)]
  · exact summable_diagonalActivationOccupancy_iff hσ
  · have hq0 : (0 : ℝ) ≤ (eulerActivationParameter hσ p : ℝ) :=
      (eulerActivationParameter hσ p).2.1
    rw [diagonalActivationOccupancyProbability]
    positivity

/-! ## The phase transition -/

/-- **The Euler edge is the occupancy phase boundary.**  The activation source is almost surely a
finite integer exactly when the exponent exceeds one. -/
theorem eulerActivationProductMeasure_finiteOccupancy_eq_one_iff {σ : ℝ} (hσ : 0 ≤ σ) :
    eulerActivationProductMeasure hσ
        {K : CriticalEulerConfiguration | (occupiedSet K).Finite} = 1 ↔ 1 < σ := by
  rw [eulerActivationProductMeasure,
    measure_finiteOccupancy_eq_one_iff _
      (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)))]
  exact tsum_eulerActivation_localMass_ne_top_iff hσ

/-- **On the closed segment up to the Euler edge the source occupies infinitely many primes.**
The corresponding statement at the edge itself is the case `σ = 1`. -/
theorem eulerActivationProductMeasure_infiniteOccupancy_of_le_one {σ : ℝ}
    (hσ : 0 ≤ σ) (h1 : σ ≤ 1) :
    eulerActivationProductMeasure hσ
        {K : CriticalEulerConfiguration | (occupiedSet K).Infinite} = 1 := by
  rw [eulerActivationProductMeasure]
  refine measure_infiniteOccupancy_eq_one _
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes))) ?_
  by_contra hne
  exact absurd ((tsum_eulerActivation_localMass_ne_top_iff hσ).mp hne) (by linarith)

/-- The dichotomy in its complementary form on the same segment. -/
theorem eulerActivationProductMeasure_finiteOccupancy_eq_zero_of_le_one {σ : ℝ}
    (hσ : 0 ≤ σ) (h1 : σ ≤ 1) :
    eulerActivationProductMeasure hσ
        {K : CriticalEulerConfiguration | (occupiedSet K).Finite} = 0 := by
  rw [finiteOccupancy_eq_compl,
    MeasureTheory.prob_compl_eq_zero_iff (measurableSet_infiniteOccupancy
      (Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes))))]
  exact eulerActivationProductMeasure_infiniteOccupancy_of_le_one hσ h1

end

end RHTower
