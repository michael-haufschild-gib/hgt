import GaloisForLFunctions.RHTower.BakerProof.BakerParameters

/-!
# Long extrapolation for the Baker auxiliary matrix

This module turns one exact component extrapolation into an iteration on auxiliary-matrix kernels.
The same nonzero Siegel vector is retained while the consecutive sample range grows and the
multiindex cutoff decreases.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerProof

namespace BakerIteration

/-- Consecutive sample count after `k` long-extrapolation enlargements. -/
def stageSampleCount (n t k : ℕ) : ℕ :=
  BakerParameters.sampleCount n t * (t / 4) ^ k

/-- Component cutoff after `k` halvings. -/
def stageOrder (n t k : ℕ) : ℕ :=
  BakerParameters.extrapolationOrder n t / 2 ^ k

@[simp] theorem stageSampleCount_zero (n t : ℕ) :
    stageSampleCount n t 0 = BakerParameters.sampleCount n t := by
  simp [stageSampleCount]

theorem stageSampleCount_succ (n t k : ℕ) :
    stageSampleCount n t (k + 1) = stageSampleCount n t k * (t / 4) := by
  simp [stageSampleCount, pow_succ, mul_assoc]

@[simp] theorem stageOrder_zero (n t : ℕ) :
    stageOrder n t 0 = BakerParameters.extrapolationOrder n t := by
  simp [stageOrder]

theorem stageOrder_succ (n t k : ℕ) :
    stageOrder n t (k + 1) = stageOrder n t k / 2 := by
  unfold stageOrder
  rw [pow_succ, ← Nat.div_div_eq_div_mul]

theorem two_mul_stageOrder_succ_le (n t k : ℕ) :
    2 * stageOrder n t (k + 1) ≤ stageOrder n t k := by
  rw [stageOrder_succ]
  exact Nat.mul_div_le _ _

/-- The next stage sample interval lies in the first quarter of the radius `t * S_k`. -/
theorem four_mul_stageSampleCount_succ_le (n t k : ℕ) :
    4 * stageSampleCount n t (k + 1) ≤ t * stageSampleCount n t k := by
  rw [stageSampleCount_succ]
  have ht := Nat.mul_div_le t 4
  calc
    4 * (stageSampleCount n t k * (t / 4)) =
        (4 * (t / 4)) * stageSampleCount n t k := by ring
    _ ≤ t * stageSampleCount n t k := Nat.mul_le_mul_right _ ht

theorem stageSample_mem_closedBall {n t k : ℕ}
    (sample : Fin (stageSampleCount n t (k + 1))) :
    ((sample : ℕ) : ℂ) ∈
      Metric.closedBall 0 (t * stageSampleCount n t k : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  simp only [sub_zero, Complex.norm_natCast]
  exact_mod_cast (le_trans (Nat.le_mul_of_pos_left (sample : ℕ) (by norm_num))
    (le_trans (Nat.mul_le_mul_left 4 sample.isLt.le)
      (four_mul_stageSampleCount_succ_le n t k)))

/-- Uniform Schwarz node decay at one long-extrapolation stage. -/
theorem stageSample_node_ratio_le_two_thirds
    {n t k : ℕ} (ht : 8 ≤ t)
    (hS : 0 < stageSampleCount n t k)
    (sample : Fin (stageSampleCount n t (k + 1))) :
    let S := stageSampleCount n t k
    let q := stageOrder n t (k + 1)
    (((((sample : ℕ) + S : ℕ) : ℝ) ^ (q * S)) /
      (((t * S : ℕ) : ℝ) - S) ^ (q * S)) ≤
        ((2 : ℝ) / 3) ^ (q * S) := by
  dsimp only
  let S := stageSampleCount n t k
  have hrpos : (0 : ℝ) < (t * S : ℕ) - S := by
    apply sub_pos.mpr
    exact_mod_cast (show S < t * S by
      simpa using (Nat.mul_lt_mul_right hS).mpr (by omega : 1 < t))
  rw [← div_pow]
  apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hrpos.le)
  rw [div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 3)]
  have hsamp : (sample : ℕ) ≤ S * (t / 4) := by
    simpa [S, stageSampleCount_succ] using sample.isLt.le
  have hfloor : 4 * (t / 4) ≤ t := Nat.mul_div_le t 4
  have hsampR : ((sample : ℕ) : ℝ) ≤ ((S * (t / 4) : ℕ) : ℝ) := by
    exact_mod_cast hsamp
  have hfloorR : ((4 * (t / 4) : ℕ) : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hfloor
  have htR : (8 : ℝ) ≤ t := by exact_mod_cast ht
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  push_cast at hsampR hfloorR
  push_cast
  nlinarith

end BakerIteration

/-- One long-extrapolation transition.  Exact zeros for every component in the new `q`-box are
reassembled as a kernel for the enlarged `S' × q^(n-1)` auxiliary matrix. -/
theorem Relation.auxiliaryMatrix_kernel_extrapolate
    (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (Hη : ℝ)
    (hη : ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤ Hη)
    (hHη : 0 ≤ Hη)
    (q : ℕ) (hqT : 2 * q ≤ T)
    {radius : ℝ} (hradius : (S : ℝ) < radius)
    (S' : ℕ)
    (hsample : ∀ sample : Fin S',
      ((sample : ℕ) : ℂ) ∈ Metric.closedBall 0 radius)
    (hsmall : ∀ sample : Fin S', ∀ ν : R.NonPivot pivot → Fin q,
      ((((sample : ℕ) + S : ℕ) : ℝ) ^ (q * S) *
        ((((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, (ν i : ℕ)) * Hη *
            Real.exp ((L * R.primeLogWeight) * radius))) /
          (radius - S) ^ (q * S))) *
        (((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, (ν i : ℕ)) * Hη *
            (R.primeProduct : ℝ) ^ (L * (sample : ℕ)))) ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S' q) η = 0 := by
  apply R.auxiliaryMatrix_mulVec_eq_zero_of_component_box_zero
  intro sample ν
  have hqT' : q + q ≤ T := by simpa [two_mul] using hqT
  have hνq : ∀ i, (ν i : ℕ) + q < T := fun i =>
    lt_of_lt_of_le (Nat.add_lt_add_right (ν i).isLt q) hqT'
  exact R.auxiliaryComponent_eq_zero_one_step_scalar
    c hc hint pivot η hker (fun i => (ν i : ℕ)) q hνq
      Hη hη hHη hradius (sample : ℕ) (hsample sample) (hsmall sample ν)

end GaloisForLFunctions.RHTower.BakerProof
