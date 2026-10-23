import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ChainLendingAndTrainCapacity

/-!
# On a two-tower grid the prime capacities add

A train carried by the bi-tower `{p^j q^k : j ≤ M, k ≤ N}` has amplitudes `f j k` on an
`(M+1) × (N+1)` grid.  With disjoint copies of one bump, its first-power charge of `p` is the
**row charge** `Σ_k Σ_{j<M} f_{j,k} f_{j+1,k}` and that of `q` the **column charge**
`Σ_j Σ_{k<N} f_{j,k} f_{j,k+1}`, both against the **grid mass** `Σ f_{j,k}²`
(the lag law of `SineTrainsAreExtremalForOnePrime`, one tower at a time).

* **Joint capacity** (`grid_joint_capacity`): for nonnegative prime weights `w_p, w_q`,
  `w_p · row + w_q · column ≤ (w_p cos(π/(M+2)) + w_q cos(π/(N+2))) · mass`.
* **The capacities add** (`grid_joint_capacity_attained`, `grid_joint_capacity_sharp`): the product
  sine `sin((j+1)π/(M+2)) sin((k+1)π/(N+2))` attains the bound, and no smaller constant holds.

So on multiplicatively aligned trains two primes never cancel: the joint charge is the sum of the
single-prime capacities, each with its own finite-length deficit.  Any cross-prime saving in the
complete prime side must come from profiles that are *not* aligned with the towers.
-/

open Finset Real

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- The mass of a grid train. -/
def gridMass (M N : ℕ) (f : ℕ → ℕ → ℝ) : ℝ := ∑ j ∈ range (M + 1), ∑ k ∈ range (N + 1), f j k ^ 2

/-- The first-power charge along the first tower. -/
def gridRowCharge (M N : ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), ∑ j ∈ range M, f j k * f (j + 1) k

/-- The first-power charge along the second tower. -/
def gridColCharge (M N : ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (M + 1), ∑ k ∈ range N, f j k * f j (k + 1)

theorem gridRowCharge_le (M N : ℕ) (f : ℕ → ℕ → ℝ) :
    gridRowCharge M N f ≤ Real.cos (π / (M + 2)) * gridMass M N f := by
  unfold gridRowCharge gridMass
  rw [sum_comm (s := range (M + 1)), mul_sum]
  refine sum_le_sum fun k _ => ?_
  have := uniformTrain_capacity M (fun j => f j k)
  linarith

theorem gridColCharge_le (M N : ℕ) (f : ℕ → ℕ → ℝ) :
    gridColCharge M N f ≤ Real.cos (π / (N + 2)) * gridMass M N f := by
  unfold gridColCharge gridMass
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  have := uniformTrain_capacity N (fun k => f j k)
  linarith

/-- **Joint capacity of two towers.** -/
theorem grid_joint_capacity (M N : ℕ) {wp wq : ℝ} (hp : 0 ≤ wp) (hq : 0 ≤ wq)
    (f : ℕ → ℕ → ℝ) :
    wp * gridRowCharge M N f + wq * gridColCharge M N f ≤
      (wp * Real.cos (π / (M + 2)) + wq * Real.cos (π / (N + 2))) * gridMass M N f := by
  have h1 := mul_le_mul_of_nonneg_left (gridRowCharge_le M N f) hp
  have h2 := mul_le_mul_of_nonneg_left (gridColCharge_le M N f) hq
  nlinarith

/-- The product sine amplitude. -/
def productSine (M N : ℕ) (j k : ℕ) : ℝ := trainSine M j * trainSine N k

/-- **The capacities add**: the product sine attains the joint capacity. -/
theorem grid_joint_capacity_attained (M N : ℕ) (wp wq : ℝ) :
    wp * gridRowCharge M N (productSine M N) + wq * gridColCharge M N (productSine M N) =
      (wp * Real.cos (π / (M + 2)) + wq * Real.cos (π / (N + 2))) *
        gridMass M N (productSine M N) := by
  have hM := uniformTrain_capacity_attained M
  have hN := uniformTrain_capacity_attained N
  have hmass : gridMass M N (productSine M N) =
      (∑ j ∈ range (M + 1), trainSine M j ^ 2) * ∑ k ∈ range (N + 1), trainSine N k ^ 2 := by
    unfold gridMass productSine
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have hrow : gridRowCharge M N (productSine M N) =
      (∑ j ∈ range M, trainSine M j * trainSine M (j + 1)) *
        ∑ k ∈ range (N + 1), trainSine N k ^ 2 := by
    unfold gridRowCharge productSine
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_mul]
    exact sum_congr rfl fun j _ => by ring
  have hcol : gridColCharge M N (productSine M N) =
      (∑ j ∈ range (M + 1), trainSine M j ^ 2) *
        ∑ k ∈ range N, trainSine N k * trainSine N (k + 1) := by
    unfold gridColCharge productSine
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  rw [hmass, hrow, hcol]
  have hPM : ∑ j ∈ range M, trainSine M j * trainSine M (j + 1) =
      Real.cos (π / (M + 2)) * ∑ j ∈ range (M + 1), trainSine M j ^ 2 := by linarith
  have hPN : ∑ k ∈ range N, trainSine N k * trainSine N (k + 1) =
      Real.cos (π / (N + 2)) * ∑ k ∈ range (N + 1), trainSine N k ^ 2 := by linarith
  rw [hPM, hPN]
  ring

theorem gridMass_productSine_pos (M N : ℕ) : 0 < gridMass M N (productSine M N) := by
  unfold gridMass productSine
  refine sum_pos (fun j hj => sum_pos (fun k hk => ?_) ⟨0, by simp⟩) ⟨0, by simp⟩
  have := trainSine_pos M (mem_range.mp hj)
  have := trainSine_pos N (mem_range.mp hk)
  positivity

/-- No constant below the sum of the single-prime capacities bounds the joint charge. -/
theorem grid_joint_capacity_sharp (M N : ℕ) (wp wq : ℝ) {c : ℝ}
    (hc : c < wp * Real.cos (π / (M + 2)) + wq * Real.cos (π / (N + 2))) :
    ∃ f : ℕ → ℕ → ℝ,
      c * gridMass M N f < wp * gridRowCharge M N f + wq * gridColCharge M N f := by
  refine ⟨productSine M N, ?_⟩
  rw [grid_joint_capacity_attained]
  exact mul_lt_mul_of_pos_right hc (gridMass_productSine_pos M N)

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
