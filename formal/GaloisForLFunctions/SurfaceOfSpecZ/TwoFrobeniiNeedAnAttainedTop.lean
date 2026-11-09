import GaloisForLFunctions.SurfaceOfSpecZ.TwoFrobeniiSeeEveryConfiguration

/-!
# Two Frobenii need an attained top at single degrees

`TwoFrobeniiSuffice` samples the degrees `pᵃqᵇ` and needs an attained maximal real part; the pairs
`log m − log n` of `TwoFrobeniiSeeEveryConfiguration` need none. In the positive-weight model of
`RHTower.WeilLagSingleBaseWolffConfiguration` the single degrees do not suffice:

**Theorem** (`exists_twoPrime_samples_bddBelow_nonattained`). For primes `p, q` and `Θ > 0` there are
depths `x_k ∈ (0, Θ)` increasing to `Θ` (not attained), ordinates `γ_k → ∞` and positive summable
weights `c_k` such that the symmetric samples

  `Φ(λ) = Σ_k c_k (e^{x_k λ} + e^{−x_k λ}) cos(γ_k λ)`

of the points `½ ± x_k ± iγ_k` satisfy `Φ(a log p + b log q) ≥ −2` for all `a, b ≥ 0`.

**Construction.** `x_k = Θ(1 − 2^{−(k+1)})`; weights and windows recursively,
`c_{k+1} = (c_k/16) e^{−ΘU_k}`, `U_{k+1} = max(U_k + 1, log(16/c_{k+1})/(x_{k+1} − x_k))`. On
`[U_k, U_{k+1}]` the quartets `k, k+1` dominate: the earlier ones by `e^{−(x_k − x_j)U_k} ≤ c_k/16`, the
later ones by `c_{k+2} = (c_{k+1}/16)e^{−ΘU_{k+1}}`. The ordinate `γ_k = 2πN_k/log p`, with
`|N_k log q/log p − r_k| ≤ 1/Q_k` by Dirichlet's approximation and `Q_k ≥ 6U_{k+1}/log q`, keeps
`γ_k (a log p + b log q)` within `π/3` of `2πℤ` for every degree up to `U_{k+1}`, so
`cos(γ_k λ) ≥ ½` there. Hence `Φ ≥ (3/8)(c_k e^{x_kλ} + c_{k+1}e^{x_{k+1}λ}) − Σ c ≥ −2`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

namespace TwoPrimeWolff

variable (Θ : ℝ)

/-- The depths `x_k = Θ(1 − 2^{−(k+1)})`. -/
def depth (k : ℕ) : ℝ := Θ * (1 - (1 / 2 : ℝ) ^ (k + 1))

/-- Weights and window starts, recursively. -/
def state : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | k + 1 =>
    ((state k).1 / 16 * Real.exp (-(Θ * (state k).2)),
      max ((state k).2 + 1)
        (Real.log (16 / ((state k).1 / 16 * Real.exp (-(Θ * (state k).2)))) /
          (Θ * (1 / 2 : ℝ) ^ (k + 2))))

/-- The weight `c_k`. -/
def weight (k : ℕ) : ℝ := (state Θ k).1

/-- The window start `U_k`. -/
def start (k : ℕ) : ℝ := (state Θ k).2

theorem weight_zero : weight Θ 0 = 1 := rfl

theorem start_zero : start Θ 0 = 0 := rfl

theorem weight_succ (k : ℕ) :
    weight Θ (k + 1) = weight Θ k / 16 * Real.exp (-(Θ * start Θ k)) := rfl

theorem start_succ (k : ℕ) :
    start Θ (k + 1) = max (start Θ k + 1)
      (Real.log (16 / weight Θ (k + 1)) / (Θ * (1 / 2 : ℝ) ^ (k + 2))) := rfl

theorem weight_pos (k : ℕ) : 0 < weight Θ k := by
  induction k with
  | zero => rw [weight_zero]; norm_num
  | succ k ih => rw [weight_succ]; positivity

theorem start_succ_ge (k : ℕ) : start Θ k + 1 ≤ start Θ (k + 1) := by
  rw [start_succ]; exact le_max_left _ _

theorem nat_le_start (k : ℕ) : (k : ℝ) ≤ start Θ k := by
  induction k with
  | zero => rw [start_zero]; simp
  | succ k ih => push_cast; linarith [start_succ_ge Θ k]

theorem start_nonneg (k : ℕ) : 0 ≤ start Θ k := (Nat.cast_nonneg k).trans (nat_le_start Θ k)

theorem start_mono {j k : ℕ} (hjk : j ≤ k) : start Θ j ≤ start Θ k := by
  induction k with
  | zero => rw [Nat.le_zero.mp hjk]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · linarith [ih (Nat.lt_succ_iff.mp h), start_succ_ge Θ k]
    · rw [le_antisymm hjk h]

variable {Θ}

theorem weight_succ_le (hΘ : 0 ≤ Θ) (k : ℕ) : weight Θ (k + 1) ≤ weight Θ k / 16 := by
  rw [weight_succ]
  have h1 : Real.exp (-(Θ * start Θ k)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := mul_nonneg hΘ (start_nonneg Θ k); linarith)
  have h2 : 0 ≤ weight Θ k / 16 := by have := weight_pos Θ k; positivity
  calc weight Θ k / 16 * Real.exp (-(Θ * start Θ k)) ≤ weight Θ k / 16 * 1 :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = weight Θ k / 16 := mul_one _

theorem weight_add_le (hΘ : 0 ≤ Θ) (m i : ℕ) : weight Θ (m + i) ≤ weight Θ m * (1 / 16) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc]
    calc weight Θ (m + i + 1) ≤ weight Θ (m + i) / 16 := weight_succ_le hΘ _
      _ ≤ weight Θ m * (1 / 16) ^ i / 16 := by linarith
      _ = weight Θ m * (1 / 16) ^ (i + 1) := by ring

theorem summable_geom16 : Summable fun i : ℕ => (1 / 16 : ℝ) ^ i :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem tsum_geom16 : ∑' i : ℕ, (1 / 16 : ℝ) ^ i = 16 / 15 := by
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

theorem summable_weight_add (hΘ : 0 ≤ Θ) (m : ℕ) : Summable fun i => weight Θ (m + i) :=
  Summable.of_nonneg_of_le (fun _ => (weight_pos Θ _).le) (weight_add_le hΘ m)
    (summable_geom16.mul_left _)

theorem summable_weight (hΘ : 0 ≤ Θ) : Summable (weight Θ) := by
  simpa using summable_weight_add hΘ 0

/-- **Tails.** `Σ_{i ≥ 0} c_{m+i} ≤ 2c_m`. -/
theorem tsum_weight_add_le (hΘ : 0 ≤ Θ) (m : ℕ) : ∑' i, weight Θ (m + i) ≤ 2 * weight Θ m := by
  calc ∑' i, weight Θ (m + i) ≤ ∑' i, weight Θ m * (1 / 16 : ℝ) ^ i :=
        Summable.tsum_le_tsum (weight_add_le hΘ m) (summable_weight_add hΘ m)
          (summable_geom16.mul_left _)
    _ = weight Θ m * (16 / 15) := by rw [tsum_mul_left, tsum_geom16]
    _ ≤ 2 * weight Θ m := by have := weight_pos Θ m; nlinarith

theorem tsum_weight_le (hΘ : 0 ≤ Θ) : ∑' k, weight Θ k ≤ 2 := by
  have := tsum_weight_add_le hΘ 0
  simp only [zero_add] at this
  rw [weight_zero] at this
  linarith

/-- **Heads.** `Σ_{j < k} c_j ≤ 2`. -/
theorem sum_range_weight_le (hΘ : 0 ≤ Θ) (k : ℕ) : ∑ j ∈ Finset.range k, weight Θ j ≤ 2 :=
  ((summable_weight hΘ).sum_le_tsum _ (fun j _ => (weight_pos Θ j).le)).trans (tsum_weight_le hΘ)

/-- **The window condition.** `e^{−(x_{k+1} − x_k) U_{k+1}} ≤ c_{k+1}/16`. -/
theorem exp_window_le (hΘ : 0 < Θ) (k : ℕ) :
    Real.exp (-(Θ * (1 / 2 : ℝ) ^ (k + 2) * start Θ (k + 1))) ≤ weight Θ (k + 1) / 16 := by
  have hd : 0 < Θ * (1 / 2 : ℝ) ^ (k + 2) := by positivity
  have hw := weight_pos Θ (k + 1)
  have h1 : Real.log (16 / weight Θ (k + 1)) / (Θ * (1 / 2 : ℝ) ^ (k + 2)) ≤ start Θ (k + 1) := by
    rw [start_succ]; exact le_max_right _ _
  rw [div_le_iff₀ hd] at h1
  have h2 : Real.exp (-(Θ * (1 / 2 : ℝ) ^ (k + 2) * start Θ (k + 1))) ≤
      Real.exp (-Real.log (16 / weight Θ (k + 1))) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-Real.log (16 / weight Θ (k + 1))) = weight Θ (k + 1) / 16 := by
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  exact h2.trans h3.le

theorem depth_pos (hΘ : 0 < Θ) (k : ℕ) : 0 < depth Θ k := by
  unfold depth
  have : (1 / 2 : ℝ) ^ (k + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have : 0 < 1 - (1 / 2 : ℝ) ^ (k + 1) := by linarith
  positivity

theorem depth_lt (hΘ : 0 < Θ) (k : ℕ) : depth Θ k < Θ := by
  unfold depth
  have : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
  nlinarith

theorem depth_le_of_le (hΘ : 0 ≤ Θ) {j k : ℕ} (hjk : j ≤ k) : depth Θ j ≤ depth Θ k := by
  unfold depth
  have : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ (j + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  nlinarith

theorem strictMono_depth (hΘ : 0 < Θ) : StrictMono (depth Θ) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  unfold depth
  have : (1 / 2 : ℝ) ^ (k + 1 + 1) < (1 / 2 : ℝ) ^ (k + 1) :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  nlinarith

/-- **The gap below `x_k`.** For `j < k`, `x_k − x_j ≥ Θ 2^{−(k+1)}`. -/
theorem depth_gap (hΘ : 0 ≤ Θ) {j k : ℕ} (hjk : j < k) :
    Θ * (1 / 2 : ℝ) ^ (k + 1) ≤ depth Θ k - depth Θ j := by
  unfold depth
  have h1 : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ (j + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k / 2 := by rw [pow_succ]; ring
  nlinarith

theorem exists_depth_gt (hΘ : 0 < Θ) {β : ℝ} (hβ : β < Θ) : ∃ k, β < depth Θ k := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < (Θ - β) / Θ by
    exact div_pos (by linarith) hΘ) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨k, ?_⟩
  unfold depth
  have h1 : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [lt_div_iff₀ hΘ] at hk
  nlinarith

end TwoPrimeWolff

end GaloisForLFunctions.SurfaceOfSpecZ
