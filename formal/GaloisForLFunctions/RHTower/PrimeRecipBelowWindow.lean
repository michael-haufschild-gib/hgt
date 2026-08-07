import GaloisForLFunctions.RHTower.MertensThirdTheorem

/-!
# The prime reciprocal sum over a power window

The half-open prime reciprocal sum `A(N) = ∑_{p < N} 1/p` satisfies Mertens' second theorem, and
for a fixed exponent `θ ∈ (0,1)` the mass of the window `[N^θ, N)` converges:

```text
A(N) - A(⌊N^θ⌋ + 1) → -log θ.
```
-/

open Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The prime reciprocal sum over `p < N`. -/
def primeRecipBelow (N : ℕ) : ℝ := ∑ p ∈ Nat.primesBelow N, ((p : ℝ))⁻¹

theorem primeRecipBelow_eq_sum_weight (N : ℕ) :
    primeRecipBelow N = ∑ n ∈ Finset.range N, primeRecipWeight n := by
  rw [primeRecipBelow, Nat.primesBelow, Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => by rw [primeRecipWeight]

theorem primeRecipSum_eq_primeRecipBelow_add (N : ℕ) :
    primeRecipSum N = primeRecipBelow N + primeRecipWeight N := by
  rw [primeRecipSum, primeRecipBelow_eq_sum_weight,
    show Finset.Icc 0 N = Finset.range (N + 1) by ext n; simp,
    Finset.sum_range_succ]

theorem primeRecipWeight_nonneg (n : ℕ) : 0 ≤ primeRecipWeight n := by
  rw [primeRecipWeight]
  split_ifs
  · positivity
  · exact le_rfl

theorem primeRecipWeight_le_one_div (n : ℕ) : primeRecipWeight n ≤ 1 / (n : ℝ) := by
  rw [primeRecipWeight]
  split_ifs with hp
  · rw [one_div]
  · positivity

theorem tendsto_primeRecipWeight : Tendsto primeRecipWeight atTop (nhds 0) :=
  squeeze_zero primeRecipWeight_nonneg primeRecipWeight_le_one_div
    tendsto_one_div_atTop_nhds_zero_nat

/-- **Mertens' second theorem for the half-open prime reciprocal sum.** -/
theorem tendsto_primeRecipBelow_sub_logLog :
    Tendsto (fun N : ℕ => primeRecipBelow N - Real.log (Real.log N)) atTop
      (nhds mertensSecondConstant) := by
  have h := tendsto_primeRecipSum_sub_logLog.sub tendsto_primeRecipWeight
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  rw [primeRecipSum_eq_primeRecipBelow_add]
  ring

theorem primeRecipBelow_nonneg (N : ℕ) : 0 ≤ primeRecipBelow N := by
  rw [primeRecipBelow_eq_sum_weight]
  exact Finset.sum_nonneg fun n _ => primeRecipWeight_nonneg n

theorem primeRecipBelow_mono {M N : ℕ} (h : M ≤ N) : primeRecipBelow M ≤ primeRecipBelow N := by
  rw [primeRecipBelow_eq_sum_weight, primeRecipBelow_eq_sum_weight]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) ?_
  exact fun n _ _ => primeRecipWeight_nonneg n

/-! ## The power window -/

/-- The first index above the power window boundary `N^θ`. -/
def powerWindowIndex (θ : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) ^ θ⌋₊ + 1

theorem rpow_le_powerWindowIndex (θ : ℝ) (N : ℕ) :
    (N : ℝ) ^ θ ≤ ((powerWindowIndex θ N : ℕ) : ℝ) := by
  rw [powerWindowIndex]
  push_cast
  exact (Nat.lt_floor_add_one _).le

theorem powerWindowIndex_le_two_mul {θ : ℝ} {N : ℕ} (h : (1 : ℝ) ≤ (N : ℝ) ^ θ) :
    ((powerWindowIndex θ N : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ θ := by
  rw [powerWindowIndex]
  push_cast
  have := Nat.floor_le (le_trans zero_le_one h)
  linarith

theorem one_le_powerWindowIndex (θ : ℝ) (N : ℕ) : 1 ≤ powerWindowIndex θ N :=
  Nat.le_add_left 1 _

theorem tendsto_powerWindowIndex {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (powerWindowIndex θ) atTop atTop := by
  have hrpow : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have hfloor : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ θ⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hrpow
  exact tendsto_atTop_mono (fun N => Nat.le_succ _) hfloor

/-- The window boundary has logarithmic ratio `θ`. -/
theorem tendsto_log_powerWindowIndex_div {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun N : ℕ => Real.log ((powerWindowIndex θ N : ℕ) : ℝ) / Real.log N) atTop
      (nhds θ) := by
  have hlower : ∀ᶠ N : ℕ in atTop,
      θ ≤ Real.log ((powerWindowIndex θ N : ℕ) : ℝ) / Real.log N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    have h1 : Real.log ((N : ℝ) ^ θ) ≤ Real.log ((powerWindowIndex θ N : ℕ) : ℝ) :=
      Real.log_le_log (Real.rpow_pos_of_pos (by linarith) θ) (rpow_le_powerWindowIndex θ N)
    rw [Real.log_rpow (by linarith)] at h1
    rw [le_div_iff₀ hlogN]
    linarith
  have hupper : ∀ᶠ N : ℕ in atTop,
      Real.log ((powerWindowIndex θ N : ℕ) : ℝ) / Real.log N ≤ θ + Real.log 2 / Real.log N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    have hone : (1 : ℝ) ≤ (N : ℝ) ^ θ := Real.one_le_rpow (by linarith) hθ.le
    have hpos : (0 : ℝ) < ((powerWindowIndex θ N : ℕ) : ℝ) :=
      lt_of_lt_of_le zero_lt_one (le_trans hone (rpow_le_powerWindowIndex θ N))
    have h1 : Real.log ((powerWindowIndex θ N : ℕ) : ℝ) ≤ Real.log (2 * (N : ℝ) ^ θ) :=
      Real.log_le_log hpos (powerWindowIndex_le_two_mul hone)
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos (by linarith) θ)),
      Real.log_rpow (by linarith)] at h1
    rw [div_le_iff₀ hlogN, add_mul, div_mul_cancel₀ _ (ne_of_gt hlogN)]
    linarith
  have htail : Tendsto (fun N : ℕ => θ + Real.log 2 / Real.log N) atTop (nhds θ) := by
    have hzero : Tendsto (fun N : ℕ => Real.log 2 / Real.log N) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => θ) atTop (nhds θ)).add hzero
    rwa [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail hlower hupper

theorem tendsto_logLog_powerWindowIndex_sub {θ : ℝ} (hθ0 : 0 < θ) :
    Tendsto (fun N : ℕ =>
        Real.log (Real.log ((powerWindowIndex θ N : ℕ) : ℝ)) - Real.log (Real.log N)) atTop
      (nhds (Real.log θ)) := by
  have hcont : Tendsto (fun N : ℕ =>
      Real.log (Real.log ((powerWindowIndex θ N : ℕ) : ℝ) / Real.log N)) atTop
      (nhds (Real.log θ)) :=
    (Real.continuousAt_log (ne_of_gt hθ0)).tendsto.comp (tendsto_log_powerWindowIndex_div hθ0)
  refine hcont.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ θ := Real.one_le_rpow (by linarith) hθ0.le
  have hle : Real.log ((N : ℝ) ^ θ) ≤ Real.log ((powerWindowIndex θ N : ℕ) : ℝ) :=
    Real.log_le_log (Real.rpow_pos_of_pos (by linarith) θ) (rpow_le_powerWindowIndex θ N)
  rw [Real.log_rpow (by linarith)] at hle
  have hlogM : 0 < Real.log ((powerWindowIndex θ N : ℕ) : ℝ) := by
    have : 0 < θ * Real.log (N : ℝ) := mul_pos hθ0 hlogN
    linarith
  rw [Real.log_div (ne_of_gt hlogM) (ne_of_gt hlogN)]

/-- **The mass of the prime power window.**  For a fixed exponent `θ ∈ (0,1)` the reciprocal mass
of the primes in `[N^θ, N)` converges to `-log θ`. -/
theorem tendsto_primeRecipBelow_window {θ : ℝ} (hθ0 : 0 < θ) :
    Tendsto (fun N : ℕ => primeRecipBelow N - primeRecipBelow (powerWindowIndex θ N)) atTop
      (nhds (-Real.log θ)) := by
  have hM : Tendsto (fun N : ℕ =>
      primeRecipBelow (powerWindowIndex θ N) -
        Real.log (Real.log ((powerWindowIndex θ N : ℕ) : ℝ))) atTop
      (nhds mertensSecondConstant) :=
    tendsto_primeRecipBelow_sub_logLog.comp (tendsto_powerWindowIndex hθ0)
  have hcomb := (tendsto_primeRecipBelow_sub_logLog.sub hM).sub
    (tendsto_logLog_powerWindowIndex_sub hθ0)
  rw [sub_self, zero_sub] at hcomb
  refine hcomb.congr fun N => ?_
  ring

end

end RHTower
