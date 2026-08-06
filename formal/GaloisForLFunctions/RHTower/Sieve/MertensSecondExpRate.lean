import GaloisForLFunctions.RHTower.Sieve.MertensDefectTail
import GaloisForLFunctions.RHTower.Sieve.MertensFirstExpRate

/-!
# Mertens' second theorem with an exponential error term

The sharp decomposition leaves exactly three remainders:

```text
mertensS N − logLog N − meisselMertensConst
    = (mertensA N − log N)/log N + ∑_{i≥N} logLogDefect i − ∑_{i≥N} mertensRemTerm i .
```

Writing `mertensA i − log i = c₁ + ε(i)`, the constant `c₁` enters the first term as `c₁/log N` and
the third as `c₁·∑_{i≥N} invLogVar i = c₁/log N` — **with the opposite sign**.  The two cancel
exactly, and what survives is governed by `ε` alone.  Charging `c₁` to the error instead, as a bound
`|mertensA i − log i| ≤ const` must, is what pins the classical estimate at `1/log N`: the loss is a
lost cancellation, not a lossy inequality.

The defect tail is `1/(N log N)`, from `logLogDefect i ≤ (1/i)·invLogVar i`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- **The exact remainder of the sharp decomposition.** -/
theorem mertensS_sub_logLog_sub_const_eq {N : ℕ} (hN : 2 ≤ N) :
    mertensS N - logLog N - meisselMertensConst
      = (mertensA N - Real.log N) / Real.log N
        + (∑' i, logLogDefect (i + N)) - ∑' i, mertensRemTerm (i + N) := by
  have hd := summable_logLogDefect.sum_add_tsum_nat_add N
  have hv := summable_mertensRemTerm.sum_add_tsum_nat_add N
  have hdec := mertensS_decomposition hN
  unfold meisselMertensConst
  linarith [hdec, hd, hv]

/-- The shifted remainder weight is dominated by the variation. -/
theorem abs_invLogVar_mul_centred_le (c₁ : ℝ) (i : ℕ) :
    |invLogVar i * (mertensA i - Real.log i - c₁)|
      ≤ (mertensFirstConst + |c₁|) * invLogVar i := by
  rcases lt_or_ge i 2 with hi | hi
  · have hz : invLogVar i = 0 := by
      unfold invLogVar
      rw [if_neg (by omega)]
    rw [hz]
    simp
  · have hvar := invLogVar_nonneg i
    have hbase := abs_mertensA_sub_log_le (N := i) (by omega)
    have hsub : |mertensA i - Real.log i - c₁| ≤ mertensFirstConst + |c₁| := by
      have := abs_sub (mertensA i - Real.log i) c₁
      linarith [hbase, abs_nonneg c₁, this]
    rw [abs_mul, abs_of_nonneg hvar, mul_comm]
    exact mul_le_mul_of_nonneg_right hsub hvar

theorem summable_invLogVar_mul_centred (c₁ : ℝ) :
    Summable (fun i => invLogVar i * (mertensA i - Real.log i - c₁)) := by
  refine Summable.of_norm_bounded (summable_invLogVar.mul_left (mertensFirstConst + |c₁|)) ?_
  intro i
  rw [Real.norm_eq_abs]
  exact abs_invLogVar_mul_centred_le c₁ i

/-- **The remainder tail, with the constant separated.**  The `c₁/log N` produced here is exactly
what the boundary term `(mertensA N − log N)/log N` also produces, and the decomposition subtracts
this tail — so the two occurrences cancel. -/
theorem tsum_mertensRemTerm_add_eq {N : ℕ} (hN : 2 ≤ N) (c₁ : ℝ) :
    ∑' i, mertensRemTerm (i + N)
      = c₁ * (1 / Real.log N)
        + ∑' i, invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁) := by
  have hw : Summable (fun i => invLogVar (i + N) * c₁) :=
    (((summable_nat_add_iff N).2 summable_invLogVar)).mul_right c₁
  have hc : Summable (fun i => invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁)) :=
    (summable_nat_add_iff N).2 (summable_invLogVar_mul_centred c₁)
  have hsplit : ∀ i : ℕ, mertensRemTerm (i + N)
      = invLogVar (i + N) * c₁
        + invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁) := by
    intro i
    unfold mertensRemTerm
    ring
  rw [tsum_congr hsplit, hw.tsum_add hc, tsum_mul_right, tsum_invLogVar_add hN]
  ring

/-- The `ε`-part of the remainder tail is below the uniform bound on `ε`. -/
theorem abs_tsum_invLogVar_mul_centred_le {N : ℕ} (hN : 2 ≤ N) {c₁ M : ℝ}
    (hbd : ∀ i : ℕ, N ≤ i → |mertensA i - Real.log i - c₁| ≤ M) :
    |∑' i, invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁)|
      ≤ M * (1 / Real.log N) := by
  have hc : Summable (fun i => invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁)) :=
    (summable_nat_add_iff N).2 (summable_invLogVar_mul_centred c₁)
  have hmaj : Summable (fun i => M * invLogVar (i + N)) :=
    (((summable_nat_add_iff N).2 summable_invLogVar)).mul_left M
  have hterm : ∀ i : ℕ,
      ‖invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁)‖
        ≤ M * invLogVar (i + N) := by
    intro i
    have hvar := invLogVar_nonneg (i + N)
    have hb := hbd (i + N) (Nat.le_add_left N i)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hvar, mul_comm]
    exact mul_le_mul_of_nonneg_right hb hvar
  have hnorm : Summable
      (fun i => ‖invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm hmaj
  have h1 : ‖∑' i, invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁)‖
      ≤ ∑' i, ‖invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁)‖ :=
    norm_tsum_le_tsum_norm hnorm
  have h2 : ∑' i, ‖invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁)‖
      ≤ ∑' i, M * invLogVar (i + N) := Summable.tsum_mono hnorm hmaj hterm
  rw [tsum_mul_left, tsum_invLogVar_add hN] at h2
  rw [Real.norm_eq_abs] at h1
  linarith [h1, h2]

/-- A constant reciprocal is below the exponential shape. -/
theorem one_div_le_exp_neg_sqrt_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, 1 / x ≤ Real.exp (-c * Real.sqrt (Real.log x)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (c ^ 2))] with x hx1 hL
  have hx0 : (0 : ℝ) < x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := le_trans (le_max_left _ _) hL
  have hLc : c ^ 2 ≤ Real.log x := le_trans (le_max_right _ _) hL
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hs : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt (by linarith)
  have hcs : c ≤ Real.sqrt (Real.log x) := by nlinarith [hs, hs0, hLc, hc]
  have hkey : c * Real.sqrt (Real.log x) ≤ Real.log x := by nlinarith [hs, hs0, hcs, hc]
  rw [div_le_iff₀ hx0]
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (Real.log x - c * Real.sqrt (Real.log x)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-c * Real.sqrt (Real.log x)) * Real.exp (Real.log x) := by
        rw [← Real.exp_add]; congr 1; ring
    _ = Real.exp (-c * Real.sqrt (Real.log x)) * x := by rw [Real.exp_log hx0]

/-- **Mertens' second theorem with an exponential error term.**  The constant is the corpus's own
`meisselMertensConst`; only the error improves, from `O(1/log N)` to `O(exp(−c√(log N)))`. -/
theorem exists_mertensS_sub_logLog_sub_const_exp_rate :
    ∃ B c : ℝ, 0 < c ∧ 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |mertensS N - logLog N - meisselMertensConst|
        ≤ B * Real.exp (-c * Real.sqrt (Real.log N)) := by
  obtain ⟨c₁, B₀, c, hc0, hB0, hrate⟩ := exists_mertensA_sub_log_exp_rate
  -- transfer the real-variable bound to natural numbers
  have hratN : ∀ᶠ n : ℕ in atTop,
      |mertensA n - Real.log n - c₁| ≤ B₀ * Real.exp (-c * Real.sqrt (Real.log n)) := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hrate
    filter_upwards [this] with n hn
    rwa [Nat.floor_natCast] at hn
  rw [eventually_atTop] at hratN
  obtain ⟨N₀, hN₀⟩ := hratN
  have hone : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) ≤ Real.exp (-c * Real.sqrt (Real.log n)) := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (one_div_le_exp_neg_sqrt_log hc0)
    exact this
  refine ⟨2 * B₀ + 1, c, hc0, by linarith, ?_⟩
  filter_upwards [hone, eventually_ge_atTop (max N₀ 3)] with N hN1 hNge
  have hN0' : N₀ ≤ N := le_trans (le_max_left _ _) hNge
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hNge
  have hN2 : 2 ≤ N := by omega
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  set E : ℝ := Real.exp (-c * Real.sqrt (Real.log N)) with hE
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  -- the uniform bound on `ε` past `N`
  have hM : ∀ i : ℕ, N ≤ i → |mertensA i - Real.log i - c₁| ≤ B₀ * E := by
    intro i hi
    have hiN₀ : N₀ ≤ i := le_trans hN0' hi
    have hmono : Real.exp (-c * Real.sqrt (Real.log i)) ≤ E := by
      refine Real.exp_le_exp.mpr ?_
      have hlog : Real.log N ≤ Real.log i :=
        Real.log_le_log (by linarith) (by exact_mod_cast hi)
      have := Real.sqrt_le_sqrt hlog
      nlinarith [Real.sqrt_nonneg (Real.log N), this, hc0]
    exact le_trans (hN₀ i hiN₀) (mul_le_mul_of_nonneg_left hmono hB0)
  -- the three remainders
  have heq := mertensS_sub_logLog_sub_const_eq hN2
  have hsplit := tsum_mertensRemTerm_add_eq hN2 c₁
  have hfrac : (mertensA N - Real.log N) / Real.log N
      = c₁ * (1 / Real.log N) + (mertensA N - Real.log N - c₁) / Real.log N := by
    field_simp
    ring
  have hcollapse : mertensS N - logLog N - meisselMertensConst
      = (mertensA N - Real.log N - c₁) / Real.log N
        + (∑' i, logLogDefect (i + N))
        - ∑' i, invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁) := by
    rw [heq, hfrac, hsplit]
    ring
  rw [hcollapse]
  -- bound each remainder
  have hb1 : |(mertensA N - Real.log N - c₁) / Real.log N| ≤ B₀ * E := by
    rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log N)]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log N)]
    have hthis := hM N le_rfl
    have hBE : (0 : ℝ) ≤ B₀ * E := by positivity
    have hstep : B₀ * E ≤ B₀ * E * Real.log N := by
      nlinarith [mul_nonneg hBE (show (0 : ℝ) ≤ Real.log N - 1 by linarith)]
    linarith [hthis, hstep]
  have hb2 : |∑' i, logLogDefect (i + N)| ≤ E := by
    have hnn : (0 : ℝ) ≤ ∑' i, logLogDefect (i + N) :=
      tsum_nonneg fun i => logLogDefect_nonneg _
    have hle := tsum_logLogDefect_add_le hN2
    have hinv : 1 / (N : ℝ) * (1 / Real.log N) ≤ 1 / (N : ℝ) := by
      have hN0 : (0 : ℝ) < 1 / (N : ℝ) := by
        have : (0 : ℝ) < (N : ℝ) := by linarith
        positivity
      have : 1 / Real.log N ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      nlinarith
    rw [abs_of_nonneg hnn]
    linarith [hle, hinv, hN1]
  have hb3 : |∑' i, invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁)|
      ≤ B₀ * E := by
    have h := abs_tsum_invLogVar_mul_centred_le hN2 (M := B₀ * E) hM
    have hinv : B₀ * E * (1 / Real.log N) ≤ B₀ * E := by
      have hBE : (0 : ℝ) ≤ B₀ * E := by positivity
      have : 1 / Real.log N ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      nlinarith
    linarith [h, hinv]
  have htri := abs_sub ((mertensA N - Real.log N - c₁) / Real.log N
    + ∑' i, logLogDefect (i + N))
    (∑' i, invLogVar (i + N) * (mertensA (i + N) - Real.log ((i + N : ℕ) : ℝ) - c₁))
  have htri2 := abs_add_le ((mertensA N - Real.log N - c₁) / Real.log N)
    (∑' i, logLogDefect (i + N))
  have hexpand : (2 * B₀ + 1) * E = B₀ * E + E + B₀ * E := by ring
  linarith [htri, htri2, hb1, hb2, hb3, hexpand]

end RHTower.Sieve
