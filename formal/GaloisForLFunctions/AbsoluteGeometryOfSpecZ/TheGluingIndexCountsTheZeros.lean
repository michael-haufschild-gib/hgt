import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGraphsAreGluedAlongTheirContacts
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.ZetaZeroCountUpperBound
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder
import GaloisForLFunctions.RHTower.ZeroCountRemainderNotIntegrable

/-!
# The gluing index counts the zeros

The first `N` Frobenius graphs of the arithmetic square form a lattice of index `N!` in `ℤ^N`
(`det_necklaceMatrix`): the graph `Γ_n` is glued to the graphs below it by `Σ_{k ∣ n} Λ(k) = log n`
conditions, in logarithmic measure. A window of `N` degrees resolves the zeros of `ζ` up to the
height `2πN`.

* **Stirling** (`log_factorial_lower`, `log_factorial_upper`):
  `N log N − N ≤ log N! ≤ N log N − N + log N + 1`.
* **The gluing index is the main term of the zero count at the height `2πN`**
  (`abs_log_det_necklaceMatrix_sub_zeroCountMain_le`):
  `|log det − N₀(2πN)| ≤ log N + 1`, where `N₀(T) = (T/2π)(log(T/2π) − 1)`.
* **Degree by degree** (`det_necklaceMatrix_succ`, `abs_zeroCountMain_succ_sub_log_le`): `Γ_{n+1}`
  multiplies the index by `n + 1`, and `N₀(2π(n+1)) − N₀(2πn) = log(n + 1) + O(1/n)`.
* **It is asymptotic to the zero count** (`eventually_abs_log_factorial_sub_xiZeroCount_le`): for
  every `ε > 0` and all large `N`, `|log N! − N(2πN)| ≤ ε N log N`, with `N(T)` the number of zeros
  of `ξ` of ordinate in `(0, T]`.
* **It is the zero count up to `O(log N)`** (`exists_abs_log_factorial_sub_xiZeroCount_le_log`):
  `|log N! − N(2πN)| ≤ C log N` for all large `N`. The smooth Riemann–von Mangoldt term at the
  height `2πN` is `N log N − N + 7/8`, Stirling's main term.
* **What it misses is the remainder** (`tendsto_log_factorial_sub_smoothCount`,
  `tendsto_log_factorial_sub_xiZeroCount_add_rvmRemainder`): at the midpoint heights
  `T_N = 2π(N + ½)`, `log N! − M(T_N) → ½ log 2π − 7/8` with `M` the smooth count, so
  `log N! = N(T_N) − S(T_N) + ½ log 2π − 7/8 + o(1)` with `S = N − M` the remainder of the zero
  count.

Each degree `n` carries `log n` gluing conditions and each unit of height `2π` at height `2πn`
carries `log n` zeros: the arithmetic genus of the union of the first `N` graphs grows as the number
of conjugate pairs of zeros that `N` degrees resolve. The square counts the zeros; it does not
place them.
-/

open Filter Topology Real

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- `log(n + 1) − log n ≤ 1/n`. -/
theorem log_succ_sub_log_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn0.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) hn0)
  have e : ((n : ℝ) + 1) / n - 1 = 1 / (n : ℝ) := by field_simp; ring
  linarith

/-- `1/(n + 1) ≤ log(n + 1) − log n`. -/
theorem inv_succ_le_log_succ_sub_log {n : ℕ} (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn0.ne']
  have h := Real.one_sub_inv_le_log_of_pos (div_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) hn0)
  have e : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by field_simp; ring
  linarith

/-- **Stirling, lower bound**: `N log N − N ≤ log N!`. -/
theorem log_factorial_lower (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h := log_succ_sub_log_le hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have h' : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
        calc (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ (n : ℝ) * (1 / (n : ℝ)) :=
              mul_le_mul_of_nonneg_left h hn0.le
          _ = 1 := by field_simp
      nlinarith

/-- **Stirling, upper bound**: `log N! ≤ N log N − N + log N + 1` for `N ≥ 1`. -/
theorem log_factorial_upper {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N - N + Real.log N + 1 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    have h := inv_succ_le_log_succ_sub_log hn
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h' : 1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
      calc (1 : ℝ) = ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := by field_simp
        _ ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) :=
            mul_le_mul_of_nonneg_left h hn0.le
    nlinarith

/-- **The gluing index of the first `N` graphs is the main term of the zero count at the height
`2πN`**, up to `log N + 1`. -/
theorem abs_log_det_necklaceMatrix_sub_zeroCountMain_le {N : ℕ} (hN : 1 ≤ N) :
    |Real.log (((necklaceMatrix N).det : ℤ) : ℝ) - RHTower.zeroCountMain (2 * π * N)| ≤
      Real.log N + 1 := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hmain : RHTower.zeroCountMain (2 * π * N) = (N : ℝ) * Real.log N - N := by
    unfold RHTower.zeroCountMain
    rw [mul_div_cancel_left₀ _ hpi.ne']
    ring
  rw [det_necklaceMatrix, Int.cast_natCast, hmain, abs_le]
  have h1 := log_factorial_lower N
  have h2 := log_factorial_upper hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  constructor <;> linarith

/-- **Degree by degree.** The graph `Γ_{n+1}` multiplies the gluing index by `n + 1`, and the main
term of the zero count over the height window `[2πn, 2π(n + 1)]` is `log(n + 1)` up to
`1/(n + 1)`. -/
theorem abs_zeroCountMain_succ_sub_log_le {n : ℕ} (hn : 1 ≤ n) :
    |RHTower.zeroCountMain (2 * π * ((n : ℝ) + 1)) - RHTower.zeroCountMain (2 * π * n) -
        Real.log ((n : ℝ) + 1)| ≤ 1 / ((n : ℝ) + 1) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmain : ∀ x : ℝ, RHTower.zeroCountMain (2 * π * x) = x * Real.log x - x := by
    intro x
    unfold RHTower.zeroCountMain
    rw [mul_div_cancel_left₀ _ hpi.ne']
    ring
  rw [hmain, hmain]
  have h1 := log_succ_sub_log_le hn
  have h2 := inv_succ_le_log_succ_sub_log hn
  have hup : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
    calc (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ (n : ℝ) * (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hn0.le
      _ = 1 := by field_simp
  have hlow : (n : ℝ) / ((n : ℝ) + 1) ≤ (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
    calc (n : ℝ) / ((n : ℝ) + 1) = (n : ℝ) * (1 / ((n : ℝ) + 1)) := by ring
      _ ≤ (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) :=
          mul_le_mul_of_nonneg_left h2 hn0.le
  have he : (n : ℝ) / ((n : ℝ) + 1) = 1 - 1 / ((n : ℝ) + 1) := by field_simp; ring
  rw [abs_le]
  constructor <;> nlinarith

theorem det_necklaceMatrix_succ (n : ℕ) :
    (necklaceMatrix (n + 1)).det = ((n + 1 : ℕ) : ℤ) * (necklaceMatrix n).det := by
  rw [det_necklaceMatrix, det_necklaceMatrix, Nat.factorial_succ]
  push_cast
  ring

/-- **The gluing index is asymptotic to the number of zeros below the height `2πN`.** -/
theorem eventually_abs_log_factorial_sub_xiZeroCount_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |Real.log (N.factorial : ℝ) - (RHTower.xiZeroCount (2 * π * N) : ℝ)| ≤
        ε * ((N : ℝ) * Real.log N) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h2pi : (1 : ℝ) < 2 * π := by nlinarith [Real.pi_gt_three]
  have hL2pi : 0 < Real.log (2 * π) := Real.log_pos h2pi
  obtain ⟨T₀, -, hT⟩ := RHTower.exists_xiZeroCount_close (ε / (16 * π)) (by positivity)
  set M : ℝ := max (4 * Real.log (2 * π) / ε) (6 / ε) with hM
  filter_upwards [eventually_ge_atTop (max (max ⌈T₀⌉₊ 7) ⌈Real.exp M⌉₊)] with N hN
  have hN1 : ⌈T₀⌉₊ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN7 : 7 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNe : ⌈Real.exp M⌉₊ ≤ N := (le_max_right _ _).trans hN
  have hN7' : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN7
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogM : M ≤ Real.log N := by
    have h1 : Real.exp M ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNe)
    calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos M) h1
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hm1 : 4 * Real.log (2 * π) / ε ≤ Real.log N := (le_max_left _ _).trans hlogM
  have hm2 : 6 / ε ≤ Real.log N := (le_max_right _ _).trans hlogM
  have hm1' : 4 * Real.log (2 * π) ≤ ε * Real.log N := by
    rw [div_le_iff₀ hε] at hm1; linarith
  have hm2' : 6 ≤ ε * Real.log N := by
    rw [div_le_iff₀ hε] at hm2; linarith
  -- the three pieces of the comparison
  have hT' : T₀ ≤ 2 * π * N := by
    have h1 : T₀ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN1)
    nlinarith
  have hrvm := hT (2 * π * N) hT'
  have hlogT : Real.log (2 * π * N) = Real.log (2 * π) + Real.log N :=
    Real.log_mul (by positivity) hN0.ne'
  have hlogT2 : Real.log (2 * π * N) ≤ 2 * Real.log N := by
    rw [hlogT]
    have : Real.log (2 * π) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by linarith [Real.pi_lt_d2])
    linarith
  have hmainT : 1 / (2 * π) * (2 * π * N * Real.log (2 * π * N)) =
      (N : ℝ) * Real.log (2 * π) + N * Real.log N := by
    rw [hlogT]; field_simp
  have hB1 : ε / (16 * π) * (2 * π * N * Real.log (2 * π * N)) ≤ ε / 4 * (N * Real.log N) := by
    have h1 : ε / (16 * π) * (2 * π * N * Real.log (2 * π * N)) =
        ε / 8 * (N * Real.log (2 * π * N)) := by field_simp; ring
    rw [h1]
    have h2 : (N : ℝ) * Real.log (2 * π * N) ≤ N * (2 * Real.log N) :=
      mul_le_mul_of_nonneg_left hlogT2 hN0.le
    nlinarith
  have hB2 : (N : ℝ) * Real.log (2 * π) ≤ ε / 4 * (N * Real.log N) := by nlinarith
  have hlower := log_factorial_lower N
  have hupper := log_factorial_upper (by omega : 1 ≤ N)
  have hlogle : Real.log (N : ℝ) ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
  have hB3 : (N : ℝ) + Real.log N + 1 ≤ ε / 2 * (N * Real.log N) := by nlinarith
  rw [hmainT] at hrvm
  rw [abs_le] at hrvm ⊢
  constructor <;> nlinarith [hrvm.1, hrvm.2]

/-- The smooth Riemann–von Mangoldt count at the height `2πx` is `x log x − x + 7/8`. -/
theorem routeKSmoothRVMCount_two_pi_mul {x : ℝ} (hx : 0 < x) :
    RHTower.routeKSmoothRVMCount (2 * π * x) = x * Real.log x - x + 7 / 8 := by
  have h2pi : (2 * π) ≠ 0 := by positivity
  unfold RHTower.routeKSmoothRVMCount RHTower.routeKRVMBase
  rw [mul_div_cancel_left₀ _ h2pi, mul_div_mul_left _ _ h2pi,
    Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp]
  ring

/-- **The gluing index is the number of zeros below the height `2πN` up to `O(log N)`.** -/
theorem exists_abs_log_factorial_sub_xiZeroCount_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |Real.log (N.factorial : ℝ) - (RHTower.xiZeroCount (2 * π * N) : ℝ)| ≤ C * Real.log N := by
  obtain ⟨C, hC, T₀, -, hrem⟩ := RHTower.exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  refine ⟨2 * C + 3, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max ⌈T₀⌉₊ 7)] with N hN
  have hN1 : ⌈T₀⌉₊ ≤ N := (le_max_left _ _).trans hN
  have hN7 : 7 ≤ N := (le_max_right _ _).trans hN
  have hN7' : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN7
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hT' : T₀ ≤ 2 * π * N := by
    have h1 : T₀ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN1)
    nlinarith [Real.pi_gt_three]
  have hrvm := hrem (2 * π * N) hT'
  rw [routeKSmoothRVMCount_two_pi_mul hN0] at hrvm
  have hlogT2 : Real.log (2 * π * N) ≤ 2 * Real.log N := by
    rw [Real.log_mul (by positivity) hN0.ne']
    have : Real.log (2 * π) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by linarith [Real.pi_lt_d2])
    linarith
  have hCl : C * Real.log (2 * π * N) ≤ C * (2 * Real.log N) :=
    mul_le_mul_of_nonneg_left hlogT2 hC.le
  have hlog1 : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hN0]
    linarith [Real.exp_one_lt_d9]
  have hlower := log_factorial_lower N
  have hupper := log_factorial_upper (by omega : 1 ≤ N)
  rw [abs_le] at hrvm ⊢
  constructor <;> nlinarith [hrvm.1, hrvm.2]

/-! ### The defect of the count -/

/-- Stirling's formula in logarithmic form: `log N! − (N log N − N) − ½ log 2N → ½ log π`. -/
theorem tendsto_log_factorial_sub_stirling :
    Tendsto (fun N : ℕ => Real.log (N.factorial : ℝ) -
      (Real.log (2 * (N : ℝ)) / 2 + N * (Real.log N - 1))) atTop (𝓝 (Real.log π / 2)) := by
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have h := (Real.continuousAt_log hpi.ne').tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
  rw [Real.log_sqrt Real.pi_pos.le] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : 0 < N := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : ((N.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply, Stirling.stirlingSeq]
  rw [Real.log_div hf (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_pow, Real.log_div hN0.ne' (Real.exp_pos 1).ne',
    Real.log_exp]

/-- **Stirling at the midpoint**: the gluing index of the first `N` graphs is the smooth
Riemann–von Mangoldt count at the height `2π(N + ½)`, up to the constant `½ log 2π − 7/8`. -/
theorem tendsto_log_factorial_sub_smoothCount :
    Tendsto (fun N : ℕ => Real.log (N.factorial : ℝ) -
      RHTower.routeKSmoothRVMCount (2 * π * ((N : ℝ) + 1 / 2))) atTop
      (𝓝 (Real.log (2 * π) / 2 - 7 / 8)) := by
  have hL : Tendsto (fun N : ℕ => ((N : ℝ) + 1 / 2) * Real.log (1 + 1 / 2 / (N : ℝ))) atTop
      (𝓝 (1 / 2)) := by
    have h1 := (Real.tendsto_mul_log_one_add_div_atTop (1 / 2)).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => 1 / 2 * Real.log (1 + 1 / 2 / (N : ℝ))) atTop (𝓝 0) := by
      have hdiv : Tendsto (fun N : ℕ => (1 : ℝ) + 1 / 2 / (N : ℝ)) atTop (𝓝 1) := by
        have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).div_atTop
          (tendsto_natCast_atTop_atTop (R := ℝ))
        have h' := (tendsto_const_nhds (x := (1 : ℝ))).add h
        rwa [add_zero] at h'
      have hlog := ((Real.continuousAt_log one_ne_zero).tendsto.comp hdiv).const_mul (1 / 2)
      rwa [Real.log_one, mul_zero] at hlog
    have h := h1.add h2
    rw [add_zero] at h
    refine h.congr fun N => ?_
    simp only [Function.comp_apply]
    ring
  have hlim := (tendsto_log_factorial_sub_stirling.add_const
    (Real.log 2 / 2 + 1 / 2 - 7 / 8)).sub hL
  have hval : Real.log π / 2 + (Real.log 2 / 2 + 1 / 2 - 7 / 8) - 1 / 2 =
      Real.log (2 * π) / 2 - 7 / 8 := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : (N : ℝ) + 1 / 2 = N * (1 + 1 / 2 / (N : ℝ)) := by field_simp
  have hlogsum : Real.log ((N : ℝ) + 1 / 2) = Real.log N + Real.log (1 + 1 / 2 / (N : ℝ)) := by
    rw [hsplit, Real.log_mul hN0.ne' (by positivity)]
  rw [routeKSmoothRVMCount_two_pi_mul (by positivity), hlogsum,
    Real.log_mul (by norm_num) hN0.ne']
  ring

/-- **What the square misses is the remainder of the zero count.** With `S = N − M` the
remainder, `log N! − N(T_N) + S(T_N) → ½ log 2π − 7/8` at the heights `T_N = 2π(N + ½)`. -/
theorem tendsto_log_factorial_sub_xiZeroCount_add_rvmRemainder :
    Tendsto (fun N : ℕ => Real.log (N.factorial : ℝ) -
        (RHTower.xiZeroCount (2 * π * ((N : ℝ) + 1 / 2)) : ℝ) +
        RHTower.rvmRemainder (2 * π * ((N : ℝ) + 1 / 2))) atTop
      (𝓝 (Real.log (2 * π) / 2 - 7 / 8)) := by
  refine tendsto_log_factorial_sub_smoothCount.congr fun N => ?_
  unfold RHTower.rvmRemainder RHTower.zeroCountReal
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
