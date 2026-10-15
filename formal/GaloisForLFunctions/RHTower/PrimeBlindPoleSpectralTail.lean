import GaloisForLFunctions.RHTower.PrimeBlindKernelSpectral

/-!
# The pole tail of a blind kernel is controlled by spectral mass at exponential frequency

Let `K_c` be the even autocorrelation of a nonnegative blind combination, with spectral density
`ρ_c ≥ 0`.  On the gap `[log n, log(n+1)]` the split gap estimate with threshold `n` gives
`|K_c| ≤ 2 μ_{≥n} + (1/n) I_{<n}`, where `μ_{≥n} = ∫_{|τ| ≥ n} ρ_c` and `I_{<n} = ∫_{|τ| < n} |τ| ρ_c`.
Integrating against `2cosh(x/2) ≤ 2√(n+1)` over the gap of length `≤ 1/n` and summing the gaps from
`n₀ = ⌊e^X⌋` on, the two telescoping sums
`Σ_{n ≤ t} n^{-1/2} ≤ 2√t` and `Σ_{n > t} n^{-3/2} ≤ 2 (⌊t⌋)^{-1/2}` give

  `∫_{X}^{2L} |K_c(x)| 2cosh(x/2) dx ≤ 20 ∫_{|τ| ≥ n₀} √|τ| ρ_c + (6/√(n₀−1)) ∫_{|τ| < n₀} |τ| ρ_c`

(`integral_abs_blindKernel_tail_le`).  Negative lag mass beyond lag `X` therefore needs spectral
mass at frequencies `≥ e^X/2`, weighted by `√|τ|`, or low-frequency first moment damped by
`e^{−X/2}`: this is the quantitative form of the exponential uncertainty principle of blind kernels
(lag `x` ↔ frequency `e^x`).  At `X = log 2` it yields the pole floor with weight `√|τ|`,
`P(c) ≥ −(4·mass(c) + 58 ∫ √|τ| ρ_c)` (`nodePoleMass_ge_sqrt_moment`), replacing the curvature
term of `PrimeBlindPoleCurvatureFloor` by the half moment of the spectral measure.
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped Interval

namespace RHTower.WeilOneSided

noncomputable section

/-! ## Two telescoping sums -/

theorem one_div_sqrt_succ_le (m : ℕ) :
    1 / Real.sqrt ((m : ℝ) + 1) ≤ 2 * Real.sqrt ((m : ℝ) + 1) - 2 * Real.sqrt m := by
  have hs : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ m + 1 by positivity)
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity)
  rw [div_le_iff₀ hs]
  nlinarith [sq_nonneg (Real.sqrt ((m : ℝ) + 1) - Real.sqrt m), Real.sqrt_nonneg (m : ℝ)]

/-- `Σ_{n=1}^{m} n^{-1/2} ≤ 2√m`. -/
theorem sum_one_div_sqrt_le (m : ℕ) :
    ∑ n ∈ Finset.Icc 1 m, 1 / Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := one_div_sqrt_succ_le m
    push_cast
    linarith

theorem one_div_mul_sqrt_le {n : ℕ} (hn : 2 ≤ n) :
    1 / ((n : ℝ) * Real.sqrt n) ≤ 2 / Real.sqrt ((n : ℝ) - 1) - 2 / Real.sqrt n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ n - 1 by linarith)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ n by linarith)
  set r := Real.sqrt ((n : ℝ) - 1) with hr_def
  set s := Real.sqrt (n : ℝ) with hs_def
  have key : r * (1 + 2 * n) ≤ 2 * n * s := by
    have h2 : (r * (1 + 2 * n)) ^ 2 ≤ (2 * n * s) ^ 2 := by
      rw [mul_pow, hr2, mul_pow, mul_pow, hs2]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2
  rw [div_sub_div _ _ hr.ne' hs.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right key hs.le]

/-- `Σ_{n=m}^{N-1} n^{-3/2} ≤ 2 (m−1)^{-1/2}` for `m ≥ 2`. -/
theorem sum_one_div_mul_sqrt_le {m : ℕ} (hm : 2 ≤ m) (N : ℕ) :
    ∑ n ∈ Finset.Ico m N, 1 / ((n : ℝ) * Real.sqrt n) ≤ 2 / Real.sqrt ((m : ℝ) - 1) := by
  have key : ∀ k : ℕ, ∑ n ∈ Finset.Ico m (m + k), 1 / ((n : ℝ) * Real.sqrt n) ≤
      2 / Real.sqrt ((m : ℝ) - 1) - 2 / Real.sqrt ((m : ℝ) + k - 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
      have h := one_div_mul_sqrt_le (n := m + k) (by omega)
      push_cast at h ⊢
      have e : (m : ℝ) + (k + 1) - 1 = (m : ℝ) + k := by ring
      rw [e]
      linarith
  rcases le_or_gt N m with hNm | hNm
  · rw [Finset.Ico_eq_empty_of_le hNm, Finset.sum_empty]
    positivity
  · obtain ⟨k, rfl⟩ : ∃ k, N = m + k := ⟨N - m, by omega⟩
    refine (key k).trans ?_
    have : 0 ≤ 2 / Real.sqrt ((m : ℝ) + k - 1) := by positivity
    linarith

/-! ## Elementary bounds on the gaps -/

theorem gap_log_le {n : ℕ} (hn : 1 ≤ n) : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hnpos.ne']
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
  have h2 : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
  linarith

theorem gap_log_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  linarith [Real.log_le_log hnpos (by linarith : (n : ℝ) ≤ n + 1)]

theorem two_cosh_half_log_le {m : ℝ} (hm : 1 ≤ m) :
    2 * Real.cosh (Real.log m / 2) ≤ 2 * Real.sqrt m := by
  rw [Real.cosh_eq, Real.exp_half, Real.exp_log (by linarith), Real.exp_neg, Real.exp_half,
    Real.exp_log (by linarith)]
  have hs : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm
  have : (Real.sqrt m)⁻¹ ≤ Real.sqrt m := (inv_le_one_of_one_le₀ hs).trans hs
  linarith

theorem sqrt_succ_div_le {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.sqrt ((n : ℝ) + 1) * (1 / n) ≤ 2 * Real.sqrt 2 / Real.sqrt n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have h1 : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt n := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hss : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have h2 : Real.sqrt ((n : ℝ) + 1) * Real.sqrt n ≤ Real.sqrt 2 * n := by
    calc Real.sqrt ((n : ℝ) + 1) * Real.sqrt n ≤ (Real.sqrt 2 * Real.sqrt n) * Real.sqrt n :=
          mul_le_mul_of_nonneg_right h1 hs.le
      _ = Real.sqrt 2 * (Real.sqrt n * Real.sqrt n) := by ring
      _ = Real.sqrt 2 * n := by rw [hss]
  rw [mul_one_div, div_le_div_iff₀ hnpos hs]
  linarith

/-! ## The per-gap bound -/

theorem measurableSet_abs_ge (T : ℝ) : MeasurableSet {τ : ℝ | T ≤ |τ|} :=
  measurableSet_le measurable_const continuous_abs.measurable

theorem measurableSet_abs_lt (T : ℝ) : MeasurableSet {τ : ℝ | |τ| < T} :=
  measurableSet_lt continuous_abs.measurable measurable_const

/-- The high-frequency mass `∫_{|τ| ≥ T} ρ_c` and the low-frequency first moment
`∫_{|τ| < T} |τ| ρ_c`. -/
def highMass (c : WeilTestFn →₀ ℝ) (T : ℝ) : ℝ := ∫ τ in {τ : ℝ | T ≤ |τ|}, specDensityC c τ

def lowMoment (c : WeilTestFn →₀ ℝ) (T : ℝ) : ℝ := ∫ τ in {τ : ℝ | |τ| < T}, |τ| * specDensityC c τ

theorem highMass_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (T : ℝ) : 0 ≤ highMass c T :=
  setIntegral_nonneg (measurableSet_abs_ge T) fun τ _ => specDensityC_nonneg hc τ

theorem lowMoment_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (T : ℝ) : 0 ≤ lowMoment c T :=
  setIntegral_nonneg (measurableSet_abs_lt T) fun τ _ =>
    mul_nonneg (abs_nonneg _) (specDensityC_nonneg hc τ)

/-- On the gap `[log n, log(n+1)]` the blind kernel is at most `2 μ_{≥n} + (1/n) I_{<n}`. -/
theorem abs_blindKernel_le_gap {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (hv : nodeVector c = 0)
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc (Real.log n) (Real.log ((n : ℝ) + 1))) :
    |blindKernel c x| ≤ 2 * highMass c n + (1 / n) * lowMoment c n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hab : Real.log n < Real.log ((n : ℝ) + 1) := Real.log_lt_log hnpos (by linarith)
  have ha : blindKernel c (Real.log n) = 0 := blindKernel_log_eq_zero hv hn
  have hb : blindKernel c (Real.log ((n : ℝ) + 1)) = 0 := by
    have := blindKernel_log_eq_zero hv (n := n + 1) (by omega)
    push_cast at this
    exact this
  have h := abs_blindKernel_le_of_eq_zero_endpoints_split hc hab ha hb hx (n : ℝ)
  have hg := gap_log_le (by omega : 1 ≤ n)
  have hI := lowMoment_nonneg hc (n : ℝ)
  unfold highMass lowMoment at *
  calc |blindKernel c x| ≤ _ := h
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hg hI)

/-- The bound for the pole integral over one gap. -/
def gapBound (c : WeilTestFn →₀ ℝ) (n : ℕ) : ℝ :=
  2 * Real.sqrt 2 / Real.sqrt n * (2 * highMass c n + (1 / n) * lowMoment c n)

theorem integral_gap_le {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (hv : nodeVector c = 0) {n : ℕ}
    (hn : 2 ≤ n) :
    ∫ x in Real.log n..Real.log ((n : ℝ) + 1), |blindKernel c x| * (2 * Real.cosh (x / 2)) ≤
      gapBound c n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hab : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hnpos (by linarith)
  set A := 2 * highMass c n + (1 / n) * lowMoment c n with hA
  have hA0 : 0 ≤ A := by
    have := highMass_nonneg hc (n : ℝ)
    have := lowMoment_nonneg hc (n : ℝ)
    positivity
  have hbound : ∀ x ∈ Ι (Real.log n) (Real.log ((n : ℝ) + 1)),
      ‖|blindKernel c x| * (2 * Real.cosh (x / 2))‖ ≤ A * (2 * Real.sqrt ((n : ℝ) + 1)) := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hx' : x ∈ Icc (Real.log n) (Real.log ((n : ℝ) + 1)) := ⟨hx.1.le, hx.2⟩
    have h1 := abs_blindKernel_le_gap hc hv hn hx'
    have h2 : 2 * Real.cosh (x / 2) ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
      refine le_trans ?_ (two_cosh_half_log_le (m := (n : ℝ) + 1) (by linarith))
      have hx0 : 0 ≤ x := hlog0.trans hx.1.le
      have hlog1 : 0 ≤ Real.log ((n : ℝ) + 1) := hlog0.trans hab
      have : Real.cosh (x / 2) ≤ Real.cosh (Real.log ((n : ℝ) + 1) / 2) := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith [hx.2]
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (by positivity))]
    exact mul_le_mul h1 h2 (by positivity) hA0
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (gap_log_nonneg (by omega))] at h
  have hg := gap_log_le (by omega : 1 ≤ n)
  have hle : ∫ x in Real.log n..Real.log ((n : ℝ) + 1), |blindKernel c x| * (2 * Real.cosh (x / 2)) ≤
      A * (2 * Real.sqrt ((n : ℝ) + 1)) * (1 / n) := by
    refine (le_abs_self _).trans (h.trans ?_)
    exact mul_le_mul_of_nonneg_left hg (by positivity)
  have h3 := sqrt_succ_div_le (by omega : 1 ≤ n)
  calc _ ≤ A * (2 * Real.sqrt ((n : ℝ) + 1)) * (1 / n) := hle
    _ = A * (2 * Real.sqrt ((n : ℝ) + 1) * (1 / n)) := by ring
    _ ≤ A * (2 * Real.sqrt 2 / Real.sqrt n) := mul_le_mul_of_nonneg_left h3 hA0
    _ = gapBound c n := by unfold gapBound; ring

/-! ## The gaps tile the lag interval -/

theorem integral_eq_sum_gaps {g : ℝ → ℝ} (hg : Continuous g) (n₀ k : ℕ) :
    ∫ x in Real.log n₀..Real.log ((n₀ : ℝ) + k), g x =
      ∑ n ∈ Finset.Ico n₀ (n₀ + k), ∫ x in Real.log n..Real.log ((n : ℝ) + 1), g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), ← ih]
    push_cast
    rw [show (n₀ : ℝ) + k + 1 = (n₀ : ℝ) + (k + 1) by ring]
    exact (intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)).symm

/-! ## The gap bounds as spectral integrals -/

/-- The weight produced by the gap `n` at frequency `τ`. -/
def gapWeight (n : ℕ) (τ : ℝ) : ℝ :=
  2 * Real.sqrt 2 / Real.sqrt n *
    (2 * (if (n : ℝ) ≤ |τ| then 1 else 0) + |τ| / n * (if |τ| < n then 1 else 0))

theorem gapWeight_nonneg (n : ℕ) (τ : ℝ) : 0 ≤ gapWeight n τ := by
  unfold gapWeight
  split_ifs <;> positivity

theorem integrable_specDensityC_mul_gapWeight (c : WeilTestFn →₀ ℝ) (n : ℕ) :
    Integrable fun τ => specDensityC c τ * gapWeight n τ := by
  have e : (fun τ => specDensityC c τ * gapWeight n τ) = fun τ =>
      2 * Real.sqrt 2 / Real.sqrt n *
        (2 * ({τ : ℝ | (n : ℝ) ≤ |τ|}.indicator (specDensityC c) τ) +
          (1 / n) * ({τ : ℝ | |τ| < n}.indicator (fun τ => |τ| * specDensityC c τ) τ)) := by
    funext τ
    simp only [gapWeight, Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> ring
  rw [e]
  exact ((((integrable_specDensityC c).indicator (measurableSet_abs_ge _)).const_mul 2).add
    (((integrable_abs_mul_specDensityC c).indicator (measurableSet_abs_lt _)).const_mul
      _)).const_mul _

theorem gapBound_eq_integral (c : WeilTestFn →₀ ℝ) (n : ℕ) :
    gapBound c n = ∫ τ, specDensityC c τ * gapWeight n τ := by
  have e : (fun τ => specDensityC c τ * gapWeight n τ) = fun τ =>
      2 * Real.sqrt 2 / Real.sqrt n *
        (2 * ({τ : ℝ | (n : ℝ) ≤ |τ|}.indicator (specDensityC c) τ) +
          (1 / n) * ({τ : ℝ | |τ| < n}.indicator (fun τ => |τ| * specDensityC c τ) τ)) := by
    funext τ
    simp only [gapWeight, Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> ring
  rw [e, MeasureTheory.integral_const_mul,
    integral_add (((integrable_specDensityC c).indicator (measurableSet_abs_ge _)).const_mul 2)
      (((integrable_abs_mul_specDensityC c).indicator (measurableSet_abs_lt _)).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_indicator (measurableSet_abs_ge _), integral_indicator (measurableSet_abs_lt _)]
  rfl

/-! ## The pointwise bound on the summed gap weights -/

theorem gapWeight_le_split {n : ℕ} (hn : 2 ≤ n) (τ : ℝ) :
    gapWeight n τ ≤ 4 * Real.sqrt 2 * (if (n : ℝ) ≤ |τ| then 1 / Real.sqrt n else 0) +
      2 * Real.sqrt 2 * |τ| * (if |τ| < n then 1 / ((n : ℝ) * Real.sqrt n) else 0) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  unfold gapWeight
  by_cases h1 : (n : ℝ) ≤ |τ|
  · have h2 : ¬ |τ| < n := not_lt.mpr h1
    rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
    apply le_of_eq
    field_simp
    ring
  · have h2 : |τ| < n := lt_of_not_ge h1
    rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
    apply le_of_eq
    field_simp
    ring

theorem floor_ge_half {t : ℝ} (ht : 2 ≤ t) : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one t
  linarith

/-- The summed gap weights are bounded by `20√|τ|` beyond `n₀` and by `6|τ|/√(n₀−1)` below. -/
theorem sum_gapWeight_le {n₀ N : ℕ} (hn₀ : 2 ≤ n₀) (τ : ℝ) :
    ∑ n ∈ Finset.Ico n₀ N, gapWeight n τ ≤
      if (n₀ : ℝ) ≤ |τ| then 20 * Real.sqrt |τ| else 6 * |τ| / Real.sqrt ((n₀ : ℝ) - 1) := by
  have hsplit : ∑ n ∈ Finset.Ico n₀ N, gapWeight n τ ≤
      ∑ n ∈ Finset.Ico n₀ N, (4 * Real.sqrt 2 * (if (n : ℝ) ≤ |τ| then 1 / Real.sqrt n else 0) +
        2 * Real.sqrt 2 * |τ| * (if |τ| < n then 1 / ((n : ℝ) * Real.sqrt n) else 0)) :=
    Finset.sum_le_sum fun n hn => gapWeight_le_split
      (show 2 ≤ n by have := (Finset.mem_Ico.mp hn).1; omega) τ
  refine hsplit.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_filter,
    ← Finset.sum_filter]
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2' : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  by_cases hτ : (n₀ : ℝ) ≤ |τ|
  · rw [if_pos hτ]
    -- first sum: over n ≤ |τ|, contained in `Icc 1 ⌊|τ|⌋`
    have hA : ∑ n ∈ (Finset.Ico n₀ N).filter (fun n : ℕ => (n : ℝ) ≤ |τ|), 1 / Real.sqrt (n : ℝ) ≤
        2 * Real.sqrt |τ| := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Icc (1 : ℕ) ⌊|τ|⌋₊) ?_
        fun n _ _ => by positivity).trans ?_
      · intro n hn
        rw [Finset.mem_filter, Finset.mem_Ico] at hn
        rw [Finset.mem_Icc]
        exact ⟨by omega, Nat.le_floor hn.2⟩
      · refine (sum_one_div_sqrt_le _).trans ?_
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le (abs_nonneg τ)))
          (by norm_num)
    -- second sum: over n > |τ|, contained in `Ico (⌊|τ|⌋+1) N`
    have hfl : (2 : ℝ) ≤ |τ| := by
      have h2 : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
      linarith
    have hfl2 : 2 ≤ ⌊|τ|⌋₊ + 1 := by
      have := Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ |τ| by push_cast; linarith)
      omega
    have hB : ∑ n ∈ (Finset.Ico n₀ N).filter (fun n : ℕ => |τ| < (n : ℝ)), 1 / ((n : ℝ) * Real.sqrt n) ≤
        2 / Real.sqrt (⌊|τ|⌋₊ : ℝ) := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Ico (⌊|τ|⌋₊ + 1) N) ?_
        fun n _ _ => by positivity).trans ?_
      · intro n hn
        rw [Finset.mem_filter, Finset.mem_Ico] at hn
        rw [Finset.mem_Ico]
        exact ⟨(Nat.floor_lt (abs_nonneg τ)).mpr hn.2, hn.1.2⟩
      · have := sum_one_div_mul_sqrt_le hfl2 N
        push_cast at this
        rwa [add_sub_cancel_right] at this
    have hhalf : Real.sqrt |τ| / Real.sqrt 2 ≤ Real.sqrt (⌊|τ|⌋₊ : ℝ) := by
      rw [← Real.sqrt_div' _ (by norm_num)]
      exact Real.sqrt_le_sqrt (floor_ge_half hfl)
    have hτpos : 0 < Real.sqrt |τ| := Real.sqrt_pos.mpr (by linarith)
    have hC : 2 / Real.sqrt (⌊|τ|⌋₊ : ℝ) ≤ 2 * Real.sqrt 2 / Real.sqrt |τ| := by
      have hpos : 0 < Real.sqrt |τ| / Real.sqrt 2 := by positivity
      calc 2 / Real.sqrt (⌊|τ|⌋₊ : ℝ) ≤ 2 / (Real.sqrt |τ| / Real.sqrt 2) :=
            div_le_div_of_nonneg_left (by norm_num) hpos hhalf
        _ = 2 * Real.sqrt 2 / Real.sqrt |τ| := by rw [div_div_eq_mul_div]
    have h8 : 2 * Real.sqrt 2 * |τ| * (2 * Real.sqrt 2 / Real.sqrt |τ|) = 8 * Real.sqrt |τ| := by
      have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hd : |τ| / Real.sqrt |τ| = Real.sqrt |τ| := Real.div_sqrt
      calc 2 * Real.sqrt 2 * |τ| * (2 * Real.sqrt 2 / Real.sqrt |τ|)
          = (Real.sqrt 2 * Real.sqrt 2) * 4 * (|τ| / Real.sqrt |τ|) := by ring
        _ = 8 * Real.sqrt |τ| := by rw [h2, hd]; ring
    calc 4 * Real.sqrt 2 * ∑ n ∈ (Finset.Ico n₀ N).filter (fun n : ℕ => (n : ℝ) ≤ |τ|),
            1 / Real.sqrt (n : ℝ) +
          2 * Real.sqrt 2 * |τ| * ∑ n ∈ (Finset.Ico n₀ N).filter (fun n : ℕ => |τ| < (n : ℝ)),
            1 / ((n : ℝ) * Real.sqrt n)
        ≤ 4 * Real.sqrt 2 * (2 * Real.sqrt |τ|) +
          2 * Real.sqrt 2 * |τ| * (2 * Real.sqrt 2 / Real.sqrt |τ|) :=
          add_le_add (mul_le_mul_of_nonneg_left hA (by positivity))
            (mul_le_mul_of_nonneg_left (hB.trans hC) (by positivity))
      _ = 8 * Real.sqrt 2 * Real.sqrt |τ| + 8 * Real.sqrt |τ| := by
          rw [h8]; ring
      _ ≤ 20 * Real.sqrt |τ| := by nlinarith [Real.sqrt_nonneg |τ|]
  · rw [if_neg hτ]
    push Not at hτ
    -- first sum is empty, second sum is the full sum
    have hA : (Finset.Ico n₀ N).filter (fun n : ℕ => (n : ℝ) ≤ |τ|) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n hn
      have : (n₀ : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      push Not
      linarith
    have hB : ∑ n ∈ (Finset.Ico n₀ N).filter (fun n : ℕ => |τ| < (n : ℝ)), 1 / ((n : ℝ) * Real.sqrt n) ≤
        2 / Real.sqrt ((n₀ : ℝ) - 1) :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun n _ _ => by positivity).trans (sum_one_div_mul_sqrt_le hn₀ N)
    rw [hA, Finset.sum_empty, mul_zero, zero_add]
    have hpos : 0 < Real.sqrt ((n₀ : ℝ) - 1) := by
      refine Real.sqrt_pos.mpr ?_
      have : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
      linarith
    calc 2 * Real.sqrt 2 * |τ| * ∑ n ∈ (Finset.Ico n₀ N).filter (fun n : ℕ => |τ| < (n : ℝ)),
            1 / ((n : ℝ) * Real.sqrt n)
        ≤ 2 * Real.sqrt 2 * |τ| * (2 / Real.sqrt ((n₀ : ℝ) - 1)) := by gcongr
      _ = 4 * Real.sqrt 2 * |τ| / Real.sqrt ((n₀ : ℝ) - 1) := by ring
      _ ≤ 6 * |τ| / Real.sqrt ((n₀ : ℝ) - 1) := by
          rw [div_le_div_iff_of_pos_right hpos]
          nlinarith [abs_nonneg τ]

/-! ## The localized tail theorem -/

theorem integrable_specDensityC_mul_tailWeight {c : WeilTestFn →₀ ℝ} (n₀ : ℕ) :
    Integrable fun τ => specDensityC c τ *
      (if (n₀ : ℝ) ≤ |τ| then 20 * Real.sqrt |τ| else 6 * |τ| / Real.sqrt ((n₀ : ℝ) - 1)) := by
  have e : (fun τ => specDensityC c τ *
      (if (n₀ : ℝ) ≤ |τ| then 20 * Real.sqrt |τ| else 6 * |τ| / Real.sqrt ((n₀ : ℝ) - 1))) =
      fun τ => 20 * ({τ : ℝ | (n₀ : ℝ) ≤ |τ|}.indicator (fun τ => Real.sqrt |τ| * specDensityC c τ) τ)
        + (6 / Real.sqrt ((n₀ : ℝ) - 1)) *
          ({τ : ℝ | |τ| < n₀}.indicator (fun τ => |τ| * specDensityC c τ) τ) := by
    funext τ
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : (n₀ : ℝ) ≤ |τ|
    · rw [if_pos h, if_pos h, if_neg (not_lt.mpr h)]; ring
    · rw [if_neg h, if_neg h, if_pos (lt_of_not_ge h)]; ring
  rw [e]
  exact (((integrable_sqrt_mul_specDensityC c).indicator (measurableSet_abs_ge _)).const_mul _).add
    (((integrable_abs_mul_specDensityC c).indicator (measurableSet_abs_lt _)).const_mul _)

theorem integral_specDensityC_mul_tailWeight {c : WeilTestFn →₀ ℝ} (n₀ : ℕ) :
    ∫ τ, specDensityC c τ *
      (if (n₀ : ℝ) ≤ |τ| then 20 * Real.sqrt |τ| else 6 * |τ| / Real.sqrt ((n₀ : ℝ) - 1)) =
      20 * (∫ τ in {τ : ℝ | (n₀ : ℝ) ≤ |τ|}, Real.sqrt |τ| * specDensityC c τ) +
        (6 / Real.sqrt ((n₀ : ℝ) - 1)) * lowMoment c n₀ := by
  have e : (fun τ => specDensityC c τ *
      (if (n₀ : ℝ) ≤ |τ| then 20 * Real.sqrt |τ| else 6 * |τ| / Real.sqrt ((n₀ : ℝ) - 1))) =
      fun τ => 20 * ({τ : ℝ | (n₀ : ℝ) ≤ |τ|}.indicator (fun τ => Real.sqrt |τ| * specDensityC c τ) τ)
        + (6 / Real.sqrt ((n₀ : ℝ) - 1)) *
          ({τ : ℝ | |τ| < n₀}.indicator (fun τ => |τ| * specDensityC c τ) τ) := by
    funext τ
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : (n₀ : ℝ) ≤ |τ|
    · rw [if_pos h, if_pos h, if_neg (not_lt.mpr h)]; ring
    · rw [if_neg h, if_neg h, if_pos (lt_of_not_ge h)]; ring
  rw [e, integral_add (((integrable_sqrt_mul_specDensityC c).indicator
      (measurableSet_abs_ge _)).const_mul _)
    (((integrable_abs_mul_specDensityC c).indicator (measurableSet_abs_lt _)).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_indicator (measurableSet_abs_ge _), integral_indicator (measurableSet_abs_lt _)]
  rfl

/-- **Localized pole tail.**  For a nonnegative blind combination of level `L` and `log 2 ≤ X ≤ 2L`,
with `n₀ = ⌊e^X⌋`, the pole integrand beyond lag `X` is controlled by the `√|τ|`-weighted spectral
mass at frequencies `≥ n₀` and the first spectral moment below `n₀`, damped by `1/√(n₀ − 1)`. -/
theorem integral_abs_blindKernel_tail_le {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hv : nodeVector c = 0) {X Y : ℝ} (hX : Real.log 2 ≤ X) (hXY : X ≤ Y) :
    ∫ x in X..Y, |blindKernel c x| * (2 * Real.cosh (x / 2)) ≤
      20 * (∫ τ in {τ : ℝ | (⌊Real.exp X⌋₊ : ℝ) ≤ |τ|}, Real.sqrt |τ| * specDensityC c τ) +
        (6 / Real.sqrt ((⌊Real.exp X⌋₊ : ℝ) - 1)) * lowMoment c ⌊Real.exp X⌋₊ := by
  set n₀ : ℕ := ⌊Real.exp X⌋₊ with hn₀def
  have hex : 0 < Real.exp X := Real.exp_pos X
  have h2le : (2 : ℝ) ≤ Real.exp X := by
    rw [← Real.exp_log two_pos]; exact Real.exp_le_exp.mpr hX
  have hn₀ : 2 ≤ n₀ := by rw [hn₀def]; exact Nat.le_floor (by exact_mod_cast h2le)
  have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast (by omega : 0 < n₀)
  have hlogn₀ : Real.log n₀ ≤ X := by
    rw [← Real.log_exp X]; exact Real.log_le_log hn₀pos (Nat.floor_le hex.le)
  -- the number of gaps: `k` with `log(n₀ + k) ≥ Y`
  set k : ℕ := ⌊Real.exp Y⌋₊ + 1 with hkdef
  have hk : Y ≤ Real.log ((n₀ : ℝ) + k) := by
    rw [← Real.log_exp Y]
    refine Real.log_le_log (Real.exp_pos _) ?_
    have := Nat.lt_floor_add_one (Real.exp Y)
    rw [hkdef]; push_cast
    linarith
  set g : ℝ → ℝ := fun x => |blindKernel c x| * (2 * Real.cosh (x / 2)) with hg
  have hgc : Continuous g := ((continuous_blindKernel c).abs).mul continuous_two_cosh_half
  have hg0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg (abs_nonneg _) (by positivity)
  -- enlarge the lag interval to the union of gaps
  have h1 : ∫ x in X..Y, g x ≤ ∫ x in Real.log n₀..Real.log ((n₀ : ℝ) + k), g x :=
    intervalIntegral.integral_mono_interval hlogn₀ hXY hk (Filter.Eventually.of_forall hg0)
      (hgc.intervalIntegrable _ _)
  -- the gaps
  have h2 : ∫ x in Real.log n₀..Real.log ((n₀ : ℝ) + k), g x ≤
      ∑ n ∈ Finset.Ico n₀ (n₀ + k), gapBound c n := by
    rw [integral_eq_sum_gaps hgc n₀ k]
    exact Finset.sum_le_sum fun n hn =>
      integral_gap_le hc hv (show 2 ≤ n by have := (Finset.mem_Ico.mp hn).1; omega)
  -- the gap bounds as one spectral integral
  have h3 : ∑ n ∈ Finset.Ico n₀ (n₀ + k), gapBound c n =
      ∫ τ, specDensityC c τ * ∑ n ∈ Finset.Ico n₀ (n₀ + k), gapWeight n τ := by
    simp_rw [gapBound_eq_integral, Finset.mul_sum]
    rw [MeasureTheory.integral_finsetSum _ fun n _ => integrable_specDensityC_mul_gapWeight c n]
  -- the pointwise bound
  have h4 : ∫ τ, specDensityC c τ * ∑ n ∈ Finset.Ico n₀ (n₀ + k), gapWeight n τ ≤
      ∫ τ, specDensityC c τ *
        (if (n₀ : ℝ) ≤ |τ| then 20 * Real.sqrt |τ| else 6 * |τ| / Real.sqrt ((n₀ : ℝ) - 1)) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => ?_)
      (integrable_specDensityC_mul_tailWeight n₀) (Filter.Eventually.of_forall fun τ => ?_)
    · exact mul_nonneg (specDensityC_nonneg hc τ)
        (Finset.sum_nonneg fun n _ => gapWeight_nonneg n τ)
    · exact mul_le_mul_of_nonneg_left (sum_gapWeight_le hn₀ τ) (specDensityC_nonneg hc τ)
  rw [integral_specDensityC_mul_tailWeight] at h4
  exact h1.trans (h2.trans (h3 ▸ h4))

/-! ## The pole floor with the half spectral moment -/

/-- At `X = log 2`: `∫_{log 2}^{2L} |K_c| 2cosh ≤ 29 ∫ √|τ| ρ_c`. -/
theorem integral_abs_blindKernel_tail_log_two_le {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hv : nodeVector c = 0) {Y : ℝ} (hY : Real.log 2 ≤ Y) :
    ∫ x in Real.log 2..Y, |blindKernel c x| * (2 * Real.cosh (x / 2)) ≤
      29 * ∫ τ, Real.sqrt |τ| * specDensityC c τ := by
  have h := integral_abs_blindKernel_tail_le hc hv le_rfl hY
  have hfl : ⌊Real.exp (Real.log 2)⌋₊ = 2 := by
    rw [Real.exp_log two_pos]; exact Nat.floor_natCast 2
  rw [hfl] at h
  push_cast at h
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.sqrt_one, div_one] at h
  have hρ0 := specDensityC_nonneg hc
  have hint := integrable_sqrt_mul_specDensityC c
  -- first piece ≤ the full half-moment
  have hA : ∫ τ in {τ : ℝ | (2 : ℝ) ≤ |τ|}, Real.sqrt |τ| * specDensityC c τ ≤
      ∫ τ, Real.sqrt |τ| * specDensityC c τ :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun τ =>
      mul_nonneg (Real.sqrt_nonneg _) (hρ0 τ))
  -- second piece: |τ| ≤ (3/2) √|τ| below 2
  have hB : lowMoment c 2 ≤ (3 / 2) * ∫ τ, Real.sqrt |τ| * specDensityC c τ := by
    unfold lowMoment
    refine (setIntegral_mono_on (integrable_abs_mul_specDensityC c).integrableOn
      (hint.const_mul (3 / 2)).integrableOn (measurableSet_abs_lt 2) fun τ hτ => ?_).trans ?_
    · have hτ2 : |τ| < 2 := hτ
      have hs : |τ| ≤ (3 / 2) * Real.sqrt |τ| := by
        have h1 : Real.sqrt |τ| ≤ 3 / 2 := by
          rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          exact Real.sqrt_le_sqrt (by nlinarith)
        have h2 : |τ| = Real.sqrt |τ| * Real.sqrt |τ| := (Real.mul_self_sqrt (abs_nonneg τ)).symm
        calc |τ| = Real.sqrt |τ| * Real.sqrt |τ| := h2
          _ ≤ (3 / 2) * Real.sqrt |τ| := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      calc |τ| * specDensityC c τ ≤ (3 / 2) * Real.sqrt |τ| * specDensityC c τ :=
            mul_le_mul_of_nonneg_right hs (hρ0 τ)
        _ = (3 / 2) * (Real.sqrt |τ| * specDensityC c τ) := by ring
    · rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left (setIntegral_le_integral hint
        (Filter.Eventually.of_forall fun τ => mul_nonneg (Real.sqrt_nonneg _) (hρ0 τ))) (by norm_num)
  linarith

/-- **Pole floor with the half spectral moment.**  On nonnegative blind combinations,
`P(c) ≥ −(4·mass(c) + 58 ∫ √|τ| ρ_c(τ) dτ)`. -/
theorem nodePoleMass_ge_sqrt_moment {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hv : nodeVector c = 0) :
    -(4 * linearCombination ℝ testMass c + 58 * ∫ τ, Real.sqrt |τ| * specDensityC c τ) ≤
      nodePoleMass c := by
  set mass := linearCombination ℝ testMass c with hmass
  have hmass0 : 0 ≤ mass := linearCombination_testMass_nonneg hc
  rw [nodePoleMass_eq_integral]
  set g : ℝ → ℝ := fun x => blindKernel c x * (2 * Real.cosh (x / 2)) with hg
  have hgc : Continuous g := (continuous_blindKernel c).mul continuous_two_cosh_half
  have hgneg : ∀ x, g (-x) = g x := by
    intro x
    simp only [hg, blindKernel_neg, neg_div, Real.cosh_neg]
  obtain ⟨L₀, -, hLc⟩ := exists_level_combination c
  set L := max L₀ 1 with hL
  have hL1 : 1 ≤ L := le_max_right _ _
  have hLc' : ∀ f ∈ c.support, LevelTest L f := fun f hf => (hLc f hf).mono (le_max_left _ _)
  have hlog2 : Real.log 2 < 2 * L := by linarith [Real.log_two_lt_d9]
  have hgzero : ∀ x, x ∉ Ioc (-(2 * L)) (2 * L) → g x = 0 := by
    intro x hx
    simp only [hg]
    rw [blindKernel_eq_zero_of_level hLc' ?_, zero_mul]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hint : ∫ x, g x = ∫ x in (-(2 * L))..(2 * L), g x := by
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero hgzero]
  have hII : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hgc.intervalIntegrable a b
  have hsplit : ∫ x in (-(2 * L))..(2 * L), g x =
      (∫ x in (-(2 * L))..(-Real.log 2), g x) + (∫ x in (-Real.log 2)..(Real.log 2), g x) +
        ∫ x in (Real.log 2)..(2 * L), g x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _),
      intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)]
  -- the middle piece
  have hmid : -(7 / 2 * mass) ≤ ∫ x in (-Real.log 2)..(Real.log 2), g x := by
    have hb : ∀ x ∈ Ι (-Real.log 2) (Real.log 2), ‖g x‖ ≤ 5 / 2 * mass := by
      intro x hx
      have hx' : |x| ≤ Real.log 2 := by
        rw [uIoc_of_le (by linarith [Real.log_pos one_lt_two])] at hx
        rw [abs_le]
        exact ⟨hx.1.le, hx.2⟩
      rw [Real.norm_eq_abs, hg]
      simp only
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.cosh (x / 2))]
      calc |blindKernel c x| * (2 * Real.cosh (x / 2)) ≤ mass * (5 / 2) :=
            mul_le_mul (abs_blindKernel_le hc x) (two_cosh_half_le_of_abs_le_log_two hx')
              (by positivity) hmass0
        _ = 5 / 2 * mass := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at h
    have hlen : |Real.log 2 - -Real.log 2| ≤ 7 / 5 := by
      rw [sub_neg_eq_add, abs_of_pos (by linarith [Real.log_pos one_lt_two])]
      linarith [Real.log_two_lt_d9]
    have h2 : |∫ x in (-Real.log 2)..(Real.log 2), g x| ≤ 5 / 2 * mass * (7 / 5) :=
      h.trans (mul_le_mul_of_nonneg_left hlen (by positivity))
    have := neg_abs_le (∫ x in (-Real.log 2)..(Real.log 2), g x)
    linarith
  -- the right tail via the spectral bound
  have htail : -(29 * ∫ τ, Real.sqrt |τ| * specDensityC c τ) ≤ ∫ x in (Real.log 2)..(2 * L), g x := by
    have hT := integral_abs_blindKernel_tail_log_two_le hc hv hlog2.le
    have hab : ∫ x in (Real.log 2)..(2 * L), -(|blindKernel c x| * (2 * Real.cosh (x / 2))) ≤
        ∫ x in (Real.log 2)..(2 * L), g x := by
      refine intervalIntegral.integral_mono_on hlog2.le
        (((continuous_blindKernel c).abs.mul continuous_two_cosh_half).neg.intervalIntegrable _ _)
        (hII _ _) fun x _ => ?_
      simp only [hg]
      have := neg_abs_le (blindKernel c x)
      have hc0 : 0 ≤ 2 * Real.cosh (x / 2) := by positivity
      nlinarith
    rw [intervalIntegral.integral_neg] at hab
    linarith
  -- the left tail equals the right tail
  have hleft : ∫ x in (-(2 * L))..(-Real.log 2), g x = ∫ x in (Real.log 2)..(2 * L), g x := by
    rw [← intervalIntegral.integral_comp_neg g]
    exact intervalIntegral.integral_congr fun x _ => (hgneg x)
  rw [hint, hsplit, hleft]
  linarith

end

end RHTower.WeilOneSided
