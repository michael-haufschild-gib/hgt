import GaloisForLFunctions.RHTower.LiEvenCrossActualClockCausalHistory

/-!
# Propagated flattening of the causal history and its moving cancellation depth

With `K = B'`, `V_{m+1} = K^{⋆(m+1)}`, `W_{m+1} = ∫_0^· V_{m+1}`, the history rows
`N_n = W_{n+1}/(n+1)`, the partial sums `S_m = Σ_{n≤m} (-1)^n N_n` and `D(T) = ∫_0^T P/t`:

* (source flattening) `K'/K → 0`, `K(t-s)/K(t) → 1` uniformly on every `[0,R]`, `∫_0^R K → ∞`;
* (propagation) for every fixed `m`: `V_m'/V_m → 0`, `V_{m+1}/V_m → ∞`, `V_m → ∞`,
  `W_m/V_m → ∞`, `W_m'/W_m → 0`, `W_{m+1}/W_m → ∞`, fixed-shift flatness of `V_m` and `W_m`;
* (all-fixed-order boundary) `N_{n+1}(T)/N_n(T) → ∞` and `N_n(T) → ∞` as `T → ∞`; earlier rows are
  negligible, `S_m/N_m → (-1)^m`, even truncations tend to `+∞`, odd ones to `-∞`, and every fixed
  adjacent pair `N_n - N_{n+1}` tends to `-∞`; the first descent index `d(T) → ∞`;
* (fixed-truncation obstruction) under RH `0 ≤ D(T) ≤ AT²/4` and `(D - S_m)/N_m → -(-1)^m`; without
  RH, along one cofinal sequence `T_l e^{-βT_l}(D - S_m)(T_l)` has a strictly negative limit
  independent of `m`; in every case `|D - S_m|` is unbounded along the clock;
* (first crossing) with `J_t(s) = sK'(t-s) - K(t-s)`: `J_t(0) = -K(t) < 0`, `J_t(t) = tK'(0) > 0`,
  both signs persist on open intervals, `tD'(t) = tK(t) - ∫_0^t D J_t`, so `D'(t) ≥ 0` iff
  `∫_0^t D J_t ≤ tK(t)`; the fixed-history coefficient `(K(t-s) - sK'(t-s))/K(t) → 1` uniformly on
  `[0,R]`, the fixed-history contribution divided by `K(t)` tends to `∫_0^R D`, and is eventually
  strictly positive for `0 < R ≤ 20`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "K" => liClockThetaKernel
local notation "K'" => liClockThetaKernelDeriv
local notation "b₀" => liClockThetaKernelDeriv 0
local notation "D" => liEvenCrossActualClockLogHistory
local notation "β" => liEvenCrossActualClockMaxGrowthRate
local notation "V" => liClockHistoryKernelPower
local notation "V'" => liClockHistoryKernelPowerDeriv
local notation "W" => liClockHistoryCumulative
local notation "N" => liClockHistoryIntegratedRow
local notation "S" => liClockHistoryPartialSum

/-! ## Source flattening -/

/-- `K'(t)/K(t) → 0`. -/
theorem tendsto_liClockThetaKernelDeriv_div_kernel :
    Tendsto (fun t => K' t / K t) atTop (𝓝 0) := by
  have hB : deriv liEvenCrossActualClockBorelKernel = K :=
    funext deriv_liEvenCrossActualClockBorelKernel_eq
  have hK : deriv K = K' := funext fun t => (hasDerivAt_liClockThetaKernel t).deriv
  refine tendsto_liEvenCrossActualClockBorel_second_div_deriv_zero.congr fun t => ?_
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, hB, hK]

/-- `∫_0^R K = B(R) - 1 → ∞`. -/
theorem tendsto_integral_liClockThetaKernel_atTop :
    Tendsto (fun R => ∫ s in (0 : ℝ)..R, K s) atTop atTop := by
  have hb := liClockThetaKernelDeriv_zero_pos
  have hlow : ∀ R : ℝ, 0 ≤ R → b₀ * (R ^ 2 / 2) ≤ ∫ s in (0 : ℝ)..R, K s := fun R hR => by
    show _ ≤ W 0 R
    simpa using liClockHistoryCumulative_ge 0 hR
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono hlow)
    (((tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos).const_mul_atTop hb)

private theorem eventually_kernelPower_pos (m : ℕ) : ∀ᶠ t in atTop, 0 < V m t :=
  (eventually_gt_atTop 0).mono fun _ ht => liClockHistoryKernelPower_pos m ht

private theorem eventually_cumulative_pos (m : ℕ) : ∀ᶠ t in atTop, 0 < W m t :=
  (eventually_gt_atTop 0).mono fun _ ht => liClockHistoryCumulative_pos m ht

private theorem shift_of_slope (m : ℕ) (hs : Tendsto (fun t => V' m t / V m t) atTop (𝓝 0)) :
    ∀ R c, 0 ≤ R → c < 1 → ∀ᶠ t in atTop, ∀ v ∈ Icc 0 R, c * V m t ≤ V m (t - v) :=
  fun _ _ hR hc => eventually_mul_le_shift_of_slope
    (Eventually.of_forall (hasDerivAt_liClockHistoryKernelPower m)) (eventually_kernelPower_pos m)
    hs hR hc

private theorem ratio_of_slope (m : ℕ) (hs : Tendsto (fun t => V' m t / V m t) atTop (𝓝 0)) :
    Tendsto (fun t => V (m + 1) t / V m t) atTop atTop :=
  tendsto_volterraConv_div_atTop (continuous_liClockHistoryKernelPower m)
    continuous_liClockThetaKernel (fun _ hs => liClockHistoryKernelPower_nonneg m hs)
    (fun _ hs => liClockThetaKernel_nonneg hs) (eventually_kernelPower_pos m) (shift_of_slope m hs)
    tendsto_integral_liClockThetaKernel_atTop

/-! ## Propagation through every fixed convolution power -/

/-- **Propagated flattening.**  `V_m'/V_m → 0` for every fixed `m`. -/
theorem tendsto_liClockHistoryKernelPower_slope (m : ℕ) :
    Tendsto (fun t => V' m t / V m t) atTop (𝓝 0) := by
  induction m with
  | zero => exact tendsto_liClockThetaKernelDeriv_div_kernel
  | succ m ih =>
    exact tendsto_volterraConv_slope_zero (continuous_liClockHistoryKernelPower m)
      hasDerivAt_liClockThetaKernel continuous_liClockThetaKernelDeriv liClockThetaKernel_zero
      (fun _ hs => liClockHistoryKernelPower_nonneg m hs) (monotoneOn_liClockHistoryKernelPower m)
      (fun _ hs => liClockThetaKernel_pos hs) (fun s _ => liClockThetaKernelDeriv_nonneg s)
      (eventually_kernelPower_pos m) (ratio_of_slope m ih) tendsto_liClockThetaKernelDeriv_div_kernel

/-- `V_{m+1}/V_m → ∞`. -/
theorem tendsto_liClockHistoryKernelPower_succ_div (m : ℕ) :
    Tendsto (fun t => V (m + 1) t / V m t) atTop atTop :=
  ratio_of_slope m (tendsto_liClockHistoryKernelPower_slope m)

/-- Fixed-shift flatness: `V_m(t - v)/V_m(t) → 1` uniformly on `[0,R]`. -/
theorem tendstoUniformlyOn_liClockHistoryKernelPower_shift (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun t v => V m (t - v) / V m t) (fun _ => 1) atTop (Icc 0 R) :=
  tendstoUniformlyOn_shift_ratio_of_slope
    (Eventually.of_forall (hasDerivAt_liClockHistoryKernelPower m)) (eventually_kernelPower_pos m)
    (tendsto_liClockHistoryKernelPower_slope m) hR
    ((eventually_ge_atTop R).mono fun t ht v hv => monotoneOn_liClockHistoryKernelPower m
      (show t - v ∈ Ici 0 by simp only [mem_Ici]; linarith [hv.2])
      (show t ∈ Ici 0 by simp only [mem_Ici]; linarith [hv.1]) (by linarith [hv.1]))

/-- `K(t - v)/K(t) → 1` uniformly on `[0,R]`. -/
theorem tendstoUniformlyOn_liClockThetaKernel_shift {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun t v => K (t - v) / K t) (fun _ => 1) atTop (Icc 0 R) :=
  tendstoUniformlyOn_liClockHistoryKernelPower_shift 0 hR

/-- Every `V_m` tends to infinity. -/
theorem tendsto_liClockHistoryKernelPower_atTop (m : ℕ) : Tendsto (V m) atTop atTop := by
  induction m with
  | zero =>
    have hb := liClockThetaKernelDeriv_zero_pos
    exact tendsto_atTop_mono' atTop
      ((eventually_ge_atTop 0).mono fun t ht => mul_le_liClockThetaKernel ht)
      (tendsto_id.const_mul_atTop hb)
  | succ m ih =>
    have h := (tendsto_liClockHistoryKernelPower_succ_div m).atTop_mul_atTop₀ ih
    refine h.congr' ((eventually_kernelPower_pos m).mono fun t ht => ?_)
    exact div_mul_cancel₀ _ ht.ne'

/-- `W_m/V_m → ∞`. -/
theorem tendsto_liClockHistoryCumulative_div_kernelPower (m : ℕ) :
    Tendsto (fun t => W m t / V m t) atTop atTop :=
  tendsto_integral_div_self_atTop_of_shift (continuous_liClockHistoryKernelPower m)
    (fun _ hs => liClockHistoryKernelPower_nonneg m hs) (eventually_kernelPower_pos m)
    (shift_of_slope m (tendsto_liClockHistoryKernelPower_slope m))

/-- `W_m'/W_m = V_m/W_m → 0`. -/
theorem tendsto_liClockHistoryCumulative_slope (m : ℕ) :
    Tendsto (fun t => V m t / W m t) atTop (𝓝 0) := by
  refine (tendsto_liClockHistoryCumulative_div_kernelPower m).inv_tendsto_atTop.congr fun t => ?_
  simp only [Pi.inv_apply, inv_div]

private theorem shift_cumulative (m : ℕ) :
    ∀ R c, 0 ≤ R → c < 1 → ∀ᶠ t in atTop, ∀ v ∈ Icc 0 R, c * W m t ≤ W m (t - v) :=
  fun _ _ hR hc => eventually_mul_le_shift_of_slope
    (Eventually.of_forall (hasDerivAt_liClockHistoryCumulative m)) (eventually_cumulative_pos m)
    (tendsto_liClockHistoryCumulative_slope m) hR hc

/-- Fixed-shift flatness of `W_m`. -/
theorem tendstoUniformlyOn_liClockHistoryCumulative_shift (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun t v => W m (t - v) / W m t) (fun _ => 1) atTop (Icc 0 R) :=
  tendstoUniformlyOn_shift_ratio_of_slope
    (Eventually.of_forall (hasDerivAt_liClockHistoryCumulative m)) (eventually_cumulative_pos m)
    (tendsto_liClockHistoryCumulative_slope m) hR
    ((eventually_ge_atTop R).mono fun t ht v hv =>
      (strictMonoOn_liClockHistoryCumulative m).monotoneOn
        (show t - v ∈ Ici 0 by simp only [mem_Ici]; linarith [hv.2])
        (show t ∈ Ici 0 by simp only [mem_Ici]; linarith [hv.1]) (by linarith [hv.1]))

/-- `W_{m+1}/W_m → ∞`. -/
theorem tendsto_liClockHistoryCumulative_succ_div (m : ℕ) :
    Tendsto (fun t => W (m + 1) t / W m t) atTop atTop := by
  rw [liClockHistoryCumulative_succ]
  exact tendsto_volterraConv_div_atTop (continuous_liClockHistoryCumulative m)
    continuous_liClockThetaKernel (fun _ hs => liClockHistoryCumulative_nonneg m hs)
    (fun _ hs => liClockThetaKernel_nonneg hs) (eventually_cumulative_pos m) (shift_cumulative m)
    tendsto_integral_liClockThetaKernel_atTop

/-! ## The all-fixed-order boundary -/

/-- **All-fixed-order boundary.**  `N_{n+1}(T)/N_n(T) → ∞` as `T → ∞`, for every fixed `n`. -/
theorem tendsto_liClockHistoryIntegratedRow_succ_div (n : ℕ) :
    Tendsto (fun T => N (n + 1) T / N n T) atTop atTop := by
  have h := (tendsto_liClockHistoryCumulative_succ_div n).const_mul_atTop
    (show (0 : ℝ) < (n + 1) / (n + 2) by positivity)
  refine h.congr' ((eventually_cumulative_pos n).mono fun T hT => ?_)
  dsimp only
  rw [liClockHistoryIntegratedRow_eq, liClockHistoryIntegratedRow_eq]
  push_cast
  field_simp
  ring

/-- Every history row tends to infinity. -/
theorem tendsto_liClockHistoryIntegratedRow_atTop (n : ℕ) : Tendsto (N n) atTop atTop := by
  have hb := liClockThetaKernelDeriv_zero_pos
  have hc : 0 < b₀ ^ (n + 1) / ((2 * n + 2).factorial : ℝ) / (n + 1) := by positivity
  refine tendsto_atTop_mono' atTop ((eventually_ge_atTop 0).mono fun T hT => ?_)
    ((tendsto_pow_atTop (by omega : 2 * n + 2 ≠ 0)).const_mul_atTop hc)
  rw [liClockHistoryIntegratedRow_eq, le_div_iff₀ (by positivity)]
  refine le_of_eq_of_le ?_ (liClockHistoryCumulative_ge n hT)
  field_simp

/-- Earlier rows are negligible against every later row. -/
theorem tendsto_liClockHistoryIntegratedRow_div_of_lt {i m : ℕ} (him : i < m) :
    Tendsto (fun T => N i T / N m T) atTop (𝓝 0) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = i + j + 1 := ⟨m - i - 1, by omega⟩
  clear him
  induction j with
  | zero =>
    refine (tendsto_liClockHistoryIntegratedRow_succ_div i).inv_tendsto_atTop.congr fun T => ?_
    simp only [Pi.inv_apply, inv_div, add_zero]
  | succ j ih =>
    have h := ih.mul (tendsto_liClockHistoryIntegratedRow_succ_div (i + j + 1)).inv_tendsto_atTop
    rw [mul_zero] at h
    refine h.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
    have h1 := liClockHistoryIntegratedRow_pos (i + j + 1) hT
    have h2 := liClockHistoryIntegratedRow_pos (i + j + 1 + 1) hT
    simp only [Pi.inv_apply, inv_div]
    rw [show i + (j + 1) + 1 = i + j + 1 + 1 by ring]
    field_simp

/-- `S_m(T)/N_m(T) → (-1)^m`. -/
theorem tendsto_liClockHistoryPartialSum_div (m : ℕ) :
    Tendsto (fun T => S m T / N m T) atTop (𝓝 ((-1) ^ m)) := by
  have h : Tendsto (fun T => ∑ n ∈ Finset.range m, (-1 : ℝ) ^ n * (N n T / N m T) + (-1) ^ m)
      atTop (𝓝 (∑ n ∈ Finset.range m, (-1 : ℝ) ^ n * 0 + (-1) ^ m)) :=
    (tendsto_finsetSum _ fun n hn =>
      (tendsto_liClockHistoryIntegratedRow_div_of_lt (Finset.mem_range.1 hn)).const_mul _).add
      tendsto_const_nhds
  simp only [mul_zero, Finset.sum_const_zero, zero_add] at h
  refine h.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
  have hN := liClockHistoryIntegratedRow_pos m hT
  dsimp only
  unfold liClockHistoryPartialSum
  rw [Finset.sum_range_succ, add_div, Finset.sum_div]
  congr 1
  · exact Finset.sum_congr rfl fun n _ => by ring
  · field_simp

/-- Every even truncation tends to `+∞`. -/
theorem tendsto_liClockHistoryPartialSum_even (j : ℕ) : Tendsto (S (2 * j)) atTop atTop := by
  have h := Tendsto.pos_mul_atTop (by simp [pow_mul] : (0 : ℝ) < (-1) ^ (2 * j))
    (tendsto_liClockHistoryPartialSum_div (2 * j)) (tendsto_liClockHistoryIntegratedRow_atTop (2 * j))
  refine h.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
  exact div_mul_cancel₀ _ (liClockHistoryIntegratedRow_pos _ hT).ne'

/-- Every odd truncation tends to `-∞`. -/
theorem tendsto_liClockHistoryPartialSum_odd (j : ℕ) : Tendsto (S (2 * j + 1)) atTop atBot := by
  have h := Tendsto.neg_mul_atTop (by simp [pow_succ, pow_mul] : (-1 : ℝ) ^ (2 * j + 1) < 0)
    (tendsto_liClockHistoryPartialSum_div (2 * j + 1))
    (tendsto_liClockHistoryIntegratedRow_atTop (2 * j + 1))
  refine h.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
  exact div_mul_cancel₀ _ (liClockHistoryIntegratedRow_pos _ hT).ne'

/-- Every fixed adjacent pair `N_n - N_{n+1}` tends to `-∞`; in particular it is eventually
negative, so positive pairing of the history series fails at every fixed order. -/
theorem tendsto_liClockHistoryPair_atBot (n : ℕ) :
    Tendsto (fun T => N n T - N (n + 1) T) atTop atBot := by
  have hr : Tendsto (fun T => N n T / N (n + 1) T - 1) atTop (𝓝 (0 - 1)) :=
    (tendsto_liClockHistoryIntegratedRow_div_of_lt (Nat.lt_succ_self n)).sub tendsto_const_nhds
  rw [zero_sub] at hr
  have h := Tendsto.neg_mul_atTop (by norm_num : (-1 : ℝ) < 0) hr
    (tendsto_liClockHistoryIntegratedRow_atTop (n + 1))
  refine h.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
  have hN := liClockHistoryIntegratedRow_pos (n + 1) hT
  field_simp

theorem eventually_liClockHistoryPair_neg (n : ℕ) : ∀ᶠ T in atTop, N n T - N (n + 1) T < 0 :=
  (tendsto_liClockHistoryPair_atBot n).eventually (eventually_lt_atBot 0)

/-- **Escaping descent depth.**  `d(T) → ∞`. -/
theorem tendsto_liClockHistoryDescentIndex_atTop :
    Tendsto liClockHistoryDescentIndex atTop atTop := by
  rw [tendsto_atTop]
  intro n₀
  have hall : ∀ᶠ T in atTop, ∀ n ∈ Finset.range n₀, N n T < N (n + 1) T := by
    rw [eventually_all_finset]
    intro n _
    filter_upwards [(tendsto_liClockHistoryIntegratedRow_succ_div n).eventually
      (eventually_gt_atTop 1), eventually_gt_atTop 0] with T h1 hT
    have := liClockHistoryIntegratedRow_pos n hT
    rwa [lt_div_iff₀ this, one_mul] at h1
  filter_upwards [hall, eventually_gt_atTop 0] with T hT hT0
  by_contra hlt
  rw [not_le] at hlt
  have h1 := (liClockHistoryDescentIndex_spec hT0).1
  have h2 := hT _ (Finset.mem_range.2 hlt)
  linarith

/-! ## Fixed truncations cannot approximate the cutoff -/

/-- Under RH, `0 ≤ D(T) ≤ AT²/4`. -/
theorem liEvenCrossActualClockLogHistory_bounds_of_rh (hRH : RiemannHypothesis) {T : ℝ}
    (hT : 0 ≤ T) : 0 ≤ D T ∧ D T ≤ xiShiftAbsoluteMass 0 * T ^ 2 / 4 := by
  have hβ : β = 0 := liEvenCrossActualClockMaxGrowthRate_eq_zero_iff.2 hRH
  have hle : ∀ t ∈ Icc 0 T, 0 ≤ liEvenCrossActualClockLogHistoryDensity t ∧
      liEvenCrossActualClockLogHistoryDensity t ≤ xiShiftAbsoluteMass 0 / 2 * t := fun t ht => by
    unfold liEvenCrossActualClockLogHistoryDensity
    have hP0 := liEvenCrossActualClockPrimitive_nonneg_of_rh hRH t
    have hP1 := abs_liEvenCrossActualClockPrimitive_le_max ht.1
    rw [hβ, zero_mul, Real.exp_zero, mul_one, abs_of_nonneg hP0] at hP1
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0; simp
    · refine ⟨div_nonneg hP0 h0.le, ?_⟩
      rw [div_le_iff₀ h0]
      nlinarith
  have hc := continuous_liEvenCrossActualClockLogHistoryDensity
  unfold liEvenCrossActualClockLogHistory
  constructor
  · exact intervalIntegral.integral_nonneg hT fun t ht => (hle t ht).1
  · refine (intervalIntegral.integral_mono_on hT (hc.intervalIntegrable 0 T)
      ((by fun_prop : Continuous fun t : ℝ => xiShiftAbsoluteMass 0 / 2 * t).intervalIntegrable 0 T)
      fun t ht => (hle t ht).2).trans_eq ?_
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring

/-- `N_0(T)/T² → ∞`, from the cubic source coefficient `K(t) ≥ k_1 t³`. -/
theorem tendsto_liClockHistoryIntegratedRow_zero_div_sq :
    Tendsto (fun T => N 0 T / T ^ 2) atTop atTop := by
  have hk1 := liClockThetaKernelTaylorCoeff_pos 1
  have hlow : ∀ T : ℝ, 0 < T → liClockThetaKernelTaylorCoeff 1 / 4 * T ^ 2 ≤ N 0 T / T ^ 2 :=
    fun T hT => by
      rw [le_div_iff₀ (by positivity), liClockHistoryIntegratedRow_eq]
      have hW : liClockThetaKernelTaylorCoeff 1 * (T ^ 4 / 4) ≤ W 0 T := by
        have hint := intervalIntegral.integral_mono_on (μ := volume) hT.le
          ((by fun_prop : Continuous fun t : ℝ =>
            liClockThetaKernelTaylorCoeff 1 * t ^ 3).intervalIntegrable 0 T)
          (continuous_liClockThetaKernel.intervalIntegrable 0 T) fun t ht => by
            have := le_hasSum (hasSum_liClockThetaKernelTaylorCoeff t) 1 fun j _ =>
              mul_nonneg (liClockThetaKernelTaylorCoeff_pos j).le (pow_nonneg ht.1 _)
            simpa using this
        refine le_of_eq_of_le ?_ hint
        rw [intervalIntegral.integral_const_mul, integral_pow]
        ring
      have : liClockThetaKernelTaylorCoeff 1 / 4 * T ^ 2 * T ^ 2 =
          liClockThetaKernelTaylorCoeff 1 * (T ^ 4 / 4) := by ring
      push_cast
      linarith
  exact tendsto_atTop_mono' atTop ((eventually_gt_atTop 0).mono hlow)
    ((tendsto_pow_atTop two_ne_zero).const_mul_atTop (by positivity))

/-- `N_n(T)/T² → ∞` for every `n`. -/
theorem tendsto_liClockHistoryIntegratedRow_div_sq (n : ℕ) :
    Tendsto (fun T => N n T / T ^ 2) atTop atTop := by
  induction n with
  | zero => exact tendsto_liClockHistoryIntegratedRow_zero_div_sq
  | succ n ih =>
    have h := (tendsto_liClockHistoryIntegratedRow_succ_div n).atTop_mul_atTop₀ ih
    refine h.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
    have hN := liClockHistoryIntegratedRow_pos n hT
    field_simp

/-- Under RH, `(D - S_m)/N_m → -(-1)^m`. -/
theorem tendsto_liClockHistory_truncation_error_of_rh (hRH : RiemannHypothesis) (m : ℕ) :
    Tendsto (fun T => (D T - S m T) / N m T) atTop (𝓝 (-(-1) ^ m)) := by
  have hD : Tendsto (fun T => D T / N m T) atTop (𝓝 0) := by
    have hup := (tendsto_liClockHistoryIntegratedRow_div_sq m).inv_tendsto_atTop.const_mul
      (xiShiftAbsoluteMass 0 / 4)
    rw [mul_zero] at hup
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [eventually_gt_atTop 0] with T hT
      exact div_nonneg (liEvenCrossActualClockLogHistory_bounds_of_rh hRH hT.le).1
        (liClockHistoryIntegratedRow_pos m hT).le
    · filter_upwards [eventually_gt_atTop 0] with T hT
      have hN := liClockHistoryIntegratedRow_pos m hT
      have hb := (liEvenCrossActualClockLogHistory_bounds_of_rh hRH hT.le).2
      simp only [Pi.inv_apply, inv_div]
      rw [div_le_iff₀ hN]
      calc D T ≤ xiShiftAbsoluteMass 0 * T ^ 2 / 4 := hb
        _ = xiShiftAbsoluteMass 0 / 4 * (T ^ 2 / N m T) * N m T := by field_simp
  have h := hD.sub (tendsto_liClockHistoryPartialSum_div m)
  rw [zero_sub] at h
  exact h.congr fun T => (sub_div _ _ _).symm

theorem liEvenCrossActualClockLogHistory_eq_dampedCutoff_zero (T : ℝ) :
    D T = liEvenCrossActualClockDampedCutoff 0 T := by
  unfold liEvenCrossActualClockLogHistory liEvenCrossActualClockDampedCutoff
    liEvenCrossActualClockLogHistoryDensity
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp

/-- `T e^{-γT} N_n(T) → 0` for every `γ > 0`. -/
theorem tendsto_mul_exp_neg_mul_liClockHistoryIntegratedRow {γ : ℝ} (hγ : 0 < γ) (n : ℕ) :
    Tendsto (fun T => T * Real.exp (-(γ * T)) * N n T) atTop (𝓝 0) := by
  have h := (tendsto_mul_exp_neg_mul_of_slope
    (Eventually.of_forall (hasDerivAt_liClockHistoryCumulative n)) (eventually_cumulative_pos n)
    (tendsto_liClockHistoryCumulative_slope n) hγ).div_const ((n : ℝ) + 1)
  rw [zero_div] at h
  refine h.congr fun T => ?_
  rw [liClockHistoryIntegratedRow_eq]
  ring

/-- `T e^{-γT} S_m(T) → 0` for every `γ > 0`. -/
theorem tendsto_mul_exp_neg_mul_liClockHistoryPartialSum {γ : ℝ} (hγ : 0 < γ) (m : ℕ) :
    Tendsto (fun T => T * Real.exp (-(γ * T)) * S m T) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range (m + 1)) fun n _ =>
    (tendsto_mul_exp_neg_mul_liClockHistoryIntegratedRow hγ n).const_mul ((-1 : ℝ) ^ n)
  simp only [mul_zero, Finset.sum_const_zero] at h
  refine h.congr fun T => ?_
  unfold liClockHistoryPartialSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Without RH, one cofinal clock sequence carries `T_l e^{-βT_l} D(T_l) → L < 0`, and the same limit
for `D - S_m` at every fixed order `m`. -/
theorem liClockHistory_truncation_escape_of_not_rh (hnot : ¬RiemannHypothesis) :
    0 < β ∧ ∃ L < 0, ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
      Tendsto (fun l => t l * Real.exp (-(β * t l)) * D (t l)) atTop (𝓝 L) ∧
      ∀ m, Tendsto (fun l => t l * Real.exp (-(β * t l)) * (D (t l) - S m (t l))) atTop (𝓝 L) := by
  have hβ : 0 < β := lt_of_le_of_ne liEvenCrossActualClockMaxGrowthRate_nonneg
    fun h => hnot (liEvenCrossActualClockMaxGrowthRate_eq_zero_iff.1 h.symm)
  obtain ⟨S', -, -, t, -, ht, hlim, hneg, -⟩ :=
    liEvenCrossActualClockDampedCutoff_escape_of_not_rh hnot hβ
  have hD := hlim.congr (f₂ := fun l => t l * Real.exp (-(β * t l)) * D (t l)) fun l => by
    rw [liEvenCrossActualClockLogHistory_eq_dampedCutoff_zero, sub_zero]
  refine ⟨hβ, _, hneg, t, ht, hD, fun m => ?_⟩
  have h := hD.sub ((tendsto_mul_exp_neg_mul_liClockHistoryPartialSum hβ m).comp ht)
  rw [sub_zero] at h
  exact h.congr fun l => by simp only [Function.comp]; ring

/-- **Fixed-truncation obstruction.**  For every fixed order `m`, the truncation error
`|D(T) - S_m(T)|` is unbounded along the clock. -/
theorem liClockHistory_truncation_error_unbounded (m : ℕ) (C : ℝ) :
    ∃ᶠ T in atTop, C < |D T - S m T| := by
  by_cases hRH : RiemannHypothesis
  · have habs : Tendsto (fun T => |(D T - S m T) / N m T|) atTop (𝓝 1) := by
      have := (tendsto_liClockHistory_truncation_error_of_rh hRH m).abs
      simpa [abs_neg, abs_pow] using this
    have h2 := Tendsto.pos_mul_atTop one_pos habs (tendsto_liClockHistoryIntegratedRow_atTop m)
    have h3 : ∀ᶠ T in atTop, C < |D T - S m T| := by
      filter_upwards [h2.eventually (eventually_gt_atTop C), eventually_gt_atTop 0] with T hT hT0
      have hN := liClockHistoryIntegratedRow_pos m hT0
      rwa [abs_div, abs_of_pos hN, div_mul_cancel₀ _ hN.ne'] at hT
    exact h3.frequently
  · obtain ⟨hβ, L, hL, t, ht, -, hlim⟩ := liClockHistory_truncation_escape_of_not_rh hRH
    have h1 : Tendsto (fun T : ℝ => T * Real.exp (-(β * T)) * 1) atTop (𝓝 0) :=
      tendsto_mul_exp_neg_mul_of_slope (f := fun _ => 1) (f' := fun _ => 0)
        (Eventually.of_forall fun t => hasDerivAt_const t 1)
        (Eventually.of_forall fun _ => one_pos) (by simp) hβ
    have hg : Tendsto (fun l => t l * Real.exp (-(β * t l))) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := h1.comp ht
        simp only [Function.comp_def, mul_one] at this
        exact this
      · filter_upwards [ht.eventually (eventually_gt_atTop 0)] with l hl
        exact mul_pos hl (Real.exp_pos _)
    have hprod := Tendsto.pos_mul_atTop (abs_pos.2 hL.ne) (hlim m).abs
      (tendsto_inv_nhdsGT_zero.comp hg)
    rw [frequently_atTop]
    intro T₀
    obtain ⟨l, hl⟩ := (((hprod.eventually (eventually_gt_atTop C)).and
      (ht.eventually (eventually_ge_atTop T₀))).and (ht.eventually (eventually_gt_atTop 0))).exists
    refine ⟨t l, hl.1.2, ?_⟩
    have hpos : 0 < t l * Real.exp (-(β * t l)) := mul_pos hl.2 (Real.exp_pos _)
    have key : |D (t l) - S m (t l)| =
        |t l * Real.exp (-(β * t l)) * (D (t l) - S m (t l))| * (t l * Real.exp (-(β * t l)))⁻¹ := by
      rw [abs_mul, abs_of_pos hpos, mul_right_comm, mul_inv_cancel₀ hpos.ne', one_mul]
    rw [key]
    exact hl.1.1

/-! ## The first-crossing law -/

/-- The crossing kernel `J_t(s) = sK'(t-s) - K(t-s)`. -/
def liClockHistoryCrossingKernel (t s : ℝ) : ℝ := s * K' (t - s) - K (t - s)

local notation "J" => liClockHistoryCrossingKernel

theorem continuous_liClockHistoryCrossingKernel (t : ℝ) : Continuous (J t) := by
  have := continuous_liClockThetaKernel
  have := continuous_liClockThetaKernelDeriv
  unfold liClockHistoryCrossingKernel
  fun_prop

theorem liClockHistoryCrossingKernel_zero (t : ℝ) : J t 0 = -K t := by
  simp [liClockHistoryCrossingKernel]

theorem liClockHistoryCrossingKernel_self (t : ℝ) : J t t = t * b₀ := by
  simp [liClockHistoryCrossingKernel, liClockThetaKernel_zero]

/-- **Two-signed crossing kernel.**  At every positive clock, `J_t < 0` on `[0, δ]` and `J_t > 0`
on `[t - δ, t]` for some `0 < δ < t`. -/
theorem liClockHistoryCrossingKernel_signs {t : ℝ} (ht : 0 < t) :
    ∃ δ, 0 < δ ∧ δ < t ∧ (∀ s ∈ Icc 0 δ, J t s < 0) ∧ ∀ s ∈ Icc (t - δ) t, 0 < J t s := by
  have hc := continuous_liClockHistoryCrossingKernel t
  have h0 : J t 0 < 0 := by
    rw [liClockHistoryCrossingKernel_zero]; exact neg_lt_zero.2 (liClockThetaKernel_pos ht)
  have h1 : 0 < J t t := by
    rw [liClockHistoryCrossingKernel_self]; exact mul_pos ht liClockThetaKernelDeriv_zero_pos
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff.1
    (hc.continuousAt.eventually_lt continuousAt_const h0)
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.eventually_nhds_iff.1
    (continuousAt_const.eventually_lt hc.continuousAt h1)
  refine ⟨min (min ε₁ ε₂) t / 2, by positivity, ?_, fun s hs => hb₁ ?_, fun s hs => hb₂ ?_⟩
  · have := min_le_right (min ε₁ ε₂) t; linarith
  · have h := (min_le_left (min ε₁ ε₂) t).trans (min_le_left ε₁ ε₂)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    have := min_le_right (min ε₁ ε₂) t
    linarith [hs.2, (by positivity : 0 < min (min ε₁ ε₂) t)]
  · have h := (min_le_left (min ε₁ ε₂) t).trans (min_le_right ε₁ ε₂)
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.2])]
    linarith [hs.1, (by positivity : 0 < min (min ε₁ ε₂) t)]

/-- **Exact crossing equation.**  `tD'(t) = tK(t) - ∫_0^t D(s) J_t(s) ds` on `t ≥ 0`. -/
theorem liEvenCrossActualClockLogHistory_crossing_eq {t : ℝ} (ht : 0 ≤ t) :
    t * deriv D t = t * K t - ∫ s in (0 : ℝ)..t, D s * J t s := by
  have hB : deriv liEvenCrossActualClockBorelKernel = K :=
    funext deriv_liEvenCrossActualClockBorelKernel_eq
  have hK : deriv K = K' := funext fun t => (hasDerivAt_liClockThetaKernel t).deriv
  have h := liEvenCrossActualClockLogHistory_slope_volterra ht
  unfold liEvenCrossActualClockHistoryCoefficient at h
  rw [hB, hK] at h
  rw [h]
  have e : ∫ s in (0 : ℝ)..t, D s * (K (t - s) - s * K' (t - s)) =
      -∫ s in (0 : ℝ)..t, D s * J t s := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    unfold liClockHistoryCrossingKernel
    ring
  rw [e]
  ring

/-- **First-crossing law.**  At every positive clock, `D'(t) ≥ 0` iff the complete correlated
history inequality `∫_0^t D(s) J_t(s) ds ≤ tK(t)` holds. -/
theorem deriv_liEvenCrossActualClockLogHistory_nonneg_iff {t : ℝ} (ht : 0 < t) :
    0 ≤ deriv D t ↔ ∫ s in (0 : ℝ)..t, D s * J t s ≤ t * K t := by
  have h := liEvenCrossActualClockLogHistory_crossing_eq ht.le
  constructor
  · intro hd
    nlinarith [mul_nonneg ht.le hd]
  · intro hi
    have : t * 0 ≤ t * deriv D t := by rw [h, mul_zero]; linarith
    exact le_of_mul_le_mul_left this ht

/-- **Fixed-history coefficient.**  `(K(t-s) - sK'(t-s))/K(t) → 1` uniformly on `[0,R]`. -/
theorem tendstoUniformlyOn_liClockHistoryCoefficient_div {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun t s => (K (t - s) - s * K' (t - s)) / K t) (fun _ => 1) atTop
      (Icc 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hshift := tendstoUniformlyOn_liClockThetaKernel_shift hR
  rw [Metric.tendstoUniformlyOn_iff] at hshift
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (tendsto_liClockThetaKernelDeriv_div_kernel.eventually
    (gt_mem_nhds (show 0 < ε / (2 * (R + 1)) by positivity)))
  filter_upwards [hshift (ε / 2) (half_pos hε), eventually_ge_atTop (T₁ + R),
    eventually_gt_atTop R] with t h1 h2 h3 s hs
  have hts : T₁ ≤ t - s := by linarith [hs.2]
  have hts0 : 0 < t - s := by linarith [hs.2]
  have hKt := liClockThetaKernel_pos (show 0 < t by linarith [hs.1])
  have hKts := liClockThetaKernel_pos hts0
  have hd := hT₁ (t - s) hts
  rw [div_lt_iff₀ hKts] at hd
  have hd0 := liClockThetaKernelDeriv_nonneg (t - s)
  have hmono : K (t - s) ≤ K t := monotone_liClockThetaKernel (by linarith [hs.1])
  have hr := h1 s hs
  rw [Real.dist_eq] at hr ⊢
  have hq : 0 ≤ s * K' (t - s) / K t := div_nonneg (mul_nonneg hs.1 hd0) hKt.le
  have hq2 : s * K' (t - s) / K t < ε / 2 := by
    rw [div_lt_iff₀ hKt]
    have hRR : R / (R + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    calc s * K' (t - s) ≤ R * K' (t - s) := mul_le_mul_of_nonneg_right hs.2 hd0
      _ ≤ R * (ε / (2 * (R + 1)) * K (t - s)) := mul_le_mul_of_nonneg_left hd.le hR
      _ = ε / 2 * (R / (R + 1)) * K (t - s) := by field_simp
      _ ≤ ε / 2 * (R / (R + 1)) * K t := mul_le_mul_of_nonneg_left hmono (by positivity)
      _ < ε / 2 * K t := by nlinarith [mul_pos (half_pos hε) hKt]
  rw [sub_div]
  change |1 - K (t - s) / K t| < ε / 2 at hr
  rw [abs_lt] at hr ⊢
  constructor <;> linarith

/-- **Fixed-history retention.**
`(1/K(t)) ∫_0^R D(s)(K(t-s) - sK'(t-s)) ds → ∫_0^R D`. -/
theorem tendsto_liClockHistoryRetention {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun t => (∫ s in (0 : ℝ)..R, D s * (K (t - s) - s * K' (t - s))) / K t) atTop
      (𝓝 (∫ s in (0 : ℝ)..R, D s)) := by
  have hDc : Continuous D := continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_liEvenCrossActualClockLogHistory t).continuousAt
  have hKc := continuous_liClockThetaKernel
  have hK'c := continuous_liClockThetaKernelDeriv
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hDc.continuousOn (s := Icc 0 R))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hR⟩)
  have hunif := tendstoUniformlyOn_liClockHistoryCoefficient_div hR
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' := ε / ((M + 1) * (R + 1)) with hε'def
  have hε' : 0 < ε' := by positivity
  filter_upwards [hunif ε' hε', eventually_gt_atTop 0] with t ht ht0
  have hKt := liClockThetaKernel_pos ht0
  have e : (∫ s in (0 : ℝ)..R, D s * (K (t - s) - s * K' (t - s))) / K t -
      ∫ s in (0 : ℝ)..R, D s =
      ∫ s in (0 : ℝ)..R, D s * ((K (t - s) - s * K' (t - s)) / K t - 1) := by
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun s => D s * (K (t - s) - s * K' (t - s)) / K t).intervalIntegrable
        _ _) (hDc.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  rw [Real.dist_eq, e, ← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := R) (C := M * ε')
    (f := fun s => D s * ((K (t - s) - s * K' (t - s)) / K t - 1)) fun s hs => by
      rw [uIoc_of_le hR] at hs
      have hsI : s ∈ Icc 0 R := ⟨hs.1.le, hs.2⟩
      have h2 := ht s hsI
      rw [Real.dist_eq, abs_sub_comm] at h2
      rw [norm_mul, Real.norm_eq_abs (_ - 1)]
      exact mul_le_mul (hM s hsI) h2.le (abs_nonneg _) hM0
  refine lt_of_le_of_lt hb ?_
  rw [sub_zero, abs_of_nonneg hR]
  have hlt : M * R < (M + 1) * (R + 1) := by nlinarith
  have e2 : M * ε' * R = ε * (M * R / ((M + 1) * (R + 1))) := by
    rw [hε'def]; field_simp
  rw [e2]
  have : M * R / ((M + 1) * (R + 1)) < 1 := by rw [div_lt_one (by positivity)]; exact hlt
  nlinarith

/-- For `0 < R ≤ 20` the fixed-history contribution is eventually strictly positive. -/
theorem eventually_liClockHistoryRetention_pos {R : ℝ} (hR : 0 < R) (hR20 : R ≤ 20) :
    ∀ᶠ t in atTop, 0 < ∫ s in (0 : ℝ)..R, D s * (K (t - s) - s * K' (t - s)) := by
  have hDc : Continuous D := continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_liEvenCrossActualClockLogHistory t).continuousAt
  have hA := xiShiftAbsoluteMass_pos 0
  have hpos : 0 < ∫ s in (0 : ℝ)..R, D s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hDc.intervalIntegrable _ _) (fun s hs => by
      have h := (liEvenCrossActualClockLogHistory_local_corridor hs.1.le (hs.2.le.trans hR20)).2.2
      have : 0 < (1051 / 2184 : ℝ) * xiShiftAbsoluteMass 0 * s ^ 2 / 4 := by
        have := hs.1; positivity
      linarith) hR
  filter_upwards [(tendsto_liClockHistoryRetention hR.le).eventually (lt_mem_nhds hpos),
    eventually_gt_atTop 0] with t ht ht0
  exact (div_pos_iff_of_pos_right (liClockThetaKernel_pos ht0)).1 ht

end RHTower
