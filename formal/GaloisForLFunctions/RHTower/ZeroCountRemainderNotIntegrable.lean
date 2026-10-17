import GaloisForLFunctions.RHTower.XiZeroCountLocalCeiling
import GaloisForLFunctions.RHTower.XiZeroCountingFunction

/-!
# The zero-count remainder is not integrable: the size law

Let `N(T)` be the number of zeros of `ξ` with ordinate in `(0, T]` (`xiZeroCount`) and
`M(T) = (T/2π) log(T/2πe) + 7/8` the smooth Riemann–von Mangoldt term (`routeKSmoothRVMCount`), and
put `S(T) = N(T) − M(T)` (`rvmRemainder`; it differs from the classical argument
`π⁻¹ arg ζ(½ + iT)` by `O(1/T)`).  The corpus proves `|S(T)| ≤ C log T`.  This module proves the
lower bound

`∫_{A}^{T} |S(t)| dt ≥ c · T / log T`   for all large `T`

(`exists_integral_abs_rvmRemainder_ge`), hence `S` is not integrable on `(0, ∞)`
(`not_integrableOn_rvmRemainder`).

**Mechanism.**  With `h = 1/(2 log T)` the increment `N(t) − N(t−h)` is a nonnegative integer,
bounded by `m_T = 1 + 2C_w log T` (local ceiling), and its integral over `[A, T]` is at least
`h (N(T − h) − N(A)) ≫ T` (shift identity for a monotone function and the Riemann–von Mangoldt
lower bound).  So the set `E` of `t` where `N` jumps in `(t − h, t]` has measure `≫ T/log T`.
On `E`, `S(t) − S(t − h) ≥ 1 − (M(t) − M(t − h)) ≥ ½` because `M' ≤ log T`, so
`|S(t)| + |S(t − h)| ≥ ½` there, and integrating gives the bound.

**Meaning.**  The spectral shift function of a trace-class perturbation is integrable (Krein), and a
finite-rank perturbation has a bounded shift.  The zero fluctuation `S` is neither, so the primes
cannot enter a spectral model as a trace-class modification of an archimedean reference whose
counting function is `M`.  The stronger classical statement that `S` is unbounded is not proved
here.
-/

open MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-- The zero count as a real-valued function. -/
def zeroCountReal (T : ℝ) : ℝ := (xiZeroCount T : ℝ)

/-- The zero-count remainder `S(T) = N(T) − M(T)`. -/
def rvmRemainder (T : ℝ) : ℝ := zeroCountReal T - routeKSmoothRVMCount T

theorem zeroCountReal_mono : Monotone zeroCountReal := fun a b h => by
  unfold zeroCountReal; exact_mod_cast xiZeroCount_mono h

theorem measurable_zeroCountReal : Measurable zeroCountReal := zeroCountReal_mono.measurable

theorem intervalIntegrable_zeroCountReal (a b : ℝ) :
    IntervalIntegrable zeroCountReal volume a b := zeroCountReal_mono.intervalIntegrable

/-! ## The smooth main term -/

theorem one_le_routeKRVMBase : 1 ≤ routeKRVMBase := by
  unfold routeKRVMBase
  have h1 := Real.pi_gt_three
  have h2 := Real.add_one_le_exp (1 : ℝ)
  nlinarith

theorem hasDerivAt_routeKSmoothRVMCount {t : ℝ} (ht : 0 < t) :
    HasDerivAt routeKSmoothRVMCount ((Real.log (t / routeKRVMBase) + 1) / (2 * Real.pi)) t := by
  have hb := routeKRVMBase_pos
  have h1 : HasDerivAt (fun u : ℝ => Real.log (u / routeKRVMBase)) (1 / t) t := by
    have := (Real.hasDerivAt_log (div_pos ht hb).ne').comp t
      ((hasDerivAt_id t).div_const routeKRVMBase)
    refine this.congr_deriv ?_
    field_simp
  have h2 : HasDerivAt (fun u : ℝ => u / (2 * Real.pi) * Real.log (u / routeKRVMBase))
      (1 / (2 * Real.pi) * Real.log (t / routeKRVMBase) + t / (2 * Real.pi) * (1 / t)) t :=
    ((hasDerivAt_id t).div_const (2 * Real.pi)).mul h1
  have h3 := h2.add_const (7 / 8 : ℝ)
  have hfun : routeKSmoothRVMCount =
      fun u : ℝ => u / (2 * Real.pi) * Real.log (u / routeKRVMBase) + 7 / 8 := rfl
  rw [hfun]
  refine h3.congr_deriv ?_
  field_simp

theorem continuousOn_routeKSmoothRVMCount : ContinuousOn routeKSmoothRVMCount (Ioi 0) :=
  fun _ ht => (hasDerivAt_routeKSmoothRVMCount ht).continuousAt.continuousWithinAt

/-- Lipschitz bound for the main term on `[A, T]` with `A ≥ 2πe`, `T ≥ e`: slope at most `log T`. -/
theorem abs_routeKSmoothRVMCount_sub_le {A T x y : ℝ} (hA : routeKRVMBase ≤ A)
    (hT : Real.exp 1 ≤ T) (hx : x ∈ Icc A T) (hy : y ∈ Icc A T) :
    |routeKSmoothRVMCount y - routeKSmoothRVMCount x| ≤ Real.log T * |y - x| := by
  have hb := routeKRVMBase_pos
  have hb1 := one_le_routeKRVMBase
  have hpos : ∀ z ∈ Icc A T, 0 < z := fun z hz => by linarith [hz.1]
  have hdiff : ∀ z ∈ Icc A T, DifferentiableAt ℝ routeKSmoothRVMCount z := fun z hz =>
    (hasDerivAt_routeKSmoothRVMCount (hpos z hz)).differentiableAt
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hT
  have hbound : ∀ z ∈ Icc A T, ‖deriv routeKSmoothRVMCount z‖ ≤ Real.log T := by
    intro z hz
    have hz0 := hpos z hz
    rw [(hasDerivAt_routeKSmoothRVMCount hz0).deriv, Real.norm_eq_abs]
    have hl1 : 0 ≤ Real.log (z / routeKRVMBase) :=
      Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith [hz.1])
    have hl2 : Real.log (z / routeKRVMBase) ≤ Real.log T :=
      Real.log_le_log (div_pos hz0 hb) ((div_le_self hz0.le hb1).trans hz.2)
    have hπ : 6 < 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc A T) hx hy
  simpa [Real.norm_eq_abs] using this

/-! ## The shift identity for a monotone function -/

/-- For monotone `N` and `0 < h`, `A + h ≤ T`: `h (N(T−h) − N(A)) ≤ ∫_A^T (N(t) − N(t−h)) dt`. -/
theorem mul_sub_le_integral_sub_comp_sub {N : ℝ → ℝ} (hN : Monotone N) {A T h : ℝ}
    (hh : 0 < h) :
    h * (N (T - h) - N A) ≤ ∫ t in A..T, (N t - N (t - h)) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable N volume a b := fun a b => hN.intervalIntegrable
  have hN' : Monotone fun t => N (t - h) := fun a b hab => hN (sub_le_sub_right hab h)
  rw [integral_sub (hint A T) hN'.intervalIntegrable, integral_comp_sub_right N h]
  have e1 : ∫ t in A..T, N t = (∫ t in A..(T - h), N t) + ∫ t in (T - h)..T, N t :=
    (integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have e2 : ∫ t in (A - h)..(T - h), N t = (∫ t in (A - h)..A, N t) + ∫ t in A..(T - h), N t :=
    (integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  rw [e1, e2]
  have l1 : h * N (T - h) ≤ ∫ t in (T - h)..T, N t := by
    have := integral_mono_on (a := T - h) (b := T) (by linarith)
      (intervalIntegrable_const (c := N (T - h))) (hint _ _) (fun x hx => hN hx.1)
    rwa [intervalIntegral.integral_const, smul_eq_mul, show T - (T - h) = h by ring] at this
  have l2 : ∫ t in (A - h)..A, N t ≤ h * N A := by
    have := integral_mono_on (a := A - h) (b := A) (by linarith) (hint _ _)
      (intervalIntegrable_const (c := N A)) (fun x hx => hN hx.2)
    rwa [intervalIntegral.integral_const, smul_eq_mul, show A - (A - h) = h by ring] at this
  linarith

/-! ## The jump set -/

/-- The set of `t` at which the count increases on `(t − h, t]`. -/
def jumpSet (h : ℝ) : Set ℝ := {t | 1 ≤ zeroCountReal t - zeroCountReal (t - h)}

theorem measurableSet_jumpSet (h : ℝ) : MeasurableSet (jumpSet h) :=
  measurableSet_le measurable_const
    (measurable_zeroCountReal.sub (measurable_zeroCountReal.comp (measurable_id.sub_const h)))

theorem intervalIntegrable_indicator_jumpSet (h : ℝ) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable ((jumpSet h).indicator (fun _ => (1 : ℝ))) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (integrableOn_const (s := Ioc a b) (μ := volume) (C := (1 : ℝ))
    measure_Ioc_lt_top.ne).indicator (measurableSet_jumpSet h)

/-- The increment of the count is a nonnegative integer: off the jump set it vanishes. -/
theorem zeroCountReal_sub_eq_zero_of_notMem {h t : ℝ} (hh : 0 ≤ h) (ht : t ∉ jumpSet h) :
    zeroCountReal t - zeroCountReal (t - h) = 0 := by
  have hmono : xiZeroCount (t - h) ≤ xiZeroCount t := xiZeroCount_mono (by linarith)
  have hlt : zeroCountReal t - zeroCountReal (t - h) < 1 := lt_of_not_ge ht
  unfold zeroCountReal at hlt ⊢
  have hz : xiZeroCount t - xiZeroCount (t - h) < 1 := by exact_mod_cast hlt
  have hz' : xiZeroCount t - xiZeroCount (t - h) = 0 := by omega
  have := congrArg (fun n : ℤ => (n : ℝ)) hz'
  push_cast at this
  exact this

/-! ## The main estimate -/

theorem exists_integral_abs_rvmRemainder_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop,
      c * (T / Real.log T) ≤ ∫ t in A..T, |rvmRemainder t| := by
  obtain ⟨Cr, hCr, T₀, hT₀4, hrem⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  obtain ⟨Cw, hCw, T₀', hT₀'4, hwin⟩ := exists_xiZeroCount_window_le
  have hb := routeKRVMBase_pos
  have hb1 := one_le_routeKRVMBase
  -- the base point
  set A₀ : ℝ := max (max T₀ T₀') (max (routeKRVMBase ^ 2) (Real.exp 1)) + 2 with hA₀
  have hA₀T₀ : T₀ + 2 ≤ A₀ := by
    have : T₀ ≤ max (max T₀ T₀') (max (routeKRVMBase ^ 2) (Real.exp 1)) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hA₀T₀' : T₀' + 2 ≤ A₀ := by
    have : T₀' ≤ max (max T₀ T₀') (max (routeKRVMBase ^ 2) (Real.exp 1)) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hA₀b : routeKRVMBase ^ 2 + 2 ≤ A₀ := by
    have : routeKRVMBase ^ 2 ≤ max (max T₀ T₀') (max (routeKRVMBase ^ 2) (Real.exp 1)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hA₀e : Real.exp 1 + 2 ≤ A₀ := by
    have : Real.exp 1 ≤ max (max T₀ T₀') (max (routeKRVMBase ^ 2) (Real.exp 1)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hA₀pos : 0 < A₀ - 1 := by linarith [Real.exp_pos 1]
  have hbA : routeKRVMBase ≤ A₀ - 1 := by nlinarith
  set K : ℝ := zeroCountReal A₀ with hK
  have hc0 : 0 < 1 / (256 * Real.pi * (1 + 2 * Cw)) := by
    have : 0 < 1 + 2 * Cw := by linarith
    positivity
  refine ⟨1 / (256 * Real.pi * (1 + 2 * Cw)), hc0, A₀ - 1, hA₀pos, ?_⟩
  -- the eventual conditions on `T`
  have hev1 : ∀ᶠ T : ℝ in atTop, A₀ + 2 ≤ T := eventually_ge_atTop _
  have hev2 : ∀ᶠ T : ℝ in atTop, Real.exp 2 ≤ T := eventually_ge_atTop _
  have hev3 : ∀ᶠ T : ℝ in atTop, 32 * Real.pi * (Cr + |K| + 1) ≤ T := eventually_ge_atTop _
  have hev4 : ∀ᶠ T : ℝ in atTop, 2 * routeKRVMBase ^ 2 + 2 ≤ T := eventually_ge_atTop _
  filter_upwards [hev1, hev2, hev3, hev4] with T hT1 hT2 hT3 hT4
  -- basic facts about `T`
  have hTpos : 0 < T := by linarith [Real.exp_pos 2]
  have hlogT : 2 ≤ Real.log T := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) hT2
  have hlogTpos : 0 < Real.log T := by linarith
  set h : ℝ := 1 / (2 * Real.log T) with hh
  have hhpos : 0 < h := by positivity
  have hh1 : h ≤ 1 / 4 := by
    rw [hh, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hT1' : A₀ + h ≤ T := by linarith
  set m : ℝ := 1 + 2 * Cw * Real.log T with hm
  have hmpos : 0 < m := by positivity
  -- Step 1: shift identity
  have hshift := mul_sub_le_integral_sub_comp_sub (A := A₀) (T := T) zeroCountReal_mono hhpos
  -- Step 2: pointwise ceiling by the jump-set indicator
  have hceil : ∀ t ∈ Icc A₀ T, zeroCountReal t - zeroCountReal (t - h) ≤
      m * (jumpSet h).indicator (fun _ => (1 : ℝ)) t := by
    intro t ht
    by_cases hmem : t ∈ jumpSet h
    · rw [indicator_of_mem hmem, mul_one]
      have hw := hwin (t - h) (by linarith [ht.1]) h hhpos.le
      rw [show t - h + h = t by ring] at hw
      unfold zeroCountReal
      refine hw.trans ?_
      have hlt : Real.log t ≤ Real.log T := Real.log_le_log (by linarith [ht.1]) ht.2
      have hlt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith [ht.1])
      have h1 : h / (2 * Real.pi) * Real.log t ≤ 1 := by
        rw [hh]
        have hπ : 6 < 2 * Real.pi := by linarith [Real.pi_gt_three]
        calc 1 / (2 * Real.log T) / (2 * Real.pi) * Real.log t
            ≤ 1 / (2 * Real.log T) / (2 * Real.pi) * Real.log T :=
              mul_le_mul_of_nonneg_left hlt (by positivity)
          _ = 1 / (2 * (2 * Real.pi)) := by field_simp
          _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have h2 : 2 * Cw * Real.log t ≤ 2 * Cw * Real.log T :=
        mul_le_mul_of_nonneg_left hlt (by positivity)
      rw [hm]; linarith
    · rw [indicator_of_notMem hmem, mul_zero]
      exact (zeroCountReal_sub_eq_zero_of_notMem hhpos.le hmem).le
  -- Step 3: integrate the ceiling
  have hint1 : IntervalIntegrable (fun t => zeroCountReal t - zeroCountReal (t - h)) volume A₀ T :=
    (intervalIntegrable_zeroCountReal _ _).sub
      (zeroCountReal_mono.comp (fun a b hab => sub_le_sub_right hab h)).intervalIntegrable
  have hint2 : IntervalIntegrable (fun t => m * (jumpSet h).indicator (fun _ => (1 : ℝ)) t)
      volume A₀ T :=
    (intervalIntegrable_indicator_jumpSet h (by linarith)).const_mul m
  have hE : ∫ t in A₀..T, (zeroCountReal t - zeroCountReal (t - h)) ≤
      m * volume.real (Ioc A₀ T ∩ jumpSet h) := by
    refine (integral_mono_on (by linarith) hint1 hint2 hceil).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_of_le (by linarith), setIntegral_indicator
      (measurableSet_jumpSet h), setIntegral_const, smul_eq_mul, mul_one]
  -- Step 4: the Riemann–von Mangoldt lower bound at `T − h`
  have hRVM : T / (64 * Real.pi) ≤ h * (zeroCountReal (T - h) - K) := by
    have hTh : routeKRVMBase ^ 2 + 1 ≤ T - h := by linarith
    have hTh0 : 0 < T - h := by linarith
    have hT0le : T₀ ≤ T - h := by linarith
    have hr := hrem (T - h) hT0le
    have hlog1 : Real.log (T - h) ≤ Real.log T := Real.log_le_log hTh0 (by linarith)
    -- `log((T−h)/b) ≥ ½ log(T−h)` since `T − h ≥ b²`
    have hlogb : Real.log routeKRVMBase ≤ Real.log (T - h) / 2 := by
      have : routeKRVMBase ^ 2 ≤ T - h := by linarith
      have h2 := Real.log_le_log (by positivity) this
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    have hlogTh : Real.log T - Real.log 2 ≤ Real.log (T - h) := by
      have : T / 2 ≤ T - h := by linarith
      have h2 := Real.log_le_log (by positivity) this
      rwa [Real.log_div hTpos.ne' (by norm_num)] at h2
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hM : (T - h) / (2 * Real.pi) * (Real.log (T - h) / 2) + 7 / 8 ≤
        routeKSmoothRVMCount (T - h) := by
      unfold routeKSmoothRVMCount
      rw [Real.log_div hTh0.ne' hb.ne']
      have hnn : 0 ≤ (T - h) / (2 * Real.pi) := by positivity
      have := mul_le_mul_of_nonneg_left
        (show Real.log (T - h) / 2 ≤ Real.log (T - h) - Real.log routeKRVMBase by linarith) hnn
      linarith
    have hN : (T - h) / (2 * Real.pi) * (Real.log (T - h) / 2) - Cr * Real.log T ≤
        zeroCountReal (T - h) := by
      unfold zeroCountReal
      have h1 := (abs_le.1 hr).1
      have h2 : Cr * Real.log (T - h) ≤ Cr * Real.log T := mul_le_mul_of_nonneg_left hlog1 hCr.le
      linarith
    -- assemble
    have hTT : T / 2 ≤ T - h := by linarith
    have hlogTh' : Real.log T / 2 ≤ Real.log (T - h) := by linarith
    have hprod : (T / 2) * (Real.log T / 2) ≤ (T - h) * Real.log (T - h) :=
      mul_le_mul hTT hlogTh' (by positivity) hTh0.le
    have hK' : K ≤ |K| := le_abs_self K
    have e2 : (T - h) / (2 * Real.pi) * (Real.log (T - h) / 2) =
        (T - h) * Real.log (T - h) / (4 * Real.pi) := by
      field_simp
      ring
    have e3 : T * Real.log T / (16 * Real.pi) ≤ (T - h) * Real.log (T - h) / (4 * Real.pi) := by
      have : T * Real.log T / (16 * Real.pi) = (T / 2) * (Real.log T / 2) / (4 * Real.pi) := by
        field_simp
        ring
      rw [this]
      exact div_le_div_of_nonneg_right hprod (by positivity)
    have e4 : Cr * Real.log T + |K| ≤ T * Real.log T / (32 * Real.pi) := by
      have h1 : (Cr + |K| + 1) * Real.log T ≤ T * Real.log T / (32 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_right hT3 hlogTpos.le
        linarith
      have h2 : |K| ≤ (|K| + 1) * Real.log T := by
        have := mul_le_mul_of_nonneg_left hlogT (by positivity : (0:ℝ) ≤ |K| + 1)
        linarith [abs_nonneg K]
      linarith [abs_nonneg K]
    have e5 : T * Real.log T / (16 * Real.pi) = 2 * (T * Real.log T / (32 * Real.pi)) := by
      field_simp
      ring
    have hN2 : T * Real.log T / (32 * Real.pi) ≤ zeroCountReal (T - h) - K := by
      rw [e2] at hN
      linarith [abs_nonneg K, e5]
    calc T / (64 * Real.pi) = 1 / (2 * Real.log T) * (T * Real.log T / (32 * Real.pi)) := by
          field_simp
          ring
      _ ≤ h * (zeroCountReal (T - h) - K) := by
          rw [hh]
          exact mul_le_mul_of_nonneg_left hN2 (by positivity)
  -- Step 5: measure of the jump set
  have hvolE : T / (64 * Real.pi) ≤ m * volume.real (Ioc A₀ T ∩ jumpSet h) :=
    hRVM.trans (hshift.trans hE)
  -- Step 6: on the jump set, `|S(t)| + |S(t − h)| ≥ ½`
  have hS : ∀ t ∈ Icc A₀ T, (1 / 2 : ℝ) * (jumpSet h).indicator (fun _ => (1 : ℝ)) t ≤
      |rvmRemainder t| + |rvmRemainder (t - h)| := by
    intro t ht
    by_cases hmem : t ∈ jumpSet h
    · rw [indicator_of_mem hmem, mul_one]
      have hjump : 1 ≤ zeroCountReal t - zeroCountReal (t - h) := hmem
      have hMlip := abs_routeKSmoothRVMCount_sub_le (A := A₀ - 1) (T := T) hbA
        (by linarith) (x := t - h) (y := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
        ⟨by linarith [ht.1], ht.2⟩
      rw [show t - (t - h) = h by ring, abs_of_pos hhpos] at hMlip
      have hMh : Real.log T * h = 1 / 2 := by
        rw [hh]; field_simp
      rw [hMh] at hMlip
      have hM2 := (abs_le.1 hMlip).2
      have hle : rvmRemainder t - rvmRemainder (t - h) ≤
          |rvmRemainder t| + |rvmRemainder (t - h)| :=
        (le_abs_self _).trans (abs_sub _ _)
      have hdiff : rvmRemainder t - rvmRemainder (t - h) =
          (zeroCountReal t - zeroCountReal (t - h)) -
            (routeKSmoothRVMCount t - routeKSmoothRVMCount (t - h)) := by
        unfold rvmRemainder; ring
      linarith
    · rw [indicator_of_notMem hmem, mul_zero]
      positivity
  -- Step 7: integrate
  have hcont : ContinuousOn routeKSmoothRVMCount (Icc (A₀ - 1 - h) T) :=
    continuousOn_routeKSmoothRVMCount.mono (fun z hz => by
      show 0 < z; linarith [hz.1, Real.exp_pos 1])
  have hSint : ∀ a b : ℝ, A₀ - 1 - h ≤ a → a ≤ b → b ≤ T →
      IntervalIntegrable rvmRemainder volume a b := by
    intro a b ha hab hb
    exact (intervalIntegrable_zeroCountReal a b).sub
      (ContinuousOn.intervalIntegrable_of_Icc hab (hcont.mono (Icc_subset_Icc ha hb)))
  have hI1 : IntervalIntegrable (fun t => |rvmRemainder t|) volume A₀ T :=
    (hSint A₀ T (by linarith) (by linarith) le_rfl).abs
  have hI2 : IntervalIntegrable (fun t => |rvmRemainder (t - h)|) volume A₀ T := by
    have := ((hSint (A₀ - h) (T - h) (by linarith) (by linarith) (by linarith)).abs).comp_sub_right h
    simpa using this
  have hI3 : IntervalIntegrable (fun t => (1 / 2 : ℝ) * (jumpSet h).indicator (fun _ => (1 : ℝ)) t)
      volume A₀ T :=
    (intervalIntegrable_indicator_jumpSet h (by linarith)).const_mul _
  have hvol : (1 / 2 : ℝ) * volume.real (Ioc A₀ T ∩ jumpSet h) ≤
      (∫ t in A₀..T, |rvmRemainder t|) + ∫ t in A₀..T, |rvmRemainder (t - h)| := by
    have := integral_mono_on (by linarith) hI3 (hI1.add hI2) hS
    rw [integral_add hI1 hI2] at this
    refine le_trans (le_of_eq ?_) this
    rw [intervalIntegral.integral_const_mul, integral_of_le (by linarith), setIntegral_indicator
      (measurableSet_jumpSet h), setIntegral_const, smul_eq_mul, mul_one]
  -- both integrals are bounded by the integral over `[A₀ − 1, T]`
  have hJ : ∀ a b : ℝ, A₀ - 1 ≤ a → a ≤ b → b ≤ T →
      ∫ t in a..b, |rvmRemainder t| ≤ ∫ t in (A₀ - 1)..T, |rvmRemainder t| := by
    intro a b ha hab hb
    exact integral_mono_interval ha hab hb (Eventually.of_forall fun t => abs_nonneg _)
      (hSint (A₀ - 1) T (by linarith) (by linarith) le_rfl).abs
  have hJ1 := hJ A₀ T (by linarith) (by linarith) le_rfl
  have hJ2 : ∫ t in A₀..T, |rvmRemainder (t - h)| ≤ ∫ t in (A₀ - 1)..T, |rvmRemainder t| := by
    rw [integral_comp_sub_right (fun t => |rvmRemainder t|) h]
    exact hJ (A₀ - h) (T - h) (by linarith) (by linarith) (by linarith)
  -- conclude
  have hfinal : T / (64 * Real.pi) / m ≤ volume.real (Ioc A₀ T ∩ jumpSet h) := by
    rw [div_le_iff₀ hmpos]; linarith
  have hmle : m ≤ (1 + 2 * Cw) * Real.log T := by
    rw [hm]; nlinarith
  calc 1 / (256 * Real.pi * (1 + 2 * Cw)) * (T / Real.log T)
      = (1 / 4) * (T / (64 * Real.pi) / ((1 + 2 * Cw) * Real.log T)) := by
        field_simp
        norm_num
    _ ≤ (1 / 4) * (T / (64 * Real.pi) / m) := by
        gcongr
    _ ≤ (1 / 4) * volume.real (Ioc A₀ T ∩ jumpSet h) := by gcongr
    _ ≤ (1 / 2) * ((∫ t in A₀..T, |rvmRemainder t|) + ∫ t in A₀..T, |rvmRemainder (t - h)|) := by
        linarith
    _ ≤ ∫ t in (A₀ - 1)..T, |rvmRemainder t| := by linarith

/-- **The size law.**  The zero-count remainder is not integrable on `(0, ∞)`. -/
theorem not_integrableOn_rvmRemainder : ¬ IntegrableOn rvmRemainder (Ioi 0) := by
  intro hint
  obtain ⟨c, hc, A, hA, hev⟩ := exists_integral_abs_rvmRemainder_ge
  have hbound : ∀ T : ℝ, A ≤ T → ∫ t in A..T, |rvmRemainder t| ≤ ∫ t in Ioi 0, |rvmRemainder t| := by
    intro T hT
    rw [integral_of_le hT]
    exact setIntegral_mono_set hint.abs (Eventually.of_forall fun t => abs_nonneg _)
      (Eventually.of_forall fun t ht => lt_trans hA ht.1)
  have hlim : Tendsto (fun T : ℝ => c * (T / Real.log T)) atTop atTop := by
    have h0 : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hpos : ∀ᶠ T : ℝ in atTop, 0 < Real.log T / T := by
      filter_upwards [eventually_gt_atTop 1] with T hT
      exact div_pos (Real.log_pos hT) (by linarith)
    have h1 : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨h0, hpos⟩
    have h2 : Tendsto (fun T : ℝ => (Real.log T / T)⁻¹) atTop atTop :=
      tendsto_inv_nhdsGT_zero.comp h1
    have h3 : Tendsto (fun T : ℝ => T / Real.log T) atTop atTop :=
      Filter.Tendsto.congr' (Eventually.of_forall fun T => inv_div (Real.log T) T) h2
    exact h3.const_mul_atTop hc
  have hev2 := (hlim.eventually (eventually_ge_atTop ((∫ t in Ioi 0, |rvmRemainder t|) + 1)))
  obtain ⟨T, hT1, hT2, hT3⟩ := (hev.and (hev2.and (eventually_ge_atTop A))).exists
  have := hbound T hT3
  linarith

end RHTower
