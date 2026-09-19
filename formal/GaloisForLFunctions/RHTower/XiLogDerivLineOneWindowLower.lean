import GaloisForLFunctions.RHTower.XiLogDerivLineOneGrowth
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder

/-!
# Bounded windows of zeros and the growth of `Re (ξ'/ξ)` on `Re s = 1`

The Riemann–von Mangoldt formula with its `O(log T)` remainder
(`exists_xiZeroCount_routeKSmoothRVMCount_log_remainder`) gives, for one fixed width `h`, at
least `log T` zeros of `ξ` with ordinate in `(T − h, T + h]` once `T` is large: the smooth main
term grows by `(2h/2π)·log(T/2π)` across the window while the two remainders cost `2C log T`.

Feeding this bounded window into the reflection-paired partial fraction of `ξ'/ξ` and the
Littlewood zero-free region (`1 − β ≥ c·log log γ / log γ`) gives

  `Re (ξ'/ξ)(1 + 2it) ≥ c₁ · log log t`   for all large `t`,

which replaces the earlier bound `c · log log t / t` obtained from the relative-error count.
In particular `Re (ξ'/ξ)(1 + 2it)` is bounded below by a positive constant and eventually
exceeds every constant.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- `(b − a)(log a + 1) ≤ b log b − a log a` for `0 < a ≤ b`. -/
theorem mul_log_sub_mul_log_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * (Real.log a + 1) ≤ b * Real.log b - a * Real.log a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h1 : 1 - (b / a)⁻¹ ≤ Real.log (b / a) := Real.one_sub_inv_le_log_of_pos (by positivity)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h1
  have h2 : b - a ≤ b * (Real.log b - Real.log a) := by
    have := mul_le_mul_of_nonneg_left h1 hb.le
    have e : b * (1 - a / b) = b - a := by field_simp
    linarith [this, e]
  nlinarith [h2]

/-- The smooth main term grows by at least `(b − a)·(log a − log 2π)/(2π)` between `a` and `b`. -/
theorem routeKSmoothRVMCount_sub_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * (Real.log a - Real.log (2 * Real.pi)) / (2 * Real.pi) ≤
      routeKSmoothRVMCount b - routeKSmoothRVMCount a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [routeKSmoothRVMCount_sub_eq ha hb]
  have hbase : Real.log routeKRVMBase = Real.log (2 * Real.pi) + 1 := by
    rw [routeKRVMBase, Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  rw [hbase]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := mul_log_sub_mul_log_ge ha hab
  nlinarith [this]

/-- **Bounded windows contain many zeros.**  There is a width `h` such that every window
`(T − h, T + h]` with `T` large contains at least `log T` zeros of `ξ` (with multiplicity). -/
theorem exists_xiZeroCount_window_ge_log :
    ∃ h : ℝ, 0 < h ∧ ∃ T₁ : ℝ, 4 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      Real.log T ≤ (xiZeroCount (T + h) : ℝ) - (xiZeroCount (T - h) : ℝ) := by
  obtain ⟨C, hC, T₀, _hT₀, hN⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  set h : ℝ := 2 * Real.pi * (4 * C + 1) with hh
  have hpos : 0 < h := by positivity
  have h144 : (144 : ℝ) ≤ (4 * Real.pi) ^ 2 := by nlinarith
  refine ⟨h, hpos, max (max (T₀ + h) (2 * h)) ((4 * Real.pi) ^ 2), ?_, fun T hT => ?_⟩
  · exact (by linarith : (4 : ℝ) ≤ (4 * Real.pi) ^ 2).trans (le_max_right _ _)
  have hT1 : T₀ + h ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans hT
  have hT2 : 2 * h ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans hT
  have hT3 : (4 * Real.pi) ^ 2 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have ha0 : 0 < T - h := by linarith
  have hab : T - h ≤ T + h := by linarith
  have hA := hN (T - h) (by linarith)
  have hB := hN (T + h) (by linarith)
  rw [abs_le] at hA hB
  have hmain := routeKSmoothRVMCount_sub_ge ha0 hab
  -- `2 log (4π) ≤ log T`
  have hlogT : 2 * Real.log (4 * Real.pi) ≤ Real.log T := by
    have := Real.log_le_log (by positivity) hT3
    rw [Real.log_pow] at this
    simp only [Nat.cast_ofNat] at this
    exact this
  have hlog4π : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
    have e : (4 : ℝ) * Real.pi = 2 * (2 * Real.pi) := by ring
    rw [e, Real.log_mul (by norm_num) (by positivity)]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2πpos : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith)
  -- `(1/2) log T ≤ log (T − h) − log (2π)`
  have hlog_a : Real.log (T / 2) ≤ Real.log (T - h) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogT2 : Real.log (T / 2) = Real.log T - Real.log 2 := Real.log_div hT0.ne' (by norm_num)
  have hhalf : (1 / 2) * Real.log T ≤ Real.log (T - h) - Real.log (2 * Real.pi) := by
    linarith
  -- `log (T ± h) ≤ 2 log T`
  have hlog2T : Real.log (2 * T) = Real.log 2 + Real.log T := Real.log_mul (by norm_num) hT0.ne'
  have hlog2le : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
  have hlogb : Real.log (T + h) ≤ 2 * Real.log T := by
    have h1 : Real.log (T + h) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
    linarith
  have hloga : Real.log (T - h) ≤ 2 * Real.log T := by
    have h1 : Real.log (T - h) ≤ Real.log T := Real.log_le_log ha0 (by linarith)
    linarith
  -- the window count from the two remainders
  have hcount : (routeKSmoothRVMCount (T + h) - routeKSmoothRVMCount (T - h)) -
      C * Real.log (T + h) - C * Real.log (T - h) ≤
      (xiZeroCount (T + h) : ℝ) - (xiZeroCount (T - h) : ℝ) := by
    linarith [hA.1, hA.2, hB.1, hB.2]
  have hmain2 : (2 * h) * ((1 / 2) * Real.log T) / (2 * Real.pi) ≤
      (T + h - (T - h)) * (Real.log (T - h) - Real.log (2 * Real.pi)) / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have e : T + h - (T - h) = 2 * h := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hhalf (by positivity)
  have hval : (2 * h) * ((1 / 2) * Real.log T) / (2 * Real.pi) = (4 * C + 1) * Real.log T := by
    rw [hh]; field_simp; try ring
  have e1 := mul_le_mul_of_nonneg_left hlogb hC.le
  have e2 := mul_le_mul_of_nonneg_left hloga hC.le
  linarith

/-- **`Re (ξ'/ξ)(1 + 2it) ≥ c₁ · log log t`.**  A bounded window around ordinate `2t` carries at
least `log (2t)` zeros, each contributing at least `c·log log t / (2 log t · (1 + h²))` to the
reflection-paired partial fraction of `ξ'/ξ` at `1 + 2it`. -/
theorem exists_re_logDeriv_xi_lineOne_loglog_lower' :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ t₀ : ℝ, 16 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      c₁ * Real.log (Real.log t) ≤ (logDeriv xi (1 + 2 * t * I)).re := by
  classical
  obtain ⟨c, TL, hc, _hTL, hzf⟩ := Sieve.exists_littlewood_zero_free_region_abs
  obtain ⟨h, hh, T₁, _hT₁, hwin⟩ := exists_xiZeroCount_window_ge_log
  refine ⟨c / (4 * (1 + h ^ 2)), by positivity, max (max T₁ TL) (max 16 h), ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  intro t ht
  have ht16 : (16 : ℝ) ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht
  have hth : h ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans ht
  have htT₁ : T₁ ≤ t := ((le_max_left _ _).trans (le_max_left _ _)).trans ht
  have htTL : TL ≤ t := ((le_max_right _ _).trans (le_max_left _ _)).trans ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : (1 : ℝ) ≤ Real.log t := by
    have h : Real.log (Real.exp 1) ≤ Real.log t :=
      Real.log_le_log (Real.exp_pos 1) ((Real.exp_one_lt_d9.le.trans (by norm_num)).trans ht16)
    rwa [Real.log_exp] at h
  have hloglog : (0 : ℝ) ≤ Real.log (Real.log t) := Real.log_nonneg hlogt
  have hlog3t : Real.log (3 * t) ≤ 2 * Real.log t := by
    rw [Real.log_mul (by norm_num) ht0.ne']
    have : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
    linarith
  set s : ℂ := 1 + 2 * t * I with hsdef
  have hs1 : s.re = 1 := by simp [hsdef]
  have hsne : xi s ≠ 0 := xi_ne_zero_of_one_le_re (by rw [hs1])
  set m : ℝ := c * Real.log (Real.log t) / (2 * Real.log t) / (1 + h ^ 2) with hmdef
  have hm0 : 0 ≤ m := by positivity
  have hlo : 0 ≤ 2 * t - h := by linarith
  -- every zero of the window `(2t − h, 2t + h]` contributes at least `m`
  have hterm : ∀ ρ ∈ xiSupportsWindow (2 * t - h) (2 * t + h), m ≤ xiPairedSupportTerm s ρ := by
    intro ρ hρ
    rw [mem_xiSupportsWindow hlo] at hρ
    obtain ⟨hγ1, hγ2⟩ := hρ
    have hγt : t ≤ (ρ : ℂ).im := by linarith
    have hγpos : 0 < (ρ : ℂ).im := by linarith
    have habs : |(ρ : ℂ).im| = (ρ : ℂ).im := abs_of_pos hγpos
    obtain ⟨hβ0, hβ1⟩ := xi_divisor_support_re_mem_open_unit ρ
    have hzf' := one_sub_re_ge_of_littlewood hzf ρ (by rw [habs]; linarith)
    rw [habs] at hzf'
    have hlogγ : Real.log t ≤ Real.log (ρ : ℂ).im := Real.log_le_log ht0 hγt
    have hlogγ3 : Real.log (ρ : ℂ).im ≤ Real.log (3 * t) :=
      Real.log_le_log hγpos (by linarith)
    have hloglogγ : Real.log (Real.log t) ≤ Real.log (Real.log (ρ : ℂ).im) :=
      Real.log_le_log (by linarith) hlogγ
    have hwidth : c * Real.log (Real.log t) / (2 * Real.log t) ≤
        c * Real.log (Real.log (ρ : ℂ).im) / Real.log (ρ : ℂ).im := by
      have hnum : c * Real.log (Real.log t) ≤ c * Real.log (Real.log (ρ : ℂ).im) :=
        mul_le_mul_of_nonneg_left hloglogγ hc.le
      have hlogγpos : 0 < Real.log (ρ : ℂ).im := by linarith
      have hden : Real.log (ρ : ℂ).im ≤ 2 * Real.log t := hlogγ3.trans hlog3t
      calc c * Real.log (Real.log t) / (2 * Real.log t)
          ≤ c * Real.log (Real.log (ρ : ℂ).im) / (2 * Real.log t) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ c * Real.log (Real.log (ρ : ℂ).im) / Real.log (ρ : ℂ).im :=
            div_le_div_of_nonneg_left
              (mul_nonneg hc.le (Real.log_nonneg (by linarith))) hlogγpos hden
    have h1β : c * Real.log (Real.log t) / (2 * Real.log t) ≤ 1 - (ρ : ℂ).re :=
      hwidth.trans hzf'
    have hnormSq : normSq (s - (ρ : ℂ)) ≤ 1 + h ^ 2 := by
      rw [Complex.normSq_apply]
      have hre : (s - (ρ : ℂ)).re = 1 - (ρ : ℂ).re := by simp [hsdef]
      have him : (s - (ρ : ℂ)).im = 2 * t - (ρ : ℂ).im := by simp [hsdef]
      rw [hre, him]
      have h1 : (1 - (ρ : ℂ).re) * (1 - (ρ : ℂ).re) ≤ 1 := by nlinarith
      have h2 : (2 * t - (ρ : ℂ).im) * (2 * t - (ρ : ℂ).im) ≤ h ^ 2 := by nlinarith
      linarith
    have hnormSq_pos : 0 < normSq (s - (ρ : ℂ)) := by
      apply Complex.normSq_pos.mpr
      intro h
      have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.zero_re, hs1] at this
      linarith
    calc m = c * Real.log (Real.log t) / (2 * Real.log t) / (1 + h ^ 2) := rfl
      _ ≤ (1 - (ρ : ℂ).re) / (1 + h ^ 2) := div_le_div_of_nonneg_right h1β (by positivity)
      _ ≤ (1 - (ρ : ℂ).re) / normSq (s - (ρ : ℂ)) :=
          div_le_div_of_nonneg_left (by linarith) hnormSq_pos hnormSq
      _ ≤ xiPairedSupportTerm s ρ := xiPairedSupportTerm_ge hs1 ρ
  -- the window count
  have hcount : Real.log t ≤ (xiZeroCount (2 * t + h) : ℝ) - (xiZeroCount (2 * t - h) : ℝ) := by
    have := hwin (2 * t) (by linarith)
    have hl : Real.log t ≤ Real.log (2 * t) := Real.log_le_log ht0 (by linarith)
    linarith
  -- assemble
  have hsum := summable_xiPairedResolventTerm hsne
  have hwinle : ∑ q ∈ xiCopiesOf (xiSupportsWindow (2 * t - h) (2 * t + h)),
      xiPairedResolventTerm s q ≤ ∑' q : XiZeroCopy, xiPairedResolventTerm s q :=
    hsum.sum_le_tsum _ (fun q _ => (xiPairedResolventTerm_pos (by rw [hs1]) q).le)
  rw [sum_xiCopiesOf] at hwinle
  have hlow : ∑ ρ ∈ xiSupportsWindow (2 * t - h) (2 * t + h),
      (xiSupportMultiplicity ρ : ℝ) * m ≤
      ∑ ρ ∈ xiSupportsWindow (2 * t - h) (2 * t + h),
        (xiSupportMultiplicity ρ : ℝ) * xiPairedSupportTerm s ρ :=
    Finset.sum_le_sum (fun ρ hρ => mul_le_mul_of_nonneg_left (hterm ρ hρ) (by positivity))
  rw [← Finset.sum_mul, sum_mult_xiSupportsWindow hlo (by linarith)] at hlow
  have htwice := two_mul_re_logDeriv_xi_eq_tsum_paired hsne
  have hprod : Real.log t * m ≤
      ((xiZeroCount (2 * t + h) : ℝ) - (xiZeroCount (2 * t - h) : ℝ)) * m :=
    mul_le_mul_of_nonneg_right hcount hm0
  have h2re : Real.log t * m ≤ 2 * (logDeriv xi s).re := by linarith
  have hlogt_pos : 0 < Real.log t := by linarith
  have hval : Real.log t * m = c * Real.log (Real.log t) / (2 * (1 + h ^ 2)) := by
    rw [hmdef]; field_simp; try ring
  have hfinal : c / (4 * (1 + h ^ 2)) * Real.log (Real.log t) =
      c * Real.log (Real.log t) / (2 * (1 + h ^ 2)) / 2 := by
    field_simp; ring
  rw [hfinal]
  linarith

/-- **A positive constant lower bound for `Re (ξ'/ξ)(1 + 2it)`.** -/
theorem exists_re_logDeriv_xi_lineOne_const_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ t₀ : ℝ, 16 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      c₀ ≤ (logDeriv xi (1 + 2 * t * I)).re := by
  obtain ⟨c₁, hc₁, t₀, ht₀, h⟩ := exists_re_logDeriv_xi_lineOne_loglog_lower'
  refine ⟨c₁, hc₁, max t₀ (Real.exp (Real.exp 1)), ht₀.trans (le_max_left _ _),
    fun t ht => ?_⟩
  have h1 : t₀ ≤ t := (le_max_left _ _).trans ht
  have h2 : Real.exp (Real.exp 1) ≤ t := (le_max_right _ _).trans ht
  have hll : 1 ≤ Real.log (Real.log t) := by
    have ha : Real.exp 1 ≤ Real.log t := by
      have := Real.log_le_log (Real.exp_pos _) h2
      rwa [Real.log_exp] at this
    have hb := Real.log_le_log (Real.exp_pos _) ha
    rwa [Real.log_exp] at hb
  calc c₁ = c₁ * 1 := by ring
    _ ≤ c₁ * Real.log (Real.log t) := mul_le_mul_of_nonneg_left hll hc₁.le
    _ ≤ _ := h t h1

/-- **`Re (ξ'/ξ)(1 + 2it)` eventually exceeds every constant.** -/
theorem exists_re_logDeriv_xi_lineOne_ge (A : ℝ) :
    ∃ t₀ : ℝ, 16 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → A ≤ (logDeriv xi (1 + 2 * t * I)).re := by
  obtain ⟨c₁, hc₁, t₀, ht₀, h⟩ := exists_re_logDeriv_xi_lineOne_loglog_lower'
  refine ⟨max t₀ (Real.exp (Real.exp (max (A / c₁) 1))), ht₀.trans (le_max_left _ _),
    fun t ht => ?_⟩
  have h1 : t₀ ≤ t := (le_max_left _ _).trans ht
  have h2 : Real.exp (Real.exp (max (A / c₁) 1)) ≤ t := (le_max_right _ _).trans ht
  have hll : max (A / c₁) 1 ≤ Real.log (Real.log t) := by
    have ha : Real.exp (max (A / c₁) 1) ≤ Real.log t := by
      have := Real.log_le_log (Real.exp_pos _) h2
      rwa [Real.log_exp] at this
    have hb := Real.log_le_log (Real.exp_pos _) ha
    rwa [Real.log_exp] at hb
  have hA : A / c₁ ≤ Real.log (Real.log t) := (le_max_left _ _).trans hll
  have hAle : A ≤ c₁ * Real.log (Real.log t) := by
    have := mul_le_mul_of_nonneg_left hA hc₁.le
    rwa [mul_div_cancel₀ _ hc₁.ne'] at this
  exact hAle.trans (h t h1)

end

end RHTower
