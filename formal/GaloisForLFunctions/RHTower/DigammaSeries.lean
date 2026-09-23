import GaloisForLFunctions.RHTower.VanDerCorput

open MeasureTheory intervalIntegral Complex Set Filter Topology

noncomputable section

namespace RHTower

/-! ## Digamma asymptotics (S4)

The digamma function `ψ = logDeriv Γ` satisfies the Weierstrass series
`ψ(s) = -γ + Σ_{n≥0} (1/(n+1) - 1/(n+s))` and the asymptotics
`ψ(z) = log z + O(1/|z|)`, `ψ'(z) = 1/z + O(1/|z|²)` on sectors away from `ℝ_{≤0}`.
Route: Euler's limit `Γ(s) = lim n!·n^s/∏_{k≤n}(s+k)` from the truncated-exponential
integral (DCT), then log-derivative interchange via locally uniform convergence.
-/

/-- For `0 ≤ x ≤ n`, `(1 - x/n)^n ≤ e^{-x}`. -/
theorem one_sub_div_pow_le_exp_neg {x : ℝ} {n : ℕ} (hn : 1 ≤ n) (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    (1 - x / n) ^ n ≤ Real.exp (-x) := by
  rcases eq_or_lt_of_le hxn with rfl | hlt
  · have h0 : (1 : ℝ) - (n : ℝ) / n = 0 := by
      rw [div_self (by positivity : (↑n : ℝ) ≠ 0), sub_self]
    rw [h0, zero_pow (Nat.one_le_iff_ne_zero.mp hn)]
    exact Real.exp_nonneg _
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (0 : ℝ) < 1 - x / n := by
      rw [sub_pos]
      exact (div_lt_iff₀ hn').mpr (by simpa using hlt)
    have h2 : Real.log (1 - x / n) ≤ -x / n :=
      (Real.log_le_sub_one_of_pos h1).trans (by ring_nf; linarith)
    have h3 : (↑n : ℝ) * Real.log (1 - x / n) ≤ -x := by
      have := mul_le_mul_of_nonneg_left h2 (le_of_lt hn')
      rw [mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt hn')] at this
      linarith [this]
    calc (1 - x / n) ^ n = (Real.exp (Real.log (1 - x / n))) ^ n := by
          rw [Real.exp_log h1]
      _ = Real.exp (↑n * Real.log (1 - x / n)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-x) := Real.exp_le_exp.mpr h3

/-- Pointwise limit: for fixed `x`, `(1 - x/n)^n → e^{-x}`. -/
theorem tendsto_one_sub_div_pow (x : ℝ) :
    Tendsto (fun n : ℕ => (1 - x / n) ^ n) atTop (𝓝 (Real.exp (-x))) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have : (fun n : ℕ => (1 - (0:ℝ)/n) ^ n) = fun _ => (1:ℝ) := by
      funext n
      simp
    rw [this]
    simp only [neg_zero, Real.exp_zero]
    exact tendsto_const_nhds
  · have hmain : Tendsto (fun n : ℕ => (↑n : ℝ) * Real.log (1 - x / n)) atTop (𝓝 (-x)) := by
      have h1 : Tendsto (fun n : ℕ => (↑n : ℝ) * Real.log (1 - x / n) + x) atTop (𝓝 0) := by
        apply squeeze_zero_norm' (a := fun n : ℕ => 2 * x ^ 2 / (n : ℝ))
        · filter_upwards [(eventually_atTop.2 ⟨⌈2 * |x|⌉₊, fun b hb => by
            have h1 : (2 * |x| : ℝ) ≤ (⌈2 * |x|⌉₊ : ℝ) := Nat.le_ceil _
            have h2 : (⌈2 * |x|⌉₊ : ℝ) ≤ b := Nat.cast_le.mpr hb
            show 2 * |x| ≤ (b : ℝ)
            linarith⟩)] with n hn
          have hn' : (0 : ℝ) < n := by
            have hnn := abs_nonneg (x : ℝ)
            have hxp : (0 : ℝ) < 2 * |x| := by positivity
            linarith
          have hxn : |x / n| ≤ 1 / 2 := by
            rw [abs_div]
            have hnabs : |(n : ℝ)| = (n : ℝ) := abs_of_pos hn'
            rw [hnabs, div_le_iff₀ hn']
            nlinarith [hn, abs_nonneg x]
          have hb := Real.abs_log_sub_add_sum_range_le (x := x / n)
            (lt_of_le_of_lt hxn (by norm_num : (1:ℝ)/2 < 1)) 1
          simp only [Finset.range_one, Finset.sum_singleton, pow_one, Nat.cast_zero,
            zero_add, div_one] at hb
          have h2 : |(↑n : ℝ) * Real.log (1 - x / n) + x| =
              ↑n * |(x / n) + Real.log (1 - x / n)| := by
            have he : (↑n : ℝ) * Real.log (1 - x / n) + x =
                ↑n * ((x / n) + Real.log (1 - x / n)) := by
              field_simp [ne_of_gt hn']
              ring
            rw [he, abs_mul, abs_of_pos hn']
          rw [Real.norm_eq_abs, h2]
          have h3 : ↑n * |(x / n) + Real.log (1 - x / n)| ≤
              ↑n * (|x / n| ^ 2 / (1 - |x / n|)) :=
            mul_le_mul_of_nonneg_left hb (le_of_lt hn')
          have h4 : ↑n * (|x / n| ^ 2 / (1 - |x / n|)) ≤ 2 * x ^ 2 / n := by
            have h5 : (1:ℝ) / 2 ≤ 1 - |x / n| := by linarith [hxn, abs_nonneg (x / n)]
            calc ↑n * (|x / n| ^ 2 / (1 - |x / n|))
                = ↑n * ((|x| / n) ^ 2 / (1 - |x / n|)) := by
                  simp only [abs_div, abs_of_pos hn']
              _ = (|x| ^ 2 / n) / (1 - |x / n|) := by
                  field_simp [ne_of_gt hn']
                  try ring
              _ ≤ (|x| ^ 2 / n) / (1 / 2) := by
                  apply div_le_div_of_nonneg_left _ (by norm_num : (0:ℝ) < 1/2) h5
                  exact div_nonneg (sq_nonneg _) (le_of_lt hn')
              _ = 2 * x ^ 2 / n := by
                  rw [sq_abs]
                  field_simp
                  try ring
          exact h3.trans h4
        · exact tendsto_const_div_atTop_nhds_zero_nat (2 * x ^ 2)
      have := h1.add (tendsto_const_nhds (x := -x))
      simpa using this
    have heq : (fun n : ℕ => (1 - x / n) ^ n) =ᶠ[atTop]
        fun n : ℕ => Real.exp ((↑n : ℝ) * Real.log (1 - x / n)) := by
      filter_upwards [(eventually_atTop.2 ⟨⌈x⌉₊ + 1, fun b hb => by
        have h1 : (x : ℝ) ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈x⌉₊ : ℝ) + 1 ≤ b := by exact_mod_cast hb
        show x < (b : ℝ) ∧ (1 : ℝ) ≤ b
        constructor
        · linarith
        · linarith⟩)] with n hn
      have hn' : (0 : ℝ) < n := by linarith [hn.2]
      have h1 : (0 : ℝ) < 1 - x / n := by
        rw [sub_pos]
        exact (div_lt_iff₀ hn').mpr (by simpa using hn.1)
      nth_rewrite 1 [← Real.exp_log h1]
      rw [← Real.exp_nat_mul]
    exact hmain.rexp.congr' heq.symm

/-- Norm of the weighted beta integrand `(1-u)^m · u^t` is dominated by `u^(t.re)`. -/
private theorem norm_beta_le {m : ℕ} {t : ℂ} {u : ℝ} (hu : u ∈ Set.Ioc (0:ℝ) 1) :
    ‖((1 - (u : ℂ))) ^ m * (u : ℂ) ^ t‖ ≤ u ^ t.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1]
  have h4 : ‖((1 - (u : ℂ))) ^ m‖ = (1 - u) ^ m := by
    have heq : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
    rw [heq, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by linarith [hu.1, hu.2]) _)]
  rw [h4]
  have h6 : (1 - u) ^ m ≤ 1 := by
    apply pow_le_one₀
    · linarith [hu.1, hu.2]
    · linarith [hu.1, hu.2]
  have h9 : 0 ≤ (1 - u) ^ m := pow_nonneg (by linarith [hu.1, hu.2]) _
  have h10 : 0 ≤ u ^ t.re := Real.rpow_nonneg (le_of_lt hu.1) t.re
  nlinarith [h6, h9, h10]

/-- Continuity of `u ↦ (u : ℂ)^t` on `(0,b]`, any complex `t`. -/
theorem continuousOn_Ioc_cpow (t : ℂ) (b : ℝ) : ContinuousOn (fun u : ℝ => (u : ℂ) ^ t)
    (Set.Ioc 0 b) := by
  by_cases ht0 : t = 0
  · rw [ht0]
    simp only [Complex.cpow_zero]
    exact continuousOn_const
  · intro u hu
    exact (DifferentiableAt.ofReal_cpow_const differentiableAt_id (ne_of_gt hu.1)
      ht0).continuousAt.continuousWithinAt

/-- Continuity of `u ↦ (u : ℂ)^t` on `(0,∞)`, any complex `t`. -/
theorem continuousOn_Ioi_cpow (t : ℂ) : ContinuousOn (fun u : ℝ => (u : ℂ) ^ t)
    (Set.Ioi 0) := by
  by_cases ht0 : t = 0
  · rw [ht0]
    simp only [Complex.cpow_zero]
    exact continuousOn_const
  · intro u hu
    exact (DifferentiableAt.ofReal_cpow_const differentiableAt_id (ne_of_gt hu)
      ht0).continuousAt.continuousWithinAt

/-- Strong measurability of a set-indicator from continuity on the set (complex). -/
theorem aestronglyMeasurable_indicator_of_continuousOn {f : ℝ → ℂ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf : ContinuousOn f s) :
    AEStronglyMeasurable (s.indicator f) volume := by
  have h1 : AEStronglyMeasurable f (volume.restrict s) := hf.aestronglyMeasurable hs
  have h2 : AEStronglyMeasurable (s.indicator (h1.mk f)) volume :=
    (h1.stronglyMeasurable_mk.indicator hs).aestronglyMeasurable
  apply h2.congr
  apply ae_of_ae_restrict_of_ae_restrict_compl s
  · exact Filter.EventuallyEq.indicator h1.ae_eq_mk.symm
  · exact ae_restrict_of_forall_mem hs.compl (fun x hx => by
      simp [Set.indicator_of_notMem hx])

/-- Strong measurability of a set-indicator from continuity on the set (real). -/
theorem aestronglyMeasurable_indicator_of_continuousOn_real {f : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf : ContinuousOn f s) :
    AEStronglyMeasurable (s.indicator f) volume := by
  have h1 : AEStronglyMeasurable f (volume.restrict s) := hf.aestronglyMeasurable hs
  have h2 : AEStronglyMeasurable (s.indicator (h1.mk f)) volume :=
    (h1.stronglyMeasurable_mk.indicator hs).aestronglyMeasurable
  apply h2.congr
  apply ae_of_ae_restrict_of_ae_restrict_compl s
  · exact Filter.EventuallyEq.indicator h1.ae_eq_mk.symm
  · exact ae_restrict_of_forall_mem hs.compl (fun x hx => by
      simp [Set.indicator_of_notMem hx])

/-- Integrability of `(1-u)^m · u^t` on `(0,1]` for `-1 < Re t`. -/
theorem integrableOn_Ioc_beta (m : ℕ) (t : ℂ) (ht : -1 < t.re) :
    IntegrableOn (fun u : ℝ => ((1 - (u : ℂ))) ^ m * (u : ℂ) ^ t)
      (Set.Ioc 0 1) volume := by
  have h1 : IntervalIntegrable (fun u : ℝ => u ^ t.re) volume 0 1 :=
    intervalIntegrable_rpow' ht
  have h2 : IntegrableOn (fun u : ℝ => u ^ t.re) (Set.Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h1
  have h3 : AEStronglyMeasurable (fun u : ℝ => ((1 - (u : ℂ))) ^ m * (u : ℂ) ^ t)
      (volume.restrict (Set.Ioc 0 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply ContinuousOn.mul
    · exact ((by continuity : Continuous (fun u : ℝ => (1 : ℂ) - (u : ℂ))).continuousOn).pow m
    · exact continuousOn_Ioc_cpow t 1
  rw [IntegrableOn] at h2 ⊢
  apply Integrable.mono' h2 h3
  exact ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => norm_beta_le hu)

/-- The beta integral at `n = 0`: `∫_0^(1 : ℕ) u^{s-1} du = 1/s` for `0 < Re s`. -/
theorem beta_integral_zero (s : ℂ) (hs : 0 < s.re) :
    ∫ u in (0 : ℝ)..1, (u : ℂ) ^ (s - 1) = 1 / s := by
  have h1 : -1 < (s - 1).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith [hs]
  have h2 := integral_cpow (a := 0) (b := 1) (r := s - 1) (Or.inl h1)
  rw [sub_add_cancel] at h2
  rw [h2]
  simp [Complex.ofReal_zero, Complex.ofReal_one, Complex.one_cpow,
    Complex.zero_cpow (Complex.ne_zero_of_re_pos hs)]

/-- IBP step for the beta integral at the singular left endpoint:
`B_{n+1}(s) = ((n+1)/s)·B_n(s+1)`. -/
theorem beta_integral_succ_step (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ∫ u in (0 : ℝ)..1, ((1 : ℂ) - u) ^ (n + 1) * (u : ℂ) ^ (s - 1) =
      ((n + 1 : ℂ) / s) * ∫ u in (0 : ℝ)..1, ((1 : ℂ) - u) ^ n * (u : ℂ) ^ s := by
  have hsne : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hs1 : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith [hs]
  set U : ℝ → ℂ := fun u => (1 - (u : ℂ)) ^ (n + 1) with hUdef
  set V : ℝ → ℂ := fun u => (u : ℂ) ^ s / s with hVdef
  have hUd : ∀ u : ℝ, HasDerivAt U (-((n + 1 : ℂ)) * ((1 - (u : ℂ))) ^ n) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => (1 - (u : ℂ))) (-1 : ℂ) u := by
      have h2 : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) u := (hasDerivAt_id u).ofReal_comp
      exact h2.const_sub (1 : ℂ)
    have h3 := h1.pow (n + 1)
    have h5 : (↑(n + 1) : ℂ) * (1 - (u : ℂ)) ^ (n + 1 - 1) * (-1 : ℂ) =
        -((n + 1 : ℂ)) * ((1 - (u : ℂ))) ^ n := by
      push_cast
      ring
    rw [h5] at h3
    exact h3
  have hVd : ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt V ((u : ℂ) ^ (s - 1)) u := by
    intro u hu
    have hr : s - 1 ≠ -1 := fun h => hsne (by
      calc s = s - 1 + 1 := by ring
        _ = -1 + 1 := by rw [h]
        _ = 0 := by ring)
    have h1 := hasDerivAt_ofReal_cpow_const' (x := u) (r := s - 1) (ne_of_gt hu.1) hr
    rw [sub_add_cancel] at h1
    exact h1
  set W : ℝ → ℂ := fun u => U u * V u with hWdef
  have hWd : ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt W
      (-((n + 1 : ℂ)) * ((1 - (u : ℂ))) ^ n * V u + U u * (u : ℂ) ^ (s - 1)) u := by
    intro u hu
    exact (hUd u).mul (hVd u hu)
  have hiiA : IntervalIntegrable (fun u : ℝ =>
      -((n + 1 : ℂ)) * ((1 - (u : ℂ))) ^ n * V u) volume 0 1 := by
    have h1 : (fun u : ℝ => -((n + 1 : ℂ)) * ((1 - (u : ℂ))) ^ n * V u) =
        fun u : ℝ => (-((n + 1 : ℂ)) / s) * (((1 - (u : ℂ))) ^ n * (u : ℂ) ^ s) := by
      ext u
      rw [hVdef]
      field_simp [hsne]
      try ring
    rw [h1]
    apply IntervalIntegrable.const_mul
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    exact integrableOn_Ioc_beta n s (by linarith [hs])
  have hiiB : IntervalIntegrable (fun u : ℝ => U u * (u : ℂ) ^ (s - 1)) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    exact integrableOn_Ioc_beta (n + 1) (s - 1) (by
      rw [Complex.sub_re, Complex.one_re]; linarith [hs])
  have hUint : IntervalIntegrable (fun u : ℝ =>
      -((n + 1 : ℂ)) * ((1 - (u : ℂ))) ^ n * V u + U u * (u : ℂ) ^ (s - 1)) volume 0 1 :=
    hiiA.add hiiB
  have ha : Tendsto W (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun u : ℝ => u ^ s.re / ‖s‖)
    · filter_upwards [Filter.inter_mem self_mem_nhdsWithin
        (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)))] with u hu
      have h1 : 0 < u := hu.1
      have hu1 : u < 1 := hu.2
      have h2 : ‖W u‖ = (1 - u) ^ (n + 1) * u ^ s.re / ‖s‖ := by
        have heq : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
        rw [hWdef, hUdef, hVdef]
        show ‖(1 - ↑u) ^ (n + 1) * ((u : ℂ) ^ s / s)‖ = (1 - u) ^ (n + 1) * u ^ s.re / ‖s‖
        rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos h1,
          heq, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (by linarith [h1, hu1]) _)]
        ring
      rw [h2]
      apply div_le_div_of_nonneg_right _ (le_of_lt (norm_pos_iff.mpr hsne))
      have h6 : (1 - u) ^ (n + 1) ≤ 1 := by
        apply pow_le_one₀
        · linarith [h1]
        · linarith [h1, hu1]
      have h9 : 0 ≤ (1 - u) ^ (n + 1) := by positivity
      have h10 : 0 ≤ u ^ s.re := Real.rpow_nonneg (le_of_lt h1) s.re
      nlinarith [h6, h9, h10]
    · have hlim : Tendsto (fun u : ℝ => u ^ s.re) (𝓝[>] 0) (𝓝 0) := by
        have h0 : (0 : ℝ) ^ s.re = 0 := Real.zero_rpow (ne_of_gt hs)
        have hcont : ContinuousAt (fun u : ℝ => u ^ s.re) 0 :=
          Real.continuousAt_rpow_const 0 s.re (Or.inr (le_of_lt hs))
        have h1 : Tendsto (fun u : ℝ => u ^ s.re) (𝓝 0) (𝓝 ((0:ℝ) ^ s.re)) := hcont.tendsto
        rw [h0] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      have h2 := hlim.div_const ‖s‖
      rwa [zero_div] at h2
  have hb : Tendsto W (𝓝[<] 1) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun u : ℝ => (1 - u) ^ (n + 1) / ‖s‖)
    · filter_upwards [Filter.inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1)))
        self_mem_nhdsWithin] with u hu
      have h1 : 0 < u := hu.1
      have hu1 : u < 1 := hu.2
      have h2 : ‖W u‖ = (1 - u) ^ (n + 1) * u ^ s.re / ‖s‖ := by
        have heq : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
        rw [hWdef, hUdef, hVdef]
        show ‖(1 - ↑u) ^ (n + 1) * ((u : ℂ) ^ s / s)‖ = (1 - u) ^ (n + 1) * u ^ s.re / ‖s‖
        rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos h1,
          heq, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (by linarith [h1, hu1]) _)]
        ring
      rw [h2]
      apply div_le_div_of_nonneg_right _ (le_of_lt (norm_pos_iff.mpr hsne))
      have h6 : u ^ s.re ≤ 1 := by
        apply Real.rpow_le_one (le_of_lt h1) (le_of_lt hu1) (le_of_lt hs)
      have h9 : 0 ≤ u ^ s.re := Real.rpow_nonneg (le_of_lt h1) s.re
      nlinarith [h6, h9, pow_nonneg (by linarith [h1] : (0:ℝ) ≤ 1 - u) (n + 1)]
    · have hlim : Tendsto (fun u : ℝ => (1 - u) ^ (n + 1)) (𝓝[<] 1) (𝓝 0) := by
        have h2 : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) :=
          (continuousAt_id.tendsto).mono_left nhdsWithin_le_nhds
        have h3 : Tendsto (fun u : ℝ => 1 - u) (𝓝[<] 1) (𝓝 0) := by
          have h4 := (tendsto_const_nhds (x := (1:ℝ))).sub h2
          simpa using h4
        have h4 := h3.pow (n + 1)
        rwa [zero_pow (show n + 1 ≠ 0 by omega)] at h4
      have h2 := hlim.div_const ‖s‖
      rwa [zero_div] at h2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hWd hUint ha hb
  have hsplit : (∫ u in (0 : ℝ)..1, (-((n + 1 : ℂ)) * ((1 - (u : ℂ))) ^ n * V u +
      U u * (u : ℂ) ^ (s - 1))) = 0 - 0 := hFTC
  rw [intervalIntegral.integral_add hiiA hiiB] at hsplit
  have hleft : (∫ u in (0 : ℝ)..1, -((n + 1 : ℂ)) * ((1 - (u : ℂ))) ^ n * V u) =
      -(((n + 1 : ℂ)) / s) * ∫ u in (0 : ℝ)..1, ((1 : ℂ) - u) ^ n * (u : ℂ) ^ s := by
    have h1 : (fun u : ℝ => -((n + 1 : ℂ)) * ((1 - (u : ℂ))) ^ n * V u) =
        fun u : ℝ => (-(((n + 1 : ℂ)) / s)) * ((((1 : ℂ) - u)) ^ n * (u : ℂ) ^ s) := by
      ext u
      rw [hVdef]
      field_simp [hsne]
      try ring
    rw [h1, intervalIntegral.integral_const_mul]
  rw [hleft] at hsplit
  have hpoint : (∫ u in (0 : ℝ)..1, U u * (u : ℂ) ^ (s - 1)) =
      ∫ u in (0 : ℝ)..1, ((1 : ℂ) - u) ^ (n + 1) * (u : ℂ) ^ (s - 1) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [hUdef]
  rw [hpoint] at hsplit
  simp only [sub_self] at hsplit
  linear_combination hsplit

/-- The finite beta integral: `∫_0^(1 : ℕ) (1-u)^n u^{s-1} du = n! / (s(s+1)⋯(s+n))`
for `0 < Re s`. -/
theorem beta_integral_eq (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ∫ u in (0 : ℝ)..1, ((1 : ℂ) - u) ^ n * (u : ℂ) ^ (s - 1) =
      Nat.factorial n / ∏ k ∈ Finset.range (n + 1), (s + k) := by
  induction n generalizing s with
  | zero =>
      have h1 := beta_integral_zero s hs
      have h2 : (fun u : ℝ => ((1 : ℂ) - u) ^ 0 * (u : ℂ) ^ (s - 1)) =
          fun u : ℝ => (u : ℂ) ^ (s - 1) := by
        ext u
        simp
      rw [h2, h1]
      simp [Nat.factorial_zero, Finset.range_one, Finset.prod_singleton]
  | succ n ih =>
      have h1 : 0 < (s + 1).re := by
        rw [Complex.add_re, Complex.one_re]
        linarith [hs]
      have hstep := beta_integral_succ_step s hs n
      have hrec := ih (s + 1) h1
      rw [add_sub_cancel_right] at hrec
      rw [hstep, hrec]
      have hprod : ∏ k ∈ Finset.range (n + 2), (s + k) =
          s * ∏ k ∈ Finset.range (n + 1), (s + 1 + k) := by
        rw [Finset.prod_range_succ']
        have h2 : (∏ k ∈ Finset.range (n + 1), (s + ↑(k + 1))) =
            ∏ k ∈ Finset.range (n + 1), (s + 1 + k) := by
          apply Finset.prod_congr rfl
          intro k _
          push_cast
          ring
        rw [h2]
        ring
      rw [hprod]
      have hfact : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := Nat.factorial_succ n
      rw [hfact]
      field_simp [Complex.ne_zero_of_re_pos hs]
      push_cast
      ring


/-- The truncated Euler integral in product form: substitution `x = n·u` plus the
beta integral. -/
theorem euler_trunc_integral_eq (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0 : ℝ)..n, (1 - x / n) ^ n * (x : ℂ) ^ (s - 1) =
      (n : ℂ) ^ s * Nat.factorial n / ∏ k ∈ Finset.range (n + 1), (s + k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set f : ℝ → ℂ := fun x => (1 - x / n) ^ n * (x : ℂ) ^ (s - 1) with hfdef
  have h2 := intervalIntegral.integral_comp_mul_left (f := f) (c := (n : ℝ)) (a := 0) (b := 1)
    (ne_of_gt hn')
  rw [mul_zero, mul_one] at h2
  have h3 : (∫ x in (0 : ℝ)..↑n, f x) = (↑n : ℝ) • ∫ u in (0 : ℝ)..1, f (↑n * u) := by
    have h4 : (↑n : ℝ) • ∫ u in (0 : ℝ)..1, f (↑n * u) = ∫ x in (0 : ℝ)..↑n, f x := by
      rw [h2, smul_smul, mul_inv_cancel₀ (ne_of_gt hn'), one_smul]
    exact h4.symm
  have hpoint : (∫ u in (0 : ℝ)..1, f (↑n * u)) =
      (n : ℂ) ^ (s - 1) * ∫ u in (0 : ℝ)..1, (1 - u) ^ n * (u : ℂ) ^ (s - 1) := by
    have h5 : ∀ u ∈ Set.uIcc (0:ℝ) 1, f (↑n * u) =
        (n : ℂ) ^ (s - 1) * ((1 - u) ^ n * (u : ℂ) ^ (s - 1)) := by
      intro u hu
      have hu0 : 0 ≤ u := by
        rw [uIcc_of_le zero_le_one] at hu
        exact hu.1
      simp only [hfdef]
      have h6 : (↑(↑n * u) : ℂ) = (n : ℂ) * (u : ℂ) := by
        rw [Complex.ofReal_mul, Complex.ofReal_natCast]
      rw [h6]
      have h7 : (1 - (n : ℂ) * (u : ℂ) / n) = (1 : ℂ) - (u : ℂ) := by
        field_simp [show (n : ℂ) ≠ 0 from by exact_mod_cast (ne_of_gt hn')]
      rw [h7]
      have h8 : ((n : ℂ) * (u : ℂ)) ^ (s - 1) = (n : ℂ) ^ (s - 1) * (u : ℂ) ^ (s - 1) := by
        rw [← Complex.ofReal_natCast n]
        exact Complex.mul_cpow_ofReal_nonneg (le_of_lt hn') hu0 _
      rw [h8]
      · ring
    rw [intervalIntegral.integral_congr (fun u hu => h5 u hu),
      intervalIntegral.integral_const_mul]
  rw [h3, hpoint, beta_integral_eq s hs n]
  have h9 : (n : ℂ) ^ s = (n : ℂ) * (n : ℂ) ^ (s - 1) := by
    have h10 : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn')
    have h11 := Complex.cpow_add (x := (n : ℂ)) 1 (s - 1) h10
    rw [show (1 : ℂ) + (s - 1) = s by ring, Complex.cpow_one] at h11
    exact h11
  rw [h9, real_smul, Complex.ofReal_natCast]
  · ring

/-- Complex-exponent form of the truncated-exponential limit. -/
theorem tendsto_one_sub_div_pow_complex (x : ℝ) :
    Tendsto (fun n : ℕ => ((1 : ℂ) - ↑x / ↑n) ^ n) atTop (𝓝 (↑(Real.exp (-x)) : ℂ)) := by
  have h1 : Tendsto (fun n : ℕ => (↑((1 - x / n) ^ n) : ℂ)) atTop (𝓝 (↑(Real.exp (-x)) : ℂ)) :=
    (tendsto_one_sub_div_pow x).ofReal
  apply h1.congr'
  · filter_upwards with n
    norm_cast

/-- The truncated Euler integrand `(1 - x/n)^n · x^{s-1}`. -/
private def truncIntegrand (s : ℂ) (n : ℕ) (x : ℝ) : ℂ := (1 - x / ↑n) ^ n * (x : ℂ) ^ (s - 1)

/-- The Euler limit: `Γ(s) = lim n!·n^s/∏_{k≤n}(s+k)` for `0 < Re s`. -/
theorem tendsto_euler_product (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ s * Nat.factorial n / ∏ k ∈ Finset.range (n + 1), (s + k))
      atTop (𝓝 (Gamma s)) := by
  have hGamma : Gamma s = s.GammaIntegral := Complex.Gamma_eq_integral hs
  have hDCT : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..n, (1 - x / n) ^ n * (x : ℂ) ^ (s - 1))
      atTop (𝓝 (s.GammaIntegral)) := by
    set g : ℝ → ℂ := fun x => ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) with hgdef
    have hconv : IntegrableOn g (Set.Ioi 0) volume := Complex.GammaIntegral_convergent hs
    have hbound : Integrable (Set.Ioi 0 |>.indicator fun x => Real.exp (-x) * x ^ (s.re - 1))
        volume := by
      have h1 : AEStronglyMeasurable g (volume.restrict (Set.Ioi 0)) := by
        apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
        apply ContinuousOn.mul
        · exact (continuous_ofReal.comp (Real.continuous_exp.comp continuous_id'.neg)).continuousOn
        · exact continuousOn_Ioi_cpow (s - 1)
      have h2 : IntegrableOn (fun x => Real.exp (-x) * x ^ (s.re - 1)) (Set.Ioi 0) volume := by
        have hconv' : Integrable (fun x => ‖g x‖) (volume.restrict (Set.Ioi 0)) :=
          (integrable_norm_iff h1).mpr hconv
        apply Integrable.congr hconv'
        apply Filter.eventuallyEq_of_mem (self_mem_ae_restrict measurableSet_Ioi)
        intro x hx
        simp only [hgdef]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]
      exact h2.integrable_indicator measurableSet_Ioi
    have hfmain := tendsto_integral_filter_of_dominated_convergence
      (bound := Set.Ioi 0 |>.indicator fun x => Real.exp (-x) * x ^ (s.re - 1))
      (F := fun n : ℕ => (Set.Ioc 0 (n : ℝ) |>.indicator (truncIntegrand s n)))
      (f := (Set.Ioi 0 |>.indicator g))
      (l := atTop)
      (by
        filter_upwards with n
        apply aestronglyMeasurable_indicator_of_continuousOn measurableSet_Ioc
        apply ContinuousOn.mul
        · exact ((by continuity : Continuous (fun x : ℝ => ((1 : ℂ) - ↑x / ↑n) ^ n))).continuousOn
        · exact continuousOn_Ioc_cpow (s - 1) n)
      (by
        filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
        filter_upwards with x
        by_cases hx : x ∈ Set.Ioc (0:ℝ) n
        · rw [Set.indicator_of_mem hx]
          have h1 : 0 < x := hx.1
          have h2 : x ≤ n := hx.2
          simp only [truncIntegrand]
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h1, Complex.sub_re, Complex.one_re]
          have h3 : ‖((1 : ℂ) - ↑x / ↑n) ^ n‖ = (1 - x / n) ^ n := by
            have hn' : (0 : ℝ) < n := by exact_mod_cast hn
            have heq : (1 : ℂ) - ↑x / ↑n = ((1 - x / n : ℝ) : ℂ) := by
              push_cast
              field_simp [ne_of_gt hn']
            rw [heq, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (by
                rw [sub_nonneg]
                exact (div_le_iff₀ hn').mpr (by simpa using h2)) n)]
          rw [h3]
          have h4 : (1 - x / n) ^ n ≤ Real.exp (-x) :=
            one_sub_div_pow_le_exp_neg hn (le_of_lt h1) h2
          have h5 : 0 ≤ x ^ (s.re - 1) := Real.rpow_nonneg (le_of_lt h1) _
          have h6 : (1 - x / n) ^ n * x ^ (s.re - 1) ≤ Real.exp (-x) * x ^ (s.re - 1) :=
            mul_le_mul_of_nonneg_right h4 h5
          rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h1)]
          exact h6
        · rw [Set.indicator_of_notMem hx, norm_zero]
          exact Set.indicator_nonneg (fun a ha =>
            mul_nonneg (Real.exp_pos (-a)).le (Real.rpow_nonneg (le_of_lt ha) (s.re - 1))) x)
      hbound
      (by
        filter_upwards with x
        by_cases hx : x ∈ Set.Ioi (0:ℝ)
        · rw [Set.indicator_of_mem hx]
          have h1 : ∀ᶠ n : ℕ in atTop, x ∈ Set.Ioc (0:ℝ) n := by
            filter_upwards [eventually_atTop.2 ⟨⌈x⌉₊, fun n hn =>
              show x ∈ Set.Ioc (0:ℝ) (n : ℝ) from by
                have h1 : (x : ℝ) ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil _
                have h2 : (⌈x⌉₊ : ℝ) ≤ n := Nat.cast_le.mpr hn
                exact ⟨hx, by linarith⟩⟩] with n hn
            exact hn
          refine Tendsto.congr' ?_ (Tendsto.mul_const ((x : ℂ) ^ (s - 1))
            (tendsto_one_sub_div_pow_complex x))
          exact h1.mono (fun n hn => (Set.indicator_of_mem hn (truncIntegrand s n)).symm)
        · rw [Set.indicator_of_notMem hx]
          have h1 : ∀ n : ℕ, x ∉ Set.Ioc (0:ℝ) n := by
            intro n
            rw [Set.mem_Ioc, not_and]
            intro h
            rw [not_le]
            exact absurd (Set.mem_Ioi.mpr h) hx
          refine Tendsto.congr' ?_ tendsto_const_nhds
          exact (Eventually.of_forall h1).mono (fun n hn => (Set.indicator_of_notMem hn (truncIntegrand s n)).symm))
    have hform : ∀ n : ℕ, (∫ (x : ℝ), (Set.Ioc 0 (n : ℝ) |>.indicator (truncIntegrand s n)) x) =
        ∫ x in (0 : ℝ)..n, (1 - x / n) ^ n * (x : ℂ) ^ (s - 1) := by
      intro n
      rw [MeasureTheory.integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
      simp only [truncIntegrand]
    have hlim : (∫ (x : ℝ), (Set.Ioi 0 |>.indicator g) x) = s.GammaIntegral := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioi]
      rfl
    rw [← hlim]
    exact hfmain.congr' (by filter_upwards with n; rw [hform n])
  rw [hGamma]
  apply Tendsto.congr' _ hDCT
  · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    rw [euler_trunc_integral_eq s hs n hn]

end RHTower
