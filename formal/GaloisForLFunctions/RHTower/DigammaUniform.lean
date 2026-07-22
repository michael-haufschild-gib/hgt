import GaloisForLFunctions.RHTower.DigammaSeries

open MeasureTheory intervalIntegral Complex Set Filter Topology

noncomputable section

namespace RHTower

/-! ## Locally uniform Euler convergence (S4, step 2)

The Euler products `P_n(s) = n!·n^s/∏_{k≤n}(s+k)` converge to `Γ` uniformly on
compact rectangles `{c ≤ Re s ≤ C, |Im s| ≤ M}`, hence locally uniformly on the
open right half-plane. This feeds the log-derivative interchange
`ψ = logDeriv Γ = lim logDeriv P_n`. -/

/-- `e^{-x}·x^r` is integrable on `(0,∞)` for `-1 < r`. -/
theorem integrableOn_exp_neg_rpow_Ioi {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun x => Real.exp (-x) * x ^ r) (Set.Ioi 0) volume := by
  have hconv : IntegrableOn (fun x : ℝ => ↑(Real.exp (-x)) * (x : ℂ) ^ (((r + 1 : ℝ) : ℂ) - 1))
      (Set.Ioi 0) volume :=
    Complex.GammaIntegral_convergent (by
      show 0 < ((r + 1 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]
      linarith [hr])
  have h1 : AEStronglyMeasurable (fun x : ℝ => ↑(Real.exp (-x)) * (x : ℂ) ^ (((r + 1 : ℝ) : ℂ) - 1))
      (volume.restrict (Set.Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul
    · exact ((by continuity : Continuous (fun x : ℝ => (↑(Real.exp (-x)) : ℂ))).continuousOn)
    · exact continuousOn_Ioi_cpow _
  have hconv' : Integrable (fun x : ℝ => ‖(↑(Real.exp (-x)) * (x : ℂ) ^ (((r + 1 : ℝ) : ℂ) - 1))‖)
      (volume.restrict (Set.Ioi 0)) := (integrable_norm_iff h1).mpr hconv
  apply Integrable.congr hconv'
  apply Filter.eventuallyEq_of_mem (self_mem_ae_restrict measurableSet_Ioi)
  intro x hx
  show ‖↑(Real.exp (-x)) * (x : ℂ) ^ (((r + 1 : ℝ) : ℂ) - 1)‖ = Real.exp (-x) * x ^ r
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-x)),
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  · congr 1
    rw [Complex.sub_re, Complex.ofReal_re, Complex.one_re, add_sub_cancel_right]

/-- `e^{-x}·x^r` is integrable on `[1,∞)` for ANY `r`. -/
theorem integrableOn_exp_neg_rpow_Ici_one (r : ℝ) :
    IntegrableOn (fun x => Real.exp (-x) * x ^ r) (Set.Ici (1:ℝ)) volume := by
  by_cases hr : -1 < r
  · exact IntegrableOn.mono (integrableOn_exp_neg_rpow_Ioi hr) (fun x hx => Set.mem_Ioi.mpr (zero_lt_one.trans_le hx)) (le_refl _)
  · have hr : r ≤ -1 := not_lt.mp hr
    have h1 : IntegrableOn (fun x => Real.exp (-x) * x ^ r) (Set.Ici (1:ℝ)) volume := by
      have h2 : IntegrableOn (fun x => Real.exp (-x)) (Set.Ici (1:ℝ)) volume := by
        have h9 := IntegrableOn.mono (integrableOn_exp_neg_rpow_Ioi (by norm_num : -1 < (0 : ℝ)))
          (fun x hx => Set.mem_Ioi.mpr (zero_lt_one.trans_le hx)) (le_refl _)
        simp only [Real.rpow_zero, mul_one] at h9
        exact h9
      have h3 : AEStronglyMeasurable (fun x => Real.exp (-x) * x ^ r)
          (volume.restrict (Set.Ici (1:ℝ))) := by
        apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ici
        apply ContinuousOn.mul
        · exact ((by continuity : Continuous (fun x : ℝ => Real.exp (-x)))).continuousOn
        · intro x hx
          exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt
            (zero_lt_one.trans_le hx)))).continuousWithinAt
      apply Integrable.mono' h2 h3
      apply ae_restrict_of_forall_mem measurableSet_Ici
      intro x hx
      have h4 : 1 ≤ x := hx
      have h5 : x ^ r ≤ 1 := by
        calc x ^ r ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le h4 (hr.trans (by norm_num : (-1:ℝ) ≤ 0))
          _ = 1 := by simp
      have h6 : Real.exp (-x) * x ^ r ≤ Real.exp (-x) := by
        simpa using (mul_le_mul_of_nonneg_left h5 (Real.exp_pos (-x)).le)
      have h7 : ‖Real.exp (-x) * x ^ r‖ = Real.exp (-x) * x ^ r := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (-x) * x ^ r)]
      rw [h7]
      show Real.exp (-x) * x ^ r ≤ Real.exp (-x)
      exact h6
    exact h1

/-- The Euler difference integrand `(e^{-x} - (1-x/n)^n)·x^r`. -/
private noncomputable def truncIntegrandA (r : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Real.exp (-x) - (1 - x / ↑n) ^ n) * x ^ r

/-- On `(0,1]`, `(e^{-x} - (1-x/n)^n)·x^r → 0` in `L¹` for `-1 < r`. -/
theorem tendsto_euler_A {r : ℝ} (hr : -1 < r) :
    Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..1, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ r)
      atTop (𝓝 0) := by
  have hbound : Integrable (Set.Ioc (0:ℝ) (1:ℝ) |>.indicator fun x : ℝ => x ^ r) volume := by
    have h1 : IntervalIntegrable (fun x : ℝ => x ^ r) volume (0:ℝ) (1:ℝ) := intervalIntegrable_rpow' hr
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h1).integrable_indicator
      measurableSet_Ioc
  have hfmain := tendsto_integral_filter_of_dominated_convergence
    (bound := Set.Ioc (0:ℝ) (1:ℝ) |>.indicator fun x : ℝ => x ^ r)
    (F := fun n : ℕ => (Set.Ioc (0:ℝ) (1:ℝ) |>.indicator (truncIntegrandA r n)))
    (f := (Set.Ioc (0:ℝ) (1:ℝ) |>.indicator fun _ => (0 : ℝ)))
    (l := atTop)
    (by
      filter_upwards with n
      apply aestronglyMeasurable_indicator_of_continuousOn_real measurableSet_Ioc
      apply ContinuousOn.mul
      · apply ContinuousOn.sub ((by continuity : Continuous (fun x : ℝ => Real.exp (-x))).continuousOn)
        · exact ((by continuity : Continuous (fun x : ℝ => (1 - x / ↑n) ^ n))).continuousOn
      · intro x hx
        exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx.1))).continuousWithinAt)
    (by
      filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      filter_upwards with x
      by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
      · rw [Set.indicator_of_mem hx]
        have h1 : 0 < x := hx.1
        have h2 : x ≤ (1 : ℝ) ∧ x ≤ (n : ℝ) := ⟨hx.2, le_trans hx.2 (by exact_mod_cast hn)⟩
        have hxn : x ≤ (n : ℝ) := le_trans hx.2 (by exact_mod_cast hn)
        have h3 : ‖(Real.exp (-x) - (1 - x / n) ^ n) * x ^ r‖ =
            (Real.exp (-x) - (1 - x / n) ^ n) * x ^ r := by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
            (sub_nonneg.mpr (one_sub_div_pow_le_exp_neg hn (le_of_lt h1) hxn))
            (Real.rpow_nonneg (le_of_lt h1) _))]
        simp only [truncIntegrandA]
        rw [h3]
        have h4 : Real.exp (-x) - (1 - x / n) ^ n ≤ Real.exp (-x) := by
          linarith [pow_nonneg (by
            have hn' : (0 : ℝ) < n := by exact_mod_cast hn
            have h5 : 0 ≤ 1 - x / n := by
              rw [sub_nonneg]
              exact (div_le_iff₀ hn').mpr (by simpa using h2.2)
            exact h5) n]
        have h6 : (Real.exp (-x) - (1 - x / n) ^ n) * x ^ r ≤ Real.exp (-x) * x ^ r :=
          mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (le_of_lt h1) _)
        have h7 : Real.exp (-x) * x ^ r ≤ x ^ r := by
          have h8 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [h1] : -x ≤ 0)
          calc Real.exp (-x) * x ^ r ≤ 1 * x ^ r :=
              mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg (le_of_lt h1) r)
            _ = x ^ r := one_mul _
        rw [Set.indicator_of_mem hx (fun x : ℝ => x ^ r)]
        exact h6.trans h7
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact Set.indicator_nonneg (s := Set.Ioc (0:ℝ) (1:ℝ))
          (fun a ha => Real.rpow_nonneg (le_of_lt ha.1) r) x)
    hbound
    (by
      filter_upwards with x
      by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
      · simp only [Set.indicator_of_mem hx]
        have h2 : Tendsto (fun n : ℕ => Real.exp (-x) - (1 - x / n) ^ n) atTop
            (𝓝 (Real.exp (-x) - Real.exp (-x))) :=
          (tendsto_one_sub_div_pow x).const_sub (Real.exp (-x))
        rw [sub_self] at h2
        have h3 : Tendsto (fun n : ℕ => (Real.exp (-x) - (1 - x / n) ^ n) * x ^ r)
            atTop (𝓝 0) := by
          have h4 := h2.mul_const (x ^ r)
          rwa [zero_mul] at h4
        exact h3
      · simp only [Set.indicator_of_notMem hx]
        exact tendsto_const_nhds)
  · have hform : ∀ n : ℕ, (∫ (x : ℝ), ((Set.Ioc (0:ℝ) (1:ℝ) |>.indicator (truncIntegrandA r n)) x)) =
        ∫ x in (0 : ℝ)..(1:ℝ), truncIntegrandA r n x := by
      intro n
      rw [MeasureTheory.integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
    have hz : (∫ (a : ℝ), (Ioc (0:ℝ) (1:ℝ)).indicator (fun x => (0 : ℝ)) a) = 0 := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioc]
      exact MeasureTheory.integral_zero ℝ ℝ
    rw [hz] at hfmain
    exact hfmain.congr' (Eventually.of_forall hform)

/-- On `[1,n]`, `(e^{-x} - (1-x/n)^n)·x^r → 0` in `L¹` (any `r`). -/
theorem tendsto_euler_B {r : ℝ} :
    Tendsto (fun n : ℕ => ∫ x in (1 : ℝ)..n, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ r)
      atTop (𝓝 0) := by
  have hbound : Integrable (Set.Ici (1:ℝ) |>.indicator fun x => Real.exp (-x) * x ^ r) volume :=
    (integrableOn_exp_neg_rpow_Ici_one r).integrable_indicator measurableSet_Ici
  have hfmain := tendsto_integral_filter_of_dominated_convergence
    (bound := Set.Ici (1:ℝ) |>.indicator fun x => Real.exp (-x) * x ^ r)
    (F := fun n : ℕ => (Set.Ioc 1 (n : ℝ) |>.indicator (truncIntegrandA r n)))
    (f := (Set.Ici (1:ℝ) |>.indicator fun _ => (0 : ℝ)))
    (l := atTop)
    (by
      filter_upwards with n
      apply aestronglyMeasurable_indicator_of_continuousOn_real measurableSet_Ioc
      apply ContinuousOn.mul
      · apply ContinuousOn.sub ((by continuity : Continuous (fun x : ℝ => Real.exp (-x))).continuousOn)
        · exact ((by continuity : Continuous (fun x : ℝ => (1 - x / ↑n) ^ n))).continuousOn
      · intro x hx
        exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt
          (zero_lt_one.trans hx.1)))).continuousWithinAt)
    (by
      filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      filter_upwards with x
      by_cases hx : x ∈ Set.Ioc 1 (n : ℝ)
      · rw [Set.indicator_of_mem hx]
        have h1 : 1 ≤ x := le_of_lt hx.1
        have h2 : x ≤ n := hx.2
        have h3 : ‖(Real.exp (-x) - (1 - x / n) ^ n) * x ^ r‖ =
            (Real.exp (-x) - (1 - x / n) ^ n) * x ^ r := by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
            (sub_nonneg.mpr (one_sub_div_pow_le_exp_neg hn (le_trans zero_le_one h1) h2))
            (Real.rpow_nonneg (le_trans zero_le_one h1) _))]
        simp only [truncIntegrandA]
        rw [h3]
        simp only [Set.indicator_of_mem (Set.mem_Ici.mpr (le_of_lt hx.1))
          (fun x => Real.exp (-x) * x ^ r)]
        have h4 : Real.exp (-x) - (1 - x / n) ^ n ≤ Real.exp (-x) := by
          linarith [pow_nonneg (by
            have hn' : (0 : ℝ) < n := by exact_mod_cast hn
            have h5 : 0 ≤ 1 - x / n := by
              rw [sub_nonneg]
              exact (div_le_iff₀ hn').mpr (by simpa using h2)
            exact h5) n]
        exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (le_trans zero_le_one h1) _)
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact Set.indicator_nonneg (s := Set.Ici (1:ℝ)) (fun a ha =>
          mul_nonneg (Real.exp_pos (-a)).le (Real.rpow_nonneg (le_trans zero_le_one ha) r)) x)
    hbound
    (by
      filter_upwards with x
      by_cases hx : x ∈ Set.Ici (1:ℝ)
      · rw [Set.indicator_of_mem hx]
        by_cases hx1 : x = 1
        · rw [hx1]
          have h1 : ∀ n : ℕ, (1:ℝ) ∉ Set.Ioc 1 (n : ℝ) := by
            intro n
            rw [Set.mem_Ioc, not_and]
            intro h
            exact absurd h (lt_irrefl _)
          refine Tendsto.congr' ?_ tendsto_const_nhds
          exact (Eventually.of_forall h1).mono (fun n hn =>
            (Set.indicator_of_notMem hn (fun x : ℝ =>
              (Real.exp (-x) - (1 - x / n) ^ n) * x ^ r)).symm)
        · have hx1 : 1 < x := lt_of_le_of_ne hx (Ne.symm hx1)
          have h1 : ∀ᶠ n : ℕ in atTop, x ∈ Set.Ioc 1 (n : ℝ) := by
            filter_upwards [eventually_atTop.2 ⟨⌈x⌉₊, fun n hn =>
              show x ∈ Set.Ioc 1 (n : ℝ) from by
                have h1 : (x : ℝ) ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil _
                have h2 : (⌈x⌉₊ : ℝ) ≤ n := Nat.cast_le.mpr hn
                exact ⟨hx1, by linarith⟩⟩] with n hn
            exact hn
          have h2 : Tendsto (fun n : ℕ => Real.exp (-x) - (1 - x / n) ^ n) atTop
              (𝓝 (Real.exp (-x) - Real.exp (-x))) :=
            (tendsto_one_sub_div_pow x).const_sub (Real.exp (-x))
          rw [sub_self] at h2
          have h3 := h2.mul_const (x ^ r)
          rw [zero_mul] at h3
          exact Tendsto.congr' (h1.mono (fun n hn => (Set.indicator_of_mem hn (fun x : ℝ =>
            (Real.exp (-x) - (1 - x / n) ^ n) * x ^ r)).symm)) h3
      · rw [Set.indicator_of_notMem hx]
        have h1 : ∀ n : ℕ, x ∉ Set.Ioc 1 (n : ℝ) := by
          intro n
          rw [Set.mem_Ioc, not_and]
          intro h
          exact absurd (Set.mem_Ici.mpr (le_of_lt h)) hx
        refine Tendsto.congr' ?_ tendsto_const_nhds
        exact (Eventually.of_forall h1).mono (fun n hn =>
          (Set.indicator_of_notMem hn (fun x : ℝ =>
            (Real.exp (-x) - (1 - x / n) ^ n) * x ^ r)).symm))
  · have hform : ∀ n : ℕ, 1 ≤ n → (∫ (x : ℝ), ((Set.Ioc 1 (n : ℝ) |>.indicator (truncIntegrandA r n)) x)) =
        ∫ x in (1 : ℝ)..n, truncIntegrandA r n x := by
      intro n hn
      rw [MeasureTheory.integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le (by exact_mod_cast hn : (1:ℝ) ≤ n)]
    have hz : (∫ (a : ℝ), (Set.Ici (1:ℝ) |>.indicator fun x => (0 : ℝ)) a) = 0 := by
      rw [MeasureTheory.integral_indicator measurableSet_Ici]
      exact MeasureTheory.integral_zero ℝ ℝ
    rw [hz] at hfmain
    exact hfmain.congr' ((eventually_atTop.2 ⟨1, fun n hn => hform n hn⟩))

/-- Tail of `e^{-x}·x^r` to zero along `(n,∞)` (any `r`). -/
theorem tendsto_euler_C {r : ℝ} :
    Tendsto (fun n : ℕ => ∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * x ^ r) atTop (𝓝 0) := by
  have hbound : Integrable (Set.Ici (1:ℝ) |>.indicator fun x => Real.exp (-x) * x ^ r) volume :=
    (integrableOn_exp_neg_rpow_Ici_one r).integrable_indicator measurableSet_Ici
  have hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable ((Set.Ioi (n : ℝ) |>.indicator fun x : ℝ => Real.exp (-x) * x ^ r)) volume := by
    filter_upwards with n
    apply aestronglyMeasurable_indicator_of_continuousOn_real measurableSet_Ioi
    apply ContinuousOn.mul
    · exact ((by continuity : Continuous (fun x : ℝ => Real.exp (-x))).continuousOn)
    · intro x hx
      have hpos : (0:ℝ) < x := lt_of_le_of_lt (Nat.cast_nonneg n) hx
      exact ContinuousAt.continuousWithinAt (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hpos)))
  have hfmain := tendsto_integral_filter_of_dominated_convergence
    (bound := Set.Ici (1:ℝ) |>.indicator fun x => Real.exp (-x) * x ^ r)
    (F := fun n : ℕ => (Set.Ioi (n : ℝ) |>.indicator fun x => Real.exp (-x) * x ^ r))
    (f := (Set.Ici (1:ℝ) |>.indicator fun _ => (0 : ℝ)))
    (l := atTop)
    hmeas
    (by
      filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      filter_upwards with x
      by_cases hx : x ∈ Set.Ioi (n : ℝ)
      · rw [Set.indicator_of_mem hx]
        have h1 : n < x := hx
        have h2 : ‖Real.exp (-x) * x ^ r‖ = Real.exp (-x) * x ^ r := by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos (-x)).le
            (Real.rpow_nonneg (by linarith [h1, (Nat.cast_nonneg n : (0:ℝ) ≤ (n : ℝ))] : (0:ℝ) ≤ x) r))]
        rw [h2]
        rw [Set.indicator_of_mem (Set.mem_Ici.mpr (by
          have h3 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith [h1, h3] : 1 ≤ x)) (fun x => Real.exp (-x) * x ^ r)]
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact Set.indicator_nonneg (s := Set.Ici (1:ℝ)) (fun a ha =>
          mul_nonneg (Real.exp_pos (-a)).le (Real.rpow_nonneg (le_trans zero_le_one ha) r)) x)
    hbound
    (by
      filter_upwards with x
      by_cases hx : x ∈ Set.Ici (1:ℝ)
      · rw [Set.indicator_of_mem hx]
        have h1 : ∀ᶠ n : ℕ in atTop, x ∉ Set.Ioi (n : ℝ) := by
          filter_upwards [eventually_atTop.2 ⟨⌈x⌉₊ + 1, fun n hn =>
            show x ∉ Set.Ioi (n : ℝ) from by
              have h1 : (x : ℝ) ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil _
              have h2 : (⌈x⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
              simp only [Set.mem_Ioi, not_lt]
              linarith [h1, h2]⟩] with n hn
          exact hn
        apply Tendsto.congr' ((h1.mono (fun n hn => (Set.indicator_of_notMem hn
          (fun x => Real.exp (-x) * x ^ r)).symm)))
        exact tendsto_const_nhds
      · have h1 : ∀ n : ℕ, 1 ≤ n → x ∉ Set.Ioi (n : ℝ) := by
          intro n hn
          rw [Set.mem_Ioi]
          by_contra h
          exact hx (Set.mem_Ici.mpr (by
            have h1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith [h, h1] : 1 ≤ x))
        have h2 : ∀ᶠ n : ℕ in atTop, ((Set.Ioi (n : ℝ) |>.indicator fun x : ℝ =>
            Real.exp (-x) * x ^ r)) x = 0 :=
          eventually_atTop.2 ⟨1, fun n hn => Set.indicator_of_notMem (h1 n hn) _⟩
        simp only [Set.indicator_of_notMem hx (fun _ => (0 : ℝ))]
        exact Tendsto.congr' (Filter.EventuallyEq.symm h2) tendsto_const_nhds)
  · have hform : ∀ n : ℕ, (∫ (x : ℝ), ((Set.Ioi (n : ℝ) |>.indicator fun x =>
        Real.exp (-x) * x ^ r) x)) = ∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * x ^ r := by
      intro n
      rw [MeasureTheory.integral_indicator measurableSet_Ioi]
    have hz : (∫ (a : ℝ), (Set.Ici (1:ℝ) |>.indicator fun x => (0 : ℝ)) a) = 0 := by
      rw [MeasureTheory.integral_indicator measurableSet_Ici]
      exact MeasureTheory.integral_zero ℝ ℝ
    rw [hz] at hfmain
    exact hfmain.congr' (Eventually.of_forall hform)

/-- Integrability of `(e^{-x} - (1-x/n)^n)·x^{s-1}` on `(0,1]`. -/
theorem intervalIntegrable_euler_sub_left {s : ℂ} (hsre : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    IntervalIntegrable (fun x : ℝ => (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1))
      volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
  have h2 : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Set.Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegrable_rpow' (by linarith [hsre] : -1 < s.re - 1))
  have h4 : AEStronglyMeasurable (fun x : ℝ =>
      (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1)) (volume.restrict (Set.Ioc 0 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply ContinuousOn.mul
    · exact ((by continuity : Continuous (fun x : ℝ =>
        Real.exp (-x) - (1 - x / ↑n) ^ n))).continuousOn
    · intro x hx
      exact (Real.continuousAt_rpow_const x (s.re - 1) (Or.inl (ne_of_gt hx.1))).continuousWithinAt
  rw [IntegrableOn] at h2 ⊢
  apply Integrable.mono' h2 h4
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro x hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h5 : (1 - x / n) ^ n ≤ Real.exp (-x) :=
    one_sub_div_pow_le_exp_neg hn (le_of_lt hx.1) (le_trans hx.2 (by exact_mod_cast hn))
  have h6 : ‖(Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1)‖ =
      (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (sub_nonneg.mpr h5) (Real.rpow_nonneg (le_of_lt hx.1) _))]
  rw [h6]
  have h7 : Real.exp (-x) - (1 - x / n) ^ n ≤ Real.exp (-x) := by
    have h9 : x ≤ (n : ℝ) := le_trans hx.2 (by exact_mod_cast hn)
    have h5 : 0 ≤ 1 - x / ↑n := by
      rw [sub_nonneg]
      exact (div_le_iff₀ hn').mpr (by simpa using h9)
    have h6 : 0 ≤ (1 - x / ↑n) ^ n := pow_nonneg h5 n
    linarith [h6]
  have h8 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.1] : -x ≤ 0)
  calc (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1)
      ≤ Real.exp (-x) * x ^ (s.re - 1) :=
        mul_le_mul_of_nonneg_right h7 (Real.rpow_nonneg (le_of_lt hx.1) _)
    _ ≤ 1 * x ^ (s.re - 1) :=
        mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg (le_of_lt hx.1) _)
    _ = x ^ (s.re - 1) := one_mul _

/-- Integrability of `(e^{-x} - (1-x/n)^n)·x^{s-1}` on `[1,n]` for every `s`.
Unlike the interval adjacent to zero, this compact interval imposes no condition on `Re s`. -/
theorem intervalIntegrable_euler_sub_right {s : ℂ} {n : ℕ} (hn : 1 ≤ n) :
    IntervalIntegrable (fun x : ℝ => (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1))
      volume 1 n := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast hn : (1:ℝ) ≤ n)).mpr
  have h3 : ContinuousOn (fun x : ℝ => (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1))
      (Set.Icc 1 (n : ℝ)) := by
    apply ContinuousOn.mul
    · exact ((by continuity : Continuous (fun x : ℝ =>
        Real.exp (-x) - (1 - x / ↑n) ^ n))).continuousOn
    · intro x hx
      exact (Real.continuousAt_rpow_const x (s.re - 1) (Or.inl (ne_of_gt
        (by linarith [hx.1] : 0 < x)))).continuousWithinAt
  exact (h3.integrableOn_Icc).mono Set.Ioc_subset_Icc_self (le_refl _)


/-- The uniform rectangle bound: `‖P_n(s) − Γ(s)‖` is bounded, uniformly in `s`
with `c ≤ Re s ≤ C`, by the three `L¹`-convergent sequences A, B, C. -/
theorem euler_rect_bound {c C : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : c ≤ s.re) (hsC : s.re ≤ C) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ s * Nat.factorial n / ∏ k ∈ Finset.range (n + 1), (s + k) - Gamma s‖ ≤
      (∫ x in (0 : ℝ)..1, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (c - 1)) +
      (∫ x in (1 : ℝ)..n, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (C - 1)) +
      (∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * x ^ (C - 1)) := by
  have hsre : 0 < s.re := lt_of_lt_of_le hc hs
  have hPn : (n : ℂ) ^ s * Nat.factorial n / ∏ k ∈ Finset.range (n + 1), (s + k) =
      ∫ x in (0 : ℝ)..n, (1 - x / n) ^ n * (x : ℂ) ^ (s - 1) :=
    (euler_trunc_integral_eq s hsre n hn).symm
  have hGamma : Gamma s = s.GammaIntegral := Complex.Gamma_eq_integral hsre
  rw [hPn, hGamma]
  set g : ℝ → ℂ := fun x => ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) with hgdef
  have hgI : IntegrableOn g (Set.Ioi 0) volume := Complex.GammaIntegral_convergent hsre
  have hgIoc : IntegrableOn g (Set.Ioc 0 (n : ℝ)) volume :=
    hgI.mono (Set.Ioc_subset_Ioi_self) (le_refl _)
  have hgIoi : IntegrableOn g (Set.Ioi (n : ℝ)) volume :=
    hgI.mono (Set.Ioi_subset_Ioi (Nat.cast_nonneg n)) (le_refl _)
  have hsplit : (∫ x in Set.Ioi (0:ℝ), g x) =
      (∫ x in Set.Ioc 0 (n : ℝ), g x) + ∫ x in Set.Ioi (n : ℝ), g x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (Nat.cast_nonneg n)]
    apply MeasureTheory.setIntegral_union (Set.disjoint_left.mpr (fun x hx => not_lt.mpr hx.2))
      measurableSet_Ioi hgIoc hgIoi
  set t : ℝ → ℂ := fun x => ((1 : ℂ) - ↑x / ↑n) ^ n * (x : ℂ) ^ (s - 1) with htdef
  have htIoc : IntegrableOn t (Set.Ioc 0 (n : ℝ)) volume := by
    have h1 : IntegrableOn t (Set.Ioc 0 (n : ℝ)) volume := by
      have h2 : IntegrableOn (fun x : ℝ => x ^ (s.re - 1)) (Set.Ioc 0 (n : ℝ)) volume := by
        apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mp
        exact intervalIntegrable_rpow' (by linarith [hsre] : -1 < s.re - 1)
      have h3 : AEStronglyMeasurable t (volume.restrict (Set.Ioc 0 (n : ℝ))) := by
        apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
        apply ContinuousOn.mul
        · exact ((by continuity : Continuous (fun x : ℝ => ((1 : ℂ) - ↑x / ↑n) ^ n))).continuousOn
        · exact continuousOn_Ioc_cpow (s - 1) n
      rw [IntegrableOn]
      apply Integrable.mono' h2 h3
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro x hx
      show ‖t x‖ ≤ x ^ (s.re - 1)
      rw [htdef, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re]
      have h4 : ‖((1 : ℂ) - ↑x / ↑n) ^ n‖ = (1 - x / n) ^ n := by
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have heq : (1 : ℂ) - ↑x / ↑n = ((1 - x / n : ℝ) : ℂ) := by
          norm_cast
        rw [heq, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (by
            rw [sub_nonneg]
            exact (div_le_iff₀ hn').mpr (by simpa using hx.2)) n)]
      rw [h4]
      have h6 : (1 - x / n) ^ n ≤ 1 := by
        apply pow_le_one₀
        · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
          rw [sub_nonneg]
          exact (div_le_iff₀ hn').mpr (by simpa using hx.2)
        · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
          linarith [hx.1, hn', div_nonneg (le_of_lt hx.1) (le_of_lt hn')]
      have h9 : 0 ≤ (1 - x / n) ^ n := by
        apply pow_nonneg
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        rw [sub_nonneg]
        exact (div_le_iff₀ hn').mpr (by simpa using hx.2)
      have h10 : 0 ≤ x ^ (s.re - 1) := Real.rpow_nonneg (le_of_lt hx.1) _
      nlinarith [h6, h9, h10]
    exact h1
  have hnorm_t_g : ∀ x ∈ Set.Ioc 0 (n : ℝ),
      ‖t x - g x‖ = (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1) := by
    intro x hx
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (1 - x / n) ^ n ≤ Real.exp (-x) :=
      one_sub_div_pow_le_exp_neg hn (le_of_lt hx.1) hx.2
    have h2 : t x - g x = (((1 : ℂ) - ↑x / ↑n) ^ n - ↑(Real.exp (-x))) * (x : ℂ) ^ (s - 1) := by
      rw [htdef, hgdef]
      ring
    rw [h2, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re]
    have h3 : (((1 : ℂ) - ↑x / ↑n) ^ n - ↑(Real.exp (-x))) =
        ↑((1 - x / n) ^ n - Real.exp (-x)) := by
      norm_cast
    rw [h3, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr h1)]
    ring
  have hdecomp : (∫ x in (0 : ℝ)..n, t x) - s.GammaIntegral =
      (∫ x in Set.Ioc 0 (n : ℝ), (t x - g x)) - ∫ x in Set.Ioi (n : ℝ), g x := by
    have h1 : s.GammaIntegral = (∫ x in Set.Ioi (0:ℝ), g x) := rfl
    rw [h1, hsplit]
    have h2 : (∫ x in (0 : ℝ)..n, t x) = ∫ x in Set.Ioc 0 (n : ℝ), t x :=
      intervalIntegral.integral_of_le (Nat.cast_nonneg n)
    rw [h2]
    rw [MeasureTheory.integral_sub htIoc hgIoc] at *
    · ring
  have hmain : ‖(∫ x in (0 : ℝ)..n, t x) - s.GammaIntegral‖ ≤
      (∫ x in (0 : ℝ)..1, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (c - 1)) +
      (∫ x in (1 : ℝ)..n, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (C - 1)) +
      (∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * x ^ (C - 1)) := by
    rw [hdecomp]
    have h1 : ‖(∫ x in Set.Ioc 0 (n : ℝ), (t x - g x)) - ∫ x in Set.Ioi (n : ℝ), g x‖ ≤
        (∫ x in Set.Ioc 0 (n : ℝ), ‖t x - g x‖) + ∫ x in Set.Ioi (n : ℝ), ‖g x‖ := by
      calc ‖(∫ x in Set.Ioc 0 (n : ℝ), (t x - g x)) - ∫ x in Set.Ioi (n : ℝ), g x‖
          ≤ ‖∫ x in Set.Ioc 0 (n : ℝ), (t x - g x)‖ + ‖∫ x in Set.Ioi (n : ℝ), g x‖ :=
            norm_sub_le _ _
        _ ≤ (∫ x in Set.Ioc 0 (n : ℝ), ‖t x - g x‖) + ∫ x in Set.Ioi (n : ℝ), ‖g x‖ := by
            gcongr
            · exact norm_integral_le_integral_norm _
            · exact norm_integral_le_integral_norm _
    apply h1.trans
    -- rewrite the norm integrands via hnorm_t_g and the norm of g
    have hn1 : (∫ x in Set.Ioc 0 (n : ℝ), ‖t x - g x‖) =
        ∫ x in Set.Ioc 0 (n : ℝ), (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      exact hnorm_t_g
    have hn2 : (∫ x in Set.Ioi (n : ℝ), ‖g x‖) =
        ∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * x ^ (s.re - 1) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [hgdef]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-x)),
        Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_le_of_lt (Nat.cast_nonneg n) hx), Complex.sub_re,
        Complex.one_re]
    rw [hn1, hn2]
    -- split the (0, n] integral at 1 and compare exponents
    have hsplit1 : (∫ x in Set.Ioc 0 (n : ℝ), (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1)) =
        (∫ x in (0 : ℝ)..1, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1)) +
          ∫ x in (1 : ℝ)..n, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1) := by
      have h2 : (∫ x in (0 : ℝ)..1, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1)) +
          ∫ x in (1 : ℝ)..n, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1) =
          ∫ x in (0 : ℝ)..n, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1) :=
        intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_euler_sub_left hsre hn)
          (intervalIntegrable_euler_sub_right (s := s) hn)
      rw [← intervalIntegral.integral_of_le ((Nat.cast_nonneg n) : (0:ℝ) ≤ (n : ℝ)), ← h2]
    rw [hsplit1]
    -- exponent comparisons
    have hcmp1 : (∫ x in (0 : ℝ)..1, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1)) ≤
        ∫ x in (0 : ℝ)..1, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (c - 1) := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (intervalIntegrable_euler_sub_left hsre hn)
        (intervalIntegrable_euler_sub_left
          (show 0 < ((c : ℂ)).re from by rw [Complex.ofReal_re]; exact hc) hn)
      intro x hx
      have h5 : (1 - x / n) ^ n ≤ Real.exp (-x) :=
        one_sub_div_pow_le_exp_neg hn hx.1 (le_trans hx.2 (by exact_mod_cast hn))
      have h6 : 0 ≤ Real.exp (-x) - (1 - x / n) ^ n := sub_nonneg.mpr h5
      by_cases hx0 : x = 0
      · rw [hx0]
        simp [Real.exp_zero, one_pow, sub_self, zero_mul]
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hx.2
            (by linarith [hsre] : c - 1 ≤ s.re - 1)) h6
    have hcmp2 : (∫ x in (1 : ℝ)..n, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1)) ≤
        ∫ x in (1 : ℝ)..n, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (C - 1) := by
      apply intervalIntegral.integral_mono_on (by exact_mod_cast hn : (1:ℝ) ≤ n)
        (intervalIntegrable_euler_sub_right (s := s) hn)
        (intervalIntegrable_euler_sub_right (s := (C : ℂ)) hn)
      intro x hx
      have h5 : (1 - x / n) ^ n ≤ Real.exp (-x) :=
        one_sub_div_pow_le_exp_neg hn (by linarith [hx.1] : 0 ≤ x) hx.2
      have h6 : 0 ≤ Real.exp (-x) - (1 - x / n) ^ n := sub_nonneg.mpr h5
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx.1 (by linarith [hsC] : s.re - 1 ≤ C - 1)) h6
    have hcmp3 : (∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * x ^ (s.re - 1)) ≤
        ∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * x ^ (C - 1) := by
      apply MeasureTheory.setIntegral_mono_on
        (IntegrableOn.mono (integrableOn_exp_neg_rpow_Ici_one (s.re - 1))
          (Set.Ioi_subset_Ici (by exact_mod_cast hn : (1:ℝ) ≤ (n : ℝ))) (le_refl _))
        (IntegrableOn.mono (integrableOn_exp_neg_rpow_Ici_one (C - 1))
          (Set.Ioi_subset_Ici (by exact_mod_cast hn : (1:ℝ) ≤ (n : ℝ))) (le_refl _))
        measurableSet_Ioi
      intro x hx
      have h6 : 0 ≤ Real.exp (-x) := (Real.exp_pos (-x)).le
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by
          have h1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith [Set.mem_Ioi.mp hx, h1] : 1 ≤ x)
          (by linarith [hsC] : s.re - 1 ≤ C - 1)) h6
    have hnnonneg1 : 0 ≤ ∫ x in Set.Ioc 0 (n : ℝ), ‖t x - g x‖ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx =>
        norm_nonneg (t x - g x)))
    have hnnonneg2 : 0 ≤ ∫ x in Set.Ioi (n : ℝ), ‖g x‖ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx =>
        norm_nonneg (g x)))
    linarith [hcmp1, hcmp2, hcmp3]
  exact hmain

/-- Locally uniform convergence of the Euler products to `Γ` on the right half-plane. -/
theorem tendstoLocallyUniformlyOn_euler :
    TendstoLocallyUniformlyOn
      (fun n : ℕ => fun s : ℂ => (n : ℂ) ^ s * Nat.factorial n / ∏ k ∈ Finset.range (n + 1), (s + k))
      Gamma atTop {s : ℂ | 0 < s.re} := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε s hs
  have hsre : 0 < s.re := hs
  refine ⟨{t : ℂ | s.re / 2 ≤ t.re ∧ t.re ≤ 2 * s.re ∧ |t.im| ≤ |s.im| + 1}, ?_, ?_⟩
  · -- the rectangle is a neighborhood of `s` within `{0 < re}`
    apply mem_nhdsWithin.mpr
    refine ⟨Metric.ball s (min (s.re / 2) (1 : ℝ)), Metric.isOpen_ball,
      Metric.mem_ball_self (by exact lt_min_iff.mpr ⟨by linarith [hsre], by norm_num⟩), ?_⟩
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hδ : |y.re - s.re| < min (s.re / 2) (1 : ℝ) := by
      have h1 := Metric.mem_ball.mp hy1
      have h2 : |y.re - s.re| ≤ ‖y - s‖ := by
        calc |y.re - s.re| = |(y - s).re| := by rw [Complex.sub_re]
          _ ≤ ‖y - s‖ := abs_re_le_norm (y - s)
      rw [dist_eq_norm] at h1
      exact h2.trans_lt h1
    have hδi : |y.im - s.im| < 1 := by
      have h1 := Metric.mem_ball.mp hy1
      have h2 : |y.im - s.im| ≤ ‖y - s‖ := by
        calc |y.im - s.im| = |(y - s).im| := by rw [Complex.sub_im]
          _ ≤ ‖y - s‖ := abs_im_le_norm (y - s)
      rw [dist_eq_norm] at h1
      exact h2.trans_lt (lt_of_lt_of_le h1 (min_le_right (s.re / 2) (1:ℝ)))
    have hb1 : s.re / 2 ≤ y.re := by
      have h3 := abs_lt.mp hδ
      linarith [h3.1, min_le_left (s.re / 2) (1:ℝ)]
    have hb2 : y.re ≤ 2 * s.re := by
      have h3 := abs_lt.mp hδ
      linarith [h3.2, min_le_left (s.re / 2) (1:ℝ), hsre]
    have hb3 : |y.im| ≤ |s.im| + 1 := by
      have h3 := abs_lt.mp hδi
      calc |y.im| = |s.im + (y.im - s.im)| := by ring_nf
        _ ≤ |s.im| + |y.im - s.im| := abs_add_le _ _
        _ ≤ |s.im| + 1 := by linarith [h3.2]
    exact show y ∈ {t : ℂ | s.re / 2 ≤ t.re ∧ t.re ≤ 2 * s.re ∧ |t.im| ≤ |s.im| + 1} from
      ⟨hb1, hb2, hb3⟩
  · -- uniform convergence on the rectangle
    have hA := (tendsto_euler_A (r := s.re / 2 - 1)
      (by linarith [hsre] : -1 < s.re / 2 - 1)).eventually
      (Iio_mem_nhds (by linarith [hε] : (0:ℝ) < ε / 3))
    have hB := (tendsto_euler_B (r := 2 * s.re - 1)).eventually
      (Iio_mem_nhds (by linarith [hε] : (0:ℝ) < ε / 3))
    have hC := (tendsto_euler_C (r := 2 * s.re - 1)).eventually
      (Iio_mem_nhds (by linarith [hε] : (0:ℝ) < ε / 3))
    filter_upwards [hA, hB, hC, eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hAn hBn hCn hn t ht
    have hb := euler_rect_bound (c := s.re / 2) (C := 2 * s.re)
      (by linarith [hsre] : 0 < s.re / 2) ht.1 ht.2.1 hn
    have hdist : dist (Gamma t) ((fun s : ℂ => (n : ℂ) ^ s * Nat.factorial n /
        ∏ k ∈ Finset.range (n + 1), (s + k)) t) =
        ‖(n : ℂ) ^ t * Nat.factorial n / ∏ k ∈ Finset.range (n + 1), (t + k) - Gamma t‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    rw [hdist]
    calc ‖(n : ℂ) ^ t * Nat.factorial n / ∏ k ∈ Finset.range (n + 1), (t + k) - Gamma t‖
        ≤ (∫ x in (0 : ℝ)..1, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re / 2 - 1)) +
          (∫ x in (1 : ℝ)..n, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (2 * s.re - 1)) +
          (∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * x ^ (2 * s.re - 1)) := hb
      _ < ε / 3 + ε / 3 + ε / 3 := by
          have hA' : (∫ x in (0 : ℝ)..1, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re / 2 - 1)) < ε / 3 := hAn
          have hB' : (∫ x in (1 : ℝ)..n, (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (2 * s.re - 1)) < ε / 3 := hBn
          have hC' : (∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * x ^ (2 * s.re - 1)) < ε / 3 := hCn
          linarith [hA', hB', hC']
      _ = ε := by ring

end RHTower
