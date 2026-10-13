import GaloisForLFunctions.RHTower.DilationAutocorrelationPeriodization

/-!
# Short cores cannot be blind for the cosine–dilation kernel

Let `f` be continuous and supported in `[α, β]` with `0 < α ≤ β ≤ 2α`, and let
`Ψ_f = Cf ⋆ f` be the cosine–dilation kernel (`cosDilationKernel`).  If `Ψ_f(0) = 0` and
`Ψ_f(n) = 0` for every integer `n ≥ 2`, then `f = 0`
(`eq_zero_of_cosDilationKernel_blind_of_le_two_mul`).  The hypothesis `Ψ_f(0) = 0` holds as soon
as `∫_0^∞ f = 0` (`cosDilationKernel_zero_of_integral_eq_zero`), which is the condition
`𝓜f(1) = 0`.

So a smooth `f` with `𝓜f(1) = 0` whose kernel `Ψ_f` vanishes on `ℕ_{≥2}` has support ratio
`β/α > 2`.

**Proof.**  By Poisson periodization (`tsum_dilationAutocorr_abs_eq`) the even `1`-periodization
of `A_f(|r|)` equals `2Ψ_f(1) cos 2πx`.  The dilation autocorrelation `A_f` is continuous and
vanishes off `[α/β, β/α]`, hence off the open interval `(α/β, β/α) ⊆ (1/2, 2)`
(`dilationAutocorr_eq_zero_of_not_mem_Ioo`).  At `x = 0` only `k = ±1` contribute and at `x = 1/2`
only `k ∈ {−2, 1}`, so `A_f(1) = Ψ_f(1)` and `A_f(3/2) = −Ψ_f(1)`.  On the other hand
`2|ab| ≤ a² + b²` and `∫ f(3y/2)² dy = (2/3) ∫ f²` give `|A_f(3/2)| ≤ (5/6) A_f(1)`, while
`A_f(1) = ∫ f² ≥ 0`.  Hence `∫ f² = 0`.
-/

open MeasureTheory Set Real

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-- **The autocorrelation vanishes off the open interval `(α/β, β/α)`.** -/
theorem dilationAutocorr_eq_zero_of_not_mem_Ioo (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {r : ℝ}
    (hr : r ∉ Ioo (α / β) (β / α)) : dilationAutocorr f r = 0 := by
  have hcl : IsClosed {r | dilationAutocorr f r = 0} :=
    isClosed_eq (continuous_dilationAutocorr hf hα hsupp) continuous_const
  have hout : ∀ s, s ∉ Icc (α / β) (β / α) → dilationAutocorr f s = 0 :=
    fun s h => dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp h
  rcases le_or_gt r (α / β) with h | h
  · have hsub : Iio (α / β) ⊆ {s | dilationAutocorr f s = 0} :=
      fun s hs => hout s fun h' => absurd h'.1 (not_le.mpr hs)
    have hc := hcl.closure_subset_iff.mpr hsub
    rw [closure_Iio] at hc
    exact hc h
  · have hr' : β / α ≤ r := by
      by_contra h'
      exact hr ⟨h, lt_of_not_ge h'⟩
    have hsub : Ioi (β / α) ⊆ {s | dilationAutocorr f s = 0} :=
      fun s hs => hout s fun h' => absurd h'.2 (not_le.mpr hs)
    have hc := hcl.closure_subset_iff.mpr hsub
    rw [closure_Ioi] at hc
    exact hc hr'

/-- **`∫ f = 0` kills the kernel at the origin**: `Cf(0) = 2 ∫ f`. -/
theorem cosDilationKernel_zero_of_integral_eq_zero (h0 : ∫ y in Ioi (0 : ℝ), f y = 0) :
    cosDilationKernel f 0 = 0 := by
  have hC : halfLineCosTransform f 0 = 0 := by
    simp [halfLineCosTransform, h0]
  simp [cosDilationKernel, zero_div, hC]

/-- Blindness on `ℕ_{≥2}` gives blindness on all integers `|n| ≥ 2`. -/
theorem cosDilationKernel_int_eq_zero (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) (n : ℤ) (hn : 2 ≤ |n|) :
    cosDilationKernel f n = 0 := by
  have hm : 2 ≤ n.natAbs := by
    rw [Int.abs_eq_natAbs] at hn
    exact_mod_cast hn
  rcases Int.natAbs_eq n with h | h
  · rw [h, Int.cast_natCast]
    exact hblind _ hm
  · rw [h, Int.cast_neg, Int.cast_natCast, cosDilationKernel_neg hf hα hαβ hsupp]
    exact hblind _ hm

/-- **Short cores cannot be blind.**  If `f` is continuous and supported in `[α, β]` with
`0 < α ≤ β ≤ 2α`, and `Ψ_f(0) = 0` and `Ψ_f(n) = 0` for every integer `n ≥ 2`, then `f = 0`. -/
theorem eq_zero_of_cosDilationKernel_blind_of_le_two_mul (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 2 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0) (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (y : ℝ) : f y = 0 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hhi : β / α ≤ 2 := by rw [div_le_iff₀ hα]; linarith
  have hlo : 1 / 2 ≤ α / β := by rw [le_div_iff₀ hβ0]; linarith
  have hZ : ∀ r : ℝ, (r ≤ 1 / 2 ∨ 2 ≤ r) → dilationAutocorr f r = 0 := by
    intro r hr
    refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun h => ?_
    rcases hr with hr | hr
    · linarith [h.1]
    · linarith [h.2]
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  -- the periodization at `x = 0`
  have hP0 := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ 0
  rw [tsum_eq_sum (s := {-1, 1}) fun k hk => ?_] at hP0
  rotate_left
  · have hk' : k = 0 ∨ 2 ≤ |k| := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      by_cases hk0 : k = 0
      · exact Or.inl hk0
      · right; rw [le_abs']; omega
    rw [hZ _ ?_, Complex.ofReal_zero]
    rcases hk' with rfl | hk'
    · left; norm_num
    · right
      rw [zero_add, ← Int.cast_abs]
      exact_mod_cast hk'
  -- the periodization at `x = 1/2`
  have hP1 := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ (1 / 2)
  rw [tsum_eq_sum (s := {-2, -1, 0, 1}) fun k hk => ?_] at hP1
  rotate_left
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [hZ _ ?_, Complex.ofReal_zero]
    right
    rcases le_or_gt 2 k with hk2 | hk2
    · have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      rw [abs_of_pos (by linarith)]; linarith
    · have hk3 : k ≤ -3 := by omega
      have : (k : ℝ) ≤ -3 := by exact_mod_cast hk3
      rw [abs_of_neg (by linarith)]; linarith
  have hA1 : dilationAutocorr f 1 = cosDilationKernel f 1 := by
    have e := hP0
    simp only [Finset.mem_singleton, Int.reduceNeg, neg_eq_self,
      one_ne_zero, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Int.cast_neg,
      Int.cast_one, zero_add, abs_neg, abs_one, mul_zero, Real.cos_zero, mul_one, h0] at e
    have e' : ((2 * dilationAutocorr f 1 : ℝ) : ℂ) = ((2 * cosDilationKernel f 1 : ℝ) : ℂ) := by
      rw [← e]; push_cast; ring
    have := Complex.ofReal_injective e'
    linarith
  have hA32 : dilationAutocorr f (3 / 2) = -cosDilationKernel f 1 := by
    have e := hP1
    have hhalf : dilationAutocorr f (1 / 2) = 0 := hZ _ (Or.inl le_rfl)
    have a1 : |(1 / 2 : ℝ) + ((-2 : ℤ) : ℝ)| = 3 / 2 := by
      rw [abs_of_neg (by push_cast; norm_num)]; push_cast; norm_num
    have a2 : |(1 / 2 : ℝ) + ((-1 : ℤ) : ℝ)| = 1 / 2 := by
      rw [abs_of_neg (by push_cast; norm_num)]; push_cast; norm_num
    have a3 : |(1 / 2 : ℝ) + ((0 : ℤ) : ℝ)| = 1 / 2 := by
      rw [abs_of_pos (by push_cast; norm_num)]; push_cast; norm_num
    have a4 : |(1 / 2 : ℝ) + ((1 : ℤ) : ℝ)| = 3 / 2 := by
      rw [abs_of_pos (by push_cast; norm_num)]; push_cast; norm_num
    have hcos : Real.cos (2 * π * (1 / 2)) = -1 := by
      rw [show 2 * π * (1 / 2) = π by ring, Real.cos_pi]
    rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
      Finset.sum_insert (by norm_num), Finset.sum_singleton, a1, a2, a3, a4, hhalf, hcos, h0] at e
    have e' : ((2 * dilationAutocorr f (3 / 2) : ℝ) : ℂ) =
        ((-(2 * cosDilationKernel f 1) : ℝ) : ℂ) := by
      push_cast; rw [show (-(2 * (cosDilationKernel f 1 : ℂ))) =
        ((0 + 2 * cosDilationKernel f 1 * -1 : ℝ) : ℂ) by push_cast; ring, ← e]
      push_cast; ring
    have := Complex.ofReal_injective e'
    linarith
  -- integrability and the energy `∫ f²`
  have hfc : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_Icc (a := α) (b := β)) fun z hz => ?_
    by_contra h
    exact hz (hsupp z h)
  have hsq : Integrable fun z => f z * f z :=
    (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
  have hsq32 : Integrable fun z => f (3 / 2 * z) * f (3 / 2 * z) := by
    have hc : HasCompactSupport fun z => f (3 / 2 * z) := by
      have h := hfc.comp_smul (by norm_num : (3 / 2 : ℝ) ≠ 0)
      simpa only [Function.comp_def, smul_eq_mul] using h
    exact ((hf.comp (continuous_const.mul continuous_id)).mul
      (hf.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport hc.mul_right
  have hIoi : ∀ g : ℝ → ℝ, (∀ z, f z = 0 → g z = 0) →
      ∫ z in Ioi (0 : ℝ), g z = ∫ z, g z := by
    intro g hg
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hg z ?_
    by_contra h
    exact hz (lt_of_lt_of_le hα (hsupp z h).1)
  set E := ∫ z, f z * f z with hE
  have hA1E : dilationAutocorr f 1 = E := by
    unfold dilationAutocorr
    simp only [one_mul]
    exact hIoi _ fun z hz => by simp [hz]
  have hE0 : 0 ≤ E := integral_nonneg fun z => mul_self_nonneg _
  have hscale : ∫ z, f (3 / 2 * z) * f (3 / 2 * z) = 2 / 3 * E := by
    have h := Measure.integral_comp_mul_left (fun z => f z * f z) (3 / 2 : ℝ)
    simp only [smul_eq_mul] at h
    rw [h, hE]
    norm_num
  have hbound : |dilationAutocorr f (3 / 2)| ≤ 5 / 6 * E := by
    have hA : dilationAutocorr f (3 / 2) = ∫ z, f z * f (3 / 2 * z) := by
      unfold dilationAutocorr
      exact hIoi _ fun z hz => by simp [hz]
    have hint : Integrable fun z => f z * f (3 / 2 * z) := by
      have hc : HasCompactSupport fun z => f z * f (3 / 2 * z) := hfc.mul_right
      exact (hf.mul (hf.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport hc
    rw [hA]
    calc |∫ z, f z * f (3 / 2 * z)| ≤ ∫ z, |f z * f (3 / 2 * z)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, (f z * f z + f (3 / 2 * z) * f (3 / 2 * z)) / 2 := by
          refine integral_mono hint.abs ((hsq.add hsq32).div_const 2) fun z => ?_
          rw [abs_mul]
          nlinarith [sq_nonneg (|f z| - |f (3 / 2 * z)|), sq_abs (f z), sq_abs (f (3 / 2 * z))]
      _ = 5 / 6 * E := by
          rw [integral_div, integral_add hsq hsq32, hscale, ← hE]
          ring
  have hEz : E = 0 := by
    have h1 : |dilationAutocorr f (3 / 2)| = E := by
      rw [hA32, ← hA1, hA1E, abs_neg, abs_of_nonneg hE0]
    linarith
  have hae : (fun z => f z * f z) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => mul_self_nonneg (f z)) hsq).mp hEz
  have heq := (Continuous.ae_eq_iff_eq volume (hf.mul hf) continuous_const).mp hae
  exact mul_self_eq_zero.mp (congrFun heq y)

end

end RHTower
