/-
The general weighted second-derivative van der Corput test.

Combines the convex one-sided bound (`norm_integral_weight_cexp_secondDeriv_oneside`) with its concave
companion — proved here for `g' ≤ 0` via the conjugation `exp(i·g) ↦ exp(−i·g)`, which flips the sign
of both `g'` and `g''`.  Splitting a general phase (`g'' ≥ λ > 0`) at its stationary point `g' = 0`
yields `‖∫_a^b w·exp(i·g)‖ ≤ 10·w(a)/√λ` with no monotonicity assumption on `g'` — the estimate the
reflected-block saddle modes need, whose phase `2πn·x + τ·log x` has an interior stationary point.
-/
import GaloisForLFunctions.RHTower.VanDerCorputWeightedSecond
import GaloisForLFunctions.RHTower.VanDerCorputWeightedAnti

open Complex intervalIntegral MeasureTheory
open scoped Interval

noncomputable section

namespace RHTower

theorem norm_integral_weight_cexp_conj_neg {a b : ℝ} {w g : ℝ → ℝ}
    (hint : IntervalIntegrable (fun x => (w x : ℂ) * Complex.exp ((g x : ℂ) * I)) volume a b) :
    ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖
      = ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((-g x : ℝ) * I)‖ := by
  have hstep : (∫ x in a..b, (w x : ℂ) * Complex.exp ((-g x : ℝ) * I))
      = (starRingEnd ℂ) (∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)) := by
    have hconj : (∫ x in a..b, (starRingEnd ℂ) ((w x : ℂ) * Complex.exp ((g x : ℂ) * I)))
        = (starRingEnd ℂ) (∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)) := by
      have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm hint
      simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using h
    rw [← hconj]
    apply intervalIntegral.integral_congr
    intro x _
    show (w x : ℂ) * Complex.exp ((-(g x) : ℝ) * I)
      = (starRingEnd ℂ) ((w x : ℂ) * Complex.exp ((g x : ℂ) * I))
    have harg : ((-(g x) : ℝ) : ℂ) * I = (starRingEnd ℂ) ((g x : ℂ) * I) := by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, harg]
  rw [hstep, Complex.norm_conj]

theorem norm_integral_weight_cexp_secondDeriv_oneside_concave
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {w w' g g' g'' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.uIcc a b, HasDerivAt w (w' x) x)
    (hw'c : ContinuousOn w' (Set.uIcc a b))
    (hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ w x)
    (hwanti : ∀ x ∈ Set.uIcc a b, w' x ≤ 0)
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hg''ub : ∀ x ∈ Set.uIcc a b, g'' x ≤ -lam)
    (hg'nn : ∀ x ∈ Set.uIcc a b, 0 ≤ g' x) :
    ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 5 * w a / Real.sqrt lam := by
  set μ := Real.sqrt lam with hμdef
  have hμpos : 0 < μ := Real.sqrt_pos.mpr hlam
  have hμ2 : μ * μ = lam := Real.mul_self_sqrt hlam.le
  have hwa0 : 0 ≤ w a := hwnn a Set.left_mem_uIcc
  have hg''np : ∀ x ∈ Set.uIcc a b, g'' x ≤ 0 := fun x hx => le_trans (hg''ub x hx) (by linarith)
  have haU : a ∈ Set.uIcc a b := Set.left_mem_uIcc
  have hbU : b ∈ Set.uIcc a b := Set.right_mem_uIcc
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hwc : ContinuousOn w (Set.uIcc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn g' (Set.uIcc a b) := fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  -- length bound from g'' ≤ -lam (g' decreasing): lam*(y-x) ≤ g'x - g'y
  have hlen : ∀ x y, x ∈ Set.uIcc a b → y ∈ Set.uIcc a b → x ≤ y → lam * (y - x) ≤ g' x - g' y := by
    intro x y hx hy hxy
    have h : lam * (y - x) ≤ -g' y - -g' x :=
      deriv_lower_length (g' := fun t => -g' t) (g'' := fun t => -g'' t)
        (fun z hz => (hg' z hz).neg) hg''c.neg (fun z hz => by linarith [hg''ub z hz]) hx hy hxy
    linarith [h]
  have hwmono : ∀ x ∈ Set.uIcc a b, w x ≤ w a := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
    have hsub : Set.uIcc a x ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc haU hx
    have hint : IntervalIntegrable w' volume a x := (hw'c.mono hsub).intervalIntegrable
    have hftc : ∫ t in a..x, w' t = w x - w a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hw t (hsub ht)) hint
    have hnp : ∫ t in a..x, w' t ≤ 0 := by
      have hm := intervalIntegral.integral_mono_on hxIcc.1 hint
        (intervalIntegral.intervalIntegrable_const (c := (0:ℝ)))
        (fun t ht => hwanti t (hsub (by rw [Set.uIcc_of_le hxIcc.1]; exact ht)))
      simpa using hm
    linarith [hftc, hnp]
  have hIcont : ContinuousOn (fun x => (w x : ℂ) * Complex.exp ((g x : ℂ) * I)) (Set.uIcc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hwc).mul
      (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const))
  have hInt : ∀ u v, u ∈ Set.uIcc a b → v ∈ Set.uIcc a b →
      IntervalIntegrable (fun x => (w x : ℂ) * Complex.exp ((g x : ℂ) * I)) volume u v :=
    fun u v hu hv => (hIcont.mono (Set.uIcc_subset_uIcc hu hv)).intervalIntegrable
  have htriv : ∀ u v, u ∈ Set.uIcc a b → v ∈ Set.uIcc a b → u ≤ v →
      ‖∫ x in u..v, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ w a * (v - u) := by
    intro u v hu hv huv
    have hsub : Set.uIcc u v ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hu hv
    calc ‖∫ x in u..v, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖
        ≤ ∫ x in u..v, ‖(w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm huv
      _ ≤ ∫ _x in u..v, w a := by
          apply intervalIntegral.integral_mono_on huv (hInt u v hu hv).norm
            (intervalIntegral.intervalIntegrable_const)
          intro x hx
          have hxab : x ∈ Set.uIcc a b := hsub (by rw [Set.uIcc_of_le huv]; exact hx)
          have hexp1 : ‖Complex.exp ((g x : ℂ) * I)‖ = 1 := by simp [Complex.norm_exp]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hwnn x hxab),
            hexp1, mul_one]
          exact hwmono x hxab
      _ = w a * (v - u) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  -- weighted-first-anti on a subinterval where g' ≥ μ
  have hwfa : ∀ u v, u ∈ Set.uIcc a b → v ∈ Set.uIcc a b → u ≤ v →
      (∀ x ∈ Set.uIcc u v, μ ≤ g' x) →
      ‖∫ x in u..v, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 4 * w u / μ := by
    intro u v hu hv huv hposuv
    have hsub : Set.uIcc u v ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hu hv
    exact norm_integral_weight_cexp_le_anti huv hμpos
      (fun x hx => hw x (hsub hx)) (hw'c.mono hsub)
      (fun x hx => hwnn x (hsub hx)) (fun x hx => hwanti x (hsub hx))
      (fun x hx => hg x (hsub hx)) (fun x hx => hg' x (hsub hx))
      (hg''c.mono hsub) hposuv (fun x hx => hg''np x (hsub hx))
  by_cases hcase1 : g' a ≤ μ
  · -- g' ≤ μ everywhere; trivial
    have hlenab := hlen a b haU hbU hab
    have hmb1 : μ * (b - a) ≤ 1 := by
      have h1 : lam * (b - a) ≤ μ := by nlinarith [hg'nn b hbU, hcase1, hlenab]
      nlinarith [h1, hμ2, hμpos, mul_nonneg hμpos.le (sub_nonneg.mpr hab)]
    have h := htriv a b haU hbU hab
    calc ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ w a * (b - a) := h
      _ ≤ 5 * w a / μ := by
          rw [le_div_iff₀ hμpos]
          nlinarith [hmb1, hwa0, mul_nonneg hwa0 (sub_nonneg.mpr hmb1)]
  · rw [not_le] at hcase1
    by_cases hcase2 : μ ≤ g' b
    · -- g' ≥ μ everywhere; weighted-first-anti
      have hpos : ∀ x ∈ Set.uIcc a b, μ ≤ g' x := by
        intro x hx
        have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
        have := hlen x b hx hbU hxIcc.2
        nlinarith [hcase2, mul_nonneg hlam.le (by linarith [hxIcc.2] : (0:ℝ) ≤ b - x)]
      have hwf := hwfa a b haU hbU hab hpos
      calc ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 4 * w a / μ := hwf
        _ ≤ 5 * w a / μ := by rw [div_le_div_iff_of_pos_right hμpos]; nlinarith [hwa0]
    · rw [not_le] at hcase2
      have hmem : μ ∈ Set.Icc (g' b) (g' a) := ⟨hcase2.le, hcase1.le⟩
      have hg'cIcc : ContinuousOn g' (Set.Icc a b) := by rw [← Set.uIcc_of_le hab]; exact hg'c
      obtain ⟨q, hq, hgq⟩ := intermediate_value_Icc' hab hg'cIcc hmem
      have hqU : q ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hq
      have haq : a ≤ q := hq.1
      have hqb : q ≤ b := hq.2
      have hsplit : (∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I))
          = (∫ x in a..q, (w x : ℂ) * Complex.exp ((g x : ℂ) * I))
            + ∫ x in q..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I) :=
        (intervalIntegral.integral_add_adjacent_intervals (hInt a q haU hqU) (hInt q b hqU hbU)).symm
      have hsubqb : Set.uIcc q b ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hqU hbU
      -- [a,q]: g' ≥ μ, weighted-first-anti
      have hAQ : ‖∫ x in a..q, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 4 * w a / μ := by
        have hposaq : ∀ x ∈ Set.uIcc a q, μ ≤ g' x := by
          intro x hx
          have hxIcc : x ∈ Set.Icc a q := by rwa [Set.uIcc_of_le haq] at hx
          have hxU : x ∈ Set.uIcc a b := (Set.uIcc_subset_uIcc haU hqU) hx
          have := hlen x q hxU hqU hxIcc.2
          rw [hgq] at this
          nlinarith [mul_nonneg hlam.le (by linarith [hxIcc.2] : (0:ℝ) ≤ q - x)]
        exact hwfa a q haU hqU haq hposaq
      -- [q,b]: g' ≤ μ, trivial
      have hQB : ‖∫ x in q..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ w a / μ := by
        have h := htriv q b hqU hbU hqb
        have hqb1 : μ * (b - q) ≤ 1 := by
          have hlenqb := hlen q b hqU hbU hqb
          rw [hgq] at hlenqb
          have h1 : lam * (b - q) ≤ μ := by nlinarith [hg'nn b hbU, hlenqb]
          nlinarith [h1, hμ2, hμpos, mul_nonneg hμpos.le (sub_nonneg.mpr hqb)]
        calc ‖∫ x in q..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ w a * (b - q) := h
          _ ≤ w a / μ := by
              rw [le_div_iff₀ hμpos]
              nlinarith [hqb1, hwa0, mul_nonneg hwa0 (sub_nonneg.mpr hqb1)]
      rw [hsplit]
      calc ‖(∫ x in a..q, (w x : ℂ) * Complex.exp ((g x : ℂ) * I))
              + ∫ x in q..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖
          ≤ ‖∫ x in a..q, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖
              + ‖∫ x in q..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ := norm_add_le _ _
        _ ≤ 4 * w a / μ + w a / μ := add_le_add hAQ hQB
        _ = 5 * w a / μ := by ring

/-- **General weighted second-derivative van der Corput** (`g''` bounded below).  For an antitone
nonnegative weight `w` and a phase with `g'' ≥ λ > 0` (no sign condition on `g'`),
`‖∫_a^b w·exp(i·g)‖ ≤ 10·w(a)/√λ`.  Split at the stationary point `g' = 0`: the `g' ≥ 0` side is the
convex one-sided bound, the `g' ≤ 0` side is its conjugate through the concave companion. -/
theorem norm_integral_weight_cexp_secondDeriv
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {w w' g g' g'' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.uIcc a b, HasDerivAt w (w' x) x)
    (hw'c : ContinuousOn w' (Set.uIcc a b))
    (hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ w x)
    (hwanti : ∀ x ∈ Set.uIcc a b, w' x ≤ 0)
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hg''lb : ∀ x ∈ Set.uIcc a b, lam ≤ g'' x) :
    ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 10 * w a / Real.sqrt lam := by
  have hμpos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hwa0 : 0 ≤ w a := hwnn a Set.left_mem_uIcc
  have haU : a ∈ Set.uIcc a b := Set.left_mem_uIcc
  have hbU : b ∈ Set.uIcc a b := Set.right_mem_uIcc
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hwc : ContinuousOn w (Set.uIcc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn g' (Set.uIcc a b) := fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  have hlen : ∀ x y, x ∈ Set.uIcc a b → y ∈ Set.uIcc a b → x ≤ y → lam * (y - x) ≤ g' y - g' x :=
    fun x y hx hy hxy => deriv_lower_length hg' hg''c hg''lb hx hy hxy
  have hIcont : ContinuousOn (fun x => (w x : ℂ) * Complex.exp ((g x : ℂ) * I)) (Set.uIcc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hwc).mul
      (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const))
  have hInt : ∀ u v, u ∈ Set.uIcc a b → v ∈ Set.uIcc a b →
      IntervalIntegrable (fun x => (w x : ℂ) * Complex.exp ((g x : ℂ) * I)) volume u v :=
    fun u v hu hv => (hIcont.mono (Set.uIcc_subset_uIcc hu hv)).intervalIntegrable
  have hwmono : ∀ x ∈ Set.uIcc a b, w x ≤ w a := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
    have hsub : Set.uIcc a x ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc haU hx
    have hint : IntervalIntegrable w' volume a x := (hw'c.mono hsub).intervalIntegrable
    have hftc : ∫ t in a..x, w' t = w x - w a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hw t (hsub ht)) hint
    have hnp : ∫ t in a..x, w' t ≤ 0 := by
      have hm := intervalIntegral.integral_mono_on hxIcc.1 hint
        (intervalIntegral.intervalIntegrable_const (c := (0:ℝ)))
        (fun t ht => hwanti t (hsub (by rw [Set.uIcc_of_le hxIcc.1]; exact ht)))
      simpa using hm
    linarith [hftc, hnp]
  -- the g' ≤ 0 side, via conjugation through the concave companion
  have hneg : ∀ u v, u ∈ Set.uIcc a b → v ∈ Set.uIcc a b → u ≤ v →
      (∀ x ∈ Set.uIcc u v, g' x ≤ 0) →
      ‖∫ x in u..v, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 5 * w u / Real.sqrt lam := by
    intro u v hu hv huv hg'np
    have hsub : Set.uIcc u v ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hu hv
    rw [norm_integral_weight_cexp_conj_neg (hInt u v hu hv)]
    have hconc := norm_integral_weight_cexp_secondDeriv_oneside_concave
      (g := fun x => -g x) (g' := fun x => -g' x) (g'' := fun x => -g'' x) huv hlam
      (fun x hx => hw x (hsub hx)) (hw'c.mono hsub)
      (fun x hx => hwnn x (hsub hx)) (fun x hx => hwanti x (hsub hx))
      (fun x hx => (hg x (hsub hx)).neg) (fun x hx => (hg' x (hsub hx)).neg) (hg''c.mono hsub).neg
      (fun x hx => by linarith [hg''lb x (hsub hx)]) (fun x hx => by linarith [hg'np x hx])
    calc ‖∫ x in u..v, (w x : ℂ) * Complex.exp ((-g x : ℝ) * I)‖
        = ‖∫ x in u..v, (w x : ℂ) * Complex.exp (((-g x : ℝ)) * I)‖ := rfl
      _ ≤ 5 * w u / Real.sqrt lam := hconc
  by_cases hga : 0 ≤ g' a
  · -- g' ≥ 0 everywhere
    have hg'nn : ∀ x ∈ Set.uIcc a b, 0 ≤ g' x := by
      intro x hx
      have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
      have := hlen a x haU hx hxIcc.1
      nlinarith [hga, mul_nonneg hlam.le (by linarith [hxIcc.1] : (0:ℝ) ≤ x - a)]
    have h := norm_integral_weight_cexp_secondDeriv_oneside hab hlam hw hw'c hwnn hwanti hg hg' hg''c
      hg''lb hg'nn
    calc ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 5 * w a / Real.sqrt lam := h
      _ ≤ 10 * w a / Real.sqrt lam := by
          rw [div_le_div_iff_of_pos_right hμpos]; nlinarith [hwa0]
  · rw [not_le] at hga
    by_cases hgb : g' b ≤ 0
    · -- g' ≤ 0 everywhere
      have hg'np : ∀ x ∈ Set.uIcc a b, g' x ≤ 0 := by
        intro x hx
        have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
        have := hlen x b hx hbU hxIcc.2
        nlinarith [hgb, mul_nonneg hlam.le (by linarith [hxIcc.2] : (0:ℝ) ≤ b - x)]
      calc ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖
          ≤ 5 * w a / Real.sqrt lam := hneg a b haU hbU hab hg'np
        _ ≤ 10 * w a / Real.sqrt lam := by
            rw [div_le_div_iff_of_pos_right hμpos]; nlinarith [hwa0]
    · rw [not_le] at hgb
      have hmem : (0 : ℝ) ∈ Set.Icc (g' a) (g' b) := ⟨hga.le, hgb.le⟩
      have hg'cIcc : ContinuousOn g' (Set.Icc a b) := by rw [← Set.uIcc_of_le hab]; exact hg'c
      obtain ⟨c, hc, hgc0⟩ := intermediate_value_Icc hab hg'cIcc hmem
      have hcU : c ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hc
      have hac : a ≤ c := hc.1
      have hcb : c ≤ b := hc.2
      have hsubac : Set.uIcc a c ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc haU hcU
      have hsubcb : Set.uIcc c b ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hcU hbU
      have hsplit : (∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I))
          = (∫ x in a..c, (w x : ℂ) * Complex.exp ((g x : ℂ) * I))
            + ∫ x in c..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I) :=
        (intervalIntegral.integral_add_adjacent_intervals (hInt a c haU hcU) (hInt c b hcU hbU)).symm
      -- [a,c]: g' ≤ 0
      have hAC : ‖∫ x in a..c, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 5 * w a / Real.sqrt lam := by
        have hg'np : ∀ x ∈ Set.uIcc a c, g' x ≤ 0 := by
          intro x hx
          have hxIcc : x ∈ Set.Icc a c := by rwa [Set.uIcc_of_le hac] at hx
          have := hlen x c (hsubac hx) hcU hxIcc.2
          rw [hgc0] at this
          nlinarith [mul_nonneg hlam.le (by linarith [hxIcc.2] : (0:ℝ) ≤ c - x)]
        exact hneg a c haU hcU hac hg'np
      -- [c,b]: g' ≥ 0
      have hCB : ‖∫ x in c..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 5 * w a / Real.sqrt lam := by
        have hg'nn : ∀ x ∈ Set.uIcc c b, 0 ≤ g' x := by
          intro x hx
          have hxIcc : x ∈ Set.Icc c b := by rwa [Set.uIcc_of_le hcb] at hx
          have := hlen c x hcU (hsubcb hx) hxIcc.1
          rw [hgc0] at this
          nlinarith [mul_nonneg hlam.le (by linarith [hxIcc.1] : (0:ℝ) ≤ x - c)]
        have h := norm_integral_weight_cexp_secondDeriv_oneside hcb hlam
          (fun x hx => hw x (hsubcb hx)) (hw'c.mono hsubcb)
          (fun x hx => hwnn x (hsubcb hx)) (fun x hx => hwanti x (hsubcb hx))
          (fun x hx => hg x (hsubcb hx)) (fun x hx => hg' x (hsubcb hx)) (hg''c.mono hsubcb)
          (fun x hx => hg''lb x (hsubcb hx)) hg'nn
        have hwc0 : w c ≤ w a := hwmono c hcU
        calc ‖∫ x in c..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 5 * w c / Real.sqrt lam := h
          _ ≤ 5 * w a / Real.sqrt lam := by
              rw [div_le_div_iff_of_pos_right hμpos]; nlinarith [hwc0]
      rw [hsplit]
      calc ‖(∫ x in a..c, (w x : ℂ) * Complex.exp ((g x : ℂ) * I))
              + ∫ x in c..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖
          ≤ ‖∫ x in a..c, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖
              + ‖∫ x in c..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ := norm_add_le _ _
        _ ≤ 5 * w a / Real.sqrt lam + 5 * w a / Real.sqrt lam := add_le_add hAC hCB
        _ = 10 * w a / Real.sqrt lam := by ring

/-- **General weighted second-derivative van der Corput** (`g''` bounded above by `−λ`).  The concave
counterpart, obtained by conjugating `exp(i·g) ↦ exp(−i·g)`: for `g'' ≤ −λ < 0`,
`‖∫_a^b w·exp(i·g)‖ ≤ 10·w(a)/√λ`.  This is the form the reflected-block saddle modes take, phase
`2πn·x + τ·log x` having `φ'' = −τ/x² < 0`. -/
theorem norm_integral_weight_cexp_secondDeriv_neg
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {w w' g g' g'' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.uIcc a b, HasDerivAt w (w' x) x)
    (hw'c : ContinuousOn w' (Set.uIcc a b))
    (hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ w x)
    (hwanti : ∀ x ∈ Set.uIcc a b, w' x ≤ 0)
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hg''ub : ∀ x ∈ Set.uIcc a b, g'' x ≤ -lam) :
    ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 10 * w a / Real.sqrt lam := by
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hwc : ContinuousOn w (Set.uIcc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hIcont : ContinuousOn (fun x => (w x : ℂ) * Complex.exp ((g x : ℂ) * I)) (Set.uIcc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hwc).mul
      (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const))
  rw [norm_integral_weight_cexp_conj_neg hIcont.intervalIntegrable]
  exact norm_integral_weight_cexp_secondDeriv (g := fun x => -g x) (g' := fun x => -g' x)
    (g'' := fun x => -g'' x) hab hlam hw hw'c hwnn hwanti (fun x hx => (hg x hx).neg)
    (fun x hx => (hg' x hx).neg) hg''c.neg (fun x hx => by linarith [hg''ub x hx])

end RHTower
