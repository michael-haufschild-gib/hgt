/-
The weighted second-derivative van der Corput test (nonnegative-derivative case).

For an antitone nonnegative weight `w` and a phase with `g'' ≥ λ > 0` and `g' ≥ 0` on `[a,b]`,
`‖∫_a^b w·exp(i·g)‖ ≤ 5·w(a)/√λ`, length-uniform even across the stationary point.  The proof is the
stationary-point split of the unweighted test carried through the weight: within the short window
where `g'` is small the trivial bound `∫ w ≤ w(a)·length` applies (the weighted length bound), and
outside it `g' ≥ √λ` so the weighted first-derivative test `norm_integral_weight_cexp_le` applies; the
two balance at `w(a)/√λ`.
-/
import GaloisForLFunctions.RHTower.VanDerCorputWeighted
import GaloisForLFunctions.RHTower.VanDerCorputSecond

open Complex intervalIntegral MeasureTheory
open scoped Interval

noncomputable section

namespace RHTower

theorem norm_integral_weight_cexp_secondDeriv_oneside
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {w w' g g' g'' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.uIcc a b, HasDerivAt w (w' x) x)
    (hw'c : ContinuousOn w' (Set.uIcc a b))
    (hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ w x)
    (hwanti : ∀ x ∈ Set.uIcc a b, w' x ≤ 0)
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hg''lb : ∀ x ∈ Set.uIcc a b, lam ≤ g'' x)
    (hg'nn : ∀ x ∈ Set.uIcc a b, 0 ≤ g' x) :
    ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 5 * w a / Real.sqrt lam := by
  set μ := Real.sqrt lam with hμdef
  have hμpos : 0 < μ := Real.sqrt_pos.mpr hlam
  have hμ2 : μ * μ = lam := Real.mul_self_sqrt hlam.le
  have hwa0 : 0 ≤ w a := hwnn a Set.left_mem_uIcc
  have hg''nn : ∀ x ∈ Set.uIcc a b, 0 ≤ g'' x := fun x hx => le_trans hlam.le (hg''lb x hx)
  have haU : a ∈ Set.uIcc a b := Set.left_mem_uIcc
  have hbU : b ∈ Set.uIcc a b := Set.right_mem_uIcc
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hwc : ContinuousOn w (Set.uIcc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn g' (Set.uIcc a b) := fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  -- length lower bound from g'' ≥ lam
  have hlen : ∀ x y, x ∈ Set.uIcc a b → y ∈ Set.uIcc a b → x ≤ y → lam * (y - x) ≤ g' y - g' x := by
    intro x y hx hy hxy
    exact deriv_lower_length hg' hg''c hg''lb hx hy hxy
  -- w antitone
  have hwmono : ∀ x ∈ Set.uIcc a b, w x ≤ w a := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
    have hsub : Set.uIcc a x ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc haU hx
    have hint : IntervalIntegrable w' volume a x := (hw'c.mono hsub).intervalIntegrable
    have hftc : ∫ t in a..x, w' t = w x - w a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hw t (hsub ht)) hint
    have hnp : ∫ t in a..x, w' t ≤ 0 := by
      have hm := intervalIntegral.integral_mono_on hxIcc.1 hint
        (intervalIntegrable_const (c := (0:ℝ)))
        (fun t ht => hwanti t (hsub (by rw [Set.uIcc_of_le hxIcc.1]; exact ht)))
      simpa using hm
    linarith [hftc, hnp]
  -- integrand continuous / integrable on subintervals
  have hIcont : ContinuousOn (fun x => (w x : ℂ) * Complex.exp ((g x : ℂ) * I)) (Set.uIcc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hwc).mul
      (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const))
  have hInt : ∀ u v, u ∈ Set.uIcc a b → v ∈ Set.uIcc a b →
      IntervalIntegrable (fun x => (w x : ℂ) * Complex.exp ((g x : ℂ) * I)) volume u v :=
    fun u v hu hv => (hIcont.mono (Set.uIcc_subset_uIcc hu hv)).intervalIntegrable
  -- weighted trivial length bound on [u,v] ⊆ [a,b]
  have htriv : ∀ u v, u ∈ Set.uIcc a b → v ∈ Set.uIcc a b → u ≤ v →
      ‖∫ x in u..v, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ w a * (v - u) := by
    intro u v hu hv huv
    have hsub : Set.uIcc u v ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hu hv
    calc ‖∫ x in u..v, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖
        ≤ ∫ x in u..v, ‖(w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm huv
      _ ≤ ∫ _x in u..v, w a := by
          apply intervalIntegral.integral_mono_on huv (hInt u v hu hv).norm
            intervalIntegrable_const
          intro x hx
          have hxab : x ∈ Set.uIcc a b := hsub (by rw [Set.uIcc_of_le huv]; exact hx)
          have hexp1 : ‖Complex.exp ((g x : ℂ) * I)‖ = 1 := by simp [Complex.norm_exp]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hwnn x hxab),
            hexp1, mul_one]
          exact hwmono x hxab
      _ = w a * (v - u) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  by_cases hcase1 : g' b ≤ μ
  · -- trivial over the whole interval
    have hlenab := hlen a b haU hbU hab
    have hmb1 : μ * (b - a) ≤ 1 := by
      have h1 : lam * (b - a) ≤ μ := by nlinarith [hg'nn a haU, hcase1, hlenab]
      nlinarith [h1, hμ2, hμpos, mul_nonneg hμpos.le (sub_nonneg.mpr hab)]
    have h := htriv a b haU hbU hab
    calc ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ w a * (b - a) := h
      _ ≤ 5 * w a / μ := by
          rw [le_div_iff₀ hμpos]
          nlinarith [hmb1, hwa0, mul_nonneg hwa0 (sub_nonneg.mpr hmb1)]
  · rw [not_le] at hcase1
    by_cases hcase2 : μ ≤ g' a
    · -- g' ≥ μ everywhere; weighted first-derivative
      have hpos : ∀ x ∈ Set.uIcc a b, μ ≤ g' x := by
        intro x hx
        have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
        have := hlen a x haU hx hxIcc.1
        nlinarith [hcase2, mul_nonneg hlam.le (by linarith [hxIcc.1] : (0:ℝ) ≤ x - a)]
      have hwf := norm_integral_weight_cexp_le hab hμpos hw hw'c hwnn hwanti hg hg' hg''c hpos hg''nn
      calc ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 4 * w a / μ := hwf
        _ ≤ 5 * w a / μ := by rw [div_le_div_iff_of_pos_right hμpos]; nlinarith [hwa0]
    · rw [not_le] at hcase2
      have hmem : μ ∈ Set.Icc (g' a) (g' b) := ⟨hcase2.le, hcase1.le⟩
      have hg'cIcc : ContinuousOn g' (Set.Icc a b) := by rw [← Set.uIcc_of_le hab]; exact hg'c
      obtain ⟨q, hq, hgq⟩ := intermediate_value_Icc hab hg'cIcc hmem
      have hqU : q ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hq
      have haq : a ≤ q := hq.1
      have hqb : q ≤ b := hq.2
      have hsplit : (∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I))
          = (∫ x in a..q, (w x : ℂ) * Complex.exp ((g x : ℂ) * I))
            + ∫ x in q..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I) :=
        (intervalIntegral.integral_add_adjacent_intervals (hInt a q haU hqU) (hInt q b hqU hbU)).symm
      have hsubqb : Set.uIcc q b ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hqU hbU
      -- [a,q]: trivial
      have hAQ : ‖∫ x in a..q, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ w a / μ := by
        have h := htriv a q haU hqU haq
        have hqa : μ * (q - a) ≤ 1 := by
          have hlenaq := hlen a q haU hqU haq
          rw [hgq] at hlenaq
          have h1 : lam * (q - a) ≤ μ := by nlinarith [hg'nn a haU, hlenaq]
          nlinarith [h1, hμ2, hμpos, mul_nonneg hμpos.le (sub_nonneg.mpr haq)]
        calc ‖∫ x in a..q, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ w a * (q - a) := h
          _ ≤ w a / μ := by
              rw [le_div_iff₀ hμpos]
              nlinarith [hqa, hwa0, mul_nonneg hwa0 (sub_nonneg.mpr hqa)]
      -- [q,b]: weighted first-derivative
      have hQB : ‖∫ x in q..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 4 * w a / μ := by
        have hposqb : ∀ x ∈ Set.uIcc q b, μ ≤ g' x := by
          intro x hx
          have hxIcc : x ∈ Set.Icc q b := by rwa [Set.uIcc_of_le hqb] at hx
          have := hlen q x hqU (hsubqb hx) hxIcc.1
          rw [hgq] at this
          nlinarith [mul_nonneg hlam.le (by linarith [hxIcc.1] : (0:ℝ) ≤ x - q)]
        have hwf := norm_integral_weight_cexp_le hqb hμpos
          (fun x hx => hw x (hsubqb hx)) (hw'c.mono hsubqb)
          (fun x hx => hwnn x (hsubqb hx)) (fun x hx => hwanti x (hsubqb hx))
          (fun x hx => hg x (hsubqb hx)) (fun x hx => hg' x (hsubqb hx))
          (hg''c.mono hsubqb) hposqb (fun x hx => hg''nn x (hsubqb hx))
        have hwq : w q ≤ w a := hwmono q hqU
        calc ‖∫ x in q..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 4 * w q / μ := hwf
          _ ≤ 4 * w a / μ := by rw [div_le_div_iff_of_pos_right hμpos]; nlinarith [hwq]
      rw [hsplit]
      calc ‖(∫ x in a..q, (w x : ℂ) * Complex.exp ((g x : ℂ) * I))
              + ∫ x in q..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖
          ≤ ‖∫ x in a..q, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖
              + ‖∫ x in q..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ := norm_add_le _ _
        _ ≤ w a / μ + 4 * w a / μ := add_le_add hAQ hQB
        _ = 5 * w a / μ := by ring

end RHTower
