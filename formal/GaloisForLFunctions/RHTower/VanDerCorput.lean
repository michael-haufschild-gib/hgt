/-
The van der Corput first-derivative test for oscillatory integrals.

If a real phase `g` has a positive derivative `g'` bounded below by `lam > 0` and monotone on an
interval, then the oscillatory integral of `exp(i·g)` is small — no larger than `2/lam`, regardless
of the length of the interval.  The mechanism is a single integration by parts: writing
`exp(i·g) = (i·g')⁻¹ · d/dx[exp(i·g)]`, the boundary term is `exp(i·g)/(i·g')` (modulus `1/g'`) and
the remaining integral is `∫ exp(i·g)·d/dx[(i·g')⁻¹]`, whose modulus is `∫ |g''|/g'²`; monotonicity of
`g'` telescopes that to `|1/g'(a) − 1/g'(b)|`, and the two contributions combine to `2/g'` at the
endpoint where `g'` is smallest, i.e. `≤ 2/lam`.

Two monotonicity directions are recorded (`g'' ≥ 0` and `g'' ≤ 0`); the pure phase `c·log x`
(`c > 0`) has decreasing derivative `c/x`, and its corollary `norm_integral_cexp_logPhase_le` gives
`‖∫_a^b exp(i·c·log x) dx‖ ≤ 2b/c` on `0 < a ≤ b` — the exponential-integral heart of the approximate
functional equation's reflected block.
-/
import Mathlib

open Complex intervalIntegral MeasureTheory
open scoped Interval

noncomputable section

namespace RHTower

/-- **van der Corput first-derivative test, increasing derivative.**  For a real phase `g` with
derivative `g'` and second derivative `g''` on `[a,b]`, with `g'` bounded below by `lam > 0` and
nondecreasing (`g'' ≥ 0`), the oscillatory integral obeys `‖∫ exp(i·g)‖ ≤ 2/lam`. -/
theorem norm_integral_cexp_ofReal_mul_I_le_mono
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {g g' g'' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hpos : ∀ x ∈ Set.uIcc a b, lam ≤ g' x)
    (hmono : ∀ x ∈ Set.uIcc a b, 0 ≤ g'' x) :
    ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖ ≤ 2 / lam := by
  have hg'pos : ∀ x ∈ Set.uIcc a b, 0 < g' x := fun x hx => lt_of_lt_of_le hlam (hpos x hx)
  have hg'ne : ∀ x ∈ Set.uIcc a b, (g' x : ℂ) * I ≠ 0 := fun x hx =>
    mul_ne_zero (by exact_mod_cast (hg'pos x hx).ne') I_ne_zero
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn g' (Set.uIcc a b) := fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  set V : ℝ → ℂ := fun t => Complex.exp ((g t : ℂ) * I) with hVdef
  set V' : ℝ → ℂ := fun t => Complex.exp ((g t : ℂ) * I) * ((g' t : ℂ) * I) with hV'def
  set U : ℝ → ℂ := fun t => ((g' t : ℂ) * I)⁻¹ with hUdef
  set U' : ℝ → ℂ := fun t => -(((g'' t : ℂ) * I) / ((g' t : ℂ) * I) ^ 2) with hU'def
  have hVderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt V (V' x) x := fun x hx =>
    (((hg x hx).ofReal_comp).mul_const I).cexp
  have hUderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt U (U' x) x := by
    intro x hx
    have hw : HasDerivAt (fun t => (g' t : ℂ) * I) ((g'' x : ℂ) * I) x :=
      ((hg' x hx).ofReal_comp).mul_const I
    have h2 := (hasDerivAt_inv (hg'ne x hx)).comp x hw
    rw [hU'def, hUdef]; convert h2 using 1; field_simp
  have hVnorm : ∀ t, ‖V t‖ = 1 := by intro t; rw [hVdef]; simp [Complex.norm_exp]
  have hUnorm : ∀ x ∈ Set.uIcc a b, ‖U x‖ = (g' x)⁻¹ := by
    intro x hx; rw [hUdef, norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hg'pos x hx)]
  have hU'norm : ∀ x ∈ Set.uIcc a b, ‖U' x‖ = g'' x / (g' x) ^ 2 := by
    intro x hx; rw [hU'def, norm_neg, norm_div, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hmono x hx)]
    rw [norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hg'pos x hx)]
  have hVcont : ContinuousOn V (Set.uIcc a b) := by
    rw [hVdef]
    exact Complex.continuous_exp.comp_continuousOn
      ((continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const)
  have hU'cont : ContinuousOn U' (Set.uIcc a b) := by
    rw [hU'def]
    refine ContinuousOn.neg (ContinuousOn.div
      ((continuous_ofReal.comp_continuousOn hg''c).mul continuousOn_const)
      (((continuous_ofReal.comp_continuousOn hg'c).mul continuousOn_const).pow 2)
      (fun x hx => pow_ne_zero _ (hg'ne x hx)))
  have hV'cont : ContinuousOn V' (Set.uIcc a b) := by
    rw [hV'def]
    exact (Complex.continuous_exp.comp_continuousOn
      ((continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const)).mul
      ((continuous_ofReal.comp_continuousOn hg'c).mul continuousOn_const)
  have hV'int : IntervalIntegrable V' volume a b := hV'cont.intervalIntegrable
  have hU'int : IntervalIntegrable U' volume a b := hU'cont.intervalIntegrable
  have hVint : IntervalIntegrable V volume a b := hVcont.intervalIntegrable
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub hUderiv hVderiv hU'int hV'int
  have hUV' : ∀ x ∈ Set.uIcc a b, U' x * V x + U x * V' x = U' x * V x + V x := by
    intro x hx
    have hval : U x * V' x = V x := by
      simp only [hUdef, hV'def, hVdef]
      rw [mul_comm (Complex.exp _) ((g' x : ℂ) * I), ← mul_assoc,
        inv_mul_cancel₀ (hg'ne x hx), one_mul]
    rw [hval]
  rw [intervalIntegral.integral_congr hUV'] at hibp
  have hUVint : IntervalIntegrable (fun x => U' x * V x) volume a b :=
    hU'int.mul_continuousOn hVcont
  rw [intervalIntegral.integral_add hUVint hVint] at hibp
  have hsplit : (∫ x in a..b, V x) = (U b * V b - U a * V a) - ∫ x in a..b, U' x * V x := by
    linear_combination hibp
  have hbdry : ‖U b * V b - U a * V a‖ ≤ (g' a)⁻¹ + (g' b)⁻¹ := by
    calc ‖U b * V b - U a * V a‖ ≤ ‖U b * V b‖ + ‖U a * V a‖ := norm_sub_le _ _
      _ = (g' b)⁻¹ + (g' a)⁻¹ := by
          rw [norm_mul, norm_mul, hVnorm, hVnorm, mul_one, mul_one,
            hUnorm b Set.right_mem_uIcc, hUnorm a Set.left_mem_uIcc]
      _ = (g' a)⁻¹ + (g' b)⁻¹ := by ring
  have hFTCderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t => -(g' t)⁻¹) (g'' x / (g' x) ^ 2) x := by
    intro x hx
    have hi := ((hg' x hx).inv (hg'pos x hx).ne').neg
    convert hi using 1
    field_simp
  have hFTCint : IntervalIntegrable (fun t => g'' t / (g' t) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.div hg''c (hg'c.pow 2) (fun x hx => pow_ne_zero _ (hg'pos x hx).ne')
  have hintUV : ‖∫ x in a..b, U' x * V x‖ ≤ (g' a)⁻¹ - (g' b)⁻¹ := by
    calc ‖∫ x in a..b, U' x * V x‖
        ≤ ∫ x in a..b, ‖U' x * V x‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ x in a..b, g'' x / (g' x) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro x hx
          show ‖U' x * V x‖ = g'' x / (g' x) ^ 2
          rw [norm_mul, hVnorm, mul_one, hU'norm x hx]
      _ = (g' a)⁻¹ - (g' b)⁻¹ := by
          have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hFTCderiv hFTCint
          linarith [hftc]
  rw [hsplit]
  calc ‖(U b * V b - U a * V a) - ∫ x in a..b, U' x * V x‖
      ≤ ‖U b * V b - U a * V a‖ + ‖∫ x in a..b, U' x * V x‖ := norm_sub_le _ _
    _ ≤ ((g' a)⁻¹ + (g' b)⁻¹) + ((g' a)⁻¹ - (g' b)⁻¹) := add_le_add hbdry hintUV
    _ = 2 * (g' a)⁻¹ := by ring
    _ ≤ 2 / lam := by rw [div_eq_mul_inv]; gcongr; exact hpos a Set.left_mem_uIcc

/-- **van der Corput first-derivative test, decreasing derivative.**  Same hypotheses as
`norm_integral_cexp_ofReal_mul_I_le_mono` but with `g'` nonincreasing (`g'' ≤ 0`); again
`‖∫ exp(i·g)‖ ≤ 2/lam`. -/
theorem norm_integral_cexp_ofReal_mul_I_le_anti
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {g g' g'' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hpos : ∀ x ∈ Set.uIcc a b, lam ≤ g' x)
    (hmono : ∀ x ∈ Set.uIcc a b, g'' x ≤ 0) :
    ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖ ≤ 2 / lam := by
  have hg'pos : ∀ x ∈ Set.uIcc a b, 0 < g' x := fun x hx => lt_of_lt_of_le hlam (hpos x hx)
  have hg'ne : ∀ x ∈ Set.uIcc a b, (g' x : ℂ) * I ≠ 0 := fun x hx =>
    mul_ne_zero (by exact_mod_cast (hg'pos x hx).ne') I_ne_zero
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn g' (Set.uIcc a b) := fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  set V : ℝ → ℂ := fun t => Complex.exp ((g t : ℂ) * I) with hVdef
  set V' : ℝ → ℂ := fun t => Complex.exp ((g t : ℂ) * I) * ((g' t : ℂ) * I) with hV'def
  set U : ℝ → ℂ := fun t => ((g' t : ℂ) * I)⁻¹ with hUdef
  set U' : ℝ → ℂ := fun t => -(((g'' t : ℂ) * I) / ((g' t : ℂ) * I) ^ 2) with hU'def
  have hVderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt V (V' x) x := fun x hx =>
    (((hg x hx).ofReal_comp).mul_const I).cexp
  have hUderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt U (U' x) x := by
    intro x hx
    have hw : HasDerivAt (fun t => (g' t : ℂ) * I) ((g'' x : ℂ) * I) x :=
      ((hg' x hx).ofReal_comp).mul_const I
    have h2 := (hasDerivAt_inv (hg'ne x hx)).comp x hw
    rw [hU'def, hUdef]; convert h2 using 1; field_simp
  have hVnorm : ∀ t, ‖V t‖ = 1 := by intro t; rw [hVdef]; simp [Complex.norm_exp]
  have hUnorm : ∀ x ∈ Set.uIcc a b, ‖U x‖ = (g' x)⁻¹ := by
    intro x hx; rw [hUdef, norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hg'pos x hx)]
  have hU'norm : ∀ x ∈ Set.uIcc a b, ‖U' x‖ = -(g'' x) / (g' x) ^ 2 := by
    intro x hx; rw [hU'def, norm_neg, norm_div, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (hmono x hx)]
    rw [norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hg'pos x hx)]
  have hVcont : ContinuousOn V (Set.uIcc a b) := by
    rw [hVdef]
    exact Complex.continuous_exp.comp_continuousOn
      ((continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const)
  have hU'cont : ContinuousOn U' (Set.uIcc a b) := by
    rw [hU'def]
    refine ContinuousOn.neg (ContinuousOn.div
      ((continuous_ofReal.comp_continuousOn hg''c).mul continuousOn_const)
      (((continuous_ofReal.comp_continuousOn hg'c).mul continuousOn_const).pow 2)
      (fun x hx => pow_ne_zero _ (hg'ne x hx)))
  have hV'cont : ContinuousOn V' (Set.uIcc a b) := by
    rw [hV'def]
    exact (Complex.continuous_exp.comp_continuousOn
      ((continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const)).mul
      ((continuous_ofReal.comp_continuousOn hg'c).mul continuousOn_const)
  have hV'int : IntervalIntegrable V' volume a b := hV'cont.intervalIntegrable
  have hU'int : IntervalIntegrable U' volume a b := hU'cont.intervalIntegrable
  have hVint : IntervalIntegrable V volume a b := hVcont.intervalIntegrable
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub hUderiv hVderiv hU'int hV'int
  have hUV' : ∀ x ∈ Set.uIcc a b, U' x * V x + U x * V' x = U' x * V x + V x := by
    intro x hx
    have hval : U x * V' x = V x := by
      simp only [hUdef, hV'def, hVdef]
      rw [mul_comm (Complex.exp _) ((g' x : ℂ) * I), ← mul_assoc,
        inv_mul_cancel₀ (hg'ne x hx), one_mul]
    rw [hval]
  rw [intervalIntegral.integral_congr hUV'] at hibp
  have hUVint : IntervalIntegrable (fun x => U' x * V x) volume a b :=
    hU'int.mul_continuousOn hVcont
  rw [intervalIntegral.integral_add hUVint hVint] at hibp
  have hsplit : (∫ x in a..b, V x) = (U b * V b - U a * V a) - ∫ x in a..b, U' x * V x := by
    linear_combination hibp
  have hbdry : ‖U b * V b - U a * V a‖ ≤ (g' a)⁻¹ + (g' b)⁻¹ := by
    calc ‖U b * V b - U a * V a‖ ≤ ‖U b * V b‖ + ‖U a * V a‖ := norm_sub_le _ _
      _ = (g' b)⁻¹ + (g' a)⁻¹ := by
          rw [norm_mul, norm_mul, hVnorm, hVnorm, mul_one, mul_one,
            hUnorm b Set.right_mem_uIcc, hUnorm a Set.left_mem_uIcc]
      _ = (g' a)⁻¹ + (g' b)⁻¹ := by ring
  have hFTCderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t => (g' t)⁻¹) (-(g'' x) / (g' x) ^ 2) x :=
    fun x hx => (hg' x hx).inv (hg'pos x hx).ne'
  have hFTCint : IntervalIntegrable (fun t => -(g'' t) / (g' t) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.div hg''c.neg (hg'c.pow 2) (fun x hx => pow_ne_zero _ (hg'pos x hx).ne')
  have hintUV : ‖∫ x in a..b, U' x * V x‖ ≤ (g' b)⁻¹ - (g' a)⁻¹ := by
    calc ‖∫ x in a..b, U' x * V x‖
        ≤ ∫ x in a..b, ‖U' x * V x‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ x in a..b, -(g'' x) / (g' x) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro x hx
          show ‖U' x * V x‖ = -(g'' x) / (g' x) ^ 2
          rw [norm_mul, hVnorm, mul_one, hU'norm x hx]
      _ = (g' b)⁻¹ - (g' a)⁻¹ := by
          have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hFTCderiv hFTCint
          linarith [hftc]
  rw [hsplit]
  calc ‖(U b * V b - U a * V a) - ∫ x in a..b, U' x * V x‖
      ≤ ‖U b * V b - U a * V a‖ + ‖∫ x in a..b, U' x * V x‖ := norm_sub_le _ _
    _ ≤ ((g' a)⁻¹ + (g' b)⁻¹) + ((g' b)⁻¹ - (g' a)⁻¹) := add_le_add hbdry hintUV
    _ = 2 * (g' b)⁻¹ := by ring
    _ ≤ 2 / lam := by rw [div_eq_mul_inv]; gcongr; exact hpos b Set.right_mem_uIcc

/-- **Pure logarithmic phase.**  For `c > 0` and `0 < a ≤ b`, the oscillatory integral of the pure
phase `c·log x` — the modulus-free factor of `x^(i c)` — obeys `‖∫_a^b exp(i·c·log x) dx‖ ≤ 2b/c`.
The phase derivative `c/x` is positive and decreasing with minimum `c/b`, so this is the decreasing
van der Corput test with `lam = c/b`. -/
theorem norm_integral_cexp_logPhase_le
    {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) :
    ‖∫ x in a..b, Complex.exp (((c * Real.log x : ℝ)) * I)‖ ≤ 2 * b / c := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hxpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx; rw [huIcc] at hx; exact lt_of_lt_of_le ha hx.1
  have hxle : ∀ x ∈ Set.uIcc a b, x ≤ b := by
    intro x hx; rw [huIcc] at hx; exact hx.2
  -- g = c log, g' = c/x, g'' = -c/x²
  have hg : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => c * Real.log x) (c * (x)⁻¹) x := by
    intro x hx
    exact (Real.hasDerivAt_log (hxpos x hx).ne').const_mul c
  have hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => c * (x)⁻¹) (c * (-((x) ^ 2)⁻¹)) x := by
    intro x hx
    exact (hasDerivAt_inv (hxpos x hx).ne').const_mul c
  have hg''c : ContinuousOn (fun x => c * (-((x) ^ 2)⁻¹)) (Set.uIcc a b) := by
    apply continuousOn_const.mul
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (continuousOn_pow 2)
    intro x hx; exact pow_ne_zero _ (hxpos x hx).ne'
  have hpos : ∀ x ∈ Set.uIcc a b, c / b ≤ c * (x)⁻¹ := by
    intro x hx
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ hc.le
    exact inv_anti₀ (hxpos x hx) (hxle x hx)
  have hmono : ∀ x ∈ Set.uIcc a b, c * (-((x) ^ 2)⁻¹) ≤ 0 := by
    intro x hx
    have : 0 ≤ ((x) ^ 2)⁻¹ := by positivity
    nlinarith [hc.le, this]
  have hcb : 0 < c / b := div_pos hc hb
  have := norm_integral_cexp_ofReal_mul_I_le_anti hab hcb hg hg' hg''c hpos hmono
  calc ‖∫ x in a..b, Complex.exp (((c * Real.log x : ℝ)) * I)‖ ≤ 2 / (c / b) := this
    _ = 2 * b / c := by field_simp

/-- An antitone nonnegative weight is bounded by its left value: for `w` with derivative `w' ≤ 0`
on `[a,b]`, `w x ≤ w a` for every `x` in the interval.  Proven by integrating `w' ≤ 0` from `a`
to `x`. -/
theorem weight_le_left_of_deriv_nonpos {a b : ℝ} (hab : a ≤ b) {w w' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.uIcc a b, HasDerivAt w (w' x) x)
    (hw'c : ContinuousOn w' (Set.uIcc a b))
    (hwanti : ∀ x ∈ Set.uIcc a b, w' x ≤ 0) :
    ∀ x ∈ Set.uIcc a b, w x ≤ w a := by
  intro x hx
  have haU : a ∈ Set.uIcc a b := Set.left_mem_uIcc
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

end RHTower
