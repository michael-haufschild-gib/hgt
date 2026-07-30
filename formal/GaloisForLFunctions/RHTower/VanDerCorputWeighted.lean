/-
The weighted van der Corput first-derivative test.

An antitone nonnegative real weight `w` against an oscillatory `exp(i·g)` whose phase has
`g' ≥ λ > 0` monotone (`g'' ≥ 0`) obeys `‖∫_a^b w·exp(i·g)‖ ≤ 4·w(a)/λ` — the length-uniform
cancellation persists through the weight.  One integration by parts with `u = w·(i·g')⁻¹`,
`v = exp(i·g)`: the boundary term has modulus `w/g'`, and the remainder splits into the two pieces
`∫ |w'|/g'` (bounded by the total variation `w(a)−w(b)` of the weight over `λ`) and `∫ w·g''/g'²`
(bounded by `w(a)/λ` via `∫ g''/g'² = 1/g'(a) − 1/g'(b)`).

This is the per-mode ingredient the approximate functional equation's reflected block needs beyond the
unweighted tests: the Fourier modes of the Euler–Maclaurin sawtooth carry a `1/x` amplitude, whose
oscillatory integral this bounds.
-/
import GaloisForLFunctions.RHTower.VanDerCorput

open Complex intervalIntegral MeasureTheory
open scoped Interval

noncomputable section

namespace RHTower

/-- **Weighted first-derivative van der Corput.**  For an antitone nonnegative weight `w`
(`w' ≤ 0`, `w ≥ 0`) and a phase with `g' ≥ λ > 0` nondecreasing (`g'' ≥ 0`),
`‖∫_a^b w·exp(i·g)‖ ≤ 4·w(a)/λ`, uniformly in the length. -/
theorem norm_integral_weight_cexp_le
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {w w' g g' g'' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.uIcc a b, HasDerivAt w (w' x) x)
    (hw'c : ContinuousOn w' (Set.uIcc a b))
    (hwnn : ∀ x ∈ Set.uIcc a b, 0 ≤ w x)
    (hwanti : ∀ x ∈ Set.uIcc a b, w' x ≤ 0)
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hg'lb : ∀ x ∈ Set.uIcc a b, lam ≤ g' x)
    (hg''nn : ∀ x ∈ Set.uIcc a b, 0 ≤ g'' x) :
    ‖∫ x in a..b, (w x : ℂ) * Complex.exp ((g x : ℂ) * I)‖ ≤ 4 * w a / lam := by
  have hg'pos : ∀ x ∈ Set.uIcc a b, 0 < g' x := fun x hx => lt_of_lt_of_le hlam (hg'lb x hx)
  have hg'ne : ∀ x ∈ Set.uIcc a b, (g' x : ℂ) * I ≠ 0 := fun x hx =>
    mul_ne_zero (by exact_mod_cast (hg'pos x hx).ne') I_ne_zero
  have hwc : ContinuousOn w (Set.uIcc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn g' (Set.uIcc a b) := fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  have haU : a ∈ Set.uIcc a b := Set.left_mem_uIcc
  have hbU : b ∈ Set.uIcc a b := Set.right_mem_uIcc
  have hwmono : ∀ x ∈ Set.uIcc a b, w x ≤ w a :=
    weight_le_left_of_deriv_nonpos hab hw hw'c hwanti
  set V : ℝ → ℂ := fun t => Complex.exp ((g t : ℂ) * I) with hVdef
  set V' : ℝ → ℂ := fun t => Complex.exp ((g t : ℂ) * I) * ((g' t : ℂ) * I) with hV'def
  set U : ℝ → ℂ := fun t => (w t : ℂ) * ((g' t : ℂ) * I)⁻¹ with hUdef
  set U' : ℝ → ℂ := fun t => (w' t : ℂ) * ((g' t : ℂ) * I)⁻¹
      + (w t : ℂ) * (-(((g'' t : ℂ) * I) / ((g' t : ℂ) * I) ^ 2)) with hU'def
  have hVderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt V (V' x) x := fun x hx =>
    (((hg x hx).ofReal_comp).mul_const I).cexp
  have hUderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt U (U' x) x := by
    intro x hx
    have hden : HasDerivAt (fun t => (g' t : ℂ) * I) ((g'' x : ℂ) * I) x :=
      ((hg' x hx).ofReal_comp).mul_const I
    have hinv : HasDerivAt (fun t => ((g' t : ℂ) * I)⁻¹)
        (-(((g'' x : ℂ) * I) / ((g' x : ℂ) * I) ^ 2)) x := by
      have h2 := (hasDerivAt_inv (hg'ne x hx)).comp x hden
      (convert! h2 using 1; field_simp)
    exact ((hw x hx).ofReal_comp).mul hinv
  have hVnorm : ∀ t, ‖V t‖ = 1 := by intro t; rw [hVdef]; simp [Complex.norm_exp]
  have hUnorm : ∀ x ∈ Set.uIcc a b, ‖U x‖ = w x / g' x := by
    intro x hx
    rw [hUdef, norm_mul, norm_inv, norm_mul]
    simp only [Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (hwnn x hx), abs_of_pos (hg'pos x hx), div_eq_mul_inv]
  have hUV : ∀ x ∈ Set.uIcc a b, U x * V' x = (w x : ℂ) * V x := by
    intro x hx
    have hthis : U x * V' x
        = (w x : ℂ) * (((g' x : ℂ) * I)⁻¹ * ((g' x : ℂ) * I)) * V x := by
      simp only [hUdef, hV'def, hVdef]; ring
    rw [hthis, inv_mul_cancel₀ (hg'ne x hx), mul_one]
  -- continuity / integrability
  have hVcont : ContinuousOn V (Set.uIcc a b) := by
    rw [hVdef]
    exact Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const)
  have hwVcont : ContinuousOn (fun x => (w x : ℂ) * V x) (Set.uIcc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hwc).mul hVcont
  have hV'cont : ContinuousOn V' (Set.uIcc a b) := by
    rw [hV'def]
    exact (Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const)).mul
      ((Complex.continuous_ofReal.comp_continuousOn hg'c).mul continuousOn_const)
  have hcplxInv : ContinuousOn (fun x => ((g' x : ℂ) * I)⁻¹) (Set.uIcc a b) :=
    ContinuousOn.inv₀ ((Complex.continuous_ofReal.comp_continuousOn hg'c).mul continuousOn_const)
      (fun x hx => hg'ne x hx)
  have hU'cont : ContinuousOn U' (Set.uIcc a b) := by
    rw [hU'def]
    refine ((Complex.continuous_ofReal.comp_continuousOn hw'c).mul hcplxInv).add ?_
    refine (Complex.continuous_ofReal.comp_continuousOn hwc).mul (ContinuousOn.neg
      (ContinuousOn.div ((Complex.continuous_ofReal.comp_continuousOn hg''c).mul continuousOn_const)
        (((Complex.continuous_ofReal.comp_continuousOn hg'c).mul continuousOn_const).pow 2)
        (fun x hx => pow_ne_zero _ (hg'ne x hx))))
  have hV'int : IntervalIntegrable V' volume a b := hV'cont.intervalIntegrable
  have hU'int : IntervalIntegrable U' volume a b := hU'cont.intervalIntegrable
  have hwVint : IntervalIntegrable (fun x => (w x : ℂ) * V x) volume a b :=
    hwVcont.intervalIntegrable
  -- IBP
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub hUderiv hVderiv hU'int hV'int
  have hcongr : ∀ x ∈ Set.uIcc a b, U' x * V x + U x * V' x = U' x * V x + (w x : ℂ) * V x :=
    fun x hx => by rw [hUV x hx]
  rw [intervalIntegral.integral_congr hcongr] at hibp
  have hUVint : IntervalIntegrable (fun x => U' x * V x) volume a b :=
    hU'int.mul_continuousOn hVcont
  rw [intervalIntegral.integral_add hUVint hwVint] at hibp
  have hsplit : (∫ x in a..b, (w x : ℂ) * V x)
      = (U b * V b - U a * V a) - ∫ x in a..b, U' x * V x := by linear_combination hibp
  -- boundary bound
  have hbdry : ‖U b * V b - U a * V a‖ ≤ w a / lam + w b / lam := by
    calc ‖U b * V b - U a * V a‖ ≤ ‖U b * V b‖ + ‖U a * V a‖ := norm_sub_le _ _
      _ = w b / g' b + w a / g' a := by
          simp only [norm_mul, hVnorm, mul_one, hUnorm b hbU, hUnorm a haU]
      _ ≤ w a / lam + w b / lam := by
          have h1 : w b / g' b ≤ w b / lam :=
            div_le_div_of_nonneg_left (hwnn b hbU) hlam (hg'lb b hbU)
          have h2 : w a / g' a ≤ w a / lam :=
            div_le_div_of_nonneg_left (hwnn a haU) hlam (hg'lb a haU)
          linarith
  -- pointwise ‖U'‖ bound
  have hU'norm : ∀ x ∈ Set.uIcc a b, ‖U' x‖ ≤ -(w' x) / g' x + w x * g'' x / g' x ^ 2 := by
    intro x hx
    rw [hU'def]
    refine le_trans (norm_add_le _ _) ?_
    have e1 : ‖(w' x : ℂ) * ((g' x : ℂ) * I)⁻¹‖ = -(w' x) / g' x := by
      rw [norm_mul, norm_inv, norm_mul]
      simp only [Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos (hwanti x hx), abs_of_pos (hg'pos x hx), div_eq_mul_inv]
    have e2 : ‖(w x : ℂ) * (-(((g'' x : ℂ) * I) / ((g' x : ℂ) * I) ^ 2))‖
        = w x * g'' x / g' x ^ 2 := by
      rw [norm_mul, norm_neg, norm_div, norm_pow]
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (hwnn x hx), abs_of_nonneg (hg''nn x hx), abs_of_pos (hg'pos x hx),
        mul_div_assoc]
    rw [e1, e2]
  -- interior bound
  have hmajInt : IntervalIntegrable (fun x => -(w' x) / g' x + w x * g'' x / g' x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact (hw'c.neg.div hg'c (fun x hx => (hg'pos x hx).ne')).add
      ((hwc.mul hg''c).div (hg'c.pow 2) (fun x hx => pow_ne_zero _ (hg'pos x hx).ne'))
  have hFTCw : (∫ x in a..b, w' x) = w b - w a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hw x (by rw [Set.uIcc_of_le hab] at hx ⊢; exact hx))
    exact (hw'c).intervalIntegrable
  have hderivInv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t => -(g' t)⁻¹) (g'' x / g' x ^ 2) x := by
    intro x hx
    have hi := ((hg' x hx).inv (hg'pos x hx).ne').neg
    simpa only [neg_div, neg_neg] using! hi
  have hFTCg : (∫ x in a..b, g'' x / g' x ^ 2) = (g' a)⁻¹ - (g' b)⁻¹ := by
    have hint : IntervalIntegrable (fun x => g'' x / g' x ^ 2) volume a b :=
      (hg''c.div (hg'c.pow 2) (fun x hx => pow_ne_zero _ (hg'pos x hx).ne')).intervalIntegrable
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivInv hint
    linarith [h]
  have hintUV : ‖∫ x in a..b, U' x * V x‖ ≤ (w a - w b) / lam + w a / lam := by
    have hstep1 : ‖∫ x in a..b, U' x * V x‖
        ≤ ∫ x in a..b, (-(w' x) / g' x + w x * g'' x / g' x ^ 2) := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
      apply intervalIntegral.integral_mono_on hab (hUVint.norm) hmajInt
      intro x hx
      have hxU : x ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hx
      rw [norm_mul, hVnorm, mul_one]
      exact hU'norm x hxU
    -- split the majorant integral and bound each piece
    have hsplitmaj : (∫ x in a..b, (-(w' x) / g' x + w x * g'' x / g' x ^ 2))
        = (∫ x in a..b, -(w' x) / g' x) + ∫ x in a..b, w x * g'' x / g' x ^ 2 := by
      apply intervalIntegral.integral_add
      · exact (hw'c.neg.div hg'c (fun x hx => (hg'pos x hx).ne')).intervalIntegrable
      · exact ((hwc.mul hg''c).div (hg'c.pow 2)
          (fun x hx => pow_ne_zero _ (hg'pos x hx).ne')).intervalIntegrable
    have hb1 : (∫ x in a..b, -(w' x) / g' x) ≤ (w a - w b) / lam := by
      have hmono : (∫ x in a..b, -(w' x) / g' x) ≤ ∫ x in a..b, -(w' x) / lam := by
        apply intervalIntegral.integral_mono_on hab
          ((hw'c.neg.div hg'c (fun x hx => (hg'pos x hx).ne')).intervalIntegrable)
          ((hw'c.neg.div continuousOn_const (fun _ _ => hlam.ne')).intervalIntegrable)
        intro x hx
        have hxU : x ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hx
        have hnn : 0 ≤ -(w' x) := by linarith [hwanti x hxU]
        apply div_le_div_of_nonneg_left hnn hlam (hg'lb x hxU)
      have hval : (∫ x in a..b, -(w' x) / lam) = (w a - w b) / lam := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_neg, hFTCw]
        ring
      linarith [hmono, hval]
    have hb2 : (∫ x in a..b, w x * g'' x / g' x ^ 2) ≤ w a / lam := by
      have hmono : (∫ x in a..b, w x * g'' x / g' x ^ 2) ≤ ∫ x in a..b, w a * (g'' x / g' x ^ 2) := by
        apply intervalIntegral.integral_mono_on hab
          (((hwc.mul hg''c).div (hg'c.pow 2)
            (fun x hx => pow_ne_zero _ (hg'pos x hx).ne')).intervalIntegrable)
          ((continuousOn_const.mul (hg''c.div (hg'c.pow 2)
            (fun x hx => pow_ne_zero _ (hg'pos x hx).ne'))).intervalIntegrable)
        intro x hx
        have hxU : x ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hx
        have hwle : w x ≤ w a := hwmono x hxU
        have hgnn : 0 ≤ g'' x / g' x ^ 2 := div_nonneg (hg''nn x hxU) (sq_nonneg _)
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hwle hgnn
      have hval : (∫ x in a..b, w a * (g'' x / g' x ^ 2)) = w a * ((g' a)⁻¹ - (g' b)⁻¹) := by
        rw [intervalIntegral.integral_const_mul, hFTCg]
      have hle2 : w a * ((g' a)⁻¹ - (g' b)⁻¹) ≤ w a / lam := by
        have hga : (g' a)⁻¹ ≤ lam⁻¹ := by
          apply inv_anti₀ hlam (hg'lb a haU)
        have hgb : 0 ≤ (g' b)⁻¹ := le_of_lt (inv_pos.mpr (hg'pos b hbU))
        have : (g' a)⁻¹ - (g' b)⁻¹ ≤ lam⁻¹ := by linarith
        calc w a * ((g' a)⁻¹ - (g' b)⁻¹) ≤ w a * lam⁻¹ :=
              mul_le_mul_of_nonneg_left this (hwnn a haU)
          _ = w a / lam := by rw [div_eq_mul_inv]
      linarith [hmono, hval, hle2]
    rw [hsplitmaj] at hstep1
    linarith [hstep1, hb1, hb2]
  -- assemble
  rw [hsplit]
  have hfinal : ‖(U b * V b - U a * V a) - ∫ x in a..b, U' x * V x‖ ≤ 4 * w a / lam := by
    have hwba : w b ≤ w a := hwmono b hbU
    calc ‖(U b * V b - U a * V a) - ∫ x in a..b, U' x * V x‖
        ≤ ‖U b * V b - U a * V a‖ + ‖∫ x in a..b, U' x * V x‖ := norm_sub_le _ _
      _ ≤ (w a / lam + w b / lam) + ((w a - w b) / lam + w a / lam) := add_le_add hbdry hintUV
      _ ≤ 4 * w a / lam := by
          have heq : (w a / lam + w b / lam) + ((w a - w b) / lam + w a / lam)
              = 3 * w a / lam := by ring
          rw [heq, div_eq_mul_inv, div_eq_mul_inv]
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (inv_pos.mpr hlam))
          nlinarith [hwnn a haU]
  exact hfinal

end RHTower
