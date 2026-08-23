import Mathlib

/-!
# The two-sided Laplace transform of a smooth compactly supported weight

For `k : ℝ → ℝ` smooth and supported in `[-R, R]` put

`logSmoothMultiplier k w = ∫_ℝ k(x) e^{wx} dx`.

Integrating by parts `n` times moves every derivative onto `k` and produces a factor `w^{-n}`, so
the transform decreases faster than every power of `|Im w|` on every vertical strip.  This is the
multiplier that a multiplicative smoothing contributes to a Mellin transform: with `t = e^x` the
weight `k` becomes a smooth function compactly supported inside `(0,∞)` and `logSmoothMultiplier k` is its
Mellin transform.

## Main results

* `logSmoothMultiplier`
* `intervalIntegral_expByParts_iterate` — `n`-fold integration by parts
* `exists_bound_pow_norm_logSmoothMultiplier` — `‖w‖^n ‖logSmoothMultiplier k w‖` is bounded on every vertical
  strip
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The two-sided Laplace transform of a weight. -/
def logSmoothMultiplier (k : ℝ → ℝ) (w : ℂ) : ℂ := ∫ x : ℝ, (k x : ℂ) * Complex.exp (w * x)

theorem continuous_expWeight {v : ℝ → ℝ} (hv : Continuous v) (w : ℂ) :
    Continuous fun x : ℝ => ((v x : ℝ) : ℂ) * Complex.exp (w * x) := by
  refine (Complex.continuous_ofReal.comp hv).mul ?_
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-- Iterated derivatives of a smooth function are smooth. -/
theorem contDiff_iteratedDeriv_of_top {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n v) := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hv
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ContDiff.deriv' ih

/-- Every iterated derivative vanishes where the weight vanishes on a neighbourhood. -/
theorem iteratedDeriv_eq_zero_of_eventually {v : ℝ → ℝ} {x : ℝ}
    (h : v =ᶠ[nhds x] fun _ => (0 : ℝ)) (n : ℕ) : iteratedDeriv n v x = 0 := by
  have h' := (h.iteratedDeriv n).eq_of_nhds
  simpa [iteratedDeriv_const] using h'

/-- A weight vanishing off `[-R, R]` vanishes on a neighbourhood of any point beyond `R`. -/
theorem eventuallyEq_zero_of_lt_abs {k : ℝ → ℝ} {R : ℝ}
    (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0) {x : ℝ} (hx : R < |x|) :
    k =ᶠ[nhds x] fun _ => (0 : ℝ) := by
  have hopen : IsOpen {y : ℝ | R < |y|} := isOpen_lt continuous_const continuous_abs
  have hmem : {y : ℝ | R < |y|} ∈ nhds x := hopen.mem_nhds hx
  filter_upwards [hmem] with y hy
  exact hsupp y (le_of_lt hy)

/-- **One integration by parts.**  The derivative moves onto the weight at the cost of `-1/w`. -/
theorem intervalIntegral_expByParts_of_vanishing {v : ℝ → ℝ} {a b : ℝ}
    (hv : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) v) (hva : v a = 0) (hvb : v b = 0)
    {w : ℂ} (hw : w ≠ 0) :
    (∫ x in a..b, ((v x : ℝ) : ℂ) * Complex.exp (w * x))
      = -(1 / w) * ∫ x in a..b, ((deriv v x : ℝ) : ℂ) * Complex.exp (w * x) := by
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => ((v y : ℝ) : ℂ)) (((deriv v x : ℝ) : ℂ)) x := by
    intro x _
    exact HasDerivAt.ofReal_comp ((hv.differentiable (by norm_num) x).hasDerivAt)
  have hV : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => Complex.exp (w * y) / w) (Complex.exp (w * x)) x := by
    intro x _
    have hid : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h1 : HasDerivAt (fun y : ℝ => w * ((y : ℝ) : ℂ)) w x := by
      simpa using hid.const_mul w
    have h2 := (h1.cexp).div_const w
    have h3 : Complex.exp (w * x) * w / w = Complex.exp (w * x) := by
      field_simp
    rwa [h3] at h2
  have hu' : IntervalIntegrable (fun x : ℝ => ((deriv v x : ℝ) : ℂ)) volume a b := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact Complex.continuous_ofReal.comp (hv.continuous_deriv (by norm_num))
  have hV' : IntervalIntegrable (fun x : ℝ => Complex.exp (w * x)) volume a b := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hV hu' hV'
  rw [hva, hvb] at key
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, zero_sub] at key
  rw [key, ← intervalIntegral.integral_neg]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  field_simp

/-- **`n`-fold integration by parts.** -/
theorem intervalIntegral_expByParts_iterate {v : ℝ → ℝ} {a b : ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvan : ∀ i : ℕ, iteratedDeriv i v a = 0 ∧ iteratedDeriv i v b = 0)
    {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    (∫ x in a..b, ((v x : ℝ) : ℂ) * Complex.exp (w * x))
      = (-1) ^ n / w ^ n *
        ∫ x in a..b, ((iteratedDeriv n v x : ℝ) : ℂ) * Complex.exp (w * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsm : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (iteratedDeriv n v) :=
        (contDiff_iteratedDeriv_of_top hv n).of_le (WithTop.coe_le_coe.mpr le_top)
      have hstep := intervalIntegral_expByParts_of_vanishing (v := iteratedDeriv n v) hsm
        (hvan n).1 (hvan n).2 hw
      rw [ih, hstep, ← iteratedDeriv_succ]
      have hwn : (w : ℂ) ^ n ≠ 0 := pow_ne_zero _ hw
      field_simp
      ring

/-- The transform is the integral over any interval containing the support. -/
theorem logSmoothMultiplier_eq_intervalIntegral {k : ℝ → ℝ} {R T : ℝ}
    (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0) (hR : 0 ≤ R) (hRT : R ≤ T) (w : ℂ) :
    logSmoothMultiplier k w = ∫ x in (-T)..T, ((k x : ℝ) : ℂ) * Complex.exp (w * x) := by
  have hT : (-T : ℝ) ≤ T := by linarith
  rw [intervalIntegral.integral_of_le hT, logSmoothMultiplier]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  have habs : T ≤ |x| := by
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with h | h
    · calc T = |(-T)| := by rw [abs_neg, abs_of_nonneg (by linarith)]
        _ ≤ |x| := by
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith : x ≤ 0)]
            linarith
    · calc T ≤ x := le_of_lt h
        _ ≤ |x| := le_abs_self x
  rw [hsupp x (le_trans hRT habs)]
  simp

/-- **The `n`-th power bound.**  `‖w‖^n ‖logSmoothMultiplier k w‖` is bounded on every vertical strip. -/
theorem exists_bound_pow_norm_logSmoothMultiplier {k : ℝ → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) {R : ℝ}
    (hR : 0 < R) (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0) (n : ℕ) (A B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, A ≤ w.re → w.re ≤ B → w ≠ 0 →
      ‖w‖ ^ n * ‖logSmoothMultiplier k w‖ ≤ C := by
  set T : ℝ := R + 1 with hTdef
  have hT0 : 0 < T := by rw [hTdef]; linarith
  have hRT : R ≤ T := by rw [hTdef]; linarith
  have hvan : ∀ i : ℕ, iteratedDeriv i k (-T) = 0 ∧ iteratedDeriv i k T = 0 := by
    intro i
    constructor
    · refine iteratedDeriv_eq_zero_of_eventually (eventuallyEq_zero_of_lt_abs hsupp ?_) i
      rw [abs_of_nonpos (by linarith), hTdef]
      linarith
    · refine iteratedDeriv_eq_zero_of_eventually (eventuallyEq_zero_of_lt_abs hsupp ?_) i
      rw [abs_of_nonneg hT0.le, hTdef]
      linarith
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    (f := fun x : ℝ => ((iteratedDeriv n k x : ℝ) : ℂ))
    ((Complex.continuous_ofReal.comp
      (contDiff_iteratedDeriv_of_top hk n).continuous).continuousOn)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM (-T) (by constructor <;> linarith))
  set D : ℝ := T * max |A| |B| with hDdef
  refine ⟨M * Real.exp D * (2 * T), by positivity, ?_⟩
  intro w hA hB hw
  have hbound : ∀ x ∈ Set.uIoc (-T) T,
      ‖((iteratedDeriv n k x : ℝ) : ℂ) * Complex.exp (w * x)‖ ≤ M * Real.exp D := by
    intro x hx
    have hxmem : x ∈ Set.Icc (-T) T := by
      rw [Set.uIoc_of_le (by linarith : (-T : ℝ) ≤ T)] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have hre : (w * (x : ℂ)).re = w.re * x := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hexp : ‖Complex.exp (w * x)‖ = Real.exp (w.re * x) := by
      rw [Complex.norm_exp, hre]
    have hwabs : |w.re| ≤ max |A| |B| := by
      rcases le_total 0 w.re with h | h
      · rw [abs_of_nonneg h]
        exact le_trans (le_trans hB (le_abs_self B)) (le_max_right _ _)
      · rw [abs_of_nonpos h]
        refine le_trans ?_ (le_max_left _ _)
        rw [← abs_neg]
        exact le_trans (by linarith) (le_abs_self (-A))
    have hxabs : |x| ≤ T := abs_le.2 ⟨hxmem.1, hxmem.2⟩
    have hle : w.re * x ≤ D := by
      calc w.re * x ≤ |w.re * x| := le_abs_self _
        _ = |w.re| * |x| := abs_mul _ _
        _ ≤ (max |A| |B|) * T := by
            refine mul_le_mul hwabs hxabs (abs_nonneg x) ?_
            exact le_trans (abs_nonneg A) (le_max_left _ _)
        _ = D := by rw [hDdef]; ring
    rw [norm_mul, hexp, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |iteratedDeriv n k x| ≤ M := by
      have := hM x hxmem
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    have h2 : Real.exp (w.re * x) ≤ Real.exp D := Real.exp_le_exp.2 hle
    exact mul_le_mul h1 h2 (Real.exp_pos _).le hM0
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [logSmoothMultiplier_eq_intervalIntegral hsupp hR.le hRT w,
    intervalIntegral_expByParts_iterate hk hvan hw n, norm_mul]
  have hwn : ‖w‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hw)
  have hfac : ‖((-1 : ℂ)) ^ n / w ^ n‖ = (‖w‖ ^ n)⁻¹ := by
    rw [norm_div, norm_pow, norm_pow, norm_neg, norm_one, one_pow]
    simp
  rw [hfac]
  have habs2 : |T - -T| = 2 * T := by
    rw [show T - -T = 2 * T by ring, abs_of_nonneg (by linarith)]
  rw [habs2] at hnorm
  calc ‖w‖ ^ n * ((‖w‖ ^ n)⁻¹
        * ‖∫ x in (-T)..T, ((iteratedDeriv n k x : ℝ) : ℂ) * Complex.exp (w * x)‖)
      = ‖∫ x in (-T)..T, ((iteratedDeriv n k x : ℝ) : ℂ) * Complex.exp (w * x)‖ := by
        field_simp
    _ ≤ M * Real.exp D * (2 * T) := hnorm

/-- **Rapid vertical decrease of the multiplier**, on every vertical strip. -/
theorem exists_bound_norm_logSmoothMultiplier_strip {k : ℝ → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) {R : ℝ}
    (hR : 0 < R) (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0) (n : ℕ) (A B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, A ≤ w.re → w.re ≤ B → 1 ≤ |w.im| →
      ‖logSmoothMultiplier k w‖ ≤ C * (1 + |w.im|) ^ (-(n : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_pow_norm_logSmoothMultiplier hk hR hsupp n A B
  refine ⟨C * 2 ^ n, by positivity, ?_⟩
  intro w hA hB him
  have hw : w ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
    linarith
  have hnw : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have hpos : (0 : ℝ) < 1 + |w.im| := by linarith [abs_nonneg w.im]
  have hhalf : (1 + |w.im|) / 2 ≤ ‖w‖ := by
    have : (1 + |w.im|) / 2 ≤ |w.im| := by linarith
    linarith
  have hval := hC w hA hB hw
  have hpow : ((1 + |w.im|) / 2) ^ n ≤ ‖w‖ ^ n := by gcongr
  have hkey : ((1 + |w.im|) / 2) ^ n * ‖logSmoothMultiplier k w‖ ≤ C := by
    refine le_trans (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hval
  have hrpow : (1 + |w.im|) ^ (-(n : ℝ)) = ((1 + |w.im|) ^ n)⁻¹ := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
  have hden : (0 : ℝ) < (1 + |w.im|) ^ n := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ h2] at hkey
  rw [hrpow, ← div_eq_mul_inv, le_div_iff₀ hden, mul_comm]
  exact hkey

end GaloisForLFunctions.HTGeometry

end
