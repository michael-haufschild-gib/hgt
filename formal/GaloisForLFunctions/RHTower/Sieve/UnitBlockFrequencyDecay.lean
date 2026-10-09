import GaloisForLFunctions.RHTower.Sieve.UnitBlockFrequencyBounds

/-!
# Quadratic decay of the Fourier coefficients of the smoothed unit block

Two integrations by parts against `e^{2πikx}` give

`‖ubFreq N N' t k‖ ≤ K(1 + t)²/k²`  for `k ≠ 0`, `1 ≤ N < N' ≤ 2N`, `t ≥ 0`,

with an absolute constant `K` (`exists_norm_ubFreq_le_decay`).  The boundary terms vanish because
the smoothed summand `f_t(x) = φ(x) x^{-1} e^{-it log x}` and its derivative vanish at `N` and at
`N' + 1`, and `|f_t''| ≤ K(1 + t)²/N` on `[N, N' + 1]`: each derivative of `e^{-it log x}`
costs a factor `t/x`, and each derivative of `φ` a bounded factor.

This decay makes the Fourier coefficients summable (Poisson summation applies) and bounds the
tail `∑_{|k| > V} ‖ubFreq k‖ ≤ 2K(1 + t)²/V`.
-/

open Complex Set MeasureTheory intervalIntegral
open GaloisForLFunctions.HTGeometry
open scoped Real

namespace RHTower.Sieve

noncomputable section

/-- **Two integrations by parts.**  If `F` and `F'` vanish at both ends of `[a, b]`, then
`‖∫_a^b F(x) e^{icx} dx‖ ≤ (∫_a^b ‖F''‖)/c²`. -/
theorem norm_integral_mul_exp_linear_le {F F' F'' : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b)
    (hc : c ≠ 0) (hF : ∀ x ∈ uIcc a b, HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ uIcc a b, HasDerivAt F' (F'' x) x) (hF'c : ContinuousOn F' (uIcc a b))
    (hF''c : ContinuousOn F'' (uIcc a b)) (ha : F a = 0) (hb : F b = 0) (ha' : F' a = 0)
    (hb' : F' b = 0) :
    ‖∫ x in a..b, F x * Complex.exp (((c * x : ℝ) : ℂ) * I)‖ ≤ (∫ x in a..b, ‖F'' x‖) / c ^ 2 := by
  have hcI : ((c : ℂ) * I) ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hc) Complex.I_ne_zero
  set v : ℝ → ℂ := fun x => Complex.exp (((c * x : ℝ) : ℂ) * I) / ((c : ℂ) * I) with hv
  have hvd : ∀ x ∈ uIcc a b, HasDerivAt v (Complex.exp (((c * x : ℝ) : ℂ) * I)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => ((c * y : ℝ) : ℂ) * I) ((c : ℂ) * I) x := by
      have := ((hasDerivAt_id' x).const_mul c).ofReal_comp.mul_const I
      simpa using this
    refine (h1.cexp.div_const ((c : ℂ) * I)).congr_deriv ?_
    rw [mul_div_assoc, div_self hcI, mul_one]
  have hEc : Continuous fun x : ℝ => Complex.exp (((c * x : ℝ) : ℂ) * I) := by fun_prop
  have hvc : Continuous v := hEc.div_const _
  have ibp1 := integral_mul_deriv_eq_deriv_mul hF hvd (hF'c.intervalIntegrable)
    (hEc.intervalIntegrable a b)
  have ibp2 := integral_mul_deriv_eq_deriv_mul hF' hvd (hF''c.intervalIntegrable)
    (hEc.intervalIntegrable a b)
  rw [ha, hb, zero_mul, zero_mul, sub_zero, zero_sub] at ibp1
  rw [ha', hb', zero_mul, zero_mul, sub_zero, zero_sub] at ibp2
  have hpull : ∀ G : ℝ → ℂ, ∫ x in a..b, G x * v x =
      (∫ x in a..b, G x * Complex.exp (((c * x : ℝ) : ℂ) * I)) / ((c : ℂ) * I) := by
    intro G
    rw [← intervalIntegral.integral_div]
    refine integral_congr fun x _ => ?_
    simp only [hv]; ring
  rw [hpull] at ibp1 ibp2
  rw [ibp1, ibp2, norm_neg, norm_div, norm_neg, norm_div, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  have hc2 : |c| * |c| = c ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
  rw [div_div, hc2]
  refine div_le_div_of_nonneg_right (le_trans
    (intervalIntegral.norm_integral_le_integral_norm hab) (le_of_eq ?_)) (sq_nonneg c)
  refine integral_congr fun x _ => ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

variable {N N' : ℕ}

/-- The first derivative of the amplitude `φ(x)/x`. -/
def ubAmpD (N N' : ℕ) (x : ℝ) : ℝ :=
  smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x / x - ubWindow N N' x / x ^ 2

/-- The second derivative of the amplitude `φ(x)/x`. -/
def ubAmpDD (N N' : ℕ) (x : ℝ) : ℝ :=
  smoothPlateauDeriv2 ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x / x -
    2 * smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x / x ^ 2 +
    2 * ubWindow N N' x / x ^ 3

theorem hasDerivAt_ubAmp {x : ℝ} (hx : x ≠ 0) : HasDerivAt (ubAmp N N') (ubAmpD N N' x) x :=
  hasDerivAt_div_self (hasDerivAt_ubWindow x) hx

theorem hasDerivAt_ubAmpD {x : ℝ} (hx : x ≠ 0) : HasDerivAt (ubAmpD N N') (ubAmpDD N N' x) x := by
  have h1 := hasDerivAt_div_self (hasDerivAt_smoothPlateauDeriv (a := (N : ℝ) + 1 / 4)
    (b := (N' : ℝ) + 3 / 4) (ℓ := 1 / 2) x) hx
  have h2 := (hasDerivAt_ubWindow (N := N) (N' := N') x).div (hasDerivAt_pow 2 x)
    (pow_ne_zero 2 hx)
  refine (h1.sub h2).congr_deriv ?_
  simp only [ubAmpDD]
  field_simp
  ring

/-- The phase factor `e^{-it log x}`. -/
def ubPhaseFactor (t x : ℝ) : ℂ := Complex.exp (((-(t * Real.log x)) : ℝ) * I)

theorem hasDerivAt_ubPhaseFactor (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (ubPhaseFactor t) (ubPhaseFactor t x * (((-(t / x)) : ℝ) * I)) x := by
  have h : HasDerivAt (fun y => -(t * Real.log y)) (-(t / x)) x := by
    refine ((Real.hasDerivAt_log hx).const_mul t).neg.congr_deriv ?_
    rw [div_eq_mul_inv]
  exact (h.ofReal_comp.mul_const I).cexp

theorem norm_ubPhaseFactor (t x : ℝ) : ‖ubPhaseFactor t x‖ = 1 := by
  rw [ubPhaseFactor, Complex.norm_exp_ofReal_mul_I]

/-- The derivative of the smoothed summand, without its phase factor. -/
def ubKernelD1 (N N' : ℕ) (t x : ℝ) : ℂ :=
  (ubAmpD N N' x : ℂ) + (ubAmp N N' x : ℂ) * (((-(t / x)) : ℝ) * I)

/-- The second derivative of the smoothed summand, without its phase factor. -/
def ubKernelD2 (N N' : ℕ) (t x : ℝ) : ℂ :=
  (ubAmpDD N N' x : ℂ) + (ubAmpD N N' x : ℂ) * (((-(t / x)) : ℝ) * I) +
    (ubAmp N N' x : ℂ) * (((t / x ^ 2) : ℝ) * I) +
    ubKernelD1 N N' t x * (((-(t / x)) : ℝ) * I)

theorem ubKernel_eq_mul (t x : ℝ) : ubKernel N N' t x = (ubAmp N N' x : ℂ) * ubPhaseFactor t x :=
  rfl

theorem hasDerivAt_ubKernel (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (ubKernel N N' t) (ubKernelD1 N N' t x * ubPhaseFactor t x) x := by
  have h := (hasDerivAt_ubAmp (N := N) (N' := N') hx).ofReal_comp.mul
    (hasDerivAt_ubPhaseFactor t hx)
  refine h.congr_deriv ?_
  simp only [ubKernelD1]; ring

theorem hasDerivAt_ubKernelD1 (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (ubKernelD1 N N' t) ((ubAmpDD N N' x : ℂ) +
      (ubAmpD N N' x : ℂ) * (((-(t / x)) : ℝ) * I) + (ubAmp N N' x : ℂ) * (((t / x ^ 2) : ℝ) * I))
      x := by
  have hr : HasDerivAt (fun y : ℝ => -(t / y)) (t / x ^ 2) x := by
    refine (((hasDerivAt_id' x).inv hx).const_mul t).neg.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
    · field_simp
    · exact Filter.Eventually.of_forall fun y => by simp [div_eq_mul_inv]
  have h := (hasDerivAt_ubAmpD (N := N) (N' := N') hx).ofReal_comp.add
    ((hasDerivAt_ubAmp (N := N) (N' := N') hx).ofReal_comp.mul (hr.ofReal_comp.mul_const I))
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_ubKernelD1_mul (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => ubKernelD1 N N' t y * ubPhaseFactor t y)
      (ubKernelD2 N N' t x * ubPhaseFactor t x) x := by
  refine ((hasDerivAt_ubKernelD1 t hx).mul (hasDerivAt_ubPhaseFactor t hx)).congr_deriv ?_
  simp only [ubKernelD2]; ring

/-- `‖(a : ℂ) * ((b : ℝ) * I)‖ = |a| |b|`. -/
private theorem norm_ofReal_mul_ofReal_I (a b : ℝ) :
    ‖(a : ℂ) * ((b : ℂ) * I)‖ = |a| * |b| := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

/-- **Pointwise bound for the second derivative.**  On `[N, N' + 1]`,
`‖f_t''‖ ≤ K(1 + t)²/N`. -/
theorem exists_norm_ubKernelD2_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (N N' : ℕ) (t x : ℝ), 1 ≤ N → 0 ≤ t → (N : ℝ) ≤ x →
      ‖ubKernelD2 N N' t x‖ ≤ K * (1 + t) ^ 2 / N := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_smoothPlateauDeriv_le
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_abs_smoothPlateauDeriv2_le
  refine ⟨4 * K₂ + 4 * K₁ + 4, by positivity, fun N N' t x hN ht hx => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 ≤ x := hN1.trans hx
  have hx0 : 0 < x := by linarith
  -- the window and its derivatives
  set p := ubWindow N N' x
  set q := smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x
  set s := smoothPlateauDeriv2 ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x
  have hp : |p| ≤ 1 := abs_ubWindow_le x
  have hq : |q| ≤ 2 * K₁ := by
    have := hK₁ ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x (by norm_num)
    rwa [div_div_eq_mul_div, div_one, mul_comm] at this
  have hs : |s| ≤ 4 * K₂ := by
    have := hK₂ ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x (by norm_num)
    rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num, div_div_eq_mul_div, div_one,
      mul_comm] at this
    exact this
  -- inverse powers of `x`
  have i1 : 1 / x ≤ 1 / N := one_div_le_one_div_of_le (by linarith) hx
  have i1' : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx1
  have i2 : 1 / x ^ 2 ≤ 1 / N := by
    refine le_trans (one_div_le_one_div_of_le (by positivity) ?_) i1
    nlinarith
  have i3 : 1 / x ^ 3 ≤ 1 / N := by
    refine le_trans (one_div_le_one_div_of_le (by positivity) ?_) i1
    nlinarith [sq_nonneg x]
  have hN0 : (0 : ℝ) < N := by linarith
  -- the amplitude and its derivatives
  have hA : |ubAmp N N' x| ≤ 1 / N := by
    rw [ubAmp, abs_div, abs_of_pos hx0]
    exact le_trans (div_le_div_of_nonneg_right hp hx0.le) i1
  have hA1 : |ubAmpD N N' x| ≤ (2 * K₁ + 1) / N := by
    rw [ubAmpD]
    refine le_trans (abs_sub _ _) ?_
    rw [abs_div, abs_div, abs_of_pos hx0, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2)]
    have e1 : |q| / x ≤ 2 * K₁ / N := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div (2 * K₁)]
      exact mul_le_mul hq i1 (by positivity) (by positivity)
    have e2 : |p| / x ^ 2 ≤ 1 / N := by
      rw [div_eq_mul_one_div]
      calc |p| * (1 / x ^ 2) ≤ 1 * (1 / N) := mul_le_mul hp i2 (by positivity) zero_le_one
        _ = 1 / N := one_mul _
    rw [add_div]; linarith
  have hA2 : |ubAmpDD N N' x| ≤ (4 * K₂ + 4 * K₁ + 2) / N := by
    rw [ubAmpDD]
    refine le_trans (abs_add_le _ _) ?_
    refine le_trans (add_le_add (abs_sub _ _) le_rfl) ?_
    rw [abs_div, abs_div, abs_div, abs_of_pos hx0, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2),
      abs_of_pos (by positivity : (0 : ℝ) < x ^ 3), abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have e1 : |s| / x ≤ 4 * K₂ / N := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div (4 * K₂)]
      exact mul_le_mul hs i1 (by positivity) (by positivity)
    have e2 : 2 * |q| / x ^ 2 ≤ 4 * K₁ / N := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div (4 * K₁)]
      exact mul_le_mul (by linarith) i2 (by positivity) (by positivity)
    have e3 : 2 * |p| / x ^ 3 ≤ 2 / N := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div 2]
      exact mul_le_mul (by linarith) i3 (by positivity) (by positivity)
    rw [add_div, add_div]; linarith
  -- the phase factors
  have ht1 : |(-(t / x))| ≤ t := by
    rw [abs_neg, abs_div, abs_of_nonneg ht, abs_of_pos hx0, div_le_iff₀ hx0]; nlinarith
  have ht2 : |t / x ^ 2| ≤ t := by
    rw [abs_div, abs_of_nonneg ht, abs_of_pos (by positivity : (0 : ℝ) < x ^ 2),
      div_le_iff₀ (by positivity)]
    have : 1 ≤ x ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this ht]
  have hD1 : ‖ubKernelD1 N N' t x‖ ≤ (2 * K₁ + 1) / N + t / N := by
    rw [ubKernelD1]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs]; exact hA1
    · rw [norm_ofReal_mul_ofReal_I]
      calc |ubAmp N N' x| * |(-(t / x))| ≤ (1 / N) * t :=
            mul_le_mul hA ht1 (abs_nonneg _) (by positivity)
        _ = t / N := by ring
  rw [ubKernelD2]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (le_trans (norm_add_le _ _)
    (add_le_add (norm_add_le _ _) le_rfl)) le_rfl) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_ofReal_mul_ofReal_I, norm_ofReal_mul_ofReal_I,
    norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have f1 : |ubAmpD N N' x| * |(-(t / x))| ≤ (2 * K₁ + 1) / N * t :=
    mul_le_mul hA1 ht1 (abs_nonneg _) (by positivity)
  have f2 : |ubAmp N N' x| * |t / x ^ 2| ≤ 1 / N * t :=
    mul_le_mul hA ht2 (abs_nonneg _) (by positivity)
  have f3 : ‖ubKernelD1 N N' t x‖ * |(-(t / x))| ≤ ((2 * K₁ + 1) / N + t / N) * t :=
    mul_le_mul hD1 ht1 (abs_nonneg _) (by positivity)
  have hfin : (4 * K₂ + 4 * K₁ + 2) / N + (2 * K₁ + 1) / N * t + 1 / N * t +
      ((2 * K₁ + 1) / N + t / N) * t ≤ (4 * K₂ + 4 * K₁ + 4) * (1 + t) ^ 2 / N := by
    have e : (4 * K₂ + 4 * K₁ + 2) / N + (2 * K₁ + 1) / N * t + 1 / N * t +
        ((2 * K₁ + 1) / N + t / N) * t =
        (4 * K₂ + 4 * K₁ + 2 + (4 * K₁ + 3) * t + t ^ 2) / N := by
      field_simp; ring
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hN0.le
    nlinarith [mul_nonneg hK₂0 ht, mul_nonneg hK₁0 ht, mul_nonneg (mul_nonneg hK₂0 ht) ht,
      mul_nonneg (mul_nonneg hK₁0 ht) ht, mul_nonneg ht ht]
  linarith

theorem continuousOn_ubKernelD2 (t : ℝ) :
    ContinuousOn (fun x => ubKernelD2 N N' t x * ubPhaseFactor t x) (Ioi 0) := by
  have hx : ∀ x ∈ Ioi (0 : ℝ), x ≠ 0 := fun x hx => (mem_Ioi.1 hx).ne'
  have hw := (continuous_ubWindow (N := N) (N' := N')).continuousOn (s := Ioi 0)
  have hd1 := (continuous_smoothPlateauDeriv (a := (N : ℝ) + 1 / 4) (b := (N' : ℝ) + 3 / 4)
    (ℓ := 1 / 2)).continuousOn (s := Ioi 0)
  have hd2 := (continuous_smoothPlateauDeriv2 (a := (N : ℝ) + 1 / 4) (b := (N' : ℝ) + 3 / 4)
    (ℓ := 1 / 2)).continuousOn (s := Ioi 0)
  have hid : ContinuousOn (fun x : ℝ => x) (Ioi 0) := continuousOn_id
  have hA : ContinuousOn (ubAmp N N') (Ioi 0) := hw.div hid hx
  have hA1 : ContinuousOn (ubAmpD N N') (Ioi 0) :=
    (hd1.div hid hx).sub (hw.div (hid.pow 2) fun x h => pow_ne_zero 2 (hx x h))
  have hA2 : ContinuousOn (ubAmpDD N N') (Ioi 0) :=
    ((hd2.div hid hx).sub ((continuousOn_const.mul hd1).div (hid.pow 2)
      fun x h => pow_ne_zero 2 (hx x h))).add ((continuousOn_const.mul hw).div (hid.pow 3)
      fun x h => pow_ne_zero 3 (hx x h))
  have hr1 : ContinuousOn (fun x : ℝ => (((-(t / x)) : ℝ) : ℂ) * I) (Ioi 0) :=
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.div hid hx).neg).mul
      continuousOn_const
  have hr2 : ContinuousOn (fun x : ℝ => (((t / x ^ 2) : ℝ) : ℂ) * I) (Ioi 0) :=
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.div (hid.pow 2)
      fun x h => pow_ne_zero 2 (hx x h))).mul continuousOn_const
  have cA := Complex.continuous_ofReal.comp_continuousOn hA
  have cA1 := Complex.continuous_ofReal.comp_continuousOn hA1
  have cA2 := Complex.continuous_ofReal.comp_continuousOn hA2
  have hD1 : ContinuousOn (ubKernelD1 N N' t) (Ioi 0) := cA1.add (cA.mul hr1)
  have hE : ContinuousOn (ubPhaseFactor t) (Ioi 0) := fun x h =>
    (hasDerivAt_ubPhaseFactor t (hx x h)).continuousAt.continuousWithinAt
  exact (((cA2.add (cA1.mul hr1)).add (cA.mul hr2)).add (hD1.mul hr1)).mul hE

/-- **Quadratic decay.**  `‖ubFreq N N' t k‖ ≤ K(1 + t)²/k²` for `k ≠ 0`. -/
theorem exists_norm_ubFreq_le_decay :
    ∃ K : ℝ, 0 < K ∧ ∀ (N N' : ℕ) (t : ℝ) (k : ℤ), 1 ≤ N → N < N' → N' ≤ 2 * N → 0 ≤ t →
      k ≠ 0 → ‖ubFreq N N' t k‖ ≤ K * (1 + t) ^ 2 / (k : ℝ) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_ubKernelD2_le
  refine ⟨K, hK0, fun N N' t k hN hNN' hN' ht hk => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNN'r : (N : ℝ) + 1 ≤ N' := by exact_mod_cast hNN'
  have hN'2 : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'
  have hab : (N : ℝ) ≤ (N' : ℝ) + 1 := by linarith
  have huI : uIcc (N : ℝ) ((N' : ℝ) + 1) = Icc (N : ℝ) ((N' : ℝ) + 1) := uIcc_of_le hab
  have hpos : ∀ x ∈ uIcc (N : ℝ) ((N' : ℝ) + 1), x ≠ 0 := fun x hx => by
    rw [huI] at hx; linarith [hx.1]
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hc : 2 * π * (k : ℝ) ≠ 0 := by positivity
  have hfreq : ubFreq N N' t k = ∫ x in (N : ℝ)..((N' : ℝ) + 1),
      ubKernel N N' t x * Complex.exp ((((2 * π * k) * x : ℝ) : ℂ) * I) := by
    refine integral_congr fun x _ => ?_
    rw [ubKernel, ubPhase, mul_assoc (ubAmp N N' x : ℂ), ← Complex.exp_add]
    congr 2; push_cast; ring
  have hD1zero : ∀ x : ℝ, ubWindow N N' x = 0 →
      smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) x = 0 →
      ubKernelD1 N N' t x = 0 := by
    intro x h1 h2
    simp only [ubKernelD1, ubAmpD, ubAmp]
    rw [h1, h2]
    simp
  have hlo1 : ubWindow N N' (N : ℝ) = 0 := ubWindow_eq_zero_of_le (by linarith)
  have hlo2 : smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2) (N : ℝ) = 0 :=
    smoothPlateauDeriv_eq_zero_of_lt (by norm_num) (by linarith)
  have hhi1 : ubWindow N N' ((N' : ℝ) + 1) = 0 := ubWindow_eq_zero_of_ge (by linarith)
  have hhi2 : smoothPlateauDeriv ((N : ℝ) + 1 / 4) ((N' : ℝ) + 3 / 4) (1 / 2)
      ((N' : ℝ) + 1) = 0 := smoothPlateauDeriv_eq_zero_of_gt (by norm_num) (by linarith)
  have hsub : uIcc (N : ℝ) ((N' : ℝ) + 1) ⊆ Ioi 0 := fun x hx => by
    rw [huI] at hx; exact mem_Ioi.2 (by linarith [hx.1])
  have h := norm_integral_mul_exp_linear_le (F := ubKernel N N' t)
    (F' := fun x => ubKernelD1 N N' t x * ubPhaseFactor t x)
    (F'' := fun x => ubKernelD2 N N' t x * ubPhaseFactor t x) hab hc
    (fun x hx => hasDerivAt_ubKernel t (hpos x hx))
    (fun x hx => hasDerivAt_ubKernelD1_mul t (hpos x hx))
    (fun x hx => (hasDerivAt_ubKernelD1_mul t (hpos x hx)).continuousAt.continuousWithinAt)
    ((continuousOn_ubKernelD2 t).mono hsub)
    (by rw [ubKernel, ubAmp, hlo1]; simp) (by rw [ubKernel, ubAmp, hhi1]; simp)
    (by rw [hD1zero _ hlo1 hlo2, zero_mul])
    (by rw [hD1zero _ hhi1 hhi2, zero_mul])
  rw [hfreq]
  refine le_trans h ?_
  have hint : ∫ x in (N : ℝ)..((N' : ℝ) + 1), ‖ubKernelD2 N N' t x * ubPhaseFactor t x‖ ≤
      ((N' : ℝ) + 1 - N) * (K * (1 + t) ^ 2 / N) := by
    have hc2 : ContinuousOn (fun x => ‖ubKernelD2 N N' t x * ubPhaseFactor t x‖)
        (Icc (N : ℝ) ((N' : ℝ) + 1)) := ((continuousOn_ubKernelD2 t).mono (huI ▸ hsub)).norm
    refine le_trans (integral_mono_on (g := fun _ => K * (1 + t) ^ 2 / N) hab
      (hc2.intervalIntegrable_of_Icc hab) intervalIntegrable_const fun x hx => ?_) (le_of_eq ?_)
    · rw [norm_mul, norm_ubPhaseFactor, mul_one]
      exact hK N N' t x hN ht hx.1
    · rw [intervalIntegral.integral_const, smul_eq_mul]
  have hlen : ((N' : ℝ) + 1 - N) * (K * (1 + t) ^ 2 / N) ≤ 2 * K * (1 + t) ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ hN0]
    have : 0 ≤ K * (1 + t) ^ 2 := by positivity
    nlinarith
  have hk2 : 0 < (2 * π * (k : ℝ)) ^ 2 := by positivity
  calc (∫ x in (N : ℝ)..((N' : ℝ) + 1), ‖ubKernelD2 N N' t x * ubPhaseFactor t x‖) /
        (2 * π * k) ^ 2 ≤ 2 * K * (1 + t) ^ 2 / (2 * π * k) ^ 2 :=
        div_le_div_of_nonneg_right (hint.trans hlen) hk2.le
    _ ≤ K * (1 + t) ^ 2 / (k : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ hk2 (by positivity)]
        have hπ : 3 < π := Real.pi_gt_three
        have hc0 : 0 ≤ K * (1 + t) ^ 2 * (k : ℝ) ^ 2 := by positivity
        have e1 : K * (1 + t) ^ 2 * (2 * π * k) ^ 2 = (K * (1 + t) ^ 2 * (k : ℝ) ^ 2) * (4 * π ^ 2) := by
          ring
        have e2 : 2 * K * (1 + t) ^ 2 * (k : ℝ) ^ 2 = (K * (1 + t) ^ 2 * (k : ℝ) ^ 2) * 2 := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left (by nlinarith) hc0

end

end RHTower.Sieve
