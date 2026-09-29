import GaloisForLFunctions.HTGeometry.BesselArgumentDerivative
import GaloisForLFunctions.RHTower.SelbergMaassSliceRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct

/-!
# Uniqueness of the Whittaker solution of the Maass modal equation

The Schläfli function `K_ν(s) = ∫_0^∞ e^{-s cosh t} cosh(νt) dt` satisfies Bessel's equation
`s²K'' + sK' - (s² + ν²)K = 0`, derived from the corpus argument derivative
`K' = -(K_{ν+1} + K_{ν-1})/2` and the order recurrence.  Hence `W(y) = √y K_ν(ky)` solves
`W'' = (k² + (ν² - 1/4)/y²) W`; it is bounded for `y ≥ 1/k` and, by the Mellin formula for
`K_ν²`, not identically zero.

For a real potential `q ≥ q₀ > 0` near infinity, `E = u²` of a real solution of `u'' = qu` is convex;
if `∫^∞ u²/y² < ∞` then `E' ≤ 0`, and `∫ E'' < ∞` makes `u` and `u'` square integrable.  The Wronskian
of two such small solutions is then an integrable constant, hence zero.  Consequently every small
solution of `a'' = (k² - λ/y²) a` is a multiple of `√y K_ν(ky)` with `ν² = 1/4 - λ`.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower.MaassWhittaker

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- `K_ν(s)` as a function of the argument. -/
abbrev besK (ν : ℂ) (s : ℝ) : ℂ := modifiedBesselKOrder s ν

/-- Its argument derivative `K_ν'(s) = -(K_{ν+1}(s) + K_{ν-1}(s))/2`. -/
def besKd (ν : ℂ) (s : ℝ) : ℂ := -(1 / 2 : ℂ) * (besK (ν + 1) s + besK (ν - 1) s)

/-- Its second argument derivative. -/
def besKdd (ν : ℂ) (s : ℝ) : ℂ := -(1 / 2 : ℂ) * (besKd (ν + 1) s + besKd (ν - 1) s)

theorem hasDerivAt_besK (ν : ℂ) {s : ℝ} (hs : 0 < s) : HasDerivAt (besK ν) (besKd ν s) s :=
  _root_.RHTower.d4BM_hasDerivAt_modifiedBesselKOrder_argument hs ν

theorem hasDerivAt_besKd (ν : ℂ) {s : ℝ} (hs : 0 < s) : HasDerivAt (besKd ν) (besKdd ν s) s := by
  unfold besKd besKdd
  exact ((hasDerivAt_besK (ν + 1) hs).add (hasDerivAt_besK (ν - 1) hs)).const_mul _

/-- **Bessel's equation** `s²K'' + sK' - (s² + ν²)K = 0`, from the order recurrence. -/
theorem bessel_ode (ν : ℂ) {s : ℝ} (hs : 0 < s) :
    (s : ℂ) ^ 2 * besKdd ν s + s * besKd ν s - ((s : ℂ) ^ 2 + ν ^ 2) * besK ν s = 0 := by
  have hr0 := modifiedBesselKOrder_add_one hs ν
  have hr1 := modifiedBesselKOrder_add_one hs (ν + 1)
  have hr2 := modifiedBesselKOrder_add_one hs (ν - 1)
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  simp only [besKdd, besKd, besK]
  rw [show ν + 1 + 1 = ν + 2 by ring, show ν + 1 - 1 = ν by ring, show ν - 1 + 1 = ν by ring,
    show ν - 1 - 1 = ν - 2 by ring]
  rw [show ν + 1 + 1 = ν + 2 by ring, show ν + 1 - 1 = ν by ring] at hr1
  rw [show ν - 1 + 1 = ν by ring, show ν - 1 - 1 = ν - 2 by ring] at hr2
  linear_combination (norm := skip) ((s : ℂ) ^ 2 / 4) * hr1 - ((s : ℂ) ^ 2 / 4) * hr2 +
    (ν * s / 2) * hr0
  field_simp
  ring

/-! ## The Whittaker function -/

/-- The Whittaker function `W(y) = √y K_ν(k y)`. -/
def whittakerW (k : ℝ) (ν : ℂ) (y : ℝ) : ℂ := (Real.sqrt y : ℂ) * besK ν (k * y)

/-- Its derivative. -/
def whittakerWd (k : ℝ) (ν : ℂ) (y : ℝ) : ℂ :=
  ((2 * Real.sqrt y)⁻¹ : ℝ) * besK ν (k * y) + (Real.sqrt y : ℂ) * (k * besKd ν (k * y))

variable {k : ℝ} {ν : ℂ} {y : ℝ}

theorem hasDerivAt_sqrt_ofReal (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => (Real.sqrt y : ℂ)) (((2 * Real.sqrt y)⁻¹ : ℝ) : ℂ) y := by
  have h := (Real.hasDerivAt_sqrt hy.ne').ofReal_comp
  simpa [one_div] using h

theorem hasDerivAt_besK_comp (hk : 0 < k) (ν : ℂ) (hy : 0 < y) :
    HasDerivAt (fun y => besK ν (k * y)) ((k : ℂ) * besKd ν (k * y)) y := by
  have h := (hasDerivAt_besK ν (mul_pos hk hy)).scomp y ((hasDerivAt_id y).const_mul k)
  simpa [Function.comp_def, Complex.real_smul] using h

theorem hasDerivAt_besKd_comp (hk : 0 < k) (ν : ℂ) (hy : 0 < y) :
    HasDerivAt (fun y => besKd ν (k * y)) ((k : ℂ) * besKdd ν (k * y)) y := by
  have h := (hasDerivAt_besKd ν (mul_pos hk hy)).scomp y ((hasDerivAt_id y).const_mul k)
  simpa [Function.comp_def, Complex.real_smul] using h

theorem hasDerivAt_whittakerW (hk : 0 < k) (hy : 0 < y) :
    HasDerivAt (whittakerW k ν) (whittakerWd k ν y) y := by
  have h := (hasDerivAt_sqrt_ofReal hy).mul (hasDerivAt_besK_comp hk ν hy)
  unfold whittakerW whittakerWd
  exact h

/-- **The Whittaker equation** `W'' = (k² + (ν² - 1/4)/y²) W`. -/
theorem hasDerivAt_whittakerWd (hk : 0 < k) (hy : 0 < y) :
    HasDerivAt (whittakerWd k ν)
      (((k : ℂ) ^ 2 + (ν ^ 2 - 1 / 4) / (y : ℂ) ^ 2) * whittakerW k ν y) y := by
  have hr : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hinv := (((Real.hasDerivAt_sqrt hy.ne').const_mul 2).inv (by positivity)).ofReal_comp
  have h := (hinv.mul (hasDerivAt_besK_comp hk ν hy)).add
    ((hasDerivAt_sqrt_ofReal hy).mul ((hasDerivAt_besKd_comp hk ν hy).const_mul (k : ℂ)))
  unfold whittakerWd
  refine h.congr_deriv ?_
  have hode := bessel_ode ν (mul_pos hk hy)
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hrC : (Real.sqrt y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk.ne'
  have hyC : (y : ℂ) = (Real.sqrt y : ℂ) ^ 2 := by rw [← Complex.ofReal_pow, hsq]
  unfold whittakerW
  simp only [Pi.inv_apply]
  push_cast at hode ⊢
  rw [hyC] at hode ⊢
  field_simp
  linear_combination 16 * hode

/-! ## Decay and nonvanishing -/

theorem norm_cosh_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  have hz : Complex.cosh z = ((Real.cosh z.re * Real.cos z.im : ℝ) : ℂ) +
      ((Real.sinh z.re * Real.sin z.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have h1 : ‖Complex.cosh z‖ ^ 2 =
      (Real.cosh z.re * Real.cos z.im) ^ 2 + (Real.sinh z.re * Real.sin z.im) ^ 2 := by
    rw [hz, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hc := Real.cosh_sq z.re
  have hs := Real.sin_sq_add_cos_sq z.im
  have hpos := Real.cosh_pos z.re
  refine le_of_sq_le_sq ?_ hpos.le
  rw [h1]
  nlinarith [sq_nonneg (Real.sinh z.re), sq_nonneg (Real.sin z.im), sq_nonneg (Real.cos z.im),
    mul_nonneg (sq_nonneg (Real.sinh z.re)) (sq_nonneg (Real.sin z.im)),
    mul_nonneg (sq_nonneg (Real.cosh z.re)) (sq_nonneg (Real.cos z.im))]

/-- `‖K_ν(x)‖ ≤ e^{1-x} K_{|Re ν|}(1)` for `x ≥ 1`. -/
theorem norm_besK_le {ν : ℂ} {x : ℝ} (hx : 1 ≤ x) :
    ‖besK ν x‖ ≤ Real.exp (1 - x) * realModifiedBesselKOrder 1 |ν.re| := by
  have hx0 : 0 < x := by linarith
  unfold besK modifiedBesselKOrder
  rw [realModifiedBesselKOrder, ← integral_const_mul]
  refine (norm_integral_le_of_norm_le ((integrableOn_realBesselOrderKernel one_pos |ν.re|).const_mul
    _) (Eventually.of_forall fun t => ?_))
  unfold besselOrderKernel realBesselOrderKernel
  rw [norm_mul, Complex.norm_exp]
  have hre : (-(x : ℂ) * Complex.cosh (t : ℂ)).re = -x * Real.cosh t := by
    rw [← Complex.ofReal_cosh]; simp
  rw [hre]
  have hcosh : ‖Complex.cosh (ν * (t : ℂ))‖ ≤ Real.cosh (|ν.re| * t) := by
    refine (norm_cosh_le _).trans ?_
    rw [show (ν * (t : ℂ)).re = ν.re * t by simp, Real.cosh_le_cosh]
    rw [abs_mul, abs_mul, abs_abs]
  have hc1 : 1 ≤ Real.cosh t := Real.one_le_cosh t
  have hexp : Real.exp (-x * Real.cosh t) ≤ Real.exp (1 - x) * Real.exp (-1 * Real.cosh t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc Real.exp (-x * Real.cosh t) * ‖Complex.cosh (ν * (t : ℂ))‖
      ≤ (Real.exp (1 - x) * Real.exp (-1 * Real.cosh t)) * Real.cosh (|ν.re| * t) :=
        mul_le_mul hexp hcosh (norm_nonneg _) (by positivity)
    _ = Real.exp (1 - x) * (Real.exp (-1 * Real.cosh t) * Real.cosh (|ν.re| * t)) := by ring

/-- `W` is bounded on `[1, ∞)`. -/
theorem norm_whittakerW_le (hk : 0 < k) {y : ℝ} (hy : 1 / k ≤ y) :
    ‖whittakerW k ν y‖ ^ 2 ≤ Real.exp 2 * realModifiedBesselKOrder 1 |ν.re| ^ 2 / (2 * k) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hky : 1 ≤ k * y := by rwa [div_le_iff₀ hk, mul_comm] at hy
  have hK := norm_besK_le (ν := ν) hky
  have hA := (realModifiedBesselKOrder_pos one_pos |ν.re|).le
  unfold whittakerW
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hy0.le]
  have h2 : ‖besK ν (k * y)‖ ^ 2 ≤ (Real.exp (1 - k * y) * realModifiedBesselKOrder 1 |ν.re|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hK 2
  have h3 : y * Real.exp (1 - k * y) ^ 2 ≤ Real.exp 2 / (2 * k) := by
    have hsq : Real.exp (1 - k * y) ^ 2 = Real.exp 2 * (Real.exp (2 * k * y))⁻¹ := by
      rw [sq, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_add]
      ring_nf
    have he : 2 * k * y ≤ Real.exp (2 * k * y) := by linarith [Real.add_one_le_exp (2 * k * y)]
    have hepos := Real.exp_pos (2 * k * y)
    rw [hsq, le_div_iff₀ (by positivity)]
    calc y * (Real.exp 2 * (Real.exp (2 * k * y))⁻¹) * (2 * k)
        = Real.exp 2 * ((2 * k * y) / Real.exp (2 * k * y)) := by field_simp
      _ ≤ Real.exp 2 * 1 := by
          gcongr
          rw [div_le_one hepos]; exact he
      _ = Real.exp 2 := mul_one _
  calc y * ‖besK ν (k * y)‖ ^ 2
      ≤ y * (Real.exp (1 - k * y) * realModifiedBesselKOrder 1 |ν.re|) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 hy0.le
    _ = (y * Real.exp (1 - k * y) ^ 2) * realModifiedBesselKOrder 1 |ν.re| ^ 2 := by ring
    _ ≤ Real.exp 2 / (2 * k) * realModifiedBesselKOrder 1 |ν.re| ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    _ = _ := by ring

/-- **`K_ν` does not vanish identically on `(0, ∞)`**, by its Mellin square formula. -/
theorem exists_besK_ne_zero (ν : ℂ) : ∃ x : ℝ, 0 < x ∧ besK ν x ≠ 0 := by
  by_contra h
  push Not at h
  set s : ℂ := ((2 * |ν.re| + 1 : ℝ) : ℂ) with hsdef
  have hsre : s.re = 2 * |ν.re| + 1 := by simp [hsdef]
  have hchamber : |ν.re| + |ν.re| < s.re := by rw [hsre]; linarith
  have hM := integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder hchamber
  have hzero : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * modifiedBesselKOrder x ν *
      modifiedBesselKOrder x ν) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => by
      have := h x hx
      simp only [besK] at this
      simp [this]
  rw [hzero] at hM
  have hre1 : 0 < ((s + ν + ν) / 2).re := by
    simp only [Complex.div_re, Complex.add_re, hsre]; norm_num
    have := neg_abs_le ν.re; nlinarith [abs_nonneg ν.re]
  have hre2 : 0 < ((s + ν - ν) / 2).re := by
    simp only [Complex.div_re, Complex.add_re, Complex.sub_re, hsre]; norm_num
    positivity
  have hre3 : 0 < ((s - ν + ν) / 2).re := by
    simp only [Complex.div_re, Complex.add_re, Complex.sub_re, hsre]; norm_num
    positivity
  have hre4 : 0 < ((s - ν - ν) / 2).re := by
    simp only [Complex.div_re, Complex.sub_re, hsre]; norm_num
    have := le_abs_self ν.re; nlinarith [abs_nonneg ν.re]
  have hs0 : 0 < s.re := by rw [hsre]; positivity
  have h2 : (2 : ℂ) ^ (s - 3) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; norm_num
  refine (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (div_ne_zero h2 (Complex.Gamma_ne_zero_of_re_pos hs0))
    (Complex.Gamma_ne_zero_of_re_pos hre1)) (Complex.Gamma_ne_zero_of_re_pos hre2))
    (Complex.Gamma_ne_zero_of_re_pos hre3)) (Complex.Gamma_ne_zero_of_re_pos hre4)) ?_
  rw [hM]
  ring

theorem exists_whittakerW_ne_zero (hk : 0 < k) (ν : ℂ) : ∃ y : ℝ, 0 < y ∧ whittakerW k ν y ≠ 0 := by
  obtain ⟨x, hx, hK⟩ := exists_besK_ne_zero ν
  refine ⟨x / k, div_pos hx hk, ?_⟩
  unfold whittakerW
  rw [mul_div_cancel₀ x hk.ne']
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (div_pos hx hk)).ne') hK

/-! ## Small solutions of `u'' = q u` -/

section Small

variable {q : ℝ → ℝ} {Y₀ q₀ : ℝ}

/-- **Small real solutions have square-integrable value and derivative.**  For `u'' = qu` with
`q ≥ q₀ > 0` beyond `Y₀`, `E = u²` is convex there; `E' > 0` somewhere would force linear growth and
contradict `∫ u²/y² < ∞`.  Hence `E' ≤ 0`, and `∫ E'' = E'(b) - E'(Y₀) ≤ -E'(Y₀)` bounds
`∫ (2u'² + 2qu²)`. -/
theorem small_solution_integrable {u u' : ℝ → ℝ} (hY₀ : 0 < Y₀) (hq₀ : 0 < q₀)
    (hu : ∀ y, 0 < y → HasDerivAt u (u' y) y) (hu' : ∀ y, 0 < y → HasDerivAt u' (q y * u y) y)
    (hqc : ContinuousOn q (Ioi 0)) (hq : ∀ y, Y₀ ≤ y → q₀ ≤ q y)
    (hsmall : IntegrableOn (fun y => u y ^ 2 / y ^ 2) (Ioi Y₀)) :
    IntegrableOn (fun y => u' y ^ 2) (Ioi Y₀) ∧ IntegrableOn (fun y => u y ^ 2) (Ioi Y₀) := by
  let E : ℝ → ℝ := fun y => u y * u y
  let E1 : ℝ → ℝ := fun y => u' y * u y + u y * u' y
  let E2 : ℝ → ℝ := fun y => q y * u y * u y + u' y * u' y + (u' y * u' y + u y * (q y * u y))
  have hE : ∀ y, 0 < y → HasDerivAt E (E1 y) y := fun y hy => (hu y hy).mul (hu y hy)
  have hE1 : ∀ y, 0 < y → HasDerivAt E1 (E2 y) y := fun y hy =>
    ((hu' y hy).mul (hu y hy)).add ((hu y hy).mul (hu' y hy))
  have hE2eq : ∀ y, E2 y = 2 * u' y ^ 2 + 2 * q y * u y ^ 2 := fun y => by
    simp only [E2]; ring
  have hE2 : ∀ y, Y₀ ≤ y → 0 ≤ E2 y := fun y hy => by
    have := hq y hy
    rw [hE2eq]
    have : 0 ≤ q y := hq₀.le.trans this
    positivity
  have hcontE2 : ContinuousOn E2 (Ioi 0) := by
    have hu1 : ContinuousOn u (Ioi 0) := HasDerivAt.continuousOn fun y hy => hu y hy
    have hu2 : ContinuousOn u' (Ioi 0) := HasDerivAt.continuousOn fun y hy => hu' y hy
    exact ((hqc.mul hu1).mul hu1).add (hu2.mul hu2) |>.add ((hu2.mul hu2).add (hu1.mul (hqc.mul hu1)))
  have hmono : MonotoneOn E1 (Ici Y₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici Y₀)
      (HasDerivAt.continuousOn fun y hy => hE1 y (lt_of_lt_of_le hY₀ hy))
      (fun y hy => ?_) fun y hy => ?_
    · rw [interior_Ici] at hy
      exact (hE1 y (hY₀.trans hy)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici] at hy
      rw [(hE1 y (hY₀.trans hy)).deriv]
      exact hE2 y hy.le
  have hneg : ∀ y, Y₀ ≤ y → E1 y ≤ 0 := by
    intro y₁ hy₁
    by_contra hpos
    push Not at hpos
    have hy₁0 : 0 < y₁ := lt_of_lt_of_le hY₀ hy₁
    have hgrow : ∀ y, y₁ ≤ y → E1 y₁ * (y - y₁) ≤ E y - E y₁ := by
      intro y hy
      refine (convex_Ici y₁).mul_sub_le_image_sub_of_le_deriv
        (HasDerivAt.continuousOn fun t ht => hE t (lt_of_lt_of_le hy₁0 ht))
        (fun t ht => ?_) (fun t ht => ?_) y₁ self_mem_Ici y hy hy
      · rw [interior_Ici] at ht
        exact (hE t (hy₁0.trans ht)).differentiableAt.differentiableWithinAt
      · rw [interior_Ici] at ht
        rw [(hE t (hy₁0.trans ht)).deriv]
        exact hmono (mem_Ici.2 hy₁) (mem_Ici.2 (hy₁.trans ht.le)) ht.le
    have hsub : Ioi (2 * y₁) ⊆ Ioi Y₀ := fun y hy => by
      simp only [mem_Ioi] at hy ⊢; linarith
    have hint : IntegrableOn (fun y : ℝ => y⁻¹) (Ioi (2 * y₁)) := by
      have h2 := (hsmall.mono_set hsub).const_mul (2 / E1 y₁)
      refine h2.mono' ?_ ?_
      · exact (continuousOn_inv₀.mono fun y hy => by
          simp only [mem_Ioi] at hy; exact ne_of_gt (by linarith)).aestronglyMeasurable
          measurableSet_Ioi
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
        simp only [mem_Ioi] at hy
        have hy0 : 0 < y := by linarith
        have hg := hgrow y (by linarith)
        have hEy : 0 ≤ E y₁ := mul_self_nonneg _
        rw [Real.norm_of_nonneg (inv_nonneg.2 hy0.le)]
        have hEy' : E y = u y ^ 2 := by simp only [E]; ring
        have key : E1 y₁ * y ≤ 2 * u y ^ 2 := by nlinarith
        calc y⁻¹ = (2 / E1 y₁) * ((E1 y₁ * y / 2) / y ^ 2) := by field_simp
          _ ≤ (2 / E1 y₁) * (u y ^ 2 / y ^ 2) := by gcongr; linarith
    exact not_integrableOn_Ioi_inv hint
  have hint2 : IntegrableOn E2 (Ioi Y₀) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (l := atTop) (b := id)
      (-E1 Y₀) Y₀ (fun i => ?_) tendsto_id ?_
    · exact ((hcontE2.mono fun y hy => lt_of_lt_of_le hY₀ hy.1).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    · filter_upwards [eventually_ge_atTop Y₀] with i hi
      simp only [id]
      have hcongr : (∫ x in Y₀..i, ‖E2 x‖) = ∫ x in Y₀..i, E2 x := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [uIcc_of_le hi] at hx
        exact Real.norm_of_nonneg (hE2 x hx.1)
      rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hE1 x (by
          rw [uIcc_of_le hi] at hx; exact lt_of_lt_of_le hY₀ hx.1))
        ((hcontE2.mono fun y hy => by
          rw [uIcc_of_le hi] at hy; exact lt_of_lt_of_le hY₀ hy.1).intervalIntegrable)]
      linarith [hneg i hi]
  have hu1 : ContinuousOn u (Ioi 0) := HasDerivAt.continuousOn fun y hy => hu y hy
  have hu2 : ContinuousOn u' (Ioi 0) := HasDerivAt.continuousOn fun y hy => hu' y hy
  have hsubI : Ioi Y₀ ⊆ Ioi 0 := fun y hy => hY₀.trans hy
  refine ⟨(hint2.div_const 2).mono' ((hu2.pow 2).mono hsubI |>.aestronglyMeasurable
      measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun y hy => ?_)),
    (hint2.div_const (2 * q₀)).mono' ((hu1.pow 2).mono hsubI |>.aestronglyMeasurable
      measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun y hy => ?_))⟩
  · rw [Real.norm_of_nonneg (sq_nonneg _), hE2eq, le_div_iff₀ two_pos]
    have := hq y (le_of_lt hy)
    have : 0 ≤ q y * u y ^ 2 := mul_nonneg (hq₀.le.trans this) (sq_nonneg _)
    nlinarith
  · rw [Real.norm_of_nonneg (sq_nonneg _), hE2eq, le_div_iff₀ (by positivity)]
    have := hq y (le_of_lt hy)
    have : q₀ * u y ^ 2 ≤ q y * u y ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
    nlinarith [sq_nonneg (u' y)]

end Small

/-! ## Complex small solutions and the Wronskian -/

section Wronskian

variable {q : ℝ → ℝ} {Y₀ q₀ : ℝ}

theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x := by
  have := (Complex.reCLM.hasFDerivAt (x := f x)).comp_hasDerivAt x h
  exact this

theorem hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).im) f'.im x := by
  have := (Complex.imCLM.hasFDerivAt (x := f x)).comp_hasDerivAt x h
  exact this

theorem small_solution_integrable_complex {a a' : ℝ → ℂ} (hY₀ : 0 < Y₀) (hq₀ : 0 < q₀)
    (ha : ∀ y, 0 < y → HasDerivAt a (a' y) y)
    (ha' : ∀ y, 0 < y → HasDerivAt a' ((q y : ℂ) * a y) y)
    (hqc : ContinuousOn q (Ioi 0)) (hq : ∀ y, Y₀ ≤ y → q₀ ≤ q y)
    (hsmall : IntegrableOn (fun y => ‖a y‖ ^ 2 / y ^ 2) (Ioi Y₀)) :
    IntegrableOn (fun y => ‖a' y‖ ^ 2) (Ioi Y₀) ∧ IntegrableOn (fun y => ‖a y‖ ^ 2) (Ioi Y₀) := by
  have hna : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hcont : ContinuousOn a (Ioi 0) := HasDerivAt.continuousOn fun y hy => ha y hy
  have hmeas : ∀ g : ℂ → ℝ, Continuous g →
      AEStronglyMeasurable (fun y => g (a y) ^ 2 / y ^ 2) (volume.restrict (Ioi Y₀)) := fun g hg =>
    (((hg.comp_continuousOn hcont).pow 2).div (continuousOn_id.pow 2) fun y hy =>
      pow_ne_zero 2 (ne_of_gt hy)).mono (fun y hy => hY₀.trans hy) |>.aestronglyMeasurable
      measurableSet_Ioi
  have hsre : IntegrableOn (fun y => (a y).re ^ 2 / y ^ 2) (Ioi Y₀) :=
    hsmall.mono' (hmeas _ Complex.continuous_re) (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (by positivity), hna]
      gcongr; nlinarith [sq_nonneg (a y).im])
  have hsim : IntegrableOn (fun y => (a y).im ^ 2 / y ^ 2) (Ioi Y₀) :=
    hsmall.mono' (hmeas _ Complex.continuous_im) (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (by positivity), hna]
      gcongr; nlinarith [sq_nonneg (a y).re])
  obtain ⟨h1, h2⟩ := small_solution_integrable (u := fun y => (a y).re) (u' := fun y => (a' y).re)
    hY₀ hq₀ (fun y hy => hasDerivAt_re (ha y hy)) (fun y hy => by
      have := hasDerivAt_re (ha' y hy); simpa using this) hqc hq hsre
  obtain ⟨h3, h4⟩ := small_solution_integrable (u := fun y => (a y).im) (u' := fun y => (a' y).im)
    hY₀ hq₀ (fun y hy => hasDerivAt_im (ha y hy)) (fun y hy => by
      have := hasDerivAt_im (ha' y hy); simpa using this) hqc hq hsim
  refine ⟨(h1.add h3).congr (Eventually.of_forall fun y => ?_),
    (h2.add h4).congr (Eventually.of_forall fun y => ?_)⟩ <;> simp [hna]

/-- **The Wronskian of two small solutions vanishes.** -/
theorem wronskian_eq_zero {a a' b b' : ℝ → ℂ} (hY₀ : 0 < Y₀) (hq₀ : 0 < q₀)
    (ha : ∀ y, 0 < y → HasDerivAt a (a' y) y)
    (ha' : ∀ y, 0 < y → HasDerivAt a' ((q y : ℂ) * a y) y)
    (hb : ∀ y, 0 < y → HasDerivAt b (b' y) y)
    (hb' : ∀ y, 0 < y → HasDerivAt b' ((q y : ℂ) * b y) y)
    (hqc : ContinuousOn q (Ioi 0)) (hq : ∀ y, Y₀ ≤ y → q₀ ≤ q y)
    (hsa : IntegrableOn (fun y => ‖a y‖ ^ 2 / y ^ 2) (Ioi Y₀))
    (hsb : IntegrableOn (fun y => ‖b y‖ ^ 2 / y ^ 2) (Ioi Y₀)) {y : ℝ} (hy : 0 < y) :
    a y * b' y - a' y * b y = 0 := by
  let Wr : ℝ → ℂ := fun y => a y * b' y - a' y * b y
  have hWr : ∀ t, 0 < t → HasDerivAt Wr 0 t := fun t ht =>
    (((ha t ht).mul (hb' t ht)).sub ((ha' t ht).mul (hb t ht))).congr_deriv (by ring)
  have hconst : ∀ s t : ℝ, 0 < s → 0 < t → Wr s = Wr t := fun s t hs ht =>
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi 0).isPreconnected
      (fun x hx => (hWr x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hWr x hx).deriv) hs ht
  obtain ⟨ia', ia⟩ := small_solution_integrable_complex hY₀ hq₀ ha ha' hqc hq hsa
  obtain ⟨ib', ib⟩ := small_solution_integrable_complex hY₀ hq₀ hb hb' hqc hq hsb
  have hcW : ContinuousOn Wr (Ioi 0) := HasDerivAt.continuousOn fun t ht => hWr t ht
  have hint : IntegrableOn Wr (Ioi Y₀) := by
    refine ((((ia.add ib').add (ia'.add ib)).div_const 2)).mono'
      ((hcW.mono fun t ht => hY₀.trans ht).aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun t => ?_)
    simp only [Wr]
    calc ‖a t * b' t - a' t * b t‖ ≤ ‖a t‖ * ‖b' t‖ + ‖a' t‖ * ‖b t‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_sub_le _ _
      _ ≤ (‖a t‖ ^ 2 + ‖b' t‖ ^ 2 + (‖a' t‖ ^ 2 + ‖b t‖ ^ 2)) / 2 := by
          nlinarith [sq_nonneg (‖a t‖ - ‖b' t‖), sq_nonneg (‖a' t‖ - ‖b t‖)]
  have hint' : IntegrableOn (fun _ : ℝ => Wr y) (Ioi Y₀) :=
    hint.congr ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
      hconst t y (hY₀.trans ht) hy))
  rw [integrableOn_const_iff, Real.volume_Ioi] at hint'
  simpa using hint'

/-- Two solutions with vanishing Wronskian are proportional where the second is nonzero. -/
theorem eq_const_mul_of_wronskian {a a' b b' : ℝ → ℂ}
    (ha : ∀ y, 0 < y → HasDerivAt a (a' y) y)
    (ha' : ∀ y, 0 < y → HasDerivAt a' ((q y : ℂ) * a y) y)
    (hb : ∀ y, 0 < y → HasDerivAt b (b' y) y)
    (hb' : ∀ y, 0 < y → HasDerivAt b' ((q y : ℂ) * b y) y)
    (hqc : ContinuousOn q (Ioi 0)) {y₀ : ℝ} (hy₀ : 0 < y₀) (hb0 : b y₀ ≠ 0)
    (hW : a y₀ * b' y₀ - a' y₀ * b y₀ = 0) {y : ℝ} (hy : 0 < y) :
    a y = a y₀ / b y₀ * b y := by
  have hqcC : ContinuousOn (fun t => (q t : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn hqc
  have h := SelbergMaassSliceRigidity.second_order_cauchy_zero
    (u := fun t => a t - a y₀ / b y₀ * b t) (v := fun t => a' t - a y₀ / b y₀ * b' t)
    (c := fun t => (q t : ℂ)) hqcC (fun t ht => (ha t ht).sub ((hb t ht).const_mul _))
    (fun t ht => ((ha' t ht).sub ((hb' t ht).const_mul _)).congr_deriv (by ring)) hy₀
    (by field_simp; ring) (by
      rw [sub_eq_zero, div_mul_eq_mul_div, eq_div_iff hb0]
      linear_combination -hW) hy
  linear_combination h.1

end Wronskian

/-! ## Uniqueness of the Whittaker solution -/

/-- **Whittaker uniqueness.**  A solution of `a'' = (k² - λ/y²) a` on `(0, ∞)` with
`∫^∞ |a|²/y² < ∞` is a multiple of `W(y) = √y K_ν(ky)`, `ν² = 1/4 - λ`. -/
theorem eq_smul_whittakerW {k : ℝ} (hk : 0 < k) {lam : ℝ} {ν : ℂ} (hν : ν ^ 2 = 1 / 4 - lam)
    {a a' : ℝ → ℂ} (ha : ∀ y, 0 < y → HasDerivAt a (a' y) y)
    (ha' : ∀ y, 0 < y → HasDerivAt a' (((k ^ 2 - lam / y ^ 2 : ℝ) : ℂ) * a y) y)
    {Y₁ : ℝ} (hY₁ : 0 < Y₁) (hsmall : IntegrableOn (fun y => ‖a y‖ ^ 2 / y ^ 2) (Ioi Y₁)) :
    ∃ c : ℂ, ∀ y, 0 < y → a y = c * whittakerW k ν y := by
  set q : ℝ → ℝ := fun y => k ^ 2 - lam / y ^ 2 with hqdef
  have hqc : ContinuousOn q (Ioi 0) :=
    continuousOn_const.sub (continuousOn_const.div (continuousOn_id.pow 2) fun y hy =>
      pow_ne_zero 2 (ne_of_gt hy))
  set Y₀ : ℝ := max Y₁ ((Real.sqrt (2 * |lam|) + 1) / k) with hY₀def
  have hY₀ : 0 < Y₀ := lt_max_of_lt_left hY₁
  have hY₀k : (Real.sqrt (2 * |lam|) + 1) / k ≤ Y₀ := le_max_right _ _
  have hq : ∀ y, Y₀ ≤ y → k ^ 2 / 2 ≤ q y := by
    intro y hy
    have hy0 : 0 < y := hY₀.trans_le hy
    have hky : Real.sqrt (2 * |lam|) + 1 ≤ k * y := by
      rw [div_le_iff₀ hk] at hY₀k; nlinarith
    have hs := Real.sq_sqrt (show 0 ≤ 2 * |lam| by positivity)
    have hs0 := Real.sqrt_nonneg (2 * |lam|)
    have h2 : 2 * |lam| ≤ (k * y) ^ 2 := by nlinarith
    have h3 : lam / y ^ 2 ≤ k ^ 2 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [le_abs_self lam]
    simp only [hqdef]
    linarith
  have hW : ∀ y, 0 < y → HasDerivAt (whittakerW k ν) (whittakerWd k ν y) y := fun y hy =>
    hasDerivAt_whittakerW hk hy
  have hW' : ∀ y, 0 < y → HasDerivAt (whittakerWd k ν) ((q y : ℂ) * whittakerW k ν y) y :=
    fun y hy => (hasDerivAt_whittakerWd hk hy).congr_deriv (by
      simp only [hqdef]; push_cast; rw [hν]; ring)
  have hWsmall : IntegrableOn (fun y => ‖whittakerW k ν y‖ ^ 2 / y ^ 2) (Ioi Y₀) := by
    have hY₀k' : 1 / k ≤ Y₀ := le_trans (by
      rw [div_le_div_iff_of_pos_right hk]; linarith [Real.sqrt_nonneg (2 * |lam|)]) hY₀k
    have hC := (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hY₀).const_mul
      (Real.exp 2 * realModifiedBesselKOrder 1 |ν.re| ^ 2 / (2 * k))
    refine hC.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_))
    · have hcW : ContinuousOn (whittakerW k ν) (Ioi 0) := HasDerivAt.continuousOn hW
      exact (((hcW.norm.pow 2).div (continuousOn_id.pow 2) fun y hy =>
        pow_ne_zero 2 (ne_of_gt hy)).mono fun y hy => hY₀.trans hy).aestronglyMeasurable
        measurableSet_Ioi
    · have hy0 : 0 < y := hY₀.trans hy
      rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hy0.le, Real.rpow_two,
        div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (norm_whittakerW_le hk (hY₀k'.trans hy.le))
        (inv_nonneg.2 (by positivity))
  have hasmall : IntegrableOn (fun y => ‖a y‖ ^ 2 / y ^ 2) (Ioi Y₀) :=
    hsmall.mono_set (Ioi_subset_Ioi (le_max_left _ _))
  have hk2 : 0 < k ^ 2 / 2 := by positivity
  obtain ⟨y₀, hy₀, hne⟩ := exists_whittakerW_ne_zero hk ν
  have hWr := wronskian_eq_zero hY₀ hk2 ha ha' hW hW' hqc hq hasmall hWsmall hy₀
  exact ⟨a y₀ / whittakerW k ν y₀, fun y hy =>
    eq_const_mul_of_wronskian ha ha' hW hW' hqc hy₀ hne hWr hy⟩

end

end GaloisForLFunctions.RHTower.MaassWhittaker
