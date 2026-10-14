import GaloisForLFunctions.RHTower.LiClockCenterAverageLaplaceDeficit

/-!
# The kink of the center-averaged Li clock at clock zero

The center-averaged Li clock `A(t) = Σ_q ∫ P₁(x) Re(1 − cos(t/(a_q − x))) dx` is even in `t`. On
`t ≥ 0` each averaged atom is given by an explicit entire formula (`centerClockAtomExt`):

* on the line (`Im a = 0`): `Re(1 − exp(i t/(a − i)))`, a single exponential;
* off the line: `Re(1 − cos(t/(a ∓ i)))`, an even function of `t`.

So `A(t) = Ẽ(|t|)` with `Ẽ(t) = Σ_q centerClockAtomExt t (a_q)` (`liClockCenterAverage_eq_ext_abs`).

**Kink law** (`liClockCenterAverageExt_sub_neg`). The odd part of `Ẽ` is carried by the critical
zeros alone:

`Ẽ(t) − Ẽ(−t) = Σ_{Im a_q = 0} Re(exp(−i t/(a_q − i)) − exp(i t/(a_q − i)))`.

Off-line zeros contribute even functions of `t`, so they are invisible in the kink of `A` at
`t = 0`, whatever their depth. For a critical zero `ρ = ½ + iγ` the term is `2 Re sinh(t/(ρ + ½))`.
-/

noncomputable section

open Complex

namespace RHTower

/-- The entire formula for the averaged atom: one exponential on the line, a cosine off it. -/
def centerClockAtomExt (t : ℝ) (a : ℂ) : ℝ :=
  if a.im = 0 then (1 - Complex.exp (I * t / (a - I))).re
  else if a.im < 0 then (1 - Complex.cos ((t : ℂ) / (a - I))).re
  else (1 - Complex.cos ((t : ℂ) / (a + I))).re

/-- The critical odd term: `Re(exp(−z) − exp(z))`, `z = i t/(a − i)`, on the line, and `0` off it. -/
def centerClockCriticalOddTerm (t : ℝ) (a : ℂ) : ℝ :=
  if a.im = 0 then (Complex.exp (-(I * t / (a - I))) - Complex.exp (I * t / (a - I))).re else 0

/-- On nonnegative clocks the averaged atom is given by the entire formula. -/
theorem centerClockAverage_eq_atomExt {t : ℝ} (ht : 0 ≤ t) (a : ℂ) :
    centerClockAverage t a = centerClockAtomExt t a := by
  unfold centerClockAtomExt
  split_ifs with h0 hneg
  · exact centerClockAverage_eq_of_im_eq_zero h0 ht
  · exact centerClockAverage_eq_of_im_neg hneg t
  · exact centerClockAverage_eq_of_im_pos (lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm h0)) t

/-- The averaged atom is even in the clock. -/
theorem centerClockAverage_neg (t : ℝ) (a : ℂ) : centerClockAverage (-t) a = centerClockAverage t a := by
  unfold centerClockAverage centerClockAtom
  congr 1
  funext x
  rw [show (((-t : ℝ)) : ℂ) / (a - x) = -((t : ℂ) / (a - x)) by push_cast; ring, Complex.cos_neg]

/-- **Atomwise kink law.** The odd part of the entire atom is the critical odd term. -/
theorem atomExt_sub_atomExt_neg (t : ℝ) (a : ℂ) :
    centerClockAtomExt t a - centerClockAtomExt (-t) a = centerClockCriticalOddTerm t a := by
  unfold centerClockAtomExt centerClockCriticalOddTerm
  have hz : I * (((-t : ℝ)) : ℂ) / (a - I) = -(I * t / (a - I)) := by push_cast; ring
  have hm : ∀ c : ℂ, (((-t : ℝ)) : ℂ) / c = -((t : ℂ) / c) := fun c => by push_cast; ring
  split_ifs with h0 hneg
  · rw [hz, Complex.sub_re, Complex.sub_re, Complex.sub_re]
    ring
  · rw [hm, Complex.cos_neg]; ring
  · rw [hm, Complex.cos_neg]; ring

/-! ### Size of the entire atoms -/

private theorem norm_inv_le_of_norm_le {a c : ℂ} (h : ‖a‖ ≤ ‖c‖) (ha : a ≠ 0) :
    ‖c⁻¹‖ ≤ ‖a‖⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (norm_pos_iff.mpr ha) h

private theorem norm_le_norm_sub_I {a : ℂ} (ha : a.im ≤ 1 / 2) : ‖a‖ ≤ ‖a - I‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im]
  nlinarith

private theorem norm_le_norm_add_I {a : ℂ} (ha : -(1 / 2) ≤ a.im) : ‖a‖ ≤ ‖a + I‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.I_re, add_zero, Complex.add_im, Complex.I_im]
  nlinarith

/-- A cosine atom with `‖c‖ ≤ ‖a‖⁻¹ ≤ 1` is at most `t² e^{|t|}/‖a‖²`. -/
private theorem abs_re_one_sub_cos_le {a c : ℂ} (ha : 1 ≤ ‖a‖) (hc : ‖c‖ ≤ ‖a‖⁻¹) (t : ℝ) :
    |(1 - Complex.cos ((t : ℂ) * c)).re| ≤ Real.exp |t| * (|t| + t ^ 2) / ‖a‖ ^ (2 : ℕ) := by
  have hpos : 0 < ‖a‖ := by linarith
  have hc1 : ‖c‖ ≤ 1 := hc.trans (inv_le_one_of_one_le₀ ha)
  have hb := liClock_norm_one_sub_cos_le_imaginary_exp t c
  have him : |c.im| ≤ 1 := (Complex.abs_im_le_norm c).trans hc1
  have hexp : Real.exp (|t| * |c.im|) ≤ Real.exp |t| := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg t, abs_nonneg c.im]
  have hc2 : ‖c‖ ^ 2 ≤ (‖a‖ ^ (2 : ℕ))⁻¹ := by
    rw [← inv_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hc 2
  have he : 0 ≤ Real.exp |t| := (Real.exp_pos _).le
  calc |(1 - Complex.cos ((t : ℂ) * c)).re| ≤ ‖1 - Complex.cos ((t : ℂ) * c)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ t ^ 2 / 2 * ‖c‖ ^ 2 * Real.exp (|t| * |c.im|) := hb
    _ ≤ t ^ 2 / 2 * (‖a‖ ^ (2 : ℕ))⁻¹ * Real.exp |t| := by gcongr
    _ ≤ Real.exp |t| * (|t| + t ^ 2) / ‖a‖ ^ (2 : ℕ) := by
        rw [div_eq_mul_inv (Real.exp |t| * (|t| + t ^ 2))]
        have hinv : 0 ≤ (‖a‖ ^ (2 : ℕ))⁻¹ := by positivity
        have : t ^ 2 / 2 ≤ |t| + t ^ 2 := by nlinarith [abs_nonneg t]
        calc t ^ 2 / 2 * (‖a‖ ^ (2 : ℕ))⁻¹ * Real.exp |t|
            = (t ^ 2 / 2) * (Real.exp |t| * (‖a‖ ^ (2 : ℕ))⁻¹) := by ring
          _ ≤ (|t| + t ^ 2) * (Real.exp |t| * (‖a‖ ^ (2 : ℕ))⁻¹) := by gcongr
          _ = Real.exp |t| * (|t| + t ^ 2) * (‖a‖ ^ (2 : ℕ))⁻¹ := by ring

/-- For real `α`, `i t/(α − i) = −t/(α² + 1) + i tα/(α² + 1)`. -/
private theorem I_mul_div_real_sub_I (t α : ℝ) :
    I * t / ((α : ℂ) - I) = ((-t / (α ^ 2 + 1) : ℝ) : ℂ) + ((t * α / (α ^ 2 + 1) : ℝ) : ℂ) * I := by
  have hne : (α : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hd : ((α ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (α ^ 2 + 1 : ℝ) ≠ 0)
  have hd' : (α ^ 2 + 1 : ℝ) ≠ 0 := by positivity
  rw [div_eq_iff hne]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    field_simp
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
    field_simp
    ring

/-- `|1 − eˣ| ≤ |x| e^{|x|}`. -/
private theorem abs_one_sub_exp_le (x : ℝ) : |1 - Real.exp x| ≤ |x| * Real.exp |x| := by
  rcases le_total 0 x with hx | hx
  · have h := Real.add_one_le_exp (-x)
    have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos x
    rw [abs_of_nonneg hx, abs_of_nonpos (by linarith [Real.one_le_exp hx])]
    nlinarith
  · have h := Real.add_one_le_exp x
    rw [abs_of_nonpos hx, abs_of_nonneg (by linarith [Real.exp_le_one_iff.mpr hx])]
    have : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    nlinarith

/-- An on-line exponential atom is at most `e^{|t|}(|t| + t²)/‖a‖²`. -/
private theorem abs_re_one_sub_exp_le {a : ℂ} (ha0 : a.im = 0) (ha : 1 ≤ ‖a‖) (t : ℝ) :
    |(1 - Complex.exp (I * t / (a - I))).re| ≤ Real.exp |t| * (|t| + t ^ 2) / ‖a‖ ^ (2 : ℕ) := by
  set α := a.re with hα
  have haα : a = (α : ℂ) := by apply Complex.ext <;> simp [hα, ha0]
  have hnorm : ‖a‖ ^ (2 : ℕ) = α ^ 2 := by
    rw [haα, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hα1 : 1 ≤ α ^ 2 := by rw [← hnorm]; nlinarith
  set x : ℝ := -t / (α ^ 2 + 1)
  set y : ℝ := t * α / (α ^ 2 + 1)
  have hz : I * t / (a - I) = (x : ℂ) + (y : ℂ) * I := by rw [haα]; exact I_mul_div_real_sub_I t α
  have hre : (1 - Complex.exp (I * t / (a - I))).re = (1 - Real.exp x) + Real.exp x * (1 - Real.cos y) := by
    rw [hz, Complex.sub_re, Complex.one_re, Complex.exp_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, Complex.add_im, Complex.mul_im]
    ring_nf
  have hden : 0 < α ^ 2 + 1 := by positivity
  have hxabs : |x| ≤ |t| / α ^ 2 := by
    simp only [x, abs_div, abs_neg, abs_of_pos hden]
    exact div_le_div_of_nonneg_left (abs_nonneg t) (by linarith) (by linarith)
  have hx1 : |x| ≤ |t| := hxabs.trans (div_le_self (abs_nonneg t) hα1)
  have hy2 : y ^ 2 ≤ t ^ 2 / α ^ 2 := by
    simp only [y, div_pow, mul_pow]
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [sq_nonneg t, sq_nonneg α]
  have h1 : |1 - Real.exp x| ≤ |x| * Real.exp |x| := abs_one_sub_exp_le x
  have h2 : 0 ≤ 1 - Real.cos y := by linarith [Real.cos_le_one y]
  have h3 : 1 - Real.cos y ≤ y ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := y); linarith
  have hex : Real.exp x ≤ Real.exp |t| := Real.exp_le_exp.mpr ((le_abs_self x).trans hx1)
  have hexa : Real.exp |x| ≤ Real.exp |t| := Real.exp_le_exp.mpr hx1
  have hA : 0 < α ^ 2 := by linarith
  rw [hre, hnorm]
  calc |1 - Real.exp x + Real.exp x * (1 - Real.cos y)|
      ≤ |1 - Real.exp x| + Real.exp x * (1 - Real.cos y) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h2)]
    _ ≤ |x| * Real.exp |x| + Real.exp |t| * (y ^ 2 / 2) := by
        gcongr
    _ ≤ (|t| / α ^ 2) * Real.exp |t| + Real.exp |t| * (t ^ 2 / α ^ 2 / 2) := by
        gcongr
    _ ≤ Real.exp |t| * (|t| + t ^ 2) / α ^ 2 := by
        rw [div_eq_mul_inv]
        have hi : 0 ≤ (α ^ 2)⁻¹ := by positivity
        have he : 0 ≤ Real.exp |t| := (Real.exp_pos _).le
        have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [mul_nonneg (mul_nonneg he ht2) hi]

/-- Every entire atom of a zero copy is at most `e^{|t|}(|t| + t²)/‖a‖²`. -/
theorem abs_centerClockAtomExt_le (q : XiZeroCopy) (t : ℝ) :
    |centerClockAtomExt t (xiSpectralPoint q)| ≤
      Real.exp |t| * (|t| + t ^ 2) / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  set a := xiSpectralPoint q
  have h150 := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  have ha1 : 1 ≤ ‖a‖ := by
    by_contra h; push Not at h
    have : ‖a‖ ^ (2 : ℕ) ≤ 1 := by
      calc ‖a‖ ^ (2 : ℕ) ≤ 1 ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) h.le 2
        _ = 1 := by norm_num
    linarith
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha1; linarith
  have hs : (a.im) = 1 / 2 - ((q.1 : ℂ)).re := by
    show (xiSpectralPoint q).im = _
    rw [xiSpectralPoint]; simp [Complex.mul_im]
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have him_hi : a.im ≤ 1 / 2 := by rw [hs]; linarith
  have him_lo : -(1 / 2) ≤ a.im := by rw [hs]; linarith
  unfold centerClockAtomExt
  split_ifs with hz hneg
  · exact abs_re_one_sub_exp_le hz ha1 t
  · rw [div_eq_mul_inv]
    exact abs_re_one_sub_cos_le ha1 (norm_inv_le_of_norm_le (norm_le_norm_sub_I him_hi) ha0) t
  · rw [div_eq_mul_inv]
    exact abs_re_one_sub_cos_le ha1 (norm_inv_le_of_norm_le (norm_le_norm_add_I him_lo) ha0) t

theorem summable_centerClockAtomExt (t : ℝ) :
    Summable fun q : XiZeroCopy => centerClockAtomExt t (xiSpectralPoint q) := by
  refine Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left (Real.exp |t| * (|t| + t ^ 2))) fun q => ?_
  rw [Real.norm_eq_abs, mul_one_div]
  exact abs_centerClockAtomExt_le q t

/-! ### The entire clock and its kink -/

/-- The entire continuation `Ẽ(t) = Σ_q centerClockAtomExt t (a_q)` of the averaged clock. -/
def liClockCenterAverageExt (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, centerClockAtomExt t (xiSpectralPoint q)

/-- On nonnegative clocks the averaged clock is the entire continuation. -/
theorem liClockCenterAverage_eq_ext {t : ℝ} (ht : 0 ≤ t) :
    liClockCenterAverage t = liClockCenterAverageExt t := by
  unfold liClockCenterAverage liClockCenterAverageExt
  exact tsum_congr fun q => centerClockAverage_eq_atomExt ht _

/-- The averaged clock is even. -/
theorem liClockCenterAverage_neg (t : ℝ) : liClockCenterAverage (-t) = liClockCenterAverage t := by
  unfold liClockCenterAverage
  exact tsum_congr fun q => centerClockAverage_neg t _

/-- **`A(t) = Ẽ(|t|)`.** -/
theorem liClockCenterAverage_eq_ext_abs (t : ℝ) :
    liClockCenterAverage t = liClockCenterAverageExt |t| := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, liClockCenterAverage_eq_ext ht]
  · rw [abs_of_nonpos ht, ← liClockCenterAverage_neg, liClockCenterAverage_eq_ext (by linarith)]

/-- **Kink law.** The odd part of the entire continuation is the sum of the critical odd terms:
off-line zeros, of any depth, drop out. -/
theorem liClockCenterAverageExt_sub_neg (t : ℝ) :
    HasSum (fun q : XiZeroCopy => centerClockCriticalOddTerm t (xiSpectralPoint q))
      (liClockCenterAverageExt t - liClockCenterAverageExt (-t)) := by
  have h := (summable_centerClockAtomExt t).hasSum.sub (summable_centerClockAtomExt (-t)).hasSum
  simp_rw [atomExt_sub_atomExt_neg] at h
  exact h

/-- **The kink of `A` at `t = 0`.** For `t ≥ 0`, `A(t) − Ẽ(−t)` is the sum over the critical zeros
of `Re(exp(−z) − exp(z))`, `z = i t/(a − i)`. -/
theorem liClockCenterAverage_sub_ext_neg_eq_tsum {t : ℝ} (ht : 0 ≤ t) :
    liClockCenterAverage t - liClockCenterAverageExt (-t) =
      ∑' q : XiZeroCopy, centerClockCriticalOddTerm t (xiSpectralPoint q) := by
  rw [liClockCenterAverage_eq_ext ht]
  exact (liClockCenterAverageExt_sub_neg t).tsum_eq.symm

end RHTower
