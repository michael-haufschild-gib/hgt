import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The saddle of a Hausdorff atom

For `p = k + 1`, the atom `z⁻²ᵖ (R - z⁻²)ʳ` has its positive real saddle at
`s² = (p + r)/(pR)`. Normalizing `z = s(1 + u)` separates the cancellation
of the two logarithmic slopes from the quadratic variation.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

/-- Change in the reciprocal square under a relative displacement. -/
def reciprocalDisplacement (u : ℂ) : ℂ :=
  1 - (1 + u)⁻¹ ^ 2

/-- The nonlinear remainder after removing the reciprocal square's first variation. -/
theorem reciprocalDisplacement_sub_linear {u : ℂ} (hu : 1 + u ≠ 0) :
    reciprocalDisplacement u - 2 * u = -u ^ 2 * (3 + 2 * u) / (1 + u) ^ 2 := by
  unfold reciprocalDisplacement
  field_simp [hu]
  ring

/-- The reciprocal-square linearization has a uniform quadratic remainder. -/
theorem norm_reciprocalDisplacement_sub_linear_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) :
    ‖reciprocalDisplacement u - 2 * u‖ ≤ 7 * ‖u‖ ^ 2 := by
  have hden : 3 / 4 ≤ ‖1 + u‖ := by
    have h := norm_sub_le (1 + u) u
    simp only [add_sub_cancel_right, norm_one] at h
    linarith only [h, hu]
  have hdenpos : 0 < ‖1 + u‖ := by linarith only [hden]
  have hne : 1 + u ≠ 0 := norm_pos_iff.mp hdenpos
  have hnum : ‖(3 : ℂ) + 2 * u‖ ≤ 7 / 2 := by
    have h := norm_add_le (3 : ℂ) (2 * u)
    norm_num only [norm_mul, Complex.norm_ofNat] at h
    linarith only [h, hu]
  rw [reciprocalDisplacement_sub_linear hne, norm_div, norm_mul, norm_neg,
    norm_pow, norm_pow, div_le_iff₀ (sq_pos_of_pos hdenpos)]
  have hsq : 7 / 2 ≤ 7 * ‖1 + u‖ ^ 2 := by nlinarith only [hden]
  calc
    ‖u‖ ^ 2 * ‖(3 : ℂ) + 2 * u‖ ≤ ‖u‖ ^ 2 * (7 / 2) :=
      mul_le_mul_of_nonneg_left hnum (sq_nonneg _)
    _ ≤ ‖u‖ ^ 2 * (7 * ‖1 + u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by ring

/-- Small relative displacements change the reciprocal square by at most four times their size. -/
theorem norm_reciprocalDisplacement_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) :
    ‖reciprocalDisplacement u‖ ≤ 4 * ‖u‖ := by
  have h := norm_add_le (reciprocalDisplacement u - 2 * u) (2 * u)
  rw [sub_add_cancel, norm_mul] at h
  norm_num only [Complex.norm_ofNat] at h
  have herr := norm_reciprocalDisplacement_sub_linear_le hu
  have hquad : 7 * ‖u‖ ^ 2 ≤ 2 * ‖u‖ := by
    nlinarith only [mul_nonneg (norm_nonneg u) (sub_nonneg.mpr hu), norm_nonneg u]
  linarith only [h, herr, hquad]

/-- Exact normalized logarithm at the saddle. -/
def saddleLog (p r : ℝ) (u : ℂ) : ℂ :=
  -2 * (p : ℂ) * Complex.log (1 + u) +
    (r : ℂ) * Complex.log (1 + (p / r : ℝ) * reciprocalDisplacement u)

private theorem norm_log_remainder_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 := by
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith only [hu]) (by norm_num)]
    linarith only [hu]
  have h := Complex.norm_log_one_add_sub_self_le (by linarith only [hu])
  have hm := mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖u‖)
  linarith only [h, hm]

/-- Cancellation of the two linear slopes leaves variation on scale `p⁻¹ᐟ²`. -/
theorem norm_saddleLog_le {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) (hpr : 8 * p ≤ r)
    {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) : ‖saddleLog p r u‖ ≤ 11 * p * ‖u‖ ^ 2 := by
  let d := reciprocalDisplacement u
  let v : ℂ := (p / r : ℝ) * d
  have ha0 : 0 ≤ p / r := div_nonneg hp hr.le
  have ha : p / r ≤ 1 / 8 := by
    rw [div_le_iff₀ hr]
    linarith only [hpr]
  have hv : ‖v‖ ≤ 4 * (p / r) * ‖u‖ := by
    dsimp [v, d]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
    calc
      _ ≤ (p / r) * (4 * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_reciprocalDisplacement_le hu) ha0
      _ = _ := by ring
  have hvhalf : ‖v‖ ≤ 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right ha (norm_nonneg u)
    linarith only [hv, hmul, hu]
  have hlogu := norm_log_remainder_le (u := u) (by linarith only [hu])
  have hlogv := norm_log_remainder_le hvhalf
  have hrem := norm_reciprocalDisplacement_sub_linear_le hu
  have hrv : (r : ℂ) * v = (p : ℂ) * d := by
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    dsimp [v]
    push_cast
    field_simp [hrne]
  have heq : saddleLog p r u =
      (-2 * (p : ℂ)) * (Complex.log (1 + u) - u) +
      (r : ℂ) * (Complex.log (1 + v) - v) + (p : ℂ) * (d - 2 * u) := by
    change -2 * (p : ℂ) * Complex.log (1 + u) + (r : ℂ) * Complex.log (1 + v) = _
    linear_combination hrv
  have hpC : ‖(p : ℂ)‖ = p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  have hrC : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hquad : r * ‖v‖ ^ 2 ≤ 2 * p * ‖u‖ ^ 2 := by
    calc
      r * ‖v‖ ^ 2 ≤ r * (4 * (p / r) * ‖u‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) hr.le
      _ = (16 * (p / r)) * (p * ‖u‖ ^ 2) := by field_simp; ring
      _ ≤ 2 * (p * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith only [ha]) (mul_nonneg hp (sq_nonneg _))
      _ = _ := by ring
  rw [heq]
  calc
    _ ≤ (‖(-2 * (p : ℂ)) * (Complex.log (1 + u) - u)‖ +
        ‖(r : ℂ) * (Complex.log (1 + v) - v)‖) + ‖(p : ℂ) * (d - 2 * u)‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = 2 * p * ‖Complex.log (1 + u) - u‖ +
        r * ‖Complex.log (1 + v) - v‖ + p * ‖d - 2 * u‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, hpC, hrC]
      norm_num
    _ ≤ 2 * p * ‖u‖ ^ 2 + r * ‖v‖ ^ 2 + p * (7 * ‖u‖ ^ 2) := by
      have h₁ := mul_le_mul_of_nonneg_left hlogu (by positivity : 0 ≤ 2 * p)
      have h₂ := mul_le_mul_of_nonneg_left hlogv hr.le
      have h₃ := mul_le_mul_of_nonneg_left hrem hp
      linarith only [h₁, h₂, h₃]
    _ ≤ 11 * p * ‖u‖ ^ 2 := by linarith only [hquad]

/-- The reciprocal displacement is holomorphic away from `-1`. -/
theorem hasDerivAt_reciprocalDisplacement {u : ℂ} (hu : 1 + u ≠ 0) :
    HasDerivAt reciprocalDisplacement (2 / (1 + u) ^ 3) u := by
  have h := ((((hasDerivAt_id u).const_add 1).inv hu).pow 2).const_sub 1
  change HasDerivAt reciprocalDisplacement _ u at h
  convert h using 1
  norm_num
  field_simp [hu]

/-- The logarithmic slope vanishes at the normalized saddle. -/
def saddleSlope (p r : ℝ) (u : ℂ) : ℂ :=
  -(2 * (p : ℂ) * (1 + (p / r : ℝ)) * u * (2 + u)) /
    ((1 + u) ^ 3 * (1 + (p / r : ℝ) * reciprocalDisplacement u))

private theorem scaled_displacement_bounds {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r)
    (hpr : 8 * p ≤ r) {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) :
    ‖(p / r : ℝ) * reciprocalDisplacement u‖ ≤ 1 / 8 := by
  have ha0 : 0 ≤ p / r := div_nonneg hp hr.le
  have ha : p / r ≤ 1 / 8 := by
    rw [div_le_iff₀ hr]
    linarith only [hpr]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  have hd := norm_reciprocalDisplacement_le hu
  have hd1 : ‖reciprocalDisplacement u‖ ≤ 1 := by linarith only [hd, hu]
  calc
    _ ≤ (1 / 8) * 1 := mul_le_mul ha hd1 (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

private theorem one_add_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) :
    1 + z ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have h := (abs_le.mp (Complex.abs_re_le_norm z)).1
  simp only [Complex.add_re, Complex.one_re]
  linarith only [h, hz]

/-- Both logarithms have positive real arguments near the saddle. Their linear terms cancel. -/
theorem hasDerivAt_saddleLog {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) (hpr : 8 * p ≤ r)
    {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) : HasDerivAt (saddleLog p r) (saddleSlope p r u) u := by
  have huSlit := one_add_mem_slitPlane (z := u) (by linarith only [hu])
  have hvBound := scaled_displacement_bounds hp hr hpr hu
  have hvSlit := one_add_mem_slitPlane (by linarith only [hvBound])
  have huNe : 1 + u ≠ 0 := Complex.slitPlane_ne_zero huSlit
  have hvNe : 1 + (p / r : ℝ) * reciprocalDisplacement u ≠ 0 :=
    Complex.slitPlane_ne_zero hvSlit
  have h₁ := ((hasDerivAt_id u).const_add 1).clog huSlit
  have h₂ := (((hasDerivAt_reciprocalDisplacement huNe).const_mul
    ((p / r : ℝ) : ℂ)).const_add 1).clog hvSlit
  have h := (h₁.const_mul (-2 * (p : ℂ))).add (h₂.const_mul (r : ℂ))
  change HasDerivAt (saddleLog p r) _ u at h
  convert h using 1
  dsimp only [saddleSlope, id_eq]
  have hrNe : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hra : (r : ℂ) * (p / r : ℝ) = (p : ℂ) := by
    push_cast
    field_simp [hrNe]
  have hrel : (1 + u) ^ 2 * (1 + (p / r : ℝ) * reciprocalDisplacement u) =
      (1 + (p / r : ℝ)) * (1 + u) ^ 2 - (p / r : ℝ) := by
    unfold reciprocalDisplacement
    field_simp [huNe]
    ring
  calc
    _ = (-2 * (p : ℂ) * (1 + u) ^ 2 *
        (1 + (p / r : ℝ) * reciprocalDisplacement u) + 2 * (r : ℂ) * (p / r : ℝ)) /
        ((1 + u) ^ 3 * (1 + (p / r : ℝ) * reciprocalDisplacement u)) := by
      congr 1
      linear_combination 2 * (p : ℂ) * hrel - 2 * hra
    _ = _ := by
      field_simp [huNe, hvNe]

/-- The combined logarithmic slope is linear in distance from the saddle. -/
theorem norm_saddleSlope_le {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) (hpr : 8 * p ≤ r)
    {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) : ‖saddleSlope p r u‖ ≤ 16 * p * ‖u‖ := by
  have ha0 : 0 ≤ p / r := div_nonneg hp hr.le
  have ha : p / r ≤ 1 / 8 := by
    rw [div_le_iff₀ hr]
    linarith only [hpr]
  have hA : ‖(1 : ℂ) + (p / r : ℝ)‖ ≤ 9 / 8 := by
    have h := norm_add_le (1 : ℂ) ((p / r : ℝ) : ℂ)
    rw [norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0] at h
    linarith only [h, ha]
  have hB : ‖(2 : ℂ) + u‖ ≤ 9 / 4 := by
    have h := norm_add_le (2 : ℂ) u
    norm_num only [Complex.norm_ofNat] at h
    linarith only [h, hu]
  have hU : 3 / 4 ≤ ‖1 + u‖ := by
    have h := norm_sub_le (1 + u) u
    simp only [add_sub_cancel_right, norm_one] at h
    linarith only [h, hu]
  have hv := scaled_displacement_bounds hp hr hpr hu
  have hV : 7 / 8 ≤ ‖1 + (p / r : ℝ) * reciprocalDisplacement u‖ := by
    have h := norm_sub_le (1 + (p / r : ℝ) * reciprocalDisplacement u)
      ((p / r : ℝ) * reciprocalDisplacement u)
    simp only [add_sub_cancel_right, norm_one] at h
    linarith only [h, hv]
  have hU3 : 27 / 64 ≤ ‖1 + u‖ ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) hU 3
    norm_num at h ⊢
    exact h
  have hden : 189 / 512 ≤
      ‖1 + u‖ ^ 3 * ‖1 + (p / r : ℝ) * reciprocalDisplacement u‖ := by
    have h := mul_le_mul hU3 hV (by norm_num : (0 : ℝ) ≤ 7 / 8)
      (pow_nonneg (norm_nonneg _) 3)
    norm_num at h ⊢
    exact h
  have hdenpos : 0 < ‖1 + u‖ ^ 3 * ‖1 + (p / r : ℝ) * reciprocalDisplacement u‖ := by
    linarith only [hden]
  have hAB := mul_le_mul hA hB (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 9 / 8)
  have hcoef : 2 * (‖(1 : ℂ) + (p / r : ℝ)‖ * ‖(2 : ℂ) + u‖) ≤
      16 * (‖1 + u‖ ^ 3 * ‖1 + (p / r : ℝ) * reciprocalDisplacement u‖) := by
    linarith only [hAB, hden]
  simp only [saddleSlope, norm_div, norm_neg, norm_mul, norm_pow,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  rw [div_le_iff₀ hdenpos]
  have h := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hp (norm_nonneg u))
  nlinarith only [h]

/-- The normalized logarithm is real on the real interval around its saddle. -/
theorem saddleLog_ofReal_im {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) (hpr : 8 * p ≤ r)
    {t : ℝ} (ht : |t| ≤ 1 / 4) : (saddleLog p r (t : ℂ)).im = 0 := by
  have hu : ‖(t : ℂ)‖ ≤ 1 / 4 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using ht
  have hv := scaled_displacement_bounds hp hr hpr hu
  have hvSlit := one_add_mem_slitPlane (by linarith only [hv])
  have heq : 1 + (p / r : ℝ) * reciprocalDisplacement (t : ℂ) =
      ((1 + (p / r) * (1 - (1 + t)⁻¹ ^ 2) : ℝ) : ℂ) := by
    simp only [reciprocalDisplacement, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_one]
  have h₁ : 0 ≤ 1 + t := by
    have h := (abs_le.mp ht).1
    linarith only [h]
  have h₂ : 0 ≤ 1 + (p / r) * (1 - (1 + t)⁻¹ ^ 2) := by
    have h := Complex.mem_slitPlane_iff.mp hvSlit
    rw [heq, Complex.ofReal_re, Complex.ofReal_im] at h
    rcases h with h | h
    · exact h.le
    · exact False.elim (h rfl)
  unfold saddleLog
  rw [show 1 + (t : ℂ) = ((1 + t : ℝ) : ℂ) by simp,
    ← Complex.ofReal_log h₁, heq, ← Complex.ofReal_log h₂]
  simp

/-- The phase measures transverse displacement times distance from the real saddle. -/
theorem abs_im_saddleLog_le {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) (hpr : 8 * p ≤ r)
    {u : ℂ} (hu : |u.re| + |u.im| ≤ 1 / 4) :
    |(saddleLog p r u).im| ≤ 16 * p * (|u.re| + |u.im|) * |u.im| := by
  let a := |u.re| + |u.im|
  have hnear {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) a) : ‖z‖ ≤ a := by
    simpa only [mem_closedBall_iff_norm, sub_zero] using hz
  have hd : ∀ z ∈ Metric.closedBall (0 : ℂ) a, DifferentiableAt ℂ (saddleLog p r) z := by
    intro z hz
    exact (hasDerivAt_saddleLog hp hr hpr ((hnear hz).trans hu)).differentiableAt
  have hb : ∀ z ∈ Metric.closedBall (0 : ℂ) a,
      ‖deriv (saddleLog p r) z‖ ≤ 16 * p * a := by
    intro z hz
    rw [(hasDerivAt_saddleLog hp hr hpr ((hnear hz).trans hu)).deriv]
    exact (norm_saddleSlope_le hp hr hpr ((hnear hz).trans hu)).trans
      (mul_le_mul_of_nonneg_left (hnear hz) (by positivity))
  have hx : (u.re : ℂ) ∈ Metric.closedBall (0 : ℂ) a := by
    rw [mem_closedBall_iff_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    dsimp [a]
    linarith only [abs_nonneg u.im]
  have hy : u ∈ Metric.closedBall (0 : ℂ) a := by
    rw [mem_closedBall_iff_norm, sub_zero]
    exact Complex.norm_le_abs_re_add_abs_im u
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_closedBall 0 a) hx hy
  have hdist : ‖u - (u.re : ℂ)‖ = |u.im| := by
    have heq : u - (u.re : ℂ) = (u.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  rw [hdist] at h
  have hre := saddleLog_ofReal_im hp hr hpr (t := u.re)
    (by linarith only [hu, abs_nonneg u.im])
  have hi := Complex.abs_im_le_norm (saddleLog p r u - saddleLog p r (u.re : ℂ))
  rw [Complex.sub_im, hre, sub_zero] at hi
  exact hi.trans h

/-- Inside the quadratic core the normalized atom keeps at least half its saddle value. -/
theorem re_exp_saddleLog_ge_half {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) (hpr : 8 * p ≤ r)
    {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) (hsmall : 11 * p * ‖u‖ ^ 2 ≤ 1 / 4) :
    1 / 2 ≤ (Complex.exp (saddleLog p r u)).re := by
  have hH := (norm_saddleLog_le hp hr hpr hu).trans hsmall
  have he := Complex.norm_exp_sub_one_le (by linarith only [hH])
  have hre := (abs_le.mp (Complex.abs_re_le_norm (Complex.exp (saddleLog p r u) - 1))).1
  simp only [Complex.sub_re, Complex.one_re] at hre
  linarith only [hH, he, hre]

/-- The wider band needs only phase control, without a lower bound for its modulus. -/
theorem re_exp_saddleLog_nonneg {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) (hpr : 8 * p ≤ r)
    {u : ℂ} (hu : |u.re| + |u.im| ≤ 1 / 4)
    (hphase : 16 * p * (|u.re| + |u.im|) * |u.im| ≤ 1 / 2) :
    0 ≤ (Complex.exp (saddleLog p r u)).re := by
  have h := (abs_im_saddleLog_le hp hr hpr hu).trans hphase
  obtain ⟨hL, hU⟩ := abs_le.mp h
  have hcos := Real.cos_pos_of_mem_Ioo (x := (saddleLog p r u).im)
    ⟨by linarith only [hL, Real.pi_gt_three], by linarith only [hU, Real.pi_gt_three]⟩
  rw [Complex.exp_re]
  exact mul_nonneg (Real.exp_pos _).le hcos.le

/-- A Hausdorff atom as a function of the centered zero. -/
def kernel (R : ℝ) (p r : ℕ) (z : ℂ) : ℂ :=
  (z⁻¹ ^ 2) ^ p * ((R : ℂ) - z⁻¹ ^ 2) ^ r

/-- Its restriction to the real axis. -/
def realKernel (R : ℝ) (p r : ℕ) (x : ℝ) : ℝ :=
  (x⁻¹ ^ 2) ^ p * (R - x⁻¹ ^ 2) ^ r

theorem kernel_ofReal (R : ℝ) (p r : ℕ) (x : ℝ) :
    kernel R p r (x : ℂ) = (realKernel R p r x : ℂ) := by
  simp only [kernel, realKernel, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_inv]

@[simp] theorem kernel_neg (R : ℝ) (p r : ℕ) (z : ℂ) :
    kernel R p r (-z) = kernel R p r z := by
  simp only [kernel, inv_neg, neg_sq]

/-- Exponentiation recovers the two normalized powers exactly. -/
theorem exp_saddleLog_nat {p r : ℕ} (hr : 0 < r) (hpr : 8 * (p : ℝ) ≤ r)
    {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) :
    Complex.exp (saddleLog p r u) =
      ((1 + u)⁻¹ ^ 2) ^ p *
        (1 + ((p : ℝ) / (r : ℝ) : ℝ) * reciprocalDisplacement u) ^ r := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have huNe := Complex.slitPlane_ne_zero
    (one_add_mem_slitPlane (z := u) (by linarith only [hu]))
  have hv := scaled_displacement_bounds (Nat.cast_nonneg p) hrR hpr hu
  have hvNe := Complex.slitPlane_ne_zero (one_add_mem_slitPlane (by linarith only [hv]))
  unfold saddleLog
  simp only [Complex.ofReal_natCast]
  rw [Complex.exp_add]
  have heq : -2 * (p : ℂ) * Complex.log (1 + u) =
      -(((2 * p : ℕ) : ℂ) * Complex.log (1 + u)) := by push_cast; ring
  rw [heq, Complex.exp_neg, Complex.exp_nat_mul, Complex.exp_log huNe,
    Complex.exp_nat_mul, Complex.exp_log hvNe, ← inv_pow, pow_mul]

/-- Algebraic normalization at the saddle, valid for every relative displacement. -/
theorem kernel_normalization {R s : ℝ} {p r : ℕ} (hs : s ≠ 0) (hr : 0 < r)
    (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r) (u : ℂ) :
    kernel R p r ((s : ℂ) * (1 + u)) =
      kernel R p r (s : ℂ) *
        (((1 + u)⁻¹ ^ 2) ^ p *
          (1 + ((p : ℝ) / (r : ℝ) : ℝ) * reciprocalDisplacement u) ^ r) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hbc : (p : ℂ) * ((R : ℂ) * (s : ℂ) ^ 2 - 1) = r := by
    exact_mod_cast hbalance
  have hcal : ((R : ℂ) - (s : ℂ)⁻¹ ^ 2) * ((p : ℝ) / (r : ℝ) : ℝ) =
      (s : ℂ)⁻¹ ^ 2 := by
    push_cast
    field_simp [hsC, hrC]
    linear_combination hbc
  have hx : ((s : ℂ) * (1 + u))⁻¹ ^ 2 = (s : ℂ)⁻¹ ^ 2 * (1 + u)⁻¹ ^ 2 := by
    rw [mul_inv, mul_pow]
  have hfactor : (R : ℂ) - (s : ℂ)⁻¹ ^ 2 * (1 + u)⁻¹ ^ 2 =
      ((R : ℂ) - (s : ℂ)⁻¹ ^ 2) *
        (1 + ((p : ℝ) / (r : ℝ) : ℝ) * reciprocalDisplacement u) := by
    unfold reciprocalDisplacement
    linear_combination ((1 + u)⁻¹ ^ 2 - 1) * hcal
  simp only [kernel, hx, hfactor, mul_pow]
  ring

/-- The exact saddle normalization, with the balance equation stated without division. -/
theorem kernel_eq_saddle_mul_exp {R s : ℝ} {p r : ℕ} (hs : s ≠ 0) (hr : 0 < r)
    (hpr : 8 * (p : ℝ) ≤ r) (hbalance : (p : ℝ) * (R * s ^ 2 - 1) = r)
    {u : ℂ} (hu : ‖u‖ ≤ 1 / 4) :
    kernel R p r ((s : ℂ) * (1 + u)) =
      kernel R p r (s : ℂ) * Complex.exp (saddleLog p r u) := by
  rw [kernel_normalization hs hr hbalance, exp_saddleLog_nat hr hpr hu]

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
