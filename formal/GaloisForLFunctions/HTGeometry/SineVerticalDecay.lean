import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Vertical decay of the reciprocal sine

Along a vertical line the complex sine grows like `sinh` of the imaginary part, so its reciprocal
decays exponentially.  This is the bound that makes the reflection kernel `π / sin (π w)`
absolutely integrable on every vertical line off the integers, and that kills the horizontal sides
of a rectangle when a Mellin contour is shifted.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- **The sine dominates the hyperbolic sine of the imaginary part.** -/
theorem sinh_abs_im_le_norm_sin (z : ℂ) : Real.sinh |z.im| ≤ ‖Complex.sin z‖ := by
  have hdef : Complex.sin z
      = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2 := rfl
  have hre1 : (-z * Complex.I).re = z.im := by
    simp [Complex.mul_re]
  have hre2 : (z * Complex.I).re = -z.im := by
    simp [Complex.mul_re]
  have hnorm : ‖Complex.sin z‖
      = ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ / 2 := by
    rw [hdef, norm_div, norm_mul, Complex.norm_I, mul_one]
    norm_num
  have hlower : |Real.exp z.im - Real.exp (-z.im)|
      ≤ ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ := by
    have h := abs_norm_sub_norm_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
    rwa [Complex.norm_exp, Complex.norm_exp, hre1, hre2] at h
  rw [hnorm]
  refine le_div_iff₀ (by norm_num) |>.mpr ?_
  refine le_trans ?_ (le_trans hlower (le_of_eq (by ring)))
  rw [Real.sinh_eq]
  rcases abs_cases z.im with ⟨habs, _⟩ | ⟨habs, _⟩
  · rw [habs]
    have : Real.exp z.im - Real.exp (-z.im) ≤ |Real.exp z.im - Real.exp (-z.im)| :=
      le_abs_self _
    linarith
  · rw [habs]
    have : -(Real.exp z.im - Real.exp (-z.im)) ≤ |Real.exp z.im - Real.exp (-z.im)| :=
      neg_le_abs _
    have hneg : Real.exp (-z.im) - Real.exp (- -z.im) = -(Real.exp z.im - Real.exp (-z.im)) := by
      rw [neg_neg]
      ring
    rw [hneg]
    linarith

/-- **Exponential decay of the reciprocal sine along a vertical line.** -/
theorem norm_inv_sin_le {z : ℂ} (hz : 0 < |z.im|) :
    ‖(Complex.sin z)⁻¹‖ ≤ (Real.sinh |z.im|)⁻¹ := by
  have hpos : 0 < Real.sinh |z.im| := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-|z.im|) < Real.exp |z.im| := Real.exp_lt_exp.mpr (by linarith)
    linarith
  rw [norm_inv, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le hpos (sinh_abs_im_le_norm_sin z)

/-- **The sine dominates the sine of the real part.**  This is the bound that keeps the reciprocal
sine bounded near the real axis, off the integers. -/
theorem abs_sin_re_le_norm_sin (z : ℂ) : |Real.sin z.re| ≤ ‖Complex.sin z‖ := by
  have hre : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
    rw [Complex.sin_eq]
    simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, Complex.add_re, Complex.mul_re]
  have hcosh : (1 : ℝ) ≤ Real.cosh z.im := Real.one_le_cosh z.im
  have hstep : |Real.sin z.re| ≤ |Real.sin z.re * Real.cosh z.im| := by
    rw [abs_mul, abs_of_nonneg (le_trans zero_le_one hcosh)]
    exact le_mul_of_one_le_right (abs_nonneg _) hcosh
  refine le_trans hstep ?_
  rw [← hre]
  exact Complex.abs_re_le_norm (Complex.sin z)

/-- **Off the integers the reciprocal sine is bounded on a vertical line.** -/
theorem norm_inv_sin_le_of_sin_re_ne {z : ℂ} (hz : Real.sin z.re ≠ 0) :
    ‖(Complex.sin z)⁻¹‖ ≤ |Real.sin z.re|⁻¹ := by
  have hpos : 0 < |Real.sin z.re| := abs_pos.mpr hz
  rw [norm_inv, ← one_div, ← one_div]
  exact one_div_le_one_div_of_le hpos (abs_sin_re_le_norm_sin z)

/-- Beyond height one the hyperbolic sine is at least a quarter of the exponential. -/
theorem exp_div_four_le_sinh {y : ℝ} (hy : 1 ≤ y) : Real.exp y / 4 ≤ Real.sinh y := by
  have hexp : Real.exp (-y) ≤ Real.exp y / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hlin := Real.add_one_le_exp (y + y)
    have h2y : (2 : ℝ) ≤ Real.exp (y + y) := by linarith
    have hpos : (0 : ℝ) < Real.exp (-y) := Real.exp_pos _
    calc Real.exp (-y) * 2 ≤ Real.exp (-y) * Real.exp (y + y) :=
          mul_le_mul_of_nonneg_left h2y (le_of_lt hpos)
      _ = Real.exp y := by
          rw [← Real.exp_add]
          congr 1
          ring
  rw [Real.sinh_eq]
  linarith

/-- **Exponential vertical decay of the reciprocal sine beyond height one.** -/
theorem norm_inv_sin_le_exp {z : ℂ} (hz : 1 ≤ |z.im|) :
    ‖(Complex.sin z)⁻¹‖ ≤ 4 * Real.exp (-|z.im|) := by
  have hpos : 0 < Real.exp |z.im| / 4 := by positivity
  have hlow : Real.exp |z.im| / 4 ≤ Real.sinh |z.im| := exp_div_four_le_sinh hz
  have hbound : ‖(Complex.sin z)⁻¹‖ ≤ (Real.sinh |z.im|)⁻¹ :=
    norm_inv_sin_le (lt_of_lt_of_le (by norm_num) hz)
  refine le_trans hbound ?_
  have hinv : (Real.sinh |z.im|)⁻¹ ≤ (Real.exp |z.im| / 4)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hpos hlow
  refine le_trans hinv (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

/-- A quadratic lower bound for the exponential, from the linear one applied at half the
argument. -/
theorem sq_div_four_le_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 / 4 ≤ Real.exp x := by
  have hhalf : x / 2 + 1 ≤ Real.exp (x / 2) := Real.add_one_le_exp (x / 2)
  have hnn : (0 : ℝ) ≤ x / 2 := by linarith
  have hsq : (x / 2) ^ 2 ≤ (Real.exp (x / 2)) ^ 2 := by
    refine pow_le_pow_left₀ hnn ?_ 2
    linarith
  have hexp : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc x ^ 2 / 4 = (x / 2) ^ 2 := by ring
    _ ≤ (Real.exp (x / 2)) ^ 2 := hsq
    _ = Real.exp x := hexp

/-- **The reciprocal sine is dominated by the Cauchy density beyond height one.** -/
theorem norm_inv_sin_le_cauchy_of_one_le {z : ℂ} (hz : 1 ≤ |z.im|) :
    ‖(Complex.sin z)⁻¹‖ ≤ 32 * (1 + z.im ^ 2)⁻¹ := by
  have habs : (0 : ℝ) < |z.im| := lt_of_lt_of_le (by norm_num) hz
  have hsq : z.im ^ 2 = |z.im| ^ 2 := by
    rw [sq_abs]
  have hquad : |z.im| ^ 2 / 4 ≤ Real.exp |z.im| := sq_div_four_le_exp (le_of_lt habs)
  have hone : (1 : ℝ) ≤ |z.im| ^ 2 := by nlinarith
  have hden : (0 : ℝ) < 1 + z.im ^ 2 := by positivity
  have hdecay : ‖(Complex.sin z)⁻¹‖ ≤ 4 * Real.exp (-|z.im|) := norm_inv_sin_le_exp hz
  refine le_trans hdecay ?_
  have hexp_pos : (0 : ℝ) < Real.exp |z.im| := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_le_div_iff₀ hexp_pos hden]
  nlinarith [hquad, hone, hsq]

/-! ### The bound along a vertical line of the reflection kernel -/

theorem re_pi_mul_vertical (σ t : ℝ) :
    ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)).re = Real.pi * σ := by
  simp [Complex.mul_re, Complex.add_re, Complex.add_im]

theorem im_pi_mul_vertical (σ t : ℝ) :
    ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)).im = Real.pi * t := by
  simp [Complex.mul_im, Complex.add_re, Complex.add_im]

/-- **A single integrable envelope for the reciprocal sine along a vertical line.**  Off the
integers the reciprocal sine is dominated on the whole line by a multiple of the Cauchy density. -/
theorem norm_inv_sin_vertical_le {σ : ℝ} (hσ : Real.sin (Real.pi * σ) ≠ 0) (t : ℝ) :
    ‖(Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)))⁻¹‖
      ≤ (max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32) * (1 + t ^ 2)⁻¹ := by
  set z : ℂ := (Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) with hz
  have hre : z.re = Real.pi * σ := re_pi_mul_vertical σ t
  have him : z.im = Real.pi * t := im_pi_mul_vertical σ t
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  rcases le_or_gt (|z.im|) 1 with hsmall | hbig
  · -- near the real axis: the constant bound, against a density bounded below
    have hbd : ‖(Complex.sin z)⁻¹‖ ≤ |Real.sin (Real.pi * σ)|⁻¹ := by
      have := norm_inv_sin_le_of_sin_re_ne (z := z) (by rw [hre]; exact hσ)
      rwa [hre] at this
    have htsq : t ^ 2 ≤ 1 := by
      rw [him] at hsmall
      have habs : |t| ≤ 1 := by
        rw [abs_mul, abs_of_pos Real.pi_pos] at hsmall
        nlinarith [abs_nonneg t, Real.pi_pos]
      nlinarith [abs_nonneg t, sq_abs t]
    have hlow : (1 : ℝ) / 2 ≤ (1 + t ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hden]
      linarith
    have hposinv : (0 : ℝ) ≤ |Real.sin (Real.pi * σ)|⁻¹ := by positivity
    calc ‖(Complex.sin z)⁻¹‖ ≤ |Real.sin (Real.pi * σ)|⁻¹ := hbd
      _ = 2 * |Real.sin (Real.pi * σ)|⁻¹ * (1 / 2) := by ring
      _ ≤ 2 * |Real.sin (Real.pi * σ)|⁻¹ * (1 + t ^ 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ (max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32) * (1 + t ^ 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (by positivity))
  · -- away from the real axis: the Cauchy-density bound
    have hbd : ‖(Complex.sin z)⁻¹‖ ≤ 32 * (1 + z.im ^ 2)⁻¹ :=
      norm_inv_sin_le_cauchy_of_one_le (le_of_lt hbig)
    have hcmp : (1 + z.im ^ 2)⁻¹ ≤ (1 + t ^ 2)⁻¹ := by
      have hpisq : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [hpi]
      have hle : 1 + t ^ 2 ≤ 1 + z.im ^ 2 := by
        rw [him]
        nlinarith [sq_nonneg t, hpisq]
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hden hle
    calc ‖(Complex.sin z)⁻¹‖ ≤ 32 * (1 + z.im ^ 2)⁻¹ := hbd
      _ ≤ 32 * (1 + t ^ 2)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hcmp (by norm_num)
      _ ≤ (max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32) * (1 + t ^ 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (by positivity))

/-! ### Holomorphy of the reflection kernel off the integers -/

theorem analyticAt_sin_pi_mul (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) z := by
  have hdiff : Differentiable ℂ fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w) :=
    Complex.differentiable_sin.comp (differentiable_id.const_mul _)
  exact hdiff.analyticAt z

/-- **The reflection kernel is analytic off the zeros of the sine.** -/
theorem analyticAt_inv_sin_pi_mul {z : ℂ} (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => (Complex.sin ((Real.pi : ℂ) * w))⁻¹) z :=
  (analyticAt_sin_pi_mul z).inv hz

/-! ### Translation of the sine by an integer -/

/-- **The sine of `π w` is periodic up to sign.**  Translating the argument by a natural number
multiplies the sine by `(-1)` to that power. -/
theorem sin_pi_mul_add_nat (w : ℂ) (k : ℕ) :
    Complex.sin ((Real.pi : ℂ) * (w + (k : ℂ)))
      = (-1) ^ k * Complex.sin ((Real.pi : ℂ) * w) := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hshift : (Real.pi : ℂ) * (w + ((n + 1 : ℕ) : ℂ))
          = (Real.pi : ℂ) * (w + (n : ℂ)) + (Real.pi : ℂ) := by
        push_cast
        ring
      rw [hshift, Complex.sin_add_pi, ih, pow_succ]
      ring

/-- The reflection kernel at an integer translate. -/
theorem inv_sin_pi_mul_add_nat (w : ℂ) (k : ℕ) :
    (Complex.sin ((Real.pi : ℂ) * (w + (k : ℂ))))⁻¹
      = (-1) ^ k * (Complex.sin ((Real.pi : ℂ) * w))⁻¹ := by
  rw [sin_pi_mul_add_nat, mul_inv]
  congr 1
  rw [← inv_pow]
  norm_num

/-! ### The simple pole of the reflection kernel at the origin -/

theorem hasDerivAt_sin_pi_mul_zero :
    HasDerivAt (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) (Real.pi : ℂ) 0 := by
  have hinner : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)
  have houter : HasDerivAt Complex.sin (Complex.cos ((Real.pi : ℂ) * 0)) ((Real.pi : ℂ) * 0) :=
    Complex.hasDerivAt_sin _
  have hcomp := houter.comp (0 : ℂ) hinner
  rw [mul_zero, Complex.cos_zero, one_mul] at hcomp
  exact hcomp

/-- **The sine slope at the origin.** -/
theorem tendsto_sin_pi_mul_div :
    Filter.Tendsto (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w) / w)
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (Real.pi : ℂ)) := by
  have h := hasDerivAt_iff_tendsto_slope.mp hasDerivAt_sin_pi_mul_zero
  refine h.congr fun w => ?_
  rw [slope_def_field]
  simp

/-- **The reflection kernel has a simple pole at the origin.**  The product with the variable tends
to the reciprocal of `π`, so `π / sin(π w)` has residue one there. -/
theorem tendsto_mul_inv_sin_pi_mul :
    Filter.Tendsto (fun w : ℂ => w * (Complex.sin ((Real.pi : ℂ) * w))⁻¹)
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds ((Real.pi : ℂ)⁻¹)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hinv := tendsto_sin_pi_mul_div.inv₀ hpi
  refine hinv.congr fun w => ?_
  rw [inv_div, div_eq_mul_inv]

/-! ### The simple-zero factorization of the sine at the origin -/

/-- The analytic cofactor of the simple zero of `sin(π ·)` at the origin. -/
noncomputable def sinPiCofactor : ℂ → ℂ :=
  dslope (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) 0

theorem analyticAt_sinPiCofactor : AnalyticAt ℂ sinPiCofactor 0 := by
  obtain ⟨p, hp⟩ := analyticAt_sin_pi_mul 0
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem sinPiCofactor_zero : sinPiCofactor 0 = (Real.pi : ℂ) := by
  rw [sinPiCofactor, dslope_same]
  exact hasDerivAt_sin_pi_mul_zero.deriv

/-- **The sine has a simple zero at the origin.**  It factors as the variable times an analytic
cofactor whose value there is `π`. -/
theorem sin_pi_mul_eq_mul_cofactor (w : ℂ) :
    Complex.sin ((Real.pi : ℂ) * w) = w * sinPiCofactor w := by
  have h := sub_smul_dslope (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z)) 0 w
  rw [sub_zero, smul_eq_mul] at h
  rw [sinPiCofactor, h]
  simp

/-! ### The residue hypothesis of the rectangle theorem -/

/-- **The reflection kernel minus its principal part is bounded at the origin.**  This is the
`near_p` hypothesis of the residue theorem for a simple pole, at `p = 0` with residue `1`. -/
theorem isBigO_inv_sin_sub_inv :
    (fun w : ℂ => (Real.pi : ℂ) * (Complex.sin ((Real.pi : ℂ) * w))⁻¹ - w⁻¹)
      =O[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ] (fun _ : ℂ => (1 : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcont : ContinuousAt sinPiCofactor 0 := analyticAt_sinPiCofactor.continuousAt
  have hne : ∀ᶠ w : ℂ in nhds (0 : ℂ), sinPiCofactor w ≠ 0 := by
    refine hcont.eventually_ne ?_
    rw [sinPiCofactor_zero]
    exact hpi
  have hbdd : ∀ᶠ w : ℂ in nhds (0 : ℂ), ‖(sinPiCofactor w)⁻¹‖ ≤ 2 * ‖(Real.pi : ℂ)⁻¹‖ := by
    have hinv : ContinuousAt (fun w : ℂ => (sinPiCofactor w)⁻¹) 0 := by
      refine hcont.inv₀ ?_
      rw [sinPiCofactor_zero]
      exact hpi
    have htarget : ‖((sinPiCofactor 0)⁻¹ : ℂ)‖ < 2 * ‖(Real.pi : ℂ)⁻¹‖ := by
      rw [sinPiCofactor_zero]
      have hpos : (0 : ℝ) < ‖(Real.pi : ℂ)⁻¹‖ := by
        simp
      linarith
    exact (hinv.norm.eventually (eventually_lt_nhds htarget)).mono fun w hw => le_of_lt hw
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp
    ((analyticAt_sinPiCofactor.differentiableAt.hasDerivAt).isBigO_sub)
  refine Asymptotics.IsBigO.of_bound (C * (2 * ‖(Real.pi : ℂ)⁻¹‖)) ?_
  filter_upwards [nhdsWithin_le_nhds hne, nhdsWithin_le_nhds hbdd,
    nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with w hwne hwbdd hwC hw0
  have hw : w ≠ 0 := hw0
  have hidentity : (Real.pi : ℂ) * (Complex.sin ((Real.pi : ℂ) * w))⁻¹ - w⁻¹
      = -((sinPiCofactor w - sinPiCofactor 0) * w⁻¹) * (sinPiCofactor w)⁻¹ := by
    rw [sin_pi_mul_eq_mul_cofactor, sinPiCofactor_zero, mul_inv]
    field_simp
    ring
  rw [hidentity, norm_mul, norm_neg, norm_mul, norm_one, mul_one]
  have hnum : ‖sinPiCofactor w - sinPiCofactor 0‖ * ‖(w : ℂ)⁻¹‖ ≤ C := by
    rw [norm_inv, ← div_eq_mul_inv, div_le_iff₀ (norm_pos_iff.mpr hw)]
    simp [sub_zero] at hwC
    exact hwC
  have hC0 : (0 : ℝ) ≤ C := le_trans (by positivity) hnum
  exact mul_le_mul hnum hwbdd (norm_nonneg _) hC0

end GaloisForLFunctions.HTGeometry
