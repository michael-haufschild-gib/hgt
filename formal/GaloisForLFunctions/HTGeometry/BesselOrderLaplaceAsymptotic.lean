import GaloisForLFunctions.HTGeometry.BesselExteriorEnvelope
import GaloisForLFunctions.HTGeometry.PrincipalSquareRootDeriv
import GaloisForLFunctions.HTGeometry.ContactOrderEulerIntegral

/-!
# The Laplace asymptotic of the order-one Schläfli integral

The substitution `v = √2 sinh(t/2)` turns `cosh t − 1` into `v²` and converts the Schläfli
integral into an exact Gaussian integral against the profile

`P(v) = (1+v²)/√(2+v²)`,

which satisfies `0 ≤ P(v) − 1/√2 ≤ v²/√2`.  Hence, for every argument in the open right half
plane,

`K₁(w) = e^{-w} (√(π/(2w)) + R(w))`,  `|R(w)| ≤ C (Re w)^{-3/2}`,

with an absolute constant.  This is the uniform large-argument asymptotic with explicit error: the
leading term carries the exact phase of the principal square root, and the remainder is smaller by
one full power of the argument.
-/

open MeasureTheory Set Filter Topology

namespace HTGeometry

/-! ## Two elementary integral facts -/

/-- The even-reflection split of a complex-valued integral. -/
theorem integral_even_eq_two_mul_complex {f : ℝ → ℂ} (hf : Integrable f)
    (he : ∀ x, f (-x) = f x) :
    (∫ x, f x) = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Ioi 0 = Iio 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, neg_pos]
  have hrefl := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (measurableEmbedding_neg (α := ℝ)) f (Ioi 0)
  rw [hpre] at hrefl
  have hle : (∫ x in Iio (0 : ℝ), f x) = ∫ y in Ioi (0 : ℝ), f y := by
    rw [← hrefl]
    exact setIntegral_congr_fun measurableSet_Iio fun x _ => (he x).symm
  have hadd := MeasureTheory.integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hf
  rw [compl_Iic, integral_Iic_eq_integral_Iio, hle] at hadd
  rw [← hadd]
  ring

/-- The half-line Gaussian integral. -/
theorem integral_Ioi_gaussian {B : ℝ} (hB : 0 < B) :
    (∫ v in Ioi (0 : ℝ), Real.exp (-B * v ^ 2)) = Real.sqrt (Real.pi / B) / 2 := by
  have hint : Integrable fun v : ℝ => Real.exp (-B * v ^ 2) := integrable_exp_neg_mul_sq hB
  have heven : ∀ v : ℝ, Real.exp (-B * (-v) ^ 2) = Real.exp (-B * v ^ 2) := by
    intro v
    congr 1
    ring
  have hsplit := GaloisForLFunctions.HTGeometry.integral_even_eq_two_mul hint heven
  rw [integral_gaussian] at hsplit
  linarith

/-- The elementary Gaussian second-moment majorant `x e^{-x} ≤ e^{-1}`. -/
theorem sq_mul_exp_neg_mul_sq_le {B : ℝ} (hB : 0 < B) (v : ℝ) :
    v ^ 2 * Real.exp (-B * v ^ 2) ≤ 2 / (Real.exp 1 * B) * Real.exp (-(B / 2) * v ^ 2) := by
  have hx : B / 2 * v ^ 2 ≤ Real.exp (B / 2 * v ^ 2 - 1) := by
    have := Real.add_one_le_exp (B / 2 * v ^ 2 - 1)
    linarith
  have hkey : B / 2 * v ^ 2 * Real.exp (-(B / 2 * v ^ 2)) ≤ Real.exp (-1 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hx (Real.exp_pos (-(B / 2 * v ^ 2))).le
    rw [← Real.exp_add] at hmul
    have : B / 2 * v ^ 2 - 1 + -(B / 2 * v ^ 2) = -1 := by ring
    rwa [this] at hmul
  have hsplit : Real.exp (-B * v ^ 2)
      = Real.exp (-(B / 2 * v ^ 2)) * Real.exp (-(B / 2) * v ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, ← mul_assoc]
  have hpos : (0 : ℝ) < Real.exp (-(B / 2) * v ^ 2) := Real.exp_pos _
  refine mul_le_mul_of_nonneg_right ?_ hpos.le
  have hB2 : (0 : ℝ) < B / 2 := by linarith
  have hinv : v ^ 2 * Real.exp (-(B / 2 * v ^ 2))
      = (B / 2 * v ^ 2 * Real.exp (-(B / 2 * v ^ 2))) / (B / 2) := by
    field_simp
  rw [hinv, div_le_iff₀ hB2]
  have hexpneg : Real.exp (-1 : ℝ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    norm_num
  have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hval : Real.exp (-1 : ℝ) = 1 / Real.exp 1 := by
    rw [Real.exp_neg, one_div]
  calc B / 2 * v ^ 2 * Real.exp (-(B / 2 * v ^ 2)) ≤ Real.exp (-1 : ℝ) := hkey
    _ = 1 / Real.exp 1 := hval
    _ ≤ 2 / (Real.exp 1 * B) * (B / 2) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ he1 (by positivity)]
        ring_nf
        nlinarith [he1]

/-- The half-line Gaussian second moment is at most an explicit multiple of `B^{-3/2}`. -/
theorem integral_Ioi_sq_mul_exp_neg_mul_sq_le {B : ℝ} (hB : 0 < B) :
    (∫ v in Ioi (0 : ℝ), v ^ 2 * Real.exp (-B * v ^ 2))
      ≤ 2 / (Real.exp 1 * B) * (Real.sqrt (2 * Real.pi / B) / 2) := by
  have hB2 : (0 : ℝ) < B / 2 := by linarith
  have hleft : IntegrableOn (fun v : ℝ => v ^ 2 * Real.exp (-B * v ^ 2)) (Ioi 0) := by
    refine (Integrable.mono' (((integrable_exp_neg_mul_sq hB2).const_mul
      (2 / (Real.exp 1 * B))).integrableOn) ?_ ?_)
    · exact (by fun_prop : Continuous fun v : ℝ => v ^ 2 * Real.exp (-B * v ^ 2)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact sq_mul_exp_neg_mul_sq_le hB v
  have hright : IntegrableOn
      (fun v : ℝ => 2 / (Real.exp 1 * B) * Real.exp (-(B / 2) * v ^ 2)) (Ioi 0) :=
    ((integrable_exp_neg_mul_sq hB2).const_mul _).integrableOn
  have hmono : (∫ v in Ioi (0 : ℝ), v ^ 2 * Real.exp (-B * v ^ 2))
      ≤ ∫ v in Ioi (0 : ℝ), 2 / (Real.exp 1 * B) * Real.exp (-(B / 2) * v ^ 2) :=
    setIntegral_mono_on hleft hright measurableSet_Ioi
      fun v _ => sq_mul_exp_neg_mul_sq_le hB v
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_gaussian hB2]
  congr 2
  rw [div_div_eq_mul_div]
  ring_nf

/-! ## The Laplace profile -/

/-- The profile of the order-one Schläfli integral after the Laplace substitution. -/
noncomputable def besselLaplaceProfile (v : ℝ) : ℝ := (1 + v ^ 2) / Real.sqrt (2 + v ^ 2)

theorem sqrt_two_le_sqrt_two_add_sq (v : ℝ) : Real.sqrt 2 ≤ Real.sqrt (2 + v ^ 2) :=
  Real.sqrt_le_sqrt (by nlinarith [sq_nonneg v])

theorem besselLaplaceProfile_sub_nonneg (v : ℝ) :
    0 ≤ besselLaplaceProfile v - 1 / Real.sqrt 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt (2 + v ^ 2) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg v])
  have hsq : Real.sqrt (2 + v ^ 2) ^ 2 = 2 + v ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg v])
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrhs : (0 : ℝ) ≤ (1 + v ^ 2) * Real.sqrt 2 := by positivity
  have hsqle : (2 + v ^ 2) ≤ ((1 + v ^ 2) * Real.sqrt 2) ^ 2 := by
    rw [mul_pow, h2sq]
    nlinarith [sq_nonneg v, sq_nonneg (v ^ 2)]
  have hkey : Real.sqrt (2 + v ^ 2) ≤ (1 + v ^ 2) * Real.sqrt 2 := by
    nlinarith [hsq, hpos.le, hrhs, hsqle]
  rw [besselLaplaceProfile, sub_nonneg, div_le_div_iff₀ h2 hpos]
  linarith [hkey]

theorem besselLaplaceProfile_sub_le (v : ℝ) :
    besselLaplaceProfile v - 1 / Real.sqrt 2 ≤ v ^ 2 / Real.sqrt 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt (2 + v ^ 2) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg v])
  have hle : Real.sqrt 2 ≤ Real.sqrt (2 + v ^ 2) := sqrt_two_le_sqrt_two_add_sq v
  have hnum : (0 : ℝ) ≤ 1 + v ^ 2 := by nlinarith [sq_nonneg v]
  have hstep : besselLaplaceProfile v ≤ (1 + v ^ 2) / Real.sqrt 2 := by
    rw [besselLaplaceProfile]
    exact div_le_div_of_nonneg_left hnum h2 hle
  have hval : (1 + v ^ 2) / Real.sqrt 2 - 1 / Real.sqrt 2 = v ^ 2 / Real.sqrt 2 := by
    field_simp
    ring
  linarith [hstep, hval]

theorem abs_besselLaplaceProfile_sub_le (v : ℝ) :
    |besselLaplaceProfile v - 1 / Real.sqrt 2| ≤ v ^ 2 / Real.sqrt 2 := by
  rw [abs_of_nonneg (besselLaplaceProfile_sub_nonneg v)]
  exact besselLaplaceProfile_sub_le v


theorem continuous_besselLaplaceProfile : Continuous besselLaplaceProfile := by
  unfold besselLaplaceProfile
  refine Continuous.div (by fun_prop) (by fun_prop) fun v => ?_
  exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith [sq_nonneg v]))

theorem integrable_sq_mul_exp_neg_mul_sq {B : ℝ} (hB : 0 < B) :
    Integrable fun v : ℝ => v ^ 2 * Real.exp (-B * v ^ 2) := by
  have hB2 : (0 : ℝ) < B / 2 := by linarith
  refine Integrable.mono' ((integrable_exp_neg_mul_sq hB2).const_mul
    (2 / (Real.exp 1 * B))) ?_ ?_
  · exact (by fun_prop : Continuous fun v : ℝ => v ^ 2 * Real.exp (-B * v ^ 2)).aestronglyMeasurable
  · filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact sq_mul_exp_neg_mul_sq_le hB v

/-! ## The Laplace substitution -/

/-- The Laplace-substituted Schläfli integrand. -/
noncomputable def besselLaplaceKernel (w : ℂ) (v : ℝ) : ℂ :=
  Complex.exp (-w * (1 + (v : ℂ) ^ 2)) * ((2 * besselLaplaceProfile v : ℝ) : ℂ)

theorem continuous_besselLaplaceKernel (w : ℂ) : Continuous (besselLaplaceKernel w) := by
  unfold besselLaplaceKernel
  exact (by fun_prop : Continuous fun v : ℝ => Complex.exp (-w * (1 + (v : ℂ) ^ 2))).mul
    (Complex.continuous_ofReal.comp (continuous_const.mul continuous_besselLaplaceProfile))

theorem norm_besselLaplaceKernel (w : ℂ) (v : ℝ) :
    ‖besselLaplaceKernel w v‖
      = Real.exp (-(w.re * (1 + v ^ 2))) * (2 * besselLaplaceProfile v) := by
  have hprofile : 0 ≤ besselLaplaceProfile v := by
    have := besselLaplaceProfile_sub_nonneg v
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
    linarith [besselLaplaceProfile_sub_nonneg v]
  have hcast : (1 : ℂ) + (v : ℂ) ^ 2 = ((1 + v ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hre : (-w * ((1 + v ^ 2 : ℝ) : ℂ)).re = -(w.re * (1 + v ^ 2)) := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [besselLaplaceKernel, hcast, norm_mul, Complex.norm_exp, hre, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem integrable_besselLaplaceKernel {w : ℂ} (hw : 0 < w.re) :
    Integrable (besselLaplaceKernel w) := by
  set B : ℝ := w.re with hB
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hmaj : Integrable fun v : ℝ =>
      Real.exp (-B) * (2 / Real.sqrt 2) * (Real.exp (-B * v ^ 2) + v ^ 2 * Real.exp (-B * v ^ 2)) :=
    (((integrable_exp_neg_mul_sq hw).add (integrable_sq_mul_exp_neg_mul_sq hw)).const_mul _)
  refine Integrable.mono' hmaj (continuous_besselLaplaceKernel w).aestronglyMeasurable ?_
  filter_upwards with v
  rw [norm_besselLaplaceKernel]
  have hprofile : besselLaplaceProfile v ≤ (1 + v ^ 2) / Real.sqrt 2 := by
    have hle : Real.sqrt 2 ≤ Real.sqrt (2 + v ^ 2) := sqrt_two_le_sqrt_two_add_sq v
    rw [besselLaplaceProfile]
    exact div_le_div_of_nonneg_left (by nlinarith [sq_nonneg v]) h2 hle
  have hexp : Real.exp (-(B * (1 + v ^ 2))) = Real.exp (-B) * Real.exp (-B * v ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hstep : (2 : ℝ) * besselLaplaceProfile v ≤ 2 / Real.sqrt 2 * (1 + v ^ 2) := by
    have := mul_le_mul_of_nonneg_left hprofile (by norm_num : (0:ℝ) ≤ 2)
    calc (2 : ℝ) * besselLaplaceProfile v ≤ 2 * ((1 + v ^ 2) / Real.sqrt 2) := this
      _ = 2 / Real.sqrt 2 * (1 + v ^ 2) := by ring
  have hpos : (0 : ℝ) ≤ Real.exp (-B) * Real.exp (-B * v ^ 2) := by positivity
  calc Real.exp (-B) * Real.exp (-B * v ^ 2) * (2 * besselLaplaceProfile v)
      ≤ Real.exp (-B) * Real.exp (-B * v ^ 2) * (2 / Real.sqrt 2 * (1 + v ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep hpos
    _ = Real.exp (-B) * (2 / Real.sqrt 2)
        * (Real.exp (-B * v ^ 2) + v ^ 2 * Real.exp (-B * v ^ 2)) := by ring

theorem integrableOn_besselK1C_integrand {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-w * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ))
      (Ici 0) := by
  set X : ℝ := w.re with hX
  have hXpos : 0 < X := hw
  have hintmaj : IntegrableOn
      (fun t : ℝ => Real.exp (-X) * Real.exp (1 / (2 * X)) * Real.exp (-(X / 2) * (t - 1 / X) ^ 2))
      (Ici 0) :=
    ((integrable_exp_quadratic hXpos).const_mul _).integrableOn
  refine Integrable.mono' hintmaj ?_ ?_
  · have h1 : Measurable fun t : ℝ => Complex.exp (-w * Complex.cosh (t : ℂ)) := by fun_prop
    have h2 : Measurable fun t : ℝ => Complex.cosh (t : ℂ) := by fun_prop
    exact (h1.mul h2).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    rw [norm_besselK1C_integrand w t]
    have hlow : 1 + t ^ 2 / 2 ≤ Real.cosh t := one_add_sq_div_two_le_cosh ht0
    have hup : Real.cosh t ≤ Real.exp t := cosh_le_exp ht0
    have hexp1 : Real.exp (-(X * Real.cosh t)) ≤ Real.exp (-(X * (1 + t ^ 2 / 2))) := by
      apply Real.exp_le_exp.2
      nlinarith
    have hstep : Real.exp (-(X * Real.cosh t)) * Real.cosh t
        ≤ Real.exp (-(X * (1 + t ^ 2 / 2))) * Real.exp t :=
      mul_le_mul hexp1 hup (le_of_lt (Real.cosh_pos t)) (le_of_lt (Real.exp_pos _))
    refine le_trans hstep (le_of_eq ?_)
    rw [← Real.exp_add]
    exact exp_quadratic_eq hXpos t

/-- **The Laplace substitution.**  The order-one Schläfli integral is an exact Gaussian integral
against the profile `(1+v²)/√(2+v²)`. -/
theorem besselK1C_eq_integral_laplaceKernel {w : ℂ} (hw : 0 < w.re) :
    besselK1C w = ∫ v in Ioi (0 : ℝ), besselLaplaceKernel w v := by
  set f : ℝ → ℝ := fun t => Real.sqrt 2 * Real.sinh (t / 2) with hf
  set f' : ℝ → ℝ := fun t => Real.sqrt 2 * (Real.cosh (t / 2) * (1 / 2)) with hf'
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfcont : ContinuousOn f (Ici 0) := (by fun_prop : Continuous f).continuousOn
  have hhalfTop : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun t ht => by linarith⟩
  have hsinhTop : Tendsto (fun t : ℝ => Real.sinh (t / 2)) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ hhalfTop
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact Real.self_le_sinh_iff.2 (by linarith)
  have hft : Tendsto f atTop atTop := hsinhTop.const_mul_atTop h2
  have hff' : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt f (f' t) (Ioi t) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2 : ℝ) t := by
      simpa using (hasDerivAt_id t).div_const 2
    have h2' : HasDerivAt (fun s : ℝ => Real.sinh (s / 2)) (Real.cosh (t / 2) * (1 / 2)) t :=
      h1.sinh
    exact (h2'.const_mul (Real.sqrt 2)).hasDerivWithinAt
  have hgcont : ContinuousOn (besselLaplaceKernel w) (f '' Ioi 0) :=
    (continuous_besselLaplaceKernel w).continuousOn
  have hg1 : IntegrableOn (besselLaplaceKernel w) (f '' Ici 0) :=
    (integrable_besselLaplaceKernel hw).integrableOn
  have hpoint : ∀ t : ℝ, f' t • (besselLaplaceKernel w ∘ f) t
      = Complex.exp (-w * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ) := by
    intro t
    have hcosh2 : Real.cosh (t / 2) ^ 2 = (1 + Real.cosh t) / 2 := by
      have := Real.cosh_two_mul (t / 2)
      have hsq := Real.cosh_sq_sub_sinh_sq (t / 2)
      have hval : (2 : ℝ) * (t / 2) = t := by ring
      rw [hval] at this
      nlinarith [this, hsq]
    have hsinh2 : Real.sinh (t / 2) ^ 2 = (Real.cosh t - 1) / 2 := by
      have hsq := Real.cosh_sq_sub_sinh_sq (t / 2)
      nlinarith [hcosh2, hsq]
    have hfsq : f t ^ 2 = Real.cosh t - 1 := by
      rw [hf]
      simp only
      rw [mul_pow, h2sq, hsinh2]
      ring
    have hroot : Real.sqrt (2 + f t ^ 2) = Real.sqrt 2 * Real.cosh (t / 2) := by
      rw [hfsq, show (2 : ℝ) + (Real.cosh t - 1) = (Real.sqrt 2 * Real.cosh (t / 2)) ^ 2 by
        rw [mul_pow, h2sq, hcosh2]; ring]
      exact Real.sqrt_sq (by positivity)
    have hprofile : besselLaplaceProfile (f t)
        = Real.cosh t / (Real.sqrt 2 * Real.cosh (t / 2)) := by
      rw [besselLaplaceProfile, hroot, hfsq,
        show (1 : ℝ) + (Real.cosh t - 1) = Real.cosh t from by ring]
    have hcoshpos : (0 : ℝ) < Real.cosh (t / 2) := Real.cosh_pos _
    have hreal : f' t * (2 * besselLaplaceProfile (f t)) = Real.cosh t := by
      rw [hprofile, hf']
      simp only
      field_simp
    have harg : Complex.exp (-w * (1 + ((f t : ℝ) : ℂ) ^ 2))
        = Complex.exp (-w * Complex.cosh (t : ℂ)) := by
      congr 2
      rw [← Complex.ofReal_pow, hfsq, ← Complex.ofReal_cosh]
      push_cast
      ring
    show ((f' t : ℝ) : ℂ) * besselLaplaceKernel w (f t) = _
    rw [besselLaplaceKernel, harg,
      show ((f' t : ℝ) : ℂ)
          * (Complex.exp (-w * Complex.cosh (t : ℂ))
            * ((2 * besselLaplaceProfile (f t) : ℝ) : ℂ))
        = Complex.exp (-w * Complex.cosh (t : ℂ))
          * ((f' t * (2 * besselLaplaceProfile (f t)) : ℝ) : ℂ) from by push_cast; ring,
      hreal, Complex.ofReal_cosh]
  have hg2 : IntegrableOn (fun t => f' t • (besselLaplaceKernel w ∘ f) t) (Ici 0) := by
    refine (integrableOn_besselK1C_integrand hw).congr_fun ?_ measurableSet_Ici
    intro t _
    exact (hpoint t).symm
  have hsub := MeasureTheory.integral_deriv_smul_comp_Ioi hfcont hft hff' hgcont hg1 hg2
  have hf0 : f 0 = 0 := by rw [hf]; simp
  rw [hf0] at hsub
  rw [besselK1C, ← hsub]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => (hpoint t).symm


/-! ## The uniform asymptotic -/

/-- The half-line complex Gaussian integral. -/
theorem integral_Ioi_cexp_neg_mul_sq {w : ℂ} (hw : 0 < w.re) :
    (∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ) ^ 2))
      = ((Real.pi : ℂ) / w) ^ (1 / 2 : ℂ) / 2 := by
  have hint := integrable_cexp_neg_mul_sq hw
  have heven : ∀ v : ℝ, Complex.exp (-w * ((-v : ℝ) : ℂ) ^ 2) = Complex.exp (-w * (v : ℂ) ^ 2) := by
    intro v
    congr 2
    push_cast
    ring
  have hsplit := integral_even_eq_two_mul_complex hint heven
  rw [integral_gaussian_complex hw] at hsplit
  rw [hsplit]
  ring

/-- The exact leading/remainder split of the order-one Schläfli integral. -/
theorem besselK1C_sub_leading {w : ℂ} (hw : 0 < w.re) :
    besselK1C w
        - Complex.exp (-w) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / w) ^ (1 / 2 : ℂ)
      = 2 * Complex.exp (-w) * ∫ v in Ioi (0 : ℝ),
          Complex.exp (-w * (v : ℂ) ^ 2)
            * ((besselLaplaceProfile v - 1 / Real.sqrt 2 : ℝ) : ℂ) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  set B : ℝ := w.re with hB
  have hmain : IntegrableOn
      (fun v : ℝ => Complex.exp (-w * (v : ℂ) ^ 2) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) (Ioi 0) :=
    ((integrable_cexp_neg_mul_sq hw).mul_const _).integrableOn
  have hnormerr : ∀ v : ℝ,
      ‖Complex.exp (-w * (v : ℂ) ^ 2) * ((besselLaplaceProfile v - 1 / Real.sqrt 2 : ℝ) : ℂ)‖
        ≤ (Real.sqrt 2)⁻¹ * (v ^ 2 * Real.exp (-B * v ^ 2)) := by
    intro v
    have hre : (-w * (v : ℂ) ^ 2).re = -B * v ^ 2 := by
      rw [← Complex.ofReal_pow]
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, hB]
      ring
    rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs]
    have hbound := abs_besselLaplaceProfile_sub_le v
    have hpos : (0 : ℝ) < Real.exp (-B * v ^ 2) := Real.exp_pos _
    calc Real.exp (-B * v ^ 2) * |besselLaplaceProfile v - 1 / Real.sqrt 2|
        ≤ Real.exp (-B * v ^ 2) * (v ^ 2 / Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hbound hpos.le
      _ = (Real.sqrt 2)⁻¹ * (v ^ 2 * Real.exp (-B * v ^ 2)) := by
          rw [div_eq_mul_inv]
          ring
  have herr : IntegrableOn
      (fun v : ℝ => Complex.exp (-w * (v : ℂ) ^ 2)
        * ((besselLaplaceProfile v - 1 / Real.sqrt 2 : ℝ) : ℂ)) (Ioi 0) := by
    refine Integrable.mono' (((integrable_sq_mul_exp_neg_mul_sq hw).const_mul
      ((Real.sqrt 2)⁻¹)).integrableOn) ?_ ?_
    · exact ((by fun_prop : Continuous fun v : ℝ => Complex.exp (-w * (v : ℂ) ^ 2)).mul
        (Complex.continuous_ofReal.comp
          (continuous_besselLaplaceProfile.sub continuous_const))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
      exact hnormerr v
  have hsplitpoint : ∀ v : ℝ, besselLaplaceKernel w v
      = 2 * Complex.exp (-w) * (Complex.exp (-w * (v : ℂ) ^ 2) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ))
        + 2 * Complex.exp (-w) * (Complex.exp (-w * (v : ℂ) ^ 2)
            * ((besselLaplaceProfile v - 1 / Real.sqrt 2 : ℝ) : ℂ)) := by
    intro v
    rw [besselLaplaceKernel, show -w * (1 + (v : ℂ) ^ 2) = -w + -w * (v : ℂ) ^ 2 from by ring,
      Complex.exp_add]
    push_cast
    ring
  rw [besselK1C_eq_integral_laplaceKernel hw]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun v _ => hsplitpoint v)]
  rw [integral_add ((hmain.const_mul _)) ((herr.const_mul _)),
    integral_const_mul, integral_const_mul, MeasureTheory.integral_mul_const,
    integral_Ioi_cexp_neg_mul_sq hw]
  ring

/-- **The uniform large-argument asymptotic of the order-one Schläfli integral.**  On the open
right half plane the leading term carries the exact phase of the principal square root and the
remainder is smaller by one full power of the argument. -/
theorem norm_besselK1C_sub_leading_le {w : ℂ} (hw : 0 < w.re) :
    ‖besselK1C w
        - Complex.exp (-w) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / w) ^ (1 / 2 : ℂ)‖
      ≤ Real.exp (-w.re)
        * (Real.sqrt 2 / (Real.exp 1 * w.re) * Real.sqrt (2 * Real.pi / w.re)) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set B : ℝ := w.re with hB
  have hnormerr : ∀ v : ℝ,
      ‖Complex.exp (-w * (v : ℂ) ^ 2) * ((besselLaplaceProfile v - 1 / Real.sqrt 2 : ℝ) : ℂ)‖
        ≤ (Real.sqrt 2)⁻¹ * (v ^ 2 * Real.exp (-B * v ^ 2)) := by
    intro v
    have hre : (-w * (v : ℂ) ^ 2).re = -B * v ^ 2 := by
      rw [← Complex.ofReal_pow]
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, hB]
      ring
    rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs]
    have hbound := abs_besselLaplaceProfile_sub_le v
    have hpos : (0 : ℝ) < Real.exp (-B * v ^ 2) := Real.exp_pos _
    calc Real.exp (-B * v ^ 2) * |besselLaplaceProfile v - 1 / Real.sqrt 2|
        ≤ Real.exp (-B * v ^ 2) * (v ^ 2 / Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hbound hpos.le
      _ = (Real.sqrt 2)⁻¹ * (v ^ 2 * Real.exp (-B * v ^ 2)) := by
          rw [div_eq_mul_inv]
          ring
  have herr : IntegrableOn
      (fun v : ℝ => Complex.exp (-w * (v : ℂ) ^ 2)
        * ((besselLaplaceProfile v - 1 / Real.sqrt 2 : ℝ) : ℂ)) (Ioi 0) := by
    refine Integrable.mono' (((integrable_sq_mul_exp_neg_mul_sq hw).const_mul
      ((Real.sqrt 2)⁻¹)).integrableOn) ?_ ?_
    · exact ((by fun_prop : Continuous fun v : ℝ => Complex.exp (-w * (v : ℂ) ^ 2)).mul
        (Complex.continuous_ofReal.comp
          (continuous_besselLaplaceProfile.sub continuous_const))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
      exact hnormerr v
  rw [besselK1C_sub_leading hw, norm_mul, norm_mul, Complex.norm_exp]
  have hnormintegral : ‖∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ) ^ 2)
      * ((besselLaplaceProfile v - 1 / Real.sqrt 2 : ℝ) : ℂ)‖
      ≤ (Real.sqrt 2)⁻¹ * (2 / (Real.exp 1 * B) * (Real.sqrt (2 * Real.pi / B) / 2)) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_trans (setIntegral_mono_on herr.norm
      (((integrable_sq_mul_exp_neg_mul_sq hw).const_mul ((Real.sqrt 2)⁻¹)).integrableOn)
      measurableSet_Ioi fun v _ => hnormerr v) ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_Ioi_sq_mul_exp_neg_mul_sq_le hw) (by positivity)
  have hnegre : (-w).re = -B := by simp [hB]
  rw [hnegre]
  have hcoef : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hcoef]
  have hstep := mul_le_mul_of_nonneg_left hnormintegral
    (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-B))
  have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hval : (2 : ℝ) * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
    field_simp
    linarith [hmul]
  refine hstep.trans (le_of_eq ?_)
  calc 2 * Real.exp (-B)
        * ((Real.sqrt 2)⁻¹ * (2 / (Real.exp 1 * B) * (Real.sqrt (2 * Real.pi / B) / 2)))
      = Real.exp (-B)
        * (2 * (Real.sqrt 2)⁻¹ / (Real.exp 1 * B) * Real.sqrt (2 * Real.pi / B)) := by ring
    _ = Real.exp (-B)
        * (Real.sqrt 2 / (Real.exp 1 * B) * Real.sqrt (2 * Real.pi / B)) := by rw [hval]


/-- The Schläfli integrand is integrable on the whole line. -/
theorem integrable_besselK1C_integrand {w : ℂ} (hw : 0 < w.re) :
    Integrable fun t : ℝ => Complex.exp (-w * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ) := by
  set F : ℝ → ℂ := fun t => Complex.exp (-w * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ) with hF
  have hIci : IntegrableOn F (Ici (0 : ℝ)) := integrableOn_besselK1C_integrand hw
  have hIoi : IntegrableOn F (Ioi (0 : ℝ)) := hIci.mono_set Ioi_subset_Ici_self
  have hIciNeg : IntegrableOn F (Ici (-(0 : ℝ))) := by simpa only [neg_zero] using hIci
  have hcomp := hIciNeg.comp_neg_Iic (c := (0 : ℝ))
  have hIic : IntegrableOn F (Iic (0 : ℝ)) := by
    refine hcomp.congr (ae_of_all _ fun t => ?_)
    rw [hF]
    simp only
    rw [Complex.ofReal_neg, Complex.cosh_neg]
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

/-- The whole-line Schläfli integral is twice the half-line one. -/
theorem integral_cosh_mul_exp_neg_cosh {w : ℂ} (hw : 0 < w.re) :
    (∫ t : ℝ, Complex.exp (-w * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ))
      = 2 * besselK1C w := by
  have heven : ∀ t : ℝ,
      Complex.exp (-w * Complex.cosh ((-t : ℝ) : ℂ)) * Complex.cosh ((-t : ℝ) : ℂ)
        = Complex.exp (-w * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ) := by
    intro t
    rw [Complex.ofReal_neg, Complex.cosh_neg]
  rw [integral_even_eq_two_mul_complex (integrable_besselK1C_integrand hw) heven, besselK1C]

/-- The odd companion integral vanishes. -/
theorem integral_odd_eq_zero {f : ℝ → ℂ} (ho : ∀ x, f (-x) = -f x) :
    (∫ x : ℝ, f x) = 0 := by
  have hrefl := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (measurableEmbedding_neg (α := ℝ)) f Set.univ
  simp only [Set.preimage_univ, setIntegral_univ] at hrefl
  have hval : (∫ x : ℝ, f (-x)) = -∫ x : ℝ, f x := by
    rw [← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun x => ho x)
  rw [hval] at hrefl
  linear_combination -hrefl / 2


/-! ## A quadratic Gaussian majorant for the differentiated Schläfli kernel -/

theorem integrable_exp_neg_mul_sq_shift {c m : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ => Real.exp (-c * (t - m) ^ 2) :=
  (integrable_exp_neg_mul_sq hc).comp_sub_right m

/-- `cosh²` against a decaying exponential of `cosh` is dominated by a shifted Gaussian pair. -/
theorem cosh_sq_mul_exp_neg_mul_cosh_le {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    Real.cosh t ^ 2 * Real.exp (-(Y * Real.cosh t))
      ≤ Real.exp (-Y) * Real.exp (2 / Y)
        * (Real.exp (-(Y / 2) * (t - 2 / Y) ^ 2) + Real.exp (-(Y / 2) * (t + 2 / Y) ^ 2)) := by
  have key : ∀ x : ℝ, 0 ≤ x →
      Real.cosh x ^ 2 * Real.exp (-(Y * Real.cosh x))
        ≤ Real.exp (-Y) * Real.exp (2 / Y) * Real.exp (-(Y / 2) * (x - 2 / Y) ^ 2) := by
    intro x hx
    have hup : Real.cosh x ≤ Real.exp x := cosh_le_exp hx
    have hlow : 1 + x ^ 2 / 2 ≤ Real.cosh x := one_add_sq_div_two_le_cosh hx
    have hsq : Real.cosh x ^ 2 ≤ Real.exp (2 * x) := by
      have hpos : 0 < Real.cosh x := Real.cosh_pos x
      calc Real.cosh x ^ 2 ≤ Real.exp x ^ 2 := by nlinarith [hpos.le, Real.exp_pos x]
        _ = Real.exp (2 * x) := by
            rw [show (2 : ℝ) * x = x + x from by ring, Real.exp_add, sq]
    have hexp : Real.exp (-(Y * Real.cosh x)) ≤ Real.exp (-(Y * (1 + x ^ 2 / 2))) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith
    have hcomb : Real.cosh x ^ 2 * Real.exp (-(Y * Real.cosh x))
        ≤ Real.exp (2 * x) * Real.exp (-(Y * (1 + x ^ 2 / 2))) :=
      mul_le_mul hsq hexp (Real.exp_pos _).le (Real.exp_pos _).le
    refine hcomb.trans (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rcases le_total 0 t with ht | ht
  · have h1 := key t ht
    have h2 : (0 : ℝ) ≤ Real.exp (-Y) * Real.exp (2 / Y) * Real.exp (-(Y / 2) * (t + 2 / Y) ^ 2) :=
      by positivity
    nlinarith [h1, h2]
  · have h1 := key (-t) (by linarith)
    have hcosh : Real.cosh (-t) = Real.cosh t := Real.cosh_neg t
    rw [hcosh] at h1
    have hsq : (-t - 2 / Y) ^ 2 = (t + 2 / Y) ^ 2 := by ring
    rw [hsq] at h1
    have h2 : (0 : ℝ) ≤ Real.exp (-Y) * Real.exp (2 / Y) * Real.exp (-(Y / 2) * (t - 2 / Y) ^ 2) :=
      by positivity
    nlinarith [h1, h2]

theorem integrable_cosh_sq_mul_exp_neg_mul_cosh {Y : ℝ} (hY : 0 < Y) :
    Integrable fun t : ℝ => Real.cosh t ^ 2 * Real.exp (-(Y * Real.cosh t)) := by
  have hY2 : (0 : ℝ) < Y / 2 := by linarith
  have hmaj : Integrable fun t : ℝ =>
      Real.exp (-Y) * Real.exp (2 / Y)
        * (Real.exp (-(Y / 2) * (t - 2 / Y) ^ 2) + Real.exp (-(Y / 2) * (t + 2 / Y) ^ 2)) := by
    refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · exact integrable_exp_neg_mul_sq_shift hY2
    · have := integrable_exp_neg_mul_sq_shift (c := Y / 2) (m := -(2 / Y)) hY2
      exact this.congr (ae_of_all _ fun t => by ring_nf)
  refine Integrable.mono' hmaj ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.cosh t ^ 2 * Real.exp (-(Y * Real.cosh t))).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact cosh_sq_mul_exp_neg_mul_cosh_le hY t


/-! ## Holomorphy of the order-one Schläfli integral -/

theorem norm_cosh_ofReal (t : ℝ) : ‖Complex.cosh (t : ℂ)‖ = Real.cosh t := by
  rw [← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.cosh_pos t).le]

/-- **The Schläfli integral is complex differentiable on the right half plane.** -/
theorem hasDerivAt_besselK1C {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt besselK1C
      (∫ t in Ioi (0 : ℝ),
        -(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-w * Complex.cosh (t : ℂ))) w := by
  set X : ℝ := w.re with hX
  have hX2 : (0 : ℝ) < X / 2 := by linarith
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set F : ℂ → ℝ → ℂ := fun v t =>
    Complex.exp (-v * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ) with hF
  set F' : ℂ → ℝ → ℂ := fun v t =>
    -(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-v * Complex.cosh (t : ℂ)) with hF'
  set bound : ℝ → ℝ := fun t => Real.cosh t ^ 2 * Real.exp (-(X / 2 * Real.cosh t)) with hbound
  have hs : Metric.ball w (X / 2) ∈ nhds w := Metric.ball_mem_nhds w hX2
  have hmeas : ∀ᶠ v : ℂ in nhds w, AEStronglyMeasurable (F v) μ := by
    filter_upwards with v
    exact ((by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (-v * Complex.cosh (t : ℂ)) * Complex.cosh (t : ℂ))).aestronglyMeasurable
  have hint : Integrable (F w) μ := integrableOn_besselK1C_integrand hw |>.mono_set
    Ioi_subset_Ici_self
  have hmeas' : AEStronglyMeasurable (F' w) μ :=
    ((by fun_prop : Continuous fun t : ℝ =>
      -(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-w * Complex.cosh (t : ℂ)))).aestronglyMeasurable
  have hre : ∀ v : ℂ, v ∈ Metric.ball w (X / 2) → X / 2 < v.re := by
    intro v hv
    have hdist : ‖v - w‖ < X / 2 := by
      rw [← Complex.dist_eq]
      exact hv
    have : |v.re - w.re| ≤ ‖v - w‖ := by
      have := Complex.abs_re_le_norm (v - w)
      simpa [Complex.sub_re] using this
    have habs : |v.re - X| < X / 2 := by rw [hX]; linarith
    have := (abs_lt.1 habs).1
    linarith
  have hbnd : ∀ᵐ t ∂μ, ∀ v ∈ Metric.ball w (X / 2), ‖F' v t‖ ≤ bound t := by
    filter_upwards with t
    intro v hv
    have hvre := hre v hv
    rw [hF', hbound]
    simp only
    rw [norm_mul, norm_neg, norm_pow, norm_cosh_ofReal, Complex.norm_exp]
    have hrev : (-v * Complex.cosh (t : ℂ)).re = -(v.re * Real.cosh t) := by
      rw [← Complex.ofReal_cosh]
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [hrev]
    have hexp : Real.exp (-(v.re * Real.cosh t)) ≤ Real.exp (-(X / 2 * Real.cosh t)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [Real.cosh_pos t]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hboundint : Integrable bound μ := by
    rw [hbound]
    exact (integrable_cosh_sq_mul_exp_neg_mul_cosh hX2).integrableOn
  have hderiv : ∀ᵐ t ∂μ, ∀ v ∈ Metric.ball w (X / 2), HasDerivAt (fun z => F z t) (F' v t) v := by
    filter_upwards with t
    intro v _
    have hbase : HasDerivAt (fun z : ℂ => -z * Complex.cosh (t : ℂ))
        (-Complex.cosh (t : ℂ)) v := by
      simpa using ((hasDerivAt_id v).neg.mul_const (Complex.cosh (t : ℂ)))
    have hexp := hbase.cexp
    have hmul := hexp.mul_const (Complex.cosh (t : ℂ))
    rw [hF, hF']
    simp only
    have heq : Complex.exp (-v * Complex.cosh (t : ℂ)) * -Complex.cosh (t : ℂ)
          * Complex.cosh (t : ℂ)
        = -(Complex.cosh (t : ℂ)) ^ 2 * Complex.exp (-v * Complex.cosh (t : ℂ)) := by ring
    rw [← heq]
    exact hmul
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := w)
    (F := F) (F' := F') (bound := bound) (s := Metric.ball w (X / 2))
    hs hmeas hint hmeas' hbnd hboundint hderiv
  have hbessel : (fun v : ℂ => ∫ t, F v t ∂μ) = besselK1C := by
    funext v
    rw [besselK1C, hμ, hF]
  rw [hbessel] at hmain
  exact hmain.2

theorem differentiableAt_besselK1C {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ besselK1C w :=
  (hasDerivAt_besselK1C hw).differentiableAt


/-! ## The asymptotic in principal-square-root form -/

theorem re_ofReal_div_pos {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    0 < ((c : ℂ) / w).re := by
  have hne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have hns : 0 < Complex.normSq w := by
    simpa using Complex.normSq_pos.2 hne
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  positivity

/-- The leading term of the Schläfli asymptotic in principal-square-root form. -/
theorem besselK1C_sub_leading_csqrt {w : ℂ} (hw : 0 < w.re) :
    besselK1C w
        - Complex.exp (-w) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * csqrt ((Real.pi : ℂ) / w)
      = 2 * Complex.exp (-w) * ∫ v in Ioi (0 : ℝ),
          Complex.exp (-w * (v : ℂ) ^ 2)
            * ((besselLaplaceProfile v - 1 / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [csqrt_eq_cpow_half (re_ofReal_div_pos hw Real.pi_pos)]
  exact besselK1C_sub_leading hw

theorem norm_besselK1C_sub_leading_csqrt_le {w : ℂ} (hw : 0 < w.re) :
    ‖besselK1C w
        - Complex.exp (-w) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * csqrt ((Real.pi : ℂ) / w)‖
      ≤ Real.exp (-w.re)
        * (Real.sqrt 2 / (Real.exp 1 * w.re) * Real.sqrt (2 * Real.pi / w.re)) := by
  rw [csqrt_eq_cpow_half (re_ofReal_div_pos hw Real.pi_pos)]
  exact norm_besselK1C_sub_leading_le hw

end HTGeometry
