import GaloisForLFunctions.HTGeometry.GammaVerticalDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Subtracted charged radial Gamma factor

The external-leg arguments at the FZZ-P receiver include real part `-3/2`. The ordinary Euler
integral diverges there. This module proves an explicit convergent prescription instead:

`integral_0^infinity t^(-5/2+i*y)*(exp(-t)-1+t) dt = Gamma(-3/2+i*y)`.

The remainder is positive for positive `t`. Logarithmic coordinates give integrable exponential
bounds at both ends. Two integrations by parts, with integrability of every product proved,
reduce the integral to the ordinary Gamma integral at real part `1/2`. The original radial cutoff
also has an exact counterterm identity. With `s=-3/2+i*y`, adding
`exp(-s*R)/s - exp(-(s+1)*R)/(s+1)` to its integral on `x>-R` tends to `Gamma(s)`.

For positive coupling and slope, write `A=exp(u)` and `b=exp(v)`. The original charged subtracted
radial integral retains the full normalization `exp(-s*u)*Gamma(s)/b`, where `s=-3/2+i*p/b`.
Its logarithmic coupling response equals `-s` and has real part `3/2` at every momentum, so this
charged factor is never coupling-stationary. No vanishing source equation is assumed.

These are exact source-factor and cutoff-prescription theorems. They do not identify the
subtractions with the complete CFT counterterm, match the physical external momentum, evaluate
nonzero modes or produce the integrated mixed replica Ward identity required for RH.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace GaloisForLFunctions.RHTower
noncomputable section

def fzzExpSecondRemainder (t : ℝ) : ℝ := Real.exp (-t) - 1 + t

private theorem remainder_nonneg (t : ℝ) : 0 ≤ fzzExpSecondRemainder t := by
  have h := Real.add_one_le_exp (-t)
  unfold fzzExpSecondRemainder
  linarith

private theorem remainder_le (t : ℝ) (ht : 0 ≤ t) : fzzExpSecondRemainder t ≤ t := by
  have h : Real.exp (-t) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr ht)
  unfold fzzExpSecondRemainder
  linarith

private theorem remainder_le_sq (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    fzzExpSecondRemainder t ≤ t^2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (x := -t) (by
    simpa only [norm_neg, Real.norm_eq_abs, abs_of_nonneg ht] using ht1)
  have hn : 0 ≤ Real.exp (-t) - 1 + t := remainder_nonneg t
  rw [sub_neg_eq_add, Real.norm_eq_abs,
    abs_of_nonneg hn, norm_neg, Real.norm_eq_abs, abs_of_nonneg ht] at h
  exact h

private theorem one_sub_exp_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ 1-Real.exp (-t) := by
  have h : Real.exp (-t) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr ht)
  linarith

private theorem one_sub_exp_le (t : ℝ) : 1-Real.exp (-t) ≤ t := by
  have h := Real.add_one_le_exp (-t)
  linarith

def fzzSubtractedGammaLogKernel (x : ℝ) : ℝ :=
  Real.exp ((-3/2:ℝ)*x) * fzzExpSecondRemainder (Real.exp x)

def fzzFirstSubtractedGammaLogKernel (x : ℝ) : ℝ :=
  Real.exp ((-1/2:ℝ)*x) * (1-Real.exp (-Real.exp x))

theorem fzzSubtractedGammaLogKernel_nonneg (x : ℝ) :
    0 ≤ fzzSubtractedGammaLogKernel x :=
  mul_nonneg (Real.exp_pos _).le (remainder_nonneg _)

theorem fzzFirstSubtractedGammaLogKernel_nonneg (x : ℝ) :
    0 ≤ fzzFirstSubtractedGammaLogKernel x :=
  mul_nonneg (Real.exp_pos _).le (one_sub_exp_nonneg _ (Real.exp_pos x).le)

private theorem second_left_bound (x : ℝ) (hx : x ≤ 0) :
    fzzSubtractedGammaLogKernel x ≤ Real.exp ((1/2:ℝ)*x) := by
  have ht1 : Real.exp x ≤ 1 := by simpa using Real.exp_le_exp.mpr hx
  calc
    _ ≤ Real.exp ((-3/2:ℝ)*x) * (Real.exp x)^2 :=
      mul_le_mul_of_nonneg_left (remainder_le_sq _ (Real.exp_pos x).le ht1) (Real.exp_pos _).le
    _ = Real.exp ((1/2:ℝ)*x) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

private theorem second_right_bound (x : ℝ) :
    fzzSubtractedGammaLogKernel x ≤ Real.exp ((-1/2:ℝ)*x) := by
  calc
    _ ≤ Real.exp ((-3/2:ℝ)*x) * Real.exp x :=
      mul_le_mul_of_nonneg_left (remainder_le _ (Real.exp_pos x).le) (Real.exp_pos _).le
    _ = Real.exp ((-1/2:ℝ)*x) := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem first_left_bound (x : ℝ) :
    fzzFirstSubtractedGammaLogKernel x ≤ Real.exp ((1/2:ℝ)*x) := by
  calc
    _ ≤ Real.exp ((-1/2:ℝ)*x) * Real.exp x :=
      mul_le_mul_of_nonneg_left (one_sub_exp_le _) (Real.exp_pos _).le
    _ = Real.exp ((1/2:ℝ)*x) := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem first_right_bound (x : ℝ) :
    fzzFirstSubtractedGammaLogKernel x ≤ Real.exp ((-1/2:ℝ)*x) := by
  have h : 1-Real.exp (-Real.exp x) ≤ 1 := by linarith [Real.exp_pos (-Real.exp x)]
  simpa only [fzzFirstSubtractedGammaLogKernel, mul_one] using
    mul_le_mul_of_nonneg_left h (Real.exp_pos ((-1/2:ℝ)*x)).le

private theorem integrable_of_two_exp_bounds (f : ℝ → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 ≤ f x) (hl : ∀ x ≤ 0, f x ≤ Real.exp ((1/2:ℝ)*x))
    (hr : ∀ x, f x ≤ Real.exp ((-1/2:ℝ)*x)) : Integrable f := by
  have hleft : IntegrableOn f (Iic (0:ℝ)) := by
    refine (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<1/2) 0).mono'
      hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos x)] using hl x hx
  have hright : IntegrableOn f (Ioi (0:ℝ)) := by
    refine (integrableOn_exp_mul_Ioi (by norm_num : (-1/2:ℝ)<0) 0).mono'
      hf.aestronglyMeasurable ?_
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos x)] using hr x
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ)), integrableOn_union]
  exact ⟨hleft, hright⟩

theorem integrable_fzzSubtractedGammaLogKernel : Integrable fzzSubtractedGammaLogKernel := by
  exact integrable_of_two_exp_bounds _ (by unfold fzzSubtractedGammaLogKernel fzzExpSecondRemainder; fun_prop)
    fzzSubtractedGammaLogKernel_nonneg second_left_bound second_right_bound

theorem integrable_fzzFirstSubtractedGammaLogKernel : Integrable fzzFirstSubtractedGammaLogKernel := by
  exact integrable_of_two_exp_bounds _ (by unfold fzzFirstSubtractedGammaLogKernel; fun_prop)
    fzzFirstSubtractedGammaLogKernel_nonneg (fun x _ => first_left_bound x) first_right_bound

private def phaseExp (a y x : ℝ) : ℂ := Complex.exp (((a:ℂ)+(y:ℂ)*Complex.I)*(x:ℂ))

private theorem phaseExp_split (a y x : ℝ) : phaseExp a y x =
    (Real.exp (a*x):ℂ)*Complex.exp (((y*x:ℝ):ℂ)*Complex.I) := by
  rw [phaseExp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phaseExp_mul_exp (a y x : ℝ) :
    phaseExp a y x * (Real.exp x:ℂ) = phaseExp (a+1) y x := by
  rw [phaseExp, phaseExp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phaseExp_deriv (a y x : ℝ) :
    HasDerivAt (phaseExp a y) (phaseExp a y x * ((a:ℂ)+(y:ℂ)*Complex.I)) x := by
  change HasDerivAt (fun x : ℝ => Complex.exp (((a:ℂ)+(y:ℂ)*Complex.I)*(x:ℂ))) _ x
  simpa only [phaseExp, Complex.ofReal_one, mul_one, id_eq] using
    (((hasDerivAt_id x).ofReal_comp).const_mul ((a:ℂ)+(y:ℂ)*Complex.I)).cexp

private theorem integrable_character (f : ℝ → ℝ) (hf : Integrable f)
    (hc : Continuous f) (y : ℝ) :
    Integrable (fun x : ℝ => (f x:ℂ)*Complex.exp (((y*x:ℝ):ℂ)*Complex.I)) := by
  refine hf.norm.mono' (by fun_prop) ?_
  filter_upwards with x
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]

private def secondIntegrand (y x : ℝ) : ℂ :=
  phaseExp (-3/2) y x * (fzzExpSecondRemainder (Real.exp x):ℂ)

private def firstIntegrand (y x : ℝ) : ℂ :=
  phaseExp (-1/2) y x * ((1-Real.exp (-Real.exp x):ℝ):ℂ)

private def zeroIntegrand (y x : ℝ) : ℂ :=
  phaseExp (1/2) y x * (Real.exp (-Real.exp x):ℂ)

private theorem secondIntegrand_eq (y x : ℝ) : secondIntegrand y x =
    (fzzSubtractedGammaLogKernel x:ℂ)*Complex.exp (((y*x:ℝ):ℂ)*Complex.I) := by
  simp only [secondIntegrand, phaseExp_split, fzzSubtractedGammaLogKernel, Complex.ofReal_mul]
  ring

private theorem firstIntegrand_eq (y x : ℝ) : firstIntegrand y x =
    (fzzFirstSubtractedGammaLogKernel x:ℂ)*Complex.exp (((y*x:ℝ):ℂ)*Complex.I) := by
  simp only [firstIntegrand, phaseExp_split, fzzFirstSubtractedGammaLogKernel, Complex.ofReal_mul]
  ring

private theorem integrable_second (y : ℝ) : Integrable (secondIntegrand y) := by
  simp_rw [show secondIntegrand y = fun x => (fzzSubtractedGammaLogKernel x:ℂ)*
    Complex.exp (((y*x:ℝ):ℂ)*Complex.I) from funext (secondIntegrand_eq y)]
  exact integrable_character _ integrable_fzzSubtractedGammaLogKernel
    (by unfold fzzSubtractedGammaLogKernel fzzExpSecondRemainder; fun_prop) y

private theorem integrable_first (y : ℝ) : Integrable (firstIntegrand y) := by
  simp_rw [show firstIntegrand y = fun x => (fzzFirstSubtractedGammaLogKernel x:ℂ)*
    Complex.exp (((y*x:ℝ):ℂ)*Complex.I) from funext (firstIntegrand_eq y)]
  exact integrable_character _ integrable_fzzFirstSubtractedGammaLogKernel
    (by unfold fzzFirstSubtractedGammaLogKernel; fun_prop) y

private theorem integral_zero (y : ℝ) :
    (∫ x : ℝ, zeroIntegrand y x) = Complex.Gamma ((1/2:ℂ)+(y:ℂ)*Complex.I) := by
  have hg := GaloisForLFunctions.Gamma_vertical_eq_fourier (σ := (1/2:ℝ)) (by norm_num) y
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hg
  rw [hg]
  apply integral_congr_ae
  filter_upwards with x
  rw [zeroIntegrand, phaseExp_split, Real.exp_sub]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Real.exp_neg, Complex.ofReal_inv]
  norm_num
  ring

private theorem integrable_zero (y : ℝ) : Integrable (zeroIntegrand y) := by
  by_contra h
  have hg := integral_zero y
  rw [integral_undef h] at hg
  exact (Complex.Gamma_ne_zero_of_re_pos (s := (1/2:ℂ)+(y:ℂ)*Complex.I)
    (by norm_num)).symm hg

private theorem remainder_exp_deriv (x : ℝ) :
    HasDerivAt (fun x : ℝ => (fzzExpSecondRemainder (Real.exp x):ℂ))
      ((Real.exp x * (1-Real.exp (-Real.exp x)):ℝ):ℂ) x := by
  have h := (((Real.hasDerivAt_exp x).neg.exp).sub_const 1).add (Real.hasDerivAt_exp x)
  simp only [Pi.neg_apply] at h
  have he : Real.exp (-Real.exp x) * -Real.exp x + Real.exp x =
      Real.exp x * (1-Real.exp (-Real.exp x)) := by ring
  rw [he] at h
  simpa only [Pi.neg_apply, Pi.add_apply, fzzExpSecondRemainder] using h.ofReal_comp

private theorem first_remainder_exp_deriv (x : ℝ) :
    HasDerivAt (fun x : ℝ => ((1-Real.exp (-Real.exp x):ℝ):ℂ))
      ((Real.exp x * Real.exp (-Real.exp x):ℝ):ℂ) x := by
  have h := ((Real.hasDerivAt_exp x).neg.exp).const_sub 1
  simp only [Pi.neg_apply] at h
  have he : -(Real.exp (-Real.exp x) * -Real.exp x) =
      Real.exp x * Real.exp (-Real.exp x) := by ring
  rw [he] at h
  simpa only [Pi.neg_apply] using h.ofReal_comp

private theorem first_ibp (y : ℝ) :
    (∫ x : ℝ, firstIntegrand y x) =
      -((-3/2:ℂ)+(y:ℂ)*Complex.I) * (∫ x : ℝ, secondIntegrand y x) := by
  have he (x : ℝ) : phaseExp (-3/2) y x *
      ((Real.exp x * (1-Real.exp (-Real.exp x)):ℝ):ℂ) = firstIntegrand y x := by
    rw [Complex.ofReal_mul, ← mul_assoc, phaseExp_mul_exp]
    norm_num [firstIntegrand]
  have he' (x : ℝ) : (phaseExp (-3/2) y x * ((-3/2:ℂ)+(y:ℂ)*Complex.I)) *
      (fzzExpSecondRemainder (Real.exp x):ℂ) =
      ((-3/2:ℂ)+(y:ℂ)*Complex.I) * secondIntegrand y x := by
    unfold secondIntegrand
    ring
  have hi : Integrable (fun x => phaseExp (-3/2) y x *
      ((Real.exp x * (1-Real.exp (-Real.exp x)):ℝ):ℂ)) := by
    simpa only [he] using integrable_first y
  have hi' : Integrable (fun x => (phaseExp (-3/2) y x * ((-3/2:ℂ)+(y:ℂ)*Complex.I)) *
      (fzzExpSecondRemainder (Real.exp x):ℂ)) := by
    simpa only [he'] using (integrable_second y).const_mul ((-3/2:ℂ)+(y:ℂ)*Complex.I)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := phaseExp (-3/2) y)
    (u' := fun x => phaseExp (-3/2) y x * ((-3/2:ℂ)+(y:ℂ)*Complex.I))
    (v := fun x => (fzzExpSecondRemainder (Real.exp x):ℂ))
    (v' := fun x => ((Real.exp x * (1-Real.exp (-Real.exp x)):ℝ):ℂ))
    (fun x _ => by simpa using phaseExp_deriv (-3/2) y x)
    (fun x _ => remainder_exp_deriv x) hi hi' (integrable_second y)
  simpa only [he, he', integral_const_mul, neg_mul] using h

private theorem second_ibp (y : ℝ) :
    (∫ x : ℝ, zeroIntegrand y x) =
      -((-1/2:ℂ)+(y:ℂ)*Complex.I) * (∫ x : ℝ, firstIntegrand y x) := by
  have he (x : ℝ) : phaseExp (-1/2) y x *
      ((Real.exp x * Real.exp (-Real.exp x):ℝ):ℂ) = zeroIntegrand y x := by
    rw [Complex.ofReal_mul, ← mul_assoc, phaseExp_mul_exp]
    norm_num [zeroIntegrand]
  have he' (x : ℝ) : (phaseExp (-1/2) y x * ((-1/2:ℂ)+(y:ℂ)*Complex.I)) *
      ((1-Real.exp (-Real.exp x):ℝ):ℂ) =
      ((-1/2:ℂ)+(y:ℂ)*Complex.I) * firstIntegrand y x := by
    unfold firstIntegrand
    ring
  have hi : Integrable (fun x => phaseExp (-1/2) y x *
      ((Real.exp x * Real.exp (-Real.exp x):ℝ):ℂ)) := by
    simpa only [he] using integrable_zero y
  have hi' : Integrable (fun x => (phaseExp (-1/2) y x * ((-1/2:ℂ)+(y:ℂ)*Complex.I)) *
      ((1-Real.exp (-Real.exp x):ℝ):ℂ)) := by
    simpa only [he'] using (integrable_first y).const_mul ((-1/2:ℂ)+(y:ℂ)*Complex.I)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := phaseExp (-1/2) y)
    (u' := fun x => phaseExp (-1/2) y x * ((-1/2:ℂ)+(y:ℂ)*Complex.I))
    (v := fun x => ((1-Real.exp (-Real.exp x):ℝ):ℂ))
    (v' := fun x => ((Real.exp x * Real.exp (-Real.exp x):ℝ):ℂ))
    (fun x _ => by simpa using phaseExp_deriv (-1/2) y x)
    (fun x _ => first_remainder_exp_deriv x) hi hi' (integrable_first y)
  simpa only [he, he', integral_const_mul, neg_mul] using h

private theorem second_integral_eq_gamma (y : ℝ) :
    (∫ x : ℝ, secondIntegrand y x) = Complex.Gamma ((-3/2:ℂ)+(y:ℂ)*Complex.I) := by
  have hs : ((-3/2:ℂ)+(y:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hs1 : ((-1/2:ℂ)+(y:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hg0 := Complex.Gamma_add_one _ hs
  have hg1 := Complex.Gamma_add_one _ hs1
  have he0 : ((-3/2:ℂ)+(y:ℂ)*Complex.I)+1 = (-1/2:ℂ)+(y:ℂ)*Complex.I := by ring
  have he1 : ((-1/2:ℂ)+(y:ℂ)*Complex.I)+1 = (1/2:ℂ)+(y:ℂ)*Complex.I := by ring
  rw [he0] at hg0
  rw [he1, hg0] at hg1
  have h := second_ibp y
  rw [integral_zero, first_ibp, hg1] at h
  simp only [neg_mul, mul_neg, neg_neg] at h
  apply mul_left_cancel₀ hs
  apply mul_left_cancel₀ hs1
  simpa only [mul_assoc] using h.symm

theorem fzzSubtractedGammaLogKernel_fourier (y : ℝ) :
    (∫ x : ℝ, (fzzSubtractedGammaLogKernel x:ℂ)*
      Complex.exp (((y*x:ℝ):ℂ)*Complex.I)) =
        Complex.Gamma ((-3/2:ℂ)+(y:ℂ)*Complex.I) := by
  simpa only [secondIntegrand_eq] using second_integral_eq_gamma y

def fzzSubtractedGammaRayIntegrand (y t : ℝ) : ℂ :=
  (t:ℂ)^((-5/2:ℂ)+(y:ℂ)*Complex.I) * (fzzExpSecondRemainder t:ℂ)

private theorem ray_pullback (y x : ℝ) :
    |Real.exp x| • fzzSubtractedGammaRayIntegrand y (Real.exp x) =
      secondIntegrand y x := by
  rw [abs_of_pos (Real.exp_pos x), Complex.real_smul, fzzSubtractedGammaRayIntegrand,
    GaloisForLFunctions.cpow_ofReal_exp, ← mul_assoc, Complex.ofReal_exp,
    ← Complex.exp_add, secondIntegrand, phaseExp]
  congr 2
  push_cast
  ring

theorem integrableOn_fzzSubtractedGammaRayIntegrand (y : ℝ) :
    IntegrableOn (fzzSubtractedGammaRayIntegrand y) (Ioi (0:ℝ)) := by
  rw [← Real.range_exp, ← Set.image_univ,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    integrableOn_univ]
  simpa only [ray_pullback] using integrable_second y

theorem fzzSubtractedGammaRayIntegral_eq_gamma (y : ℝ) :
    (∫ t in Ioi (0:ℝ), fzzSubtractedGammaRayIntegrand y t) =
      Complex.Gamma ((-3/2:ℂ)+(y:ℂ)*Complex.I) := by
  rw [← Real.range_exp, ← Set.image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    setIntegral_univ]
  simpa only [ray_pullback] using second_integral_eq_gamma y

theorem fzzSubtractedGammaLogKernel_pos (x : ℝ) :
    0 < fzzSubtractedGammaLogKernel x := by
  apply mul_pos (Real.exp_pos _)
  have h := Real.add_one_lt_exp (neg_ne_zero.mpr (Real.exp_ne_zero x))
  unfold fzzExpSecondRemainder
  linarith

private theorem gamma_negative_half_ne_zero (y : ℝ) :
    Complex.Gamma ((-3/2:ℂ)+(y:ℂ)*Complex.I) ≠ 0 := by
  have hs : ((-3/2:ℂ)+(y:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hs1 : ((-1/2:ℂ)+(y:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hg0 := Complex.Gamma_add_one _ hs
  have hg1 := Complex.Gamma_add_one _ hs1
  have he0 : ((-3/2:ℂ)+(y:ℂ)*Complex.I)+1 = (-1/2:ℂ)+(y:ℂ)*Complex.I := by ring
  have he1 : ((-1/2:ℂ)+(y:ℂ)*Complex.I)+1 = (1/2:ℂ)+(y:ℂ)*Complex.I := by ring
  rw [he0] at hg0
  rw [he1, hg0] at hg1
  intro h
  rw [h, mul_zero, mul_zero] at hg1
  exact Complex.Gamma_ne_zero_of_re_pos (by norm_num) hg1

def fzzSubtractedRadialCharge (v p : ℝ) : ℂ :=
  (-3/2:ℂ) + ((p/Real.exp v:ℝ):ℂ)*Complex.I

def fzzSubtractedChargedRadialIntegrand (u v p x : ℝ) : ℂ :=
  Complex.exp (fzzSubtractedRadialCharge v p * ((Real.exp v*x:ℝ):ℂ)) *
    (fzzExpSecondRemainder (Real.exp (u+Real.exp v*x)):ℂ)

def fzzSubtractedChargedRadialIntegral (u v p : ℝ) : ℂ :=
  ∫ x : ℝ, fzzSubtractedChargedRadialIntegrand u v p x

private theorem charged_pullback (u v p x : ℝ) :
    fzzSubtractedChargedRadialIntegrand u v p x =
      Complex.exp (-fzzSubtractedRadialCharge v p*(u:ℂ)) *
        secondIntegrand (p/Real.exp v) (u+Real.exp v*x) := by
  unfold fzzSubtractedChargedRadialIntegrand secondIntegrand phaseExp fzzSubtractedRadialCharge
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem fzzSubtractedChargedRadialIntegral_eq (u v p : ℝ) :
    fzzSubtractedChargedRadialIntegral u v p =
      Complex.exp (-fzzSubtractedRadialCharge v p*(u:ℂ)) *
        Complex.Gamma (fzzSubtractedRadialCharge v p) / (Real.exp v:ℂ) := by
  unfold fzzSubtractedChargedRadialIntegral
  simp_rw [charged_pullback]
  rw [integral_const_mul]
  have h := Measure.integral_comp_mul_left (fun x => secondIntegrand (p/Real.exp v) (u+x))
    (Real.exp v)
  rw [integral_add_left_eq_self, abs_of_pos (inv_pos.mpr (Real.exp_pos v)),
    Complex.real_smul, Complex.ofReal_inv, second_integral_eq_gamma] at h
  rw [h]
  unfold fzzSubtractedRadialCharge
  ring

theorem fzzSubtractedChargedRadialIntegral_ne_zero (u v p : ℝ) :
    fzzSubtractedChargedRadialIntegral u v p ≠ 0 := by
  rw [fzzSubtractedChargedRadialIntegral_eq]
  exact div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _)
    (gamma_negative_half_ne_zero (p/Real.exp v))) (by exact_mod_cast Real.exp_ne_zero v)

theorem integrable_fzzSubtractedChargedRadialIntegrand (u v p : ℝ) :
    Integrable (fzzSubtractedChargedRadialIntegrand u v p) := by
  by_contra h
  exact fzzSubtractedChargedRadialIntegral_ne_zero u v p (integral_undef h)

theorem hasDerivAt_fzzSubtractedChargedRadialIntegral_logCoupling (u v p : ℝ) :
    HasDerivAt (fun a => fzzSubtractedChargedRadialIntegral a v p)
      (-fzzSubtractedRadialCharge v p * fzzSubtractedChargedRadialIntegral u v p) u := by
  have h := ((((hasDerivAt_id u).ofReal_comp).const_mul
    (-fzzSubtractedRadialCharge v p)).cexp).mul_const
      (Complex.Gamma (fzzSubtractedRadialCharge v p) / (Real.exp v:ℂ))
  simpa only [fzzSubtractedChargedRadialIntegral_eq, div_eq_mul_inv,
    Complex.ofReal_one, mul_one, one_mul, id_eq, mul_comm, mul_left_comm, mul_assoc] using h

theorem fzzSubtractedChargedRadialIntegral_couplingWard (u v p : ℝ) :
    deriv (fun a => fzzSubtractedChargedRadialIntegral a v p) u /
      fzzSubtractedChargedRadialIntegral u v p = -fzzSubtractedRadialCharge v p := by
  rw [(hasDerivAt_fzzSubtractedChargedRadialIntegral_logCoupling u v p).deriv,
    mul_div_cancel_right₀ _ (fzzSubtractedChargedRadialIntegral_ne_zero u v p)]

theorem fzzSubtractedChargedRadialIntegral_couplingWard_re (u v p : ℝ) :
    (deriv (fun a => fzzSubtractedChargedRadialIntegral a v p) u /
      fzzSubtractedChargedRadialIntegral u v p).re = 3/2 := by
  rw [fzzSubtractedChargedRadialIntegral_couplingWard]
  unfold fzzSubtractedRadialCharge
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  norm_num

theorem fzzSubtractedChargedRadialIntegral_coupling_deriv_ne_zero (u v p : ℝ) :
    deriv (fun a => fzzSubtractedChargedRadialIntegral a v p) u ≠ 0 := by
  intro h
  have hw := fzzSubtractedChargedRadialIntegral_couplingWard_re u v p
  rw [h, zero_div, Complex.zero_re] at hw
  norm_num at hw

def fzzNegativeChargedRadialCutoff (y R : ℝ) : ℂ :=
  ∫ x in Ioi (-R), phaseExp (-3/2) y x * (Real.exp (-Real.exp x):ℂ)

def fzzNegativeChargedRadialCounterterms (y R : ℝ) : ℂ :=
  Complex.exp (-((-3/2:ℂ)+(y:ℂ)*Complex.I)*(R:ℂ)) /
      ((-3/2:ℂ)+(y:ℂ)*Complex.I) -
    Complex.exp (-((-1/2:ℂ)+(y:ℂ)*Complex.I)*(R:ℂ)) /
      ((-1/2:ℂ)+(y:ℂ)*Complex.I)

private theorem phaseExp_norm (a y x : ℝ) : ‖phaseExp a y x‖ = Real.exp (a*x) := by
  rw [phaseExp, Complex.norm_exp]
  congr 1
  simp

private theorem integrable_cutoff (y R : ℝ) :
    IntegrableOn (fun x => phaseExp (-3/2) y x * (Real.exp (-Real.exp x):ℂ)) (Ioi (-R)) := by
  refine (integrableOn_exp_mul_Ioi (by norm_num : (-3/2:ℝ)<0) (-R)).mono'
    (by unfold phaseExp; fun_prop) ?_
  filter_upwards with x
  rw [norm_mul, phaseExp_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have h : Real.exp (-Real.exp x) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (Real.exp_pos x).le)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

theorem fzzNegativeChargedRadialCutoff_counterterms_eq (y R : ℝ) :
    fzzNegativeChargedRadialCutoff y R + fzzNegativeChargedRadialCounterterms y R =
      ∫ x in Ioi (-R), (fzzSubtractedGammaLogKernel x:ℂ)*
        Complex.exp (((y*x:ℝ):ℂ)*Complex.I) := by
  simp_rw [← secondIntegrand_eq]
  have h0 : IntegrableOn (phaseExp (-3/2) y) (Ioi (-R)) := by
    unfold phaseExp
    apply integrableOn_exp_mul_complex_Ioi
    norm_num
  have h1 : IntegrableOn (phaseExp (-1/2) y) (Ioi (-R)) := by
    unfold phaseExp
    apply integrableOn_exp_mul_complex_Ioi
    norm_num
  have he (x : ℝ) : secondIntegrand y x =
      phaseExp (-3/2) y x * (Real.exp (-Real.exp x):ℂ) -
        phaseExp (-3/2) y x + phaseExp (-1/2) y x := by
    have hs := phaseExp_mul_exp (-3/2) y x
    rw [show (-3/2:ℝ)+1=(-1/2:ℝ) by ring] at hs
    rw [secondIntegrand, fzzExpSecondRemainder, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_one, mul_add, mul_sub, mul_one, hs]
  have he0 : (∫ x in Ioi (-R), phaseExp (-3/2) y x) =
      -Complex.exp (-((-3/2:ℂ)+(y:ℂ)*Complex.I)*(R:ℂ)) /
        ((-3/2:ℂ)+(y:ℂ)*Complex.I) := by
    simpa only [phaseExp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Complex.ofReal_one, neg_mul, mul_neg] using
        integral_exp_mul_complex_Ioi (a := (-3/2:ℂ)+(y:ℂ)*Complex.I) (by norm_num) (-R)
  have he1 : (∫ x in Ioi (-R), phaseExp (-1/2) y x) =
      -Complex.exp (-((-1/2:ℂ)+(y:ℂ)*Complex.I)*(R:ℂ)) /
        ((-1/2:ℂ)+(y:ℂ)*Complex.I) := by
    simpa only [phaseExp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Complex.ofReal_one, neg_mul, mul_neg] using
        integral_exp_mul_complex_Ioi (a := (-1/2:ℂ)+(y:ℂ)*Complex.I) (by norm_num) (-R)
  simp_rw [he]
  have hsub : IntegrableOn (fun x => phaseExp (-3/2) y x * (Real.exp (-Real.exp x):ℂ) -
      phaseExp (-3/2) y x) (Ioi (-R)) := (integrable_cutoff y R).sub h0
  rw [integral_add hsub h1,
    integral_sub (integrable_cutoff y R) h0, he0, he1]
  unfold fzzNegativeChargedRadialCutoff fzzNegativeChargedRadialCounterterms
  ring

theorem fzzNegativeChargedRadialCutoff_finitePart (y : ℝ) :
    Tendsto (fun R : ℝ => fzzNegativeChargedRadialCutoff y R +
      fzzNegativeChargedRadialCounterterms y R) atTop
        (𝓝 (Complex.Gamma ((-3/2:ℂ)+(y:ℂ)*Complex.I))) := by
  have h := (aecover_Ioi (μ := (volume : Measure ℝ))
    (a := fun R : ℝ => -R) tendsto_neg_atTop_atBot).integral_tendsto_of_countably_generated
      (integrable_second y)
  rw [second_integral_eq_gamma] at h
  simpa only [fzzNegativeChargedRadialCutoff_counterterms_eq, ← secondIntegrand_eq] using h

end
end GaloisForLFunctions.RHTower
