import GaloisForLFunctions.RHTower.ThetaRenewalAnalyticContinuation

/-!
# The hyperbolic-cosine factorization of `Ξ` through the renewal kernel

For `|Re s| < a = 1/4` put `C(s) = ∫₀^∞ Q(t) cosh(st) dt`, `S(s) = ∫₀^∞ Q(t) sinh(st) dt`
(holomorphic: `Q(t) ≤ a e^{-βt}`) and `η(s) = ½[log(a + s) - log(a - s)]`.  Then `Q̂ = C - S`, and
`D(s) = c e^{-Q̂(s)}` together with the two-ended identity `Ξ(2is) = (a+s)D(s) + (a-s)D(-s)` and
`e^{2η} = (a+s)/(a-s)` give
`Ξ(2is) = 2ac e^{-C(s)} cosh(η(s) + S(s))/cosh η(s)`,
with a holomorphic, nowhere vanishing prefactor.  Since `‖S‖ ≤ ∫ e^{at}Q < 1/5` and
`0 < Im η < π/2` in the upper half, `Ξ(2is) = 0 ⟺ η(s) + S(s) = iπ/2` there, and the reflected
level `-iπ/2` in the lower half.  On real frequencies `η(iτ) = i arctan(τ/a)`, giving
`Ξ(2τ) = 2c √(a² + τ²) exp(-∫₀^∞ Q cos τt) cos(arctan(τ/a) + ∫₀^∞ Q sin τt)`.
The Frullani-type integral `∫₀^∞ e^{-at} sinh(st)/t dt` equals `η(s)` (both vanish at `0` and have
derivative `a/(a² - s²)`), so `η + S = ∫₀^∞ W(t) sinh(st) dt` with the odd kernel `W`.
-/
open Complex Filter Topology Set MeasureTheory HurwitzZeta
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The cosine and sine transforms of the kernel -/

theorem integrableOn_exp_mul_thetaRenewalLogKernel :
    IntegrableOn (fun t => Real.exp (t / 4) * thetaRenewalLogKernel t) (Ioi 0) := by
  have hβ : 0 < Real.pi - 3 / 2 - 1 / 4 := by linarith [Real.pi_gt_three]
  refine ((integrableOn_exp_mul_Ioi (by linarith : -(Real.pi - 3 / 2 - 1 / 4) < 0) 0).const_mul
    (1 / 4)).mono' ((by have := continuous_thetaRenewalLogKernel; fun_prop : Continuous fun t =>
      Real.exp (t / 4) * thetaRenewalLogKernel t).aestronglyMeasurable.restrict) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (thetaRenewalLogKernel_pos ht0))]
  calc Real.exp (t / 4) * thetaRenewalLogKernel t ≤
        Real.exp (t / 4) * (1 / 4 * Real.exp (-((Real.pi - 3 / 2) * t))) :=
        mul_le_mul_of_nonneg_left (thetaRenewalLogKernel_le_quarter ht0) (Real.exp_pos _).le
    _ = 1 / 4 * Real.exp (-(Real.pi - 3 / 2 - 1 / 4) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

theorem norm_cexp_mul_le_exp {s : ℂ} (hs : |s.re| ≤ 1 / 4) {t : ℝ} (ht : 0 ≤ t) :
    ‖cexp (s * t)‖ ≤ Real.exp (t / 4) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith [abs_le.mp hs]

theorem integrableOn_cexp_mul_thetaRenewalLogKernel {s : ℂ} (hs : |s.re| ≤ 1 / 4) :
    IntegrableOn (fun t : ℝ => cexp (s * t) * (thetaRenewalLogKernel t : ℂ)) (Ioi 0) := by
  refine integrableOn_exp_mul_thetaRenewalLogKernel.mono'
    ((by have := continuous_thetaRenewalLogKernel; fun_prop : Continuous fun t : ℝ =>
      cexp (s * t) * (thetaRenewalLogKernel t : ℂ)).aestronglyMeasurable.restrict) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thetaRenewalLogKernel_pos ht0)]
  exact mul_le_mul_of_nonneg_right (norm_cexp_mul_le_exp hs ht0.le)
    (thetaRenewalLogKernel_pos ht0).le

/-- `C(s) = ∫₀^∞ Q(t) cosh(st) dt`. -/
def thetaRenewalCosTransform (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (thetaRenewalLogKernel t : ℂ) * Complex.cosh (s * t)

/-- `S(s) = ∫₀^∞ Q(t) sinh(st) dt`. -/
def thetaRenewalSinTransform (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (thetaRenewalLogKernel t : ℂ) * Complex.sinh (s * t)

theorem integrableOn_thetaRenewalLogKernel_mul_cosh {s : ℂ} (hs : |s.re| ≤ 1 / 4) :
    IntegrableOn (fun t : ℝ => (thetaRenewalLogKernel t : ℂ) * Complex.cosh (s * t)) (Ioi 0) := by
  have h1 := integrableOn_cexp_mul_thetaRenewalLogKernel hs
  have h2 := integrableOn_cexp_mul_thetaRenewalLogKernel (s := -s) (by simpa using hs)
  refine IntegrableOn.congr_fun ((h1.add h2).div_const 2) (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, Complex.cosh]
  ring_nf

theorem integrableOn_thetaRenewalLogKernel_mul_sinh {s : ℂ} (hs : |s.re| ≤ 1 / 4) :
    IntegrableOn (fun t : ℝ => (thetaRenewalLogKernel t : ℂ) * Complex.sinh (s * t)) (Ioi 0) := by
  have h1 := integrableOn_cexp_mul_thetaRenewalLogKernel hs
  have h2 := integrableOn_cexp_mul_thetaRenewalLogKernel (s := -s) (by simpa using hs)
  refine IntegrableOn.congr_fun ((h1.sub h2).div_const 2) (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, Complex.sinh]
  ring_nf

/-- `Q̂(s) = C(s) - S(s)`. -/
theorem thetaRenewalLogKernelLaplace_eq_cos_sub_sin {s : ℂ} (hs : |s.re| ≤ 1 / 4) :
    thetaRenewalLogKernelLaplace s = thetaRenewalCosTransform s - thetaRenewalSinTransform s := by
  rw [thetaRenewalLogKernelLaplace, thetaRenewalCosTransform, thetaRenewalSinTransform,
    ← integral_sub (integrableOn_thetaRenewalLogKernel_mul_cosh hs)
      (integrableOn_thetaRenewalLogKernel_mul_sinh hs)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.cosh, Complex.sinh]
  ring_nf

theorem thetaRenewalCosTransform_neg (s : ℂ) :
    thetaRenewalCosTransform (-s) = thetaRenewalCosTransform s := by
  simp only [thetaRenewalCosTransform, neg_mul, Complex.cosh_neg]

theorem thetaRenewalSinTransform_neg (s : ℂ) :
    thetaRenewalSinTransform (-s) = -thetaRenewalSinTransform s := by
  simp only [thetaRenewalSinTransform, neg_mul, Complex.sinh_neg, mul_neg, integral_neg]

/-! ## The hyperbolic-cosine factorization -/

/-- The principal branch `η(s) = ½ [log(a + s) - log(a - s)]`. -/
def thetaRenewalPhase (s : ℂ) : ℂ := (Complex.log (1 / 4 + s) - Complex.log (1 / 4 - s)) / 2

theorem add_ne_zero_of_abs_re_lt {s : ℂ} (hs : |s.re| < 1 / 4) : (1 / 4 : ℂ) + s ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [abs_lt.mp hs]

theorem sub_ne_zero_of_abs_re_lt {s : ℂ} (hs : |s.re| < 1 / 4) : (1 / 4 : ℂ) - s ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [abs_lt.mp hs]

/-- `e^{2η} = (a + s)/(a - s)`. -/
theorem cexp_two_mul_thetaRenewalPhase {s : ℂ} (hs : |s.re| < 1 / 4) :
    cexp (2 * thetaRenewalPhase s) = (1 / 4 + s) / (1 / 4 - s) := by
  rw [thetaRenewalPhase, show 2 * ((Complex.log (1 / 4 + s) - Complex.log (1 / 4 - s)) / 2) =
    Complex.log (1 / 4 + s) - Complex.log (1 / 4 - s) by ring, Complex.exp_sub,
    Complex.exp_log (add_ne_zero_of_abs_re_lt hs), Complex.exp_log (sub_ne_zero_of_abs_re_lt hs)]

theorem cosh_thetaRenewalPhase_ne_zero {s : ℂ} (hs : |s.re| < 1 / 4) :
    Complex.cosh (thetaRenewalPhase s) ≠ 0 := by
  intro h
  have h2 : cexp (thetaRenewalPhase s) * cexp (thetaRenewalPhase s) = -1 := by
    have e : Complex.cosh (thetaRenewalPhase s) =
        (cexp (thetaRenewalPhase s) + cexp (-thetaRenewalPhase s)) / 2 := rfl
    rw [e, Complex.exp_neg] at h
    have hne := Complex.exp_ne_zero (thetaRenewalPhase s)
    field_simp at h
    linear_combination h
  rw [← Complex.exp_add, ← two_mul, cexp_two_mul_thetaRenewalPhase hs] at h2
  have hsub := sub_ne_zero_of_abs_re_lt hs
  rw [div_eq_iff hsub] at h2
  have := congrArg Complex.re h2
  simp at this
  linarith

/-- The algebraic identity `(a + s) e^{S} + (a - s) e^{-S} = 2a cosh(η + S)/cosh η`. -/
theorem add_mul_exp_add_sub_mul_exp {s : ℂ} (hs : |s.re| < 1 / 4) (S : ℂ) :
    (1 / 4 + s) * cexp S + (1 / 4 - s) * cexp (-S) =
      2 * (1 / 4) * Complex.cosh (thetaRenewalPhase s + S) / Complex.cosh (thetaRenewalPhase s) := by
  have hc := cosh_thetaRenewalPhase_ne_zero hs
  have hE := cexp_two_mul_thetaRenewalPhase hs
  have hsub := sub_ne_zero_of_abs_re_lt hs
  rw [eq_div_iff hc]
  have e1 : Complex.cosh (thetaRenewalPhase s + S) =
      (cexp (thetaRenewalPhase s) * cexp S + cexp (-thetaRenewalPhase s) * cexp (-S)) / 2 := by
    rw [show Complex.cosh (thetaRenewalPhase s + S) = (cexp (thetaRenewalPhase s + S) +
      cexp (-(thetaRenewalPhase s + S))) / 2 from rfl, Complex.exp_add, neg_add, Complex.exp_add]
  have e2 : Complex.cosh (thetaRenewalPhase s) =
      (cexp (thetaRenewalPhase s) + cexp (-thetaRenewalPhase s)) / 2 := rfl
  rw [e1, e2]
  have hEE : cexp (thetaRenewalPhase s) * cexp (thetaRenewalPhase s) = (1 / 4 + s) / (1 / 4 - s) := by
    rw [← Complex.exp_add, ← two_mul, hE]
  have hinv : cexp (-thetaRenewalPhase s) * cexp (thetaRenewalPhase s) = 1 := by
    rw [← Complex.exp_add]; simp
  have hne := Complex.exp_ne_zero (thetaRenewalPhase s)
  set E := cexp (thetaRenewalPhase s)
  set F := cexp (-thetaRenewalPhase s)
  have hF : F = E⁻¹ := eq_inv_of_mul_eq_one_left hinv
  rw [hF]
  field_simp
  rw [eq_div_iff hsub] at hEE
  linear_combination (-4 * cexp S + 4 * cexp (-S)) * hEE

/-- **Hyperbolic-cosine factorization (4).** For `|Re s| < 1/4`,
`Ξ(2is) = 2ac e^{-C(s)} cosh(η(s) + S(s))/cosh η(s)`. -/
theorem XiC_two_I_mul_eq_cosh {s : ℂ} (hs : |s.re| < 1 / 4) :
    XiC (2 * I * s) = 2 * (1 / 4) * (Θ 1 : ℂ) * cexp (-thetaRenewalCosTransform s) *
      Complex.cosh (thetaRenewalPhase s + thetaRenewalSinTransform s) /
        Complex.cosh (thetaRenewalPhase s) := by
  have hs' : |s.re| ≤ 1 / 4 := hs.le
  have hsn : |(-s).re| ≤ 1 / 4 := by simpa using hs'
  have h1 : -(1 / 4) ≤ s.re := by linarith [abs_le.mp hs']
  have h2 : -(1 / 4) ≤ (-s).re := by simp; linarith [abs_le.mp hs']
  have htwo := thetaRenewal_two_ended (-(I * s))
  have e1 : I * -(I * s) = s := by linear_combination (-s) * I_sq
  rw [e1, show 2 * -(I * s) = -(2 * I * s) by ring, XiC_even] at htwo
  rw [← htwo, thetaRenewalDenominator_eq_exp h1, thetaRenewalDenominator_eq_exp h2,
    thetaRenewalLogKernelLaplace_eq_cos_sub_sin hs', thetaRenewalLogKernelLaplace_eq_cos_sub_sin hsn,
    thetaRenewalCosTransform_neg, thetaRenewalSinTransform_neg]
  have key := add_mul_exp_add_sub_mul_exp hs (thetaRenewalSinTransform s)
  have eA : cexp (-(thetaRenewalCosTransform s - -thetaRenewalSinTransform s)) =
      cexp (-thetaRenewalCosTransform s) * cexp (-thetaRenewalSinTransform s) := by
    rw [← Complex.exp_add]; ring_nf
  have eB : cexp (-(thetaRenewalCosTransform s - thetaRenewalSinTransform s)) =
      cexp (-thetaRenewalCosTransform s) * cexp (thetaRenewalSinTransform s) := by
    rw [← Complex.exp_add]; ring_nf
  rw [eA, eB]
  calc (1 / 4 - s) * ((Θ 1 : ℂ) * (cexp (-thetaRenewalCosTransform s) *
        cexp (-thetaRenewalSinTransform s))) + (1 / 4 + s) * ((Θ 1 : ℂ) *
        (cexp (-thetaRenewalCosTransform s) * cexp (thetaRenewalSinTransform s)))
      = (Θ 1 : ℂ) * cexp (-thetaRenewalCosTransform s) * ((1 / 4 + s) *
          cexp (thetaRenewalSinTransform s) + (1 / 4 - s) * cexp (-thetaRenewalSinTransform s)) := by
        ring
    _ = _ := by rw [key]; ring

/-- `‖S(s)‖ ≤ ∫₀^∞ e^{at} Q < 1/5` on `|Re s| ≤ 1/4`. -/
theorem norm_thetaRenewalSinTransform_lt {s : ℂ} (hs : |s.re| ≤ 1 / 4) :
    ‖thetaRenewalSinTransform s‖ < 1 / 5 := by
  refine lt_of_le_of_lt ?_ (integral_exp_mul_thetaRenewalLogKernel ▸
    neg_log_one_sub_thetaRenewalMass_lt)
  rw [thetaRenewalSinTransform]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
    (integrableOn_thetaRenewalLogKernel_mul_sinh hs).norm integrableOn_exp_mul_thetaRenewalLogKernel
    measurableSet_Ioi fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thetaRenewalLogKernel_pos ht0),
    mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (thetaRenewalLogKernel_pos ht0).le
  rw [show Complex.sinh (s * t) = (cexp (s * t) - cexp (-(s * t))) / 2 from rfl, norm_div,
    Complex.norm_two]
  have h1 := norm_cexp_mul_le_exp hs ht0.le
  have h2 := norm_cexp_mul_le_exp (s := -s) (by simpa using hs) ht0.le
  rw [neg_mul] at h2
  have := norm_sub_le (cexp (s * t)) (cexp (-(s * t)))
  linarith

theorem im_thetaRenewalPhase_mem {s : ℂ} (hs : |s.re| < 1 / 4) (him : 0 < s.im) :
    0 < (thetaRenewalPhase s).im ∧ (thetaRenewalPhase s).im < Real.pi / 2 := by
  have hr1 : 0 < (1 / 4 + s).re := by simp; linarith [abs_lt.mp hs]
  have hr2 : 0 < (1 / 4 - s).re := by simp; linarith [abs_lt.mp hs]
  have ha1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr1)
  have ha2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr2)
  have hp1 : 0 < (1 / 4 + s).arg := by
    refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr (by simp; linarith)) ?_
    intro h; have := Complex.arg_eq_zero_iff.mp h.symm; simp at this; linarith [this.2]
  have hp2 : (1 / 4 - s).arg < 0 := Complex.arg_neg_iff.mpr (by simp; linarith)
  simp only [thetaRenewalPhase, Complex.div_ofNat_im, Complex.sub_im, Complex.log_im]
  constructor
  · linarith
  · linarith [abs_lt.mp ha1, abs_lt.mp ha2]

theorem cosh_eq_zero_iff' {w : ℂ} : Complex.cosh w = 0 ↔ ∃ k : ℤ, w = (2 * k + 1) * Real.pi / 2 * I := by
  have h : Complex.cosh w = Complex.cos (-(w * I)) := by
    rw [Complex.cos_neg, ← Complex.cosh_mul_I, mul_assoc, I_mul_I, mul_neg_one, Complex.cosh_neg]
  rw [h, Complex.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : w = -(w * I) * I := by rw [neg_mul, mul_assoc, I_mul_I]; ring
    rw [this, hk]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    linear_combination (-((2 * (k : ℂ) + 1) * Real.pi / 2)) * I_sq

/-- **The single cosh level (5).** In the upper half `0 < Im s` of `|Re s| < 1/4`,
`Ξ(2is) = 0 ⟺ η(s) + S(s) = iπ/2`. -/
theorem XiC_two_I_mul_eq_zero_iff {s : ℂ} (hs : |s.re| < 1 / 4) (him : 0 < s.im) :
    XiC (2 * I * s) = 0 ↔ thetaRenewalPhase s + thetaRenewalSinTransform s = Real.pi / 2 * I := by
  have hc := thetaSeam_pos
  have hcC : ((Θ 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [XiC_two_I_mul_eq_cosh hs, div_eq_zero_iff, or_iff_left (cosh_thetaRenewalPhase_ne_zero hs),
    mul_eq_zero, or_iff_right (mul_ne_zero (by norm_num [hcC]) (Complex.exp_ne_zero _)),
    cosh_eq_zero_iff']
  have hη := im_thetaRenewalPhase_mem hs him
  have hS := norm_thetaRenewalSinTransform_lt hs.le
  have hSim : |(thetaRenewalSinTransform s).im| < 1 / 5 :=
    lt_of_le_of_lt (Complex.abs_im_le_norm _) hS
  constructor
  · rintro ⟨k, hk⟩
    have him' := congrArg Complex.im hk
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one]
      at him'
    have hre : (((2 * (k : ℂ) + 1) * Real.pi / 2)).re = (2 * k + 1) * Real.pi / 2 := by simp
    rw [hre] at him'
    have hpi := Real.pi_gt_three
    have hSb := abs_lt.mp hSim
    have hk0 : k = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        have : (2 * (k : ℝ) + 1) * Real.pi / 2 ≤ -(Real.pi / 2) := by nlinarith
        linarith [hη.1]
      · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hgt
        have : 3 * (Real.pi / 2) ≤ (2 * (k : ℝ) + 1) * Real.pi / 2 := by nlinarith
        linarith [hη.2]
    rw [hk, hk0]; push_cast; ring
  · intro h
    exact ⟨0, by rw [h]; push_cast; ring⟩

theorem thetaRenewalPhase_neg (s : ℂ) : thetaRenewalPhase (-s) = -thetaRenewalPhase s := by
  simp only [thetaRenewalPhase, sub_neg_eq_add]
  ring_nf

/-- The reflected level: for `Im s < 0`, `Ξ(2is) = 0 ⟺ η(s) + S(s) = -iπ/2`. -/
theorem XiC_two_I_mul_eq_zero_iff_of_im_neg {s : ℂ} (hs : |s.re| < 1 / 4) (him : s.im < 0) :
    XiC (2 * I * s) = 0 ↔ thetaRenewalPhase s + thetaRenewalSinTransform s = -(Real.pi / 2 * I) := by
  have hs' : |(-s).re| < 1 / 4 := by simpa using hs
  have him' : 0 < (-s).im := by simp; linarith
  have h := XiC_two_I_mul_eq_zero_iff hs' him'
  rw [show 2 * I * -s = -(2 * I * s) by ring, XiC_even, thetaRenewalPhase_neg,
    thetaRenewalSinTransform_neg] at h
  rw [h]
  constructor <;> intro h' <;> linear_combination -h'

/-- The prefactor `2ac e^{-C(s)}/cosh η(s)` never vanishes on `|Re s| < 1/4`. -/
theorem thetaRenewal_prefactor_ne_zero {s : ℂ} (hs : |s.re| < 1 / 4) :
    2 * (1 / 4) * (Θ 1 : ℂ) * cexp (-thetaRenewalCosTransform s) /
      Complex.cosh (thetaRenewalPhase s) ≠ 0 := by
  have hc := thetaSeam_pos
  have hcC : ((Θ 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hcC) (Complex.exp_ne_zero _))
    (cosh_thetaRenewalPhase_ne_zero hs)

theorem arg_quarter_add_I_mul (τ : ℝ) : ((1 / 4 : ℂ) + I * τ).arg = Real.arctan (4 * τ) := by
  have hre : (0 : ℝ) < ((1 / 4 : ℂ) + I * τ).re := by simp
  have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have ht := Complex.tan_arg ((1 / 4 : ℂ) + I * τ)
  have e : ((1 / 4 : ℂ) + I * τ).im / ((1 / 4 : ℂ) + I * τ).re = 4 * τ := by
    simp; ring
  rw [e] at ht
  rw [← ht, Real.arctan_tan (by linarith [abs_lt.mp ha]) (by linarith [abs_lt.mp ha])]

/-- `η(iτ) = i arctan(τ/a)`. -/
theorem thetaRenewalPhase_I_mul (τ : ℝ) :
    thetaRenewalPhase (I * τ) = ((Real.arctan (4 * τ) : ℝ) : ℂ) * I := by
  have hconj : (1 / 4 : ℂ) - I * τ = (starRingEnd ℂ) ((1 / 4 : ℂ) + I * τ) := by
    apply Complex.ext <;> simp
  have harg : ((1 / 4 : ℂ) + I * τ).arg ≠ Real.pi := by
    rw [arg_quarter_add_I_mul]
    have := Real.arctan_lt_pi_div_two (4 * τ)
    linarith [Real.pi_pos]
  rw [thetaRenewalPhase, hconj, Complex.log_conj _ harg]
  apply Complex.ext
  · simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.conj_re, sub_self,
      zero_div, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul]
  · simp only [Complex.div_ofNat_im, Complex.sub_im, Complex.conj_im, Complex.log_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      add_zero, mul_one, arg_quarter_add_I_mul]
    ring

/-- **Real-frequency amplitude–phase form (6).**
`Ξ(2τ) = 2c √(a² + τ²) exp(-∫₀^∞ Q cos τt) cos(arctan(τ/a) + ∫₀^∞ Q sin τt)`. -/
theorem XiC_two_mul_ofReal_eq (τ : ℝ) :
    XiC (2 * τ) = ((2 * Θ 1 * Real.sqrt (1 / 16 + τ ^ 2) *
      Real.exp (-∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.cos (τ * t)) *
      Real.cos (Real.arctan (4 * τ) + ∫ t in Ioi (0 : ℝ),
        thetaRenewalLogKernel t * Real.sin (τ * t)) : ℝ) : ℂ) := by
  have hs : |(I * (τ : ℂ)).re| < 1 / 4 := by simp
  have h4 := XiC_two_I_mul_eq_cosh hs
  rw [show 2 * I * (I * (τ : ℂ)) = -(2 * τ) by linear_combination (2 * (τ : ℂ)) * I_sq,
    XiC_even] at h4
  have hC : thetaRenewalCosTransform (I * τ) =
      ((∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.cos (τ * t) : ℝ) : ℂ) := by
    rw [thetaRenewalCosTransform, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show I * (τ : ℂ) * t = ((τ * t : ℝ) : ℂ) * I by push_cast; ring, Complex.cosh_mul_I]
    push_cast; ring
  have hS : thetaRenewalSinTransform (I * τ) =
      ((∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.sin (τ * t) : ℝ) : ℂ) * I := by
    rw [thetaRenewalSinTransform, ← integral_complex_ofReal, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show I * (τ : ℂ) * t = ((τ * t : ℝ) : ℂ) * I by push_cast; ring, Complex.sinh_mul_I]
    push_cast; ring
  rw [h4, hC, hS, thetaRenewalPhase_I_mul, ← add_mul, Complex.cosh_mul_I, Complex.cosh_mul_I]
  set θ := Real.arctan (4 * τ)
  set σ := ∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.sin (τ * t)
  set κ := ∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.cos (τ * t)
  have hcos : Real.cos θ = 1 / Real.sqrt (1 + (4 * τ) ^ 2) := Real.cos_arctan _
  have hsq : Real.sqrt (1 + (4 * τ) ^ 2) = 4 * Real.sqrt (1 / 16 + τ ^ 2) := by
    rw [show 1 + (4 * τ) ^ 2 = 4 ^ 2 * (1 / 16 + τ ^ 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hpos : 0 < Real.sqrt (1 / 16 + τ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hcC : Complex.cos (θ : ℂ) = ((1 / (4 * Real.sqrt (1 / 16 + τ ^ 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos, hcos, hsq]
  rw [hcC]
  push_cast
  field_simp

/-! ## The odd kernel pairing (3b) -/

theorem norm_sinh_le_mul_exp (w : ℂ) : ‖Complex.sinh w‖ ≤ ‖w‖ * Real.exp |w.re| := by
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => Complex.sinh (s * w))
      (Complex.cosh (s * w) * w) s := by
    intro s _
    exact (Complex.hasDerivAt_sinh _).comp s (((hasDerivAt_id (s : ℂ)).mul_const w).comp_ofReal
      |>.congr_deriv (one_mul w))
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun s : ℝ => Complex.cosh (s * w) * w).intervalIntegrable 0 1)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.sinh_zero,
    sub_zero] at hint
  rw [← hint]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := ‖w‖ * Real.exp |w.re|) (f := fun s : ℝ => Complex.cosh (s * w) * w) (fun s hs => by
      rw [uIoc_of_le zero_le_one] at hs
      rw [norm_mul, mul_comm]
      refine mul_le_mul_of_nonneg_left ((norm_cosh_le_exp_abs_re _).trans
        (Real.exp_le_exp.mpr ?_)) (norm_nonneg _)
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [abs_mul, abs_of_pos hs.1]
      nlinarith [abs_nonneg w.re, hs.2])
  simpa using hb

/-- The Frullani-type integral `F(s) = ∫₀^∞ e^{-at} sinh(st)/t dt`. -/
def thetaRenewalFrullani (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (Real.exp (-(t / 4)) : ℂ) * Complex.sinh (s * t) / t

/-- The domain `|Re s| < 1/4`. -/
def thetaRenewalStrip : Set ℂ := {s | |s.re| < 1 / 4}

theorem isOpen_thetaRenewalStrip : IsOpen thetaRenewalStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

theorem convex_thetaRenewalStrip : Convex ℝ thetaRenewalStrip := by
  intro x hx y hy a b ha hb hab
  simp only [thetaRenewalStrip, mem_setOf_eq] at hx hy ⊢
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  calc |a * x.re + b * y.re| ≤ a * |x.re| + b * |y.re| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < 1 / 4 := by
        rcases eq_or_lt_of_le ha with rfl | ha'
        · simp at hab; subst hab; simpa using hy
        · have h1 := mul_lt_mul_of_pos_left hx ha'
          have h2 := mul_le_mul_of_nonneg_left hy.le hb
          nlinarith

theorem continuousOn_frullani_integrand (s : ℂ) :
    ContinuousOn (fun t : ℝ => (Real.exp (-(t / 4)) : ℂ) * Complex.sinh (s * t) / t) (Ioi 0) := by
  have hA : Continuous fun t : ℝ => (Real.exp (-(t / 4)) : ℂ) * Complex.sinh (s * t) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_id.div_const 4).neg)).mul
      (Complex.continuous_sinh.comp (continuous_const.mul Complex.continuous_ofReal))
  exact hA.continuousOn.div Complex.continuous_ofReal.continuousOn fun t ht =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt ht)

theorem integrableOn_thetaRenewalFrullani_integrand {s : ℂ} {b : ℝ} (hb : b < 1 / 4)
    (hsb : |s.re| ≤ b) :
    IntegrableOn (fun t : ℝ => (Real.exp (-(t / 4)) : ℂ) * Complex.sinh (s * t) / t) (Ioi 0) := by
  have hbound : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 4 - b) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  refine (hbound.const_mul ‖s‖).mono' ((continuousOn_frullani_integrand s).aestronglyMeasurable
      measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have hsinh := norm_sinh_le_mul_exp (s * t)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0] at hsinh
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    abs_mul, abs_of_pos ht0] at hsinh
  rw [div_le_iff₀ ht0]
  calc Real.exp (-(t / 4)) * ‖Complex.sinh (s * t)‖ ≤
        Real.exp (-(t / 4)) * (‖s‖ * t * Real.exp (|s.re| * t)) :=
        mul_le_mul_of_nonneg_left hsinh (Real.exp_pos _).le
    _ ≤ Real.exp (-(t / 4)) * (‖s‖ * t * Real.exp (b * t)) := by
        gcongr
    _ = ‖s‖ * Real.exp (-(1 / 4 - b) * t) * t := by
        rw [show -(1 / 4 - b) * t = -(t / 4) + b * t by ring, Real.exp_add]; ring

theorem hasDerivAt_thetaRenewalFrullani {s : ℂ} (hs : s ∈ thetaRenewalStrip) :
    HasDerivAt thetaRenewalFrullani
      (∫ t in Ioi (0 : ℝ), (Real.exp (-(t / 4)) : ℂ) * Complex.cosh (s * t)) s := by
  have hs' : |s.re| < 1 / 4 := hs
  set δ := (1 / 4 - |s.re|) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set b := |s.re| + δ
  have hb : b < 1 / 4 := by simp only [b, hδ]; linarith
  have hball : ∀ z ∈ Metric.ball s δ, |z.re| ≤ b := by
    intro z hz
    have h1 : |z.re - s.re| < δ := by
      have := Complex.abs_re_le_norm (z - s)
      rw [Complex.sub_re] at this
      exact lt_of_le_of_lt this (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz)
    have h2 : |z.re| ≤ |s.re| + |z.re - s.re| := by
      have := abs_add_le s.re (z.re - s.re); simp only [add_sub_cancel] at this; linarith
    simp only [b]; linarith
  have hbound : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 4 - b) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun z (t : ℝ) => (Real.exp (-(t / 4)) : ℂ) * Complex.sinh (z * t) / t)
    (F' := fun z (t : ℝ) => (Real.exp (-(t / 4)) : ℂ) * Complex.cosh (z * t))
    (bound := fun t => Real.exp (-(1 / 4 - b) * t)) (x₀ := s) (Metric.ball_mem_nhds s hδ0)
    (Eventually.of_forall fun z => (continuousOn_frullani_integrand z).aestronglyMeasurable
        measurableSet_Ioi)
    (integrableOn_thetaRenewalFrullani_integrand hb (by simp only [b]; linarith))
    ((by fun_prop : ContinuousOn (fun t : ℝ => (Real.exp (-(t / 4)) : ℂ) *
      Complex.cosh (s * t)) (Ioi 0)).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine (mul_le_mul_of_nonneg_left (norm_cosh_le_exp_abs_re _) (Real.exp_pos _).le).trans ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have ht0 : (0 : ℝ) < t := ht
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        abs_mul, abs_of_pos ht0]
      nlinarith [hball z hz]))
    hbound
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z _ => by
      have ht0 : (0 : ℝ) < t := ht
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have h := ((Complex.hasDerivAt_sinh (z * t)).comp z ((hasDerivAt_id z).mul_const (t : ℂ))).const_mul
        (Real.exp (-(t / 4)) : ℂ) |>.div_const (t : ℂ)
      refine h.congr_deriv ?_
      simp only [one_mul]
      field_simp))
  exact key.2

theorem integral_exp_mul_cosh_eq {s : ℂ} (hs : |s.re| < 1 / 4) :
    (∫ t in Ioi (0 : ℝ), (Real.exp (-(t / 4)) : ℂ) * Complex.cosh (s * t)) =
      (1 / (1 / 4 - s) + 1 / (1 / 4 + s)) / 2 := by
  have ha : (s - 1 / 4).re < 0 := by simp; linarith [abs_lt.mp hs]
  have hb : (-s - 1 / 4).re < 0 := by simp; linarith [abs_lt.mp hs]
  have h1 := integral_exp_mul_complex_Ioi ha 0
  have h2 := integral_exp_mul_complex_Ioi hb 0
  have i1 := integrableOn_exp_mul_complex_Ioi ha 0
  have i2 := integrableOn_exp_mul_complex_Ioi hb 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h1 h2
  have e : ∀ t : ℝ, (Real.exp (-(t / 4)) : ℂ) * Complex.cosh (s * t) =
      (cexp ((s - 1 / 4) * t) + cexp ((-s - 1 / 4) * t)) / 2 := by
    intro t
    rw [show Complex.cosh (s * t) = (cexp (s * t) + cexp (-(s * t))) / 2 from rfl,
      Complex.ofReal_exp]
    rw [show (s - 1 / 4) * (t : ℂ) = s * t + ((-(t / 4) : ℝ) : ℂ) by push_cast; ring,
      show (-s - 1 / 4) * (t : ℂ) = -(s * t) + ((-(t / 4) : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_add, Complex.exp_add]
    push_cast; ring
  simp_rw [e]
  rw [integral_div, integral_add i1 i2, h1, h2]
  have hs1 : (1 / 4 : ℂ) - s ≠ 0 := sub_ne_zero_of_abs_re_lt hs
  have hs2 : (1 / 4 : ℂ) + s ≠ 0 := add_ne_zero_of_abs_re_lt hs
  have hs1' : s - 1 / 4 ≠ 0 := fun h => hs1 (by linear_combination -h)
  have hs2' : -s - 1 / 4 ≠ 0 := fun h => hs2 (by linear_combination -h)
  have ea : -1 / (s - 1 / 4) = 1 / (1 / 4 - s) := by rw [div_eq_div_iff hs1' hs1]; ring
  have eb : -1 / (-s - 1 / 4) = 1 / (1 / 4 + s) := by rw [div_eq_div_iff hs2' hs2]; ring
  rw [ea, eb]

theorem hasDerivAt_thetaRenewalPhase {s : ℂ} (hs : |s.re| < 1 / 4) :
    HasDerivAt thetaRenewalPhase ((1 / (1 / 4 - s) + 1 / (1 / 4 + s)) / 2) s := by
  have h1 : (1 / 4 + s) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [abs_lt.mp hs]))
  have h2 : (1 / 4 - s) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [abs_lt.mp hs]))
  have d1 := (Complex.hasDerivAt_log h1).comp s ((hasDerivAt_id s).const_add (1 / 4 : ℂ))
  have d2 := (Complex.hasDerivAt_log h2).comp s ((hasDerivAt_id s).const_sub (1 / 4 : ℂ))
  refine ((d1.sub d2).div_const 2).congr_deriv ?_
  ring

/-- `∫₀^∞ e^{-at} sinh(st)/t dt = η(s)` on `|Re s| < 1/4`. -/
theorem thetaRenewalFrullani_eq {s : ℂ} (hs : |s.re| < 1 / 4) :
    thetaRenewalFrullani s = thetaRenewalPhase s := by
  have hpre : IsPreconnected thetaRenewalStrip := convex_thetaRenewalStrip.isPreconnected
  have hdF : DifferentiableOn ℂ thetaRenewalFrullani thetaRenewalStrip := fun z hz =>
    (hasDerivAt_thetaRenewalFrullani hz).differentiableAt.differentiableWithinAt
  have hdη : DifferentiableOn ℂ thetaRenewalPhase thetaRenewalStrip := fun z hz =>
    (hasDerivAt_thetaRenewalPhase hz).differentiableAt.differentiableWithinAt
  have heq : EqOn (deriv thetaRenewalFrullani) (deriv thetaRenewalPhase) thetaRenewalStrip := by
    intro z hz
    rw [(hasDerivAt_thetaRenewalFrullani hz).deriv, (hasDerivAt_thetaRenewalPhase hz).deriv,
      integral_exp_mul_cosh_eq hz]
  have h0 : thetaRenewalFrullani 0 = thetaRenewalPhase 0 := by
    simp [thetaRenewalFrullani, thetaRenewalPhase]
  exact IsOpen.eqOn_of_deriv_eq isOpen_thetaRenewalStrip hpre hdF hdη heq
    (show (0 : ℂ) ∈ thetaRenewalStrip by simp [thetaRenewalStrip]) h0 hs

/-- **The odd-kernel pairing (3b).** `η(s) + S(s) = ∫₀^∞ W(t) sinh(st) dt` on `|Re s| < 1/4`. -/
theorem thetaRenewalPhase_add_sin_eq_integral {s : ℂ} (hs : |s.re| < 1 / 4) :
    thetaRenewalPhase s + thetaRenewalSinTransform s =
      ∫ t in Ioi (0 : ℝ), (thetaRenewalOddKernel t : ℂ) * Complex.sinh (s * t) := by
  have hF := integrableOn_thetaRenewalFrullani_integrand (s := s) (b := |s.re|) hs le_rfl
  have hS := integrableOn_thetaRenewalLogKernel_mul_sinh hs.le
  rw [← thetaRenewalFrullani_eq hs, thetaRenewalFrullani, thetaRenewalSinTransform,
    ← integral_add hF hS]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  simp only [thetaRenewalOddKernel]
  push_cast
  field_simp

/-! ## Holomorphy of the transforms and of the prefactor -/

theorem integrableOn_mul_exp_mul_thetaRenewalLogKernel {b : ℝ} (hb : b < 1 / 4) :
    IntegrableOn (fun t => t * Real.exp (b * t) * thetaRenewalLogKernel t) (Ioi 0) := by
  have hκ : 0 < Real.pi - 3 / 2 - b := by linarith [Real.pi_gt_three]
  refine (integrableOn_of_le_mul_exp (D := 1 / 4) (δ := Real.pi - 3 / 2 - b)
    (by have := continuous_thetaRenewalLogKernel; fun_prop : Continuous fun t =>
      t * Real.exp (b * t) * thetaRenewalLogKernel t).continuousOn hκ fun t ht => ?_)
  rw [abs_of_pos (mul_pos (mul_pos ht (Real.exp_pos _)) (thetaRenewalLogKernel_pos ht))]
  calc t * Real.exp (b * t) * thetaRenewalLogKernel t ≤
        t * Real.exp (b * t) * (1 / 4 * Real.exp (-((Real.pi - 3 / 2) * t))) :=
        mul_le_mul_of_nonneg_left (thetaRenewalLogKernel_le_quarter ht) (by positivity)
    _ = 1 / 4 * (t * Real.exp (-((Real.pi - 3 / 2 - b) * t))) := by
        rw [show -((Real.pi - 3 / 2 - b) * t) = b * t + -((Real.pi - 3 / 2) * t) by ring,
          Real.exp_add]; ring

/-- Derivative of a transform `∫₀^∞ Q(t) φ(st) dt` with `|φ|, |φ'| ≤ e^{|Re w|}`. -/
theorem hasDerivAt_thetaRenewal_transform {φ φ' : ℂ → ℂ} (hφ : ∀ w, HasDerivAt φ (φ' w) w)
    (hcont : Continuous φ) (hcont' : Continuous φ')
    (hbφ : ∀ w, ‖φ w‖ ≤ Real.exp |w.re|) (hbφ' : ∀ w, ‖φ' w‖ ≤ Real.exp |w.re|)
    {s : ℂ} (hs : s ∈ thetaRenewalStrip) :
    HasDerivAt (fun z => ∫ t in Ioi (0 : ℝ), (thetaRenewalLogKernel t : ℂ) * φ (z * t))
      (∫ t in Ioi (0 : ℝ), (thetaRenewalLogKernel t : ℂ) * (φ' (s * t) * t)) s := by
  have hs' : |s.re| < 1 / 4 := hs
  set δ := (1 / 4 - |s.re|) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set b := |s.re| + δ
  have hb : b < 1 / 4 := by simp only [b, hδ]; linarith
  have hball : ∀ z ∈ Metric.ball s δ, |z.re| ≤ b := by
    intro z hz
    have h1 : |z.re - s.re| < δ := by
      have := Complex.abs_re_le_norm (z - s)
      rw [Complex.sub_re] at this
      exact lt_of_le_of_lt this (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz)
    have h2 : |z.re| ≤ |s.re| + |z.re - s.re| := by
      have := abs_add_le s.re (z.re - s.re); simp only [add_sub_cancel] at this; linarith
    simp only [b]; linarith
  have hQc := continuous_thetaRenewalLogKernel
  have hbd : ∀ z : ℂ, |z.re| ≤ b → ∀ t : ℝ, 0 < t → Real.exp |(z * t).re| ≤ Real.exp (b * t) := by
    intro z hz t ht
    refine Real.exp_le_exp.mpr ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, abs_mul,
      abs_of_pos ht]
    nlinarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun z (t : ℝ) => (thetaRenewalLogKernel t : ℂ) * φ (z * t))
    (F' := fun z (t : ℝ) => (thetaRenewalLogKernel t : ℂ) * (φ' (z * t) * t))
    (bound := fun t => t * Real.exp (b * t) * thetaRenewalLogKernel t) (x₀ := s)
    (Metric.ball_mem_nhds s hδ0)
    (Eventually.of_forall fun z => ((by fun_prop : Continuous fun t : ℝ =>
      (thetaRenewalLogKernel t : ℂ) * φ (z * t))).aestronglyMeasurable.restrict)
    (by
      refine integrableOn_exp_mul_thetaRenewalLogKernel.mono' ((by fun_prop : Continuous fun t : ℝ =>
        (thetaRenewalLogKernel t : ℂ) * φ (s * t))).aestronglyMeasurable.restrict ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thetaRenewalLogKernel_pos ht0),
        mul_comm]
      refine mul_le_mul_of_nonneg_right ((hbφ _).trans (Real.exp_le_exp.mpr ?_))
        (thetaRenewalLogKernel_pos ht0).le
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, abs_mul,
        abs_of_pos ht0]
      nlinarith [abs_nonneg s.re])
    ((by fun_prop : Continuous fun t : ℝ =>
      (thetaRenewalLogKernel t : ℂ) * (φ' (s * t) * t)).aestronglyMeasurable.restrict)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z hz => by
      have ht0 : (0 : ℝ) < t := ht
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (thetaRenewalLogKernel_pos ht0), Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
      calc thetaRenewalLogKernel t * (‖φ' (z * t)‖ * t) ≤
            thetaRenewalLogKernel t * (Real.exp (b * t) * t) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              ((hbφ' _).trans (hbd z (hball z hz) t ht0)) ht0.le) (thetaRenewalLogKernel_pos ht0).le
        _ = t * Real.exp (b * t) * thetaRenewalLogKernel t := by ring))
    (integrableOn_mul_exp_mul_thetaRenewalLogKernel hb)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht z _ => by
      have h := ((hφ (z * t)).comp z ((hasDerivAt_id z).mul_const (t : ℂ))).const_mul
        (thetaRenewalLogKernel t : ℂ)
      exact h.congr_deriv (by simp only [one_mul])))
  exact key.2

theorem norm_sinh_le_exp_abs_re' (w : ℂ) : ‖Complex.sinh w‖ ≤ Real.exp |w.re| := by
  rw [show Complex.sinh w = (cexp w - cexp (-w)) / 2 from rfl, norm_div, Complex.norm_two]
  have h1 : ‖cexp w‖ ≤ Real.exp |w.re| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (le_abs_self _)
  have h2 : ‖cexp (-w)‖ ≤ Real.exp |w.re| := by
    rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (by simp [neg_le_abs])
  have := norm_sub_le (cexp w) (cexp (-w))
  linarith

theorem differentiableOn_thetaRenewalCosTransform :
    DifferentiableOn ℂ thetaRenewalCosTransform thetaRenewalStrip := fun _ hs =>
  (hasDerivAt_thetaRenewal_transform Complex.hasDerivAt_cosh Complex.continuous_cosh
    Complex.continuous_sinh norm_cosh_le_exp_abs_re norm_sinh_le_exp_abs_re' hs).differentiableAt
    |>.differentiableWithinAt

theorem differentiableOn_thetaRenewalSinTransform :
    DifferentiableOn ℂ thetaRenewalSinTransform thetaRenewalStrip := fun _ hs =>
  (hasDerivAt_thetaRenewal_transform Complex.hasDerivAt_sinh Complex.continuous_sinh
    Complex.continuous_cosh norm_sinh_le_exp_abs_re' norm_cosh_le_exp_abs_re hs).differentiableAt
    |>.differentiableWithinAt

theorem differentiableOn_thetaRenewalPhase :
    DifferentiableOn ℂ thetaRenewalPhase thetaRenewalStrip := fun _ hs =>
  (hasDerivAt_thetaRenewalPhase hs).differentiableAt.differentiableWithinAt

/-- The prefactor `2ac e^{-C(s)}/cosh η(s)` is holomorphic on `|Re s| < 1/4`. -/
theorem differentiableOn_thetaRenewal_prefactor :
    DifferentiableOn ℂ (fun s => 2 * (1 / 4) * (Θ 1 : ℂ) * cexp (-thetaRenewalCosTransform s) /
      Complex.cosh (thetaRenewalPhase s)) thetaRenewalStrip := by
  refine DifferentiableOn.div (by
    exact (differentiableOn_const _).mul (differentiableOn_thetaRenewalCosTransform.neg.cexp))
    (Complex.differentiable_cosh.comp_differentiableOn differentiableOn_thetaRenewalPhase)
    fun s hs => cosh_thetaRenewalPhase_ne_zero hs

end RHTower
