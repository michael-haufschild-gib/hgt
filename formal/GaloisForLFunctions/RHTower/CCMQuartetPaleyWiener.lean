import GaloisForLFunctions.RHTower.CCMQuartetResolventPolarization
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Paley–Wiener graph form of the quartet resolvent coordinates

The scalar polarization of the off-line quartet is already formalized in
`CCMQuartetResolventPolarization.lean`: the cross packet is one positive square minus one negative
square, and the negative coordinate is proportional to the transverse charge `lambda + conj lambda`.
This module supplies the missing half of the same card — the Laplace/Paley–Wiener representation of the
two coordinates, and the metric cost of the anti-causal residue mode.

* `integrableOn_Ioi_cexp_neg_mul`, `integral_Ioi_cexp_neg_mul`, `integral_Ioi_exp_neg_mul` — the
  Laplace transform of an exponential ray, for a complex rate of positive real part and for a positive
  real rate.  Mathlib has the Gaussian and Gamma integrals but not this one.
* `ccmCausalResolvent_eq_laplace`, `ccmAntiCausalResolvent_eq_laplace` — equations `(7)` and `(11)`.
* `quartetSymCoord`, `quartetAntisymCoord`, `ccmQuartetPositiveSquare_eq`,
  `ccmQuartetNegativeSquare_eq` — the two light-cone coordinates, tied to the squares of the existing
  module.
* `quartetSymCoord_eq_laplace`, `quartetAntisymCoord_eq_laplace` — equations `(6)` and `(12)`: the
  horizontal displacement `a` is carried by `cosh(a t)` and `sinh(a t)`, not by the ordinate phase.
* `quartetResidueMode`, `integral_norm_sq_quartetResidueMode`,
  `four_mul_lt_integral_norm_sq_quartetResidueMode` — equations `(15)`–`(16)`: squared norm
  `2 m^2 / a`, strictly more than four trace units per multiplicity unit when `0 < a < 1/2`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

/-! ## The Laplace transform of an exponential ray -/

theorem re_neg_mul_ofReal (b : ℂ) (t : ℝ) : (-(b * (t : ℂ))).re = -(b.re * t) := by
  simp [Complex.mul_re]

theorem integrableOn_Ioi_cexp_neg_mul {b : ℂ} (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(b * (t : ℂ)))) (Ioi (0 : ℝ)) volume := by
  have hmeas : Measurable fun t : ℝ => Complex.exp (-(b * (t : ℂ))) := by fun_prop
  refine MeasureTheory.Integrable.mono' (exp_neg_integrableOn_Ioi (0 : ℝ) hb)
    hmeas.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Complex.norm_exp, re_neg_mul_ofReal, show -(b.re * t) = -b.re * t from by ring]

/-- The Laplace transform of `exp(-b t)` on the positive ray, for a complex rate of positive real
part.  Proved from the fundamental theorem of calculus on `Ioi 0`. -/
theorem integral_Ioi_cexp_neg_mul {b : ℂ} (hb : 0 < b.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(b * (t : ℂ)))) = b⁻¹ := by
  have hbne : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => -b⁻¹ * Complex.exp (-(b * (s : ℂ))))
        (Complex.exp (-(b * (t : ℂ)))) t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 t := by
      simpa using HasDerivAt.ofReal_comp (hasDerivAt_id t)
    have h1 : HasDerivAt (fun s : ℝ => -(b * ((s : ℝ) : ℂ))) (-(b * 1)) t :=
      HasDerivAt.neg (HasDerivAt.const_mul b h0)
    have h2 := HasDerivAt.cexp h1
    have h3 := HasDerivAt.const_mul (-b⁻¹) h2
    have hval : -b⁻¹ * (Complex.exp (-(b * (t : ℂ))) * -(b * 1))
        = Complex.exp (-(b * (t : ℂ))) := by
      field_simp
    rw [hval] at h3
    exact h3
  have hlim : Tendsto (fun s : ℝ => -b⁻¹ * Complex.exp (-(b * (s : ℂ)))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hexp : Tendsto (fun s : ℝ => Real.exp (-(b.re * s))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_neg_atBot_iff.mpr (Filter.Tendsto.const_mul_atTop hb tendsto_id)
    have hzero : ‖(-b⁻¹ : ℂ)‖ * 0 = 0 := by ring
    rw [← hzero]
    refine (hexp.const_mul ‖(-b⁻¹ : ℂ)‖).congr fun s => ?_
    rw [norm_mul, Complex.norm_exp, re_neg_mul_ofReal]
  have hcont : ContinuousWithinAt (fun s : ℝ => -b⁻¹ * Complex.exp (-(b * (s : ℂ))))
      (Ici (0 : ℝ)) 0 := (hderiv 0).continuousAt.continuousWithinAt
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun t _ => hderiv t)
    (integrableOn_Ioi_cexp_neg_mul hb) hlim
  rw [hmain]
  simp

/-- The Laplace transform of a real exponential ray. -/
theorem integral_Ioi_exp_neg_mul {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(r * t))) = 1 / r := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := r) one_pos hr
  rw [Real.Gamma_one, mul_one, Real.rpow_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [sub_self, Real.rpow_zero, one_mul]

/-! ## The two quartet rays -/

theorem re_sub_ofReal (lam : ℂ) (x : ℝ) : (((x : ℂ) - lam)).re = x - lam.re := by simp

theorem re_add_star_ofReal (lam : ℂ) (x : ℝ) :
    (((x : ℂ) + star lam)).re = x + lam.re := by
  simp [Complex.add_re, Complex.conj_re]

/-- **Equation (11), causal half.** -/
theorem ccmCausalResolvent_eq_laplace {lam : ℂ} {x : ℝ} (hx : lam.re < x) :
    _root_.RHTower.ccmCausalResolvent lam x
      = ∫ t in Ioi (0 : ℝ), Complex.exp (-(((x : ℂ) - lam) * (t : ℂ))) := by
  have hpos : 0 < (((x : ℂ) - lam)).re := by rw [re_sub_ofReal]; linarith
  rw [integral_Ioi_cexp_neg_mul hpos, _root_.RHTower.ccmCausalResolvent]

/-- **Equation (7).**  The anti-causal half is the Paley–Wiener image of the upper-half-plane Cauchy
residue. -/
theorem ccmAntiCausalResolvent_eq_laplace {lam : ℂ} {x : ℝ} (hx : -lam.re < x) :
    _root_.RHTower.ccmAntiCausalResolvent lam x
      = ∫ t in Ioi (0 : ℝ), Complex.exp (-(((x : ℂ) + star lam) * (t : ℂ))) := by
  have hpos : 0 < (((x : ℂ) + star lam)).re := by rw [re_add_star_ofReal]; linarith
  rw [integral_Ioi_cexp_neg_mul hpos, _root_.RHTower.ccmAntiCausalResolvent]

/-! ## The two light-cone coordinates -/

theorem ofReal_sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

theorem ofReal_sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The symmetric light-cone coordinate `u_lambda = (f + g)/sqrt 2`. -/
def quartetSymCoord (lam : ℂ) (x : ℝ) : ℂ :=
  (_root_.RHTower.ccmCausalResolvent lam x + _root_.RHTower.ccmAntiCausalResolvent lam x)
    / ((Real.sqrt 2 : ℝ) : ℂ)

/-- The antisymmetric light-cone coordinate `v_lambda = (f - g)/sqrt 2`. -/
def quartetAntisymCoord (lam : ℂ) (x : ℝ) : ℂ :=
  (_root_.RHTower.ccmCausalResolvent lam x - _root_.RHTower.ccmAntiCausalResolvent lam x)
    / ((Real.sqrt 2 : ℝ) : ℂ)

theorem ccmQuartetPositiveSquare_eq (lam : ℂ) (x y : ℝ) :
    _root_.RHTower.ccmQuartetPositiveSquare lam x y
      = quartetSymCoord lam x * star (quartetSymCoord lam y) := by
  have hs := ofReal_sqrt_two_sq
  have hsne := ofReal_sqrt_two_ne_zero
  have hconj : star ((Real.sqrt 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [_root_.RHTower.ccmQuartetPositiveSquare, quartetSymCoord, quartetSymCoord]
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
  rw [div_mul_div_comm, hs]

theorem ccmQuartetNegativeSquare_eq (lam : ℂ) (x y : ℝ) :
    _root_.RHTower.ccmQuartetNegativeSquare lam x y
      = quartetAntisymCoord lam x * star (quartetAntisymCoord lam y) := by
  have hs := ofReal_sqrt_two_sq
  have hsne := ofReal_sqrt_two_ne_zero
  have hconj : star ((Real.sqrt 2 : ℝ) : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [_root_.RHTower.ccmQuartetNegativeSquare, quartetAntisymCoord, quartetAntisymCoord]
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
  rw [div_mul_div_comm, hs]

/-! ## The hyperbolic graph form -/

theorem cexp_ray_cosh_split (lam : ℂ) (x t : ℝ) :
    Complex.exp (-((x : ℂ) * (t : ℂ))) * Complex.exp ((lam.im : ℂ) * Complex.I * (t : ℂ))
        * Complex.cosh ((lam.re : ℂ) * (t : ℂ))
      = (1 / 2) * (Complex.exp (-(((x : ℂ) - lam) * (t : ℂ)))
          + Complex.exp (-(((x : ℂ) + star lam) * (t : ℂ)))) := by
  have hre : (lam.re : ℂ) + (lam.im : ℂ) * Complex.I = lam := Complex.re_add_im lam
  have hstar : star lam = (lam.re : ℂ) - (lam.im : ℂ) * Complex.I := by
    rw [Complex.star_def]
    apply Complex.ext <;> simp
  have h1 : -(((x : ℂ) - lam) * (t : ℂ))
      = (-((x : ℂ) * (t : ℂ)) + (lam.im : ℂ) * Complex.I * (t : ℂ)) + (lam.re : ℂ) * (t : ℂ) := by
    linear_combination (-(t : ℂ)) * hre
  have h2 : -(((x : ℂ) + star lam) * (t : ℂ))
      = (-((x : ℂ) * (t : ℂ)) + (lam.im : ℂ) * Complex.I * (t : ℂ))
        + (-((lam.re : ℂ) * (t : ℂ))) := by
    linear_combination (-(t : ℂ)) * hstar
  rw [h1, h2]
  simp only [Complex.exp_add]
  rw [Complex.cosh]
  ring

theorem cexp_ray_sinh_split (lam : ℂ) (x t : ℝ) :
    Complex.exp (-((x : ℂ) * (t : ℂ))) * Complex.exp ((lam.im : ℂ) * Complex.I * (t : ℂ))
        * Complex.sinh ((lam.re : ℂ) * (t : ℂ))
      = (1 / 2) * (Complex.exp (-(((x : ℂ) - lam) * (t : ℂ)))
          - Complex.exp (-(((x : ℂ) + star lam) * (t : ℂ)))) := by
  have hre : (lam.re : ℂ) + (lam.im : ℂ) * Complex.I = lam := Complex.re_add_im lam
  have hstar : star lam = (lam.re : ℂ) - (lam.im : ℂ) * Complex.I := by
    rw [Complex.star_def]
    apply Complex.ext <;> simp
  have h1 : -(((x : ℂ) - lam) * (t : ℂ))
      = (-((x : ℂ) * (t : ℂ)) + (lam.im : ℂ) * Complex.I * (t : ℂ)) + (lam.re : ℂ) * (t : ℂ) := by
    linear_combination (-(t : ℂ)) * hre
  have h2 : -(((x : ℂ) + star lam) * (t : ℂ))
      = (-((x : ℂ) * (t : ℂ)) + (lam.im : ℂ) * Complex.I * (t : ℂ))
        + (-((lam.re : ℂ) * (t : ℂ))) := by
    linear_combination (-(t : ℂ)) * hstar
  rw [h1, h2]
  simp only [Complex.exp_add]
  rw [Complex.sinh]
  ring

/-- **Equation (12), even mode.**  The symmetric coordinate is the `cosh` Laplace transform. -/
theorem quartetSymCoord_eq_laplace {lam : ℂ} {x : ℝ} (hx : |lam.re| < x) :
    quartetSymCoord lam x
      = ((Real.sqrt 2 : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ),
          Complex.exp (-((x : ℂ) * (t : ℂ))) * Complex.exp ((lam.im : ℂ) * Complex.I * (t : ℂ))
            * Complex.cosh ((lam.re : ℂ) * (t : ℂ)) := by
  have habs := abs_lt.mp hx
  have hposm : 0 < (((x : ℂ) - lam)).re := by rw [re_sub_ofReal]; linarith [habs.2]
  have hposp : 0 < (((x : ℂ) + star lam)).re := by rw [re_add_star_ofReal]; linarith [habs.1]
  have hsplit : (∫ t in Ioi (0 : ℝ),
      Complex.exp (-((x : ℂ) * (t : ℂ))) * Complex.exp ((lam.im : ℂ) * Complex.I * (t : ℂ))
        * Complex.cosh ((lam.re : ℂ) * (t : ℂ)))
      = (1 / 2) * (((x : ℂ) - lam)⁻¹ + ((x : ℂ) + star lam)⁻¹) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => cexp_ray_cosh_split lam x t,
      integral_const_mul,
      integral_add (integrableOn_Ioi_cexp_neg_mul hposm) (integrableOn_Ioi_cexp_neg_mul hposp),
      integral_Ioi_cexp_neg_mul hposm, integral_Ioi_cexp_neg_mul hposp]
  have hs := ofReal_sqrt_two_sq
  have hsne := ofReal_sqrt_two_ne_zero
  have hhalf : ((Real.sqrt 2 : ℝ) : ℂ) * (1 / 2) = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
    field_simp
    linear_combination hs
  rw [hsplit, quartetSymCoord, _root_.RHTower.ccmCausalResolvent,
    _root_.RHTower.ccmAntiCausalResolvent,
    show ((Real.sqrt 2 : ℝ) : ℂ) * (1 / 2 * (((x : ℂ) - lam)⁻¹ + ((x : ℂ) + star lam)⁻¹))
      = (((Real.sqrt 2 : ℝ) : ℂ) * (1 / 2)) * (((x : ℂ) - lam)⁻¹ + ((x : ℂ) + star lam)⁻¹) from
      by ring,
    hhalf, div_eq_inv_mul]

/-- **Equations (6) and (12), odd mode.**  The antisymmetric coordinate is the `sinh` Laplace
transform: the horizontal displacement is carried by the odd hyperbolic mode. -/
theorem quartetAntisymCoord_eq_laplace {lam : ℂ} {x : ℝ} (hx : |lam.re| < x) :
    quartetAntisymCoord lam x
      = ((Real.sqrt 2 : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ),
          Complex.exp (-((x : ℂ) * (t : ℂ))) * Complex.exp ((lam.im : ℂ) * Complex.I * (t : ℂ))
            * Complex.sinh ((lam.re : ℂ) * (t : ℂ)) := by
  have habs := abs_lt.mp hx
  have hposm : 0 < (((x : ℂ) - lam)).re := by rw [re_sub_ofReal]; linarith [habs.2]
  have hposp : 0 < (((x : ℂ) + star lam)).re := by rw [re_add_star_ofReal]; linarith [habs.1]
  have hsplit : (∫ t in Ioi (0 : ℝ),
      Complex.exp (-((x : ℂ) * (t : ℂ))) * Complex.exp ((lam.im : ℂ) * Complex.I * (t : ℂ))
        * Complex.sinh ((lam.re : ℂ) * (t : ℂ)))
      = (1 / 2) * (((x : ℂ) - lam)⁻¹ - ((x : ℂ) + star lam)⁻¹) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => cexp_ray_sinh_split lam x t,
      integral_const_mul,
      integral_sub (integrableOn_Ioi_cexp_neg_mul hposm) (integrableOn_Ioi_cexp_neg_mul hposp),
      integral_Ioi_cexp_neg_mul hposm, integral_Ioi_cexp_neg_mul hposp]
  have hs := ofReal_sqrt_two_sq
  have hsne := ofReal_sqrt_two_ne_zero
  have hhalf : ((Real.sqrt 2 : ℝ) : ℂ) * (1 / 2) = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
    field_simp
    linear_combination hs
  rw [hsplit, quartetAntisymCoord, _root_.RHTower.ccmCausalResolvent,
    _root_.RHTower.ccmAntiCausalResolvent,
    show ((Real.sqrt 2 : ℝ) : ℂ) * (1 / 2 * (((x : ℂ) - lam)⁻¹ - ((x : ℂ) + star lam)⁻¹))
      = (((Real.sqrt 2 : ℝ) : ℂ) * (1 / 2)) * (((x : ℂ) - lam)⁻¹ - ((x : ℂ) + star lam)⁻¹) from
      by ring,
    hhalf, div_eq_inv_mul]

/-! ## The anti-causal residue mode and the four-unit budget -/

/-- The anti-causal residue mode of equation `(14)`, with residue amplitude `2 m`. -/
def quartetResidueMode (lam : ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  (2 * (m : ℂ)) * Complex.exp (-((lam.re : ℂ) * (t : ℂ)))
    * Complex.exp ((lam.im : ℂ) * Complex.I * (t : ℂ))

theorem norm_quartetResidueMode (lam : ℂ) (m : ℕ) (t : ℝ) :
    ‖quartetResidueMode lam m t‖ = 2 * (m : ℝ) * Real.exp (-(lam.re * t)) := by
  have h1 : ‖Complex.exp (-((lam.re : ℂ) * (t : ℂ)))‖ = Real.exp (-(lam.re * t)) := by
    rw [Complex.norm_exp, re_neg_mul_ofReal, Complex.ofReal_re]
  have h2 : ‖Complex.exp ((lam.im : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
    rw [show (lam.im : ℂ) * Complex.I * (t : ℂ) = ((lam.im * t : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [quartetResidueMode, norm_mul, norm_mul, h1, h2, mul_one]
  congr 1
  rw [norm_mul]
  simp

/-- **Equation (15).**  The squared norm of the residue mode is `2 m^2 / a`. -/
theorem integral_norm_sq_quartetResidueMode {lam : ℂ} (ha : 0 < lam.re) (m : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖quartetResidueMode lam m t‖ ^ 2) = 2 * (m : ℝ) ^ 2 / lam.re := by
  have h2a : 0 < 2 * lam.re := by linarith
  have hcongr : ∀ t : ℝ, ‖quartetResidueMode lam m t‖ ^ 2
      = (4 * (m : ℝ) ^ 2) * Real.exp (-((2 * lam.re) * t)) := by
    intro t
    rw [norm_quartetResidueMode,
      show -((2 * lam.re) * t) = -(lam.re * t) + -(lam.re * t) from by ring, Real.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => hcongr t,
    integral_const_mul, integral_Ioi_exp_neg_mul h2a]
  field_simp
  ring

/-- **Equation (16).**  With `0 < a < 1/2` and multiplicity at least one, the metric reading strictly
exceeds four trace units per multiplicity unit. -/
theorem four_mul_lt_integral_norm_sq_quartetResidueMode {lam : ℂ} (ha : 0 < lam.re)
    (ha2 : lam.re < 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    4 * (m : ℝ) < ∫ t in Ioi (0 : ℝ), ‖quartetResidueMode lam m t‖ ^ 2 := by
  rw [integral_norm_sq_quartetResidueMode ha]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [lt_div_iff₀ ha]
  nlinarith

end GaloisForLFunctions.RHTower

end
