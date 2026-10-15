import GaloisForLFunctions.RHTower.ThetaRenewalFullDivisorCharge
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The full renewal charge is an injective analytic coordinate

The literal exit law has mass one and mean `q/a`, where `a=1/4`,
`c=Theta(1)`, and the renewal mass satisfies `0<q<1`. Its Laplace transform
is therefore `q/a`-Lipschitz on the closed right half-plane. The exact
service-law identity makes `A(lambda)-c*lambda` a `c*q`-Lipschitz remainder
on `Re lambda >= -a`.

Reflection gives the same remainder bound for `C(lambda)+i*c*lambda`
throughout the closed critical strip. Since `q<1`, the full charge is
injective there, its real values occur exactly on the critical axis, and
its derivative has strictly negative imaginary part in the interior.
The physical boundary charge is strictly increasing at all heights.

This establishes a coordinate with no branching. It does not show that
Xi's full divisor has real charge and makes no zero-location assumption.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta
open scoped ComplexConjugate

namespace RHTower
noncomputable section
local notation "Θ" => evenKernel (0 : UnitAddCircle)

private theorem norm_exp_sub_exp_le_left {z w : ℂ}
    (hz : z.re ≤ 0) (hw : w.re ≤ 0) : ‖cexp z - cexp w‖ ≤ ‖z - w‖ := by
  have hc : Convex ℝ {v : ℂ | v.re ≤ 0} := by
    intro x hx y hy a b ha hb hab
    change (a • x + b • y).re ≤ 0
    simp only [add_re, Complex.smul_re, smul_eq_mul]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
      (mul_nonpos_of_nonneg_of_nonpos hb hy)
  have h := hc.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v _ => (Complex.hasDerivAt_exp v).hasDerivWithinAt)
    (C := 1) (fun v hv => by rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hv)
    hw hz
  simpa using h

private theorem integrableOn_exitLaplace {s : ℂ} (hs : 0 ≤ s.re) :
    IntegrableOn (fun t : ℝ => cexp (-(s * t)) * (thetaRenewalExitDensity t : ℂ)) (Ioi 0) := by
  apply integrableOn_thetaRenewalExitDensity.mono'
  · exact ((by fun_prop : Continuous fun t : ℝ => cexp (-(s * t))).mul
      (Complex.continuous_ofReal.comp continuous_thetaRenewalExitDensity)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_of_nonneg (thetaRenewalExitDensity_pos t).le]
    have he : Real.exp (-(s * (t : ℂ))).re ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact neg_nonpos.mpr (mul_nonneg hs ht0)
    simpa using mul_le_mul_of_nonneg_right he (thetaRenewalExitDensity_pos t).le

private theorem norm_exitLaplace_sub_le {s r : ℂ} (hs : 0 ≤ s.re) (hr : 0 ≤ r.re) :
    ‖(∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (thetaRenewalExitDensity t : ℂ)) -
      ∫ t in Ioi (0 : ℝ), cexp (-(r * t)) * (thetaRenewalExitDensity t : ℂ)‖ ≤
      (thetaRenewalMass / (1 / 4)) * ‖s - r‖ := by
  rw [← integral_sub (integrableOn_exitLaplace hs) (integrableOn_exitLaplace hr)]
  have h := norm_integral_le_of_norm_le
    (f := fun t : ℝ => cexp (-(s * t)) * (thetaRenewalExitDensity t : ℂ) -
      cexp (-(r * t)) * (thetaRenewalExitDensity t : ℂ))
    (integral_mul_thetaRenewalExitDensity.1.mul_const ‖s - r‖) ?_
  · simpa only [integral_mul_const, integral_mul_thetaRenewalExitDensity.2] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hsr : (-(s * (t : ℂ))).re ≤ 0 := by
      simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact neg_nonpos.mpr (mul_nonneg hs ht0)
    have hrr : (-(r * (t : ℂ))).re ≤ 0 := by
      simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact neg_nonpos.mpr (mul_nonneg hr ht0)
    have hnorm := norm_exp_sub_exp_le_left hsr hrr
    rw [show -(s * (t : ℂ)) - -(r * (t : ℂ)) = -(s - r) * t by ring,
      norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht0] at hnorm
    rw [← sub_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (thetaRenewalExitDensity_pos t).le]
    calc ‖cexp (-(s * (t : ℂ))) - cexp (-(r * (t : ℂ)))‖ * thetaRenewalExitDensity t
        ≤ (‖s - r‖ * t) * thetaRenewalExitDensity t :=
          mul_le_mul_of_nonneg_right hnorm (thetaRenewalExitDensity_pos t).le
      _ = (t * thetaRenewalExitDensity t) * ‖s - r‖ := by ring

/-- The exact positive exit-law representation of the linear channel remainder. -/
theorem thetaLoopA_sub_linear_eq_exitLaplace (lam : ℂ) :
    thetaLoopA lam - (Θ 1 : ℂ) * lam =
      (1 / 4) * (Θ 1 : ℂ) *
        ∫ t in Ioi (0 : ℝ), cexp (-((1 / 4 + lam) * t)) *
          (thetaRenewalExitDensity t : ℂ) := by
  have hI : I * (I * lam) = -lam := by linear_combination lam * I_sq
  have hterm : I * (Θ 1 : ℂ) * (I * lam) = -(Θ 1 : ℂ) * lam := by
    linear_combination ((Θ 1 : ℂ) * lam) * I_sq
  have h := thetaOneSidedConnection_two_mul_eq_denominator (I * lam)
  rw [hI, sub_neg_eq_add, neg_neg, hterm] at h
  rw [thetaOneSidedConnection_two_mul_eq_exitDensity, hI, sub_neg_eq_add] at h
  change _ = thetaLoopA lam + -(Θ 1 : ℂ) * lam at h
  linear_combination -h

/-- The channel remainder is a strict Lipschitz perturbation on the whole shifted half-plane. -/
theorem norm_thetaLoopA_sub_linear_sub_le {lam mu : ℂ}
    (hlam : -(1 / 4) ≤ lam.re) (hmu : -(1 / 4) ≤ mu.re) :
    ‖thetaLoopA lam - thetaLoopA mu - (Θ 1 : ℂ) * (lam - mu)‖ ≤
      Θ 1 * thetaRenewalMass * ‖lam - mu‖ := by
  have hs : 0 ≤ ((1 / 4 : ℂ) + lam).re := by simp only [add_re]; norm_num; linarith
  have hr : 0 ≤ ((1 / 4 : ℂ) + mu).re := by simp only [add_re]; norm_num; linarith
  have h := norm_exitLaplace_sub_le hs hr
  rw [add_sub_add_left_eq_sub] at h
  rw [show thetaLoopA lam - thetaLoopA mu - (Θ 1 : ℂ) * (lam - mu) =
    (thetaLoopA lam - (Θ 1 : ℂ) * lam) -
      (thetaLoopA mu - (Θ 1 : ℂ) * mu) by ring,
    thetaLoopA_sub_linear_eq_exitLaplace, thetaLoopA_sub_linear_eq_exitLaplace,
    ← mul_sub, norm_mul]
  have hc : ‖(1 / 4 : ℂ) * (Θ 1 : ℂ)‖ = 1 / 4 * Θ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg thetaSeam_pos.le]
    norm_num
  rw [hc]
  calc _ ≤ (1 / 4 * Θ 1) * ((thetaRenewalMass / (1 / 4)) * ‖lam - mu‖) :=
        mul_le_mul_of_nonneg_left h (by positivity [thetaSeam_pos])
    _ = _ := by ring

/-- Both reflected channels retain the same strict remainder bound on the closed strip. -/
theorem norm_thetaRenewalFullCharge_sub_linear_sub_le {lam mu : ℂ}
    (hlam : |lam.re| ≤ 1 / 4) (hmu : |mu.re| ≤ 1 / 4) :
    ‖thetaRenewalFullCharge lam - thetaRenewalFullCharge mu +
      I * (Θ 1 : ℂ) * (lam - mu)‖ ≤ Θ 1 * thetaRenewalMass * ‖lam - mu‖ := by
  have h1 := norm_thetaLoopA_sub_linear_sub_le (abs_le.mp hlam).1 (abs_le.mp hmu).1
  have h2 := norm_thetaLoopA_sub_linear_sub_le
    (lam := -lam) (mu := -mu) (by simpa using neg_le_neg (abs_le.mp hlam).2)
      (by simpa using neg_le_neg (abs_le.mp hmu).2)
  have hn : ‖-lam - -mu‖ = ‖lam - mu‖ := by rw [neg_sub_neg, norm_sub_rev]
  rw [hn] at h2
  have he : thetaRenewalFullCharge lam - thetaRenewalFullCharge mu +
      I * (Θ 1 : ℂ) * (lam - mu) =
      ((thetaLoopA lam - thetaLoopA mu - (Θ 1 : ℂ) * (lam - mu)) -
        (thetaLoopA (-lam) - thetaLoopA (-mu) - (Θ 1 : ℂ) * (-lam - -mu))) /
        (2 * I) := by
    simp only [thetaRenewalFullCharge, thetaLoopB, thetaLoopA]
    field_simp
    rw [I_sq]
    ring
  rw [he, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
  have ht := norm_sub_le
    (thetaLoopA lam - thetaLoopA mu - (Θ 1 : ℂ) * (lam - mu))
    (thetaLoopA (-lam) - thetaLoopA (-mu) - (Θ 1 : ℂ) * (-lam - -mu))
  linarith

/-- The physical charge separates every two points of the closed critical strip. -/
theorem thetaRenewalFullCharge_lower_lipschitz {lam mu : ℂ}
    (hlam : |lam.re| ≤ 1 / 4) (hmu : |mu.re| ≤ 1 / 4) :
    Θ 1 * (1 - thetaRenewalMass) * ‖lam - mu‖ ≤
      ‖thetaRenewalFullCharge lam - thetaRenewalFullCharge mu‖ := by
  have he := norm_thetaRenewalFullCharge_sub_linear_sub_le hlam hmu
  have ht := norm_sub_le
    (thetaRenewalFullCharge lam - thetaRenewalFullCharge mu + I * (Θ 1 : ℂ) * (lam - mu))
    (thetaRenewalFullCharge lam - thetaRenewalFullCharge mu)
  rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg thetaSeam_pos.le] at ht
  nlinarith

/-- No folds of the full physical charge occur anywhere in the closed critical strip. -/
theorem thetaRenewalFullCharge_injOn :
    Set.InjOn thetaRenewalFullCharge {lam : ℂ | |lam.re| ≤ 1 / 4} := by
  intro lam hlam mu hmu heq
  have h := thetaRenewalFullCharge_lower_lipschitz hlam hmu
  rw [heq, sub_self, norm_zero] at h
  have hp : 0 < Θ 1 * (1 - thetaRenewalMass) :=
    mul_pos thetaSeam_pos (by linarith [thetaRenewalMass_lt])
  have hn : ‖lam - mu‖ = 0 := by nlinarith [norm_nonneg (lam - mu)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Reality of the physical charge characterizes the critical axis, without a zero premise. -/
theorem im_thetaRenewalFullCharge_eq_zero_iff {x y : ℝ} (hx : |x| ≤ 1 / 4) :
    (thetaRenewalFullCharge (x + y * I)).im = 0 ↔ x = 0 := by
  constructor
  · intro him
    have hc : conj (thetaRenewalFullCharge (x + y * I)) =
        thetaRenewalFullCharge (x + y * I) := by
      apply Complex.ext <;> simp [him]
    have heq := thetaRenewalFullCharge_injOn
      (x₁ := (-x : ℂ) + y * I) (x₂ := (x : ℂ) + y * I)
      (by simpa using hx) (by simpa using hx)
      ((thetaRenewalFullCharge_reflect x y).trans hc)
    have hre := congrArg Complex.re heq
    simp only [add_re, neg_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at hre
    linarith
  · rintro rfl
    simp [thetaRenewalFullCharge_I_mul]

/-- A positive uniform lower slope for the physical boundary clock. -/
theorem thetaLoopCharge_sub_lower {u v : ℝ} (huv : u ≤ v) :
    Θ 1 * (1 - thetaRenewalMass) * (v - u) ≤ thetaLoopCharge v - thetaLoopCharge u := by
  have h := norm_thetaRenewalFullCharge_sub_linear_sub_le
    (lam := (v : ℂ) * I) (mu := (u : ℂ) * I) (by simp) (by simp)
  rw [thetaRenewalFullCharge_I_mul, thetaRenewalFullCharge_I_mul] at h
  have he : (thetaLoopCharge v : ℂ) - (thetaLoopCharge u : ℂ) +
      I * (Θ 1 : ℂ) * ((v : ℂ) * I - (u : ℂ) * I) =
      ((thetaLoopCharge v - thetaLoopCharge u - Θ 1 * (v - u) : ℝ) : ℂ) := by
    push_cast
    linear_combination ((Θ 1 : ℂ) * ((v : ℂ) - (u : ℂ))) * I_sq
  have hd : ‖(v : ℂ) * I - (u : ℂ) * I‖ = v - u := by
    rw [← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr huv)]
  rw [he, Complex.norm_real, Real.norm_eq_abs, hd] at h
  have hl := (abs_le.mp h).1
  nlinarith

/-- The physical boundary charge is globally strictly increasing. -/
theorem strictMono_thetaLoopCharge : StrictMono thetaLoopCharge := by
  intro u v huv
  have h := thetaLoopCharge_sub_lower huv.le
  have hc : 0 < Θ 1 * (1 - thetaRenewalMass) :=
    mul_pos thetaSeam_pos (by linarith [thetaRenewalMass_lt])
  have hp := mul_pos hc (sub_pos.mpr huv)
  linarith

/-- The derivative inherits the strict linear remainder bound. -/
theorem norm_deriv_thetaRenewalFullCharge_add_linear_le {lam : ℂ}
    (hlam : |lam.re| < 1 / 4) :
    ‖deriv thetaRenewalFullCharge lam + I * (Θ 1 : ℂ)‖ ≤ Θ 1 * thetaRenewalMass := by
  have hd := (differentiable_thetaRenewalFullCharge lam).hasDerivAt.add
    ((hasDerivAt_id lam).const_mul (I * (Θ 1 : ℂ)))
  simp only [mul_one] at hd
  apply hd.le_of_lip' (mul_nonneg thetaSeam_pos.le thetaRenewalMass_pos.le)
  have hnear : ∀ᶠ z : ℂ in 𝓝 lam, |z.re| < 1 / 4 :=
    (Complex.continuous_re.abs.continuousAt.tendsto).eventually (gt_mem_nhds hlam)
  filter_upwards [hnear] with z hz
  have h := norm_thetaRenewalFullCharge_sub_linear_sub_le hz.le hlam.le
  convert h using 1
  congr 1
  simp only [Pi.add_apply, id_eq]
  ring

/-- The charge coordinate has a fixed derivative orientation throughout the open strip. -/
theorem im_deriv_thetaRenewalFullCharge_neg {lam : ℂ}
    (hlam : |lam.re| < 1 / 4) : (deriv thetaRenewalFullCharge lam).im < 0 := by
  have h := norm_deriv_thetaRenewalFullCharge_add_linear_le hlam
  have hi := Complex.im_le_norm (deriv thetaRenewalFullCharge lam + I * (Θ 1 : ℂ))
  simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, zero_add] at hi
  have hp : 0 < Θ 1 * (1 - thetaRenewalMass) :=
    mul_pos thetaSeam_pos (by linarith [thetaRenewalMass_lt])
  nlinarith

/-- The charge coordinate has no interior critical points. -/
theorem deriv_thetaRenewalFullCharge_ne_zero {lam : ℂ}
    (hlam : |lam.re| < 1 / 4) : deriv thetaRenewalFullCharge lam ≠ 0 := by
  intro hz
  have h := im_deriv_thetaRenewalFullCharge_neg hlam
  simp [hz] at h

/-- Every interior point has local coordinate order one, including all divisor points. -/
theorem analyticOrderAt_thetaRenewalFullCharge_sub {lam : ℂ}
    (hlam : |lam.re| < 1 / 4) :
    analyticOrderAt (fun z => thetaRenewalFullCharge z - thetaRenewalFullCharge lam) lam = 1 :=
  (differentiable_thetaRenewalFullCharge.analyticAt lam).analyticOrderAt_sub_eq_one_of_deriv_ne_zero
    (deriv_thetaRenewalFullCharge_ne_zero hlam)

end
end RHTower
