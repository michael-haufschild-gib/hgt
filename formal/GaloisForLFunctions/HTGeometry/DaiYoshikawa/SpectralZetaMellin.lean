import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Mellin representation of an eigenvalue power

Section 3.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), defines the analytic torsion through the spectral zeta function

```text
ζ(s) = Σ_{λ>0} λ^{−s} = (1/Γ(s)) ∫_0^∞ (Tr e^{−tΔ} − h) t^{s−1} dt .
```

The elementary identity behind that formula is the scaled Gamma integral

```text
∫_0^∞ e^{−λt} t^{s−1} dt = Γ(s) λ^{−s}          (λ > 0, s > 0),
```

which mathlib does not carry: it has the Gamma integral itself and the change of variables on
`Ioi 0`, but not their combination.  This file supplies it, together with the convergence of the
scaled integrand, so that summing over the spectrum is the only remaining step.
-/

open MeasureTheory Set Real

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- **The scaled Gamma integral.**  `∫_0^∞ e^{−bx} x^{s−1} dx = Γ(s)/b^s` for `b, s > 0`. -/
theorem integral_exp_neg_mul_rpow {b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(b * x)) * x ^ (s - 1)) = Real.Gamma s / b ^ s := by
  have hchange := integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y) * y ^ (s - 1)) 0 hb
  rw [mul_zero] at hchange
  have hsplit : (∫ x in Ioi (0 : ℝ), Real.exp (-(b * x)) * (b * x) ^ (s - 1))
      = b ^ (s - 1) * ∫ x in Ioi (0 : ℝ), Real.exp (-(b * x)) * x ^ (s - 1) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.mul_rpow hb.le hx0.le]
    ring
  rw [hsplit] at hchange
  rw [smul_eq_mul, ← Real.Gamma_eq_integral hs] at hchange
  have hbpos : (0 : ℝ) < b ^ s := Real.rpow_pos_of_pos hb s
  have hprod : b ^ (s - 1) * b = b ^ s := by
    have hadd : b ^ (s - 1) * b ^ (1 : ℝ) = b ^ (s - 1 + 1) := (Real.rpow_add hb _ _).symm
    rw [Real.rpow_one] at hadd
    rw [hadd]
    norm_num
  rw [eq_div_iff (ne_of_gt hbpos), ← hprod]
  have hcomm : (∫ x in Ioi (0 : ℝ), Real.exp (-(b * x)) * x ^ (s - 1)) * (b ^ (s - 1) * b)
      = (b ^ (s - 1) * ∫ x in Ioi (0 : ℝ), Real.exp (-(b * x)) * x ^ (s - 1)) * b := by
    ring
  rw [hcomm, hchange]
  field_simp

/-- The Mellin representation of a single eigenvalue power:
`Γ(s) λ^{−s} = ∫_0^∞ e^{−λt} t^{s−1} dt`. -/
theorem gamma_mul_rpow_neg_eq_integral {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) :
    Real.Gamma s * lam ^ (-s) = ∫ t in Ioi (0 : ℝ), Real.exp (-(lam * t)) * t ^ (s - 1) := by
  rw [integral_exp_neg_mul_rpow hlam hs, Real.rpow_neg hlam.le]
  field_simp

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
