import GaloisForLFunctions.RHTower.Deninger.DeningerZetaLowerBound
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import GaloisForLFunctions.RHTower.CothInfra

/-!
# The archimedean factor of the functional equation is bounded below

Euler's reflection formula computes the modulus of the Gamma factor on a vertical line exactly:
`|Γ(1 − it)|² = πt/sinh(πt)`.  Combined with the elementary inequality `sinh u ≤ u cosh u` this
gives

`cosh²(πt/2)·|Γ(2 − it)|² ≥ 1 + t²`,

which is the lower bound for the archimedean factor of the functional equation on the line
`Re s = −1`.  No Stirling asymptotics are involved.

* `one_le_mul_cosh_div_sinh` : `1 ≤ u cosh u / sinh u` for `u ≠ 0`.
* `norm_Gamma_one_sub_mul_I_sq` : **`|Γ(1 − it)|² = πt/sinh(πt)`.**
* `one_add_sq_le_cosh_sq_mul_gamma` : **`1 + t² ≤ cosh²(πt/2)|Γ(2 − it)|²`.**
-/

open scoped Real
open Complex

noncomputable section

namespace RHTower

/-! ## Two hyperbolic inequalities -/

theorem one_le_mul_cosh_div_sinh {u : ℝ} (hu : u ≠ 0) :
    (1 : ℝ) ≤ u * Real.cosh u / Real.sinh u := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have hsinh : Real.sinh u < 0 := Real.sinh_neg_iff.mpr hneg
    rw [le_div_iff_of_neg hsinh]
    have h := sinh_le_mul_cosh (x := -u) (by linarith)
    rw [Real.sinh_neg, Real.cosh_neg] at h
    linarith
  · have hsinh : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hpos
    rw [le_div_iff₀ hsinh]
    have h := sinh_le_mul_cosh (x := u) hpos.le
    linarith

/-! ## The modulus of the Gamma factor -/

theorem pi_mul_div_sinh_pos {t : ℝ} (ht : t ≠ 0) : 0 < π * t / Real.sinh (π * t) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have hnum : π * t < 0 := by nlinarith
    have hden : Real.sinh (π * t) < 0 := Real.sinh_neg_iff.mpr hnum
    exact div_pos_of_neg_of_neg hnum hden
  · have hnum : 0 < π * t := by positivity
    have hden : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr hnum
    exact div_pos hnum hden

theorem norm_Gamma_one_sub_mul_I_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 - (t : ℂ) * I)‖ ^ 2 = π * t / Real.sinh (π * t) := by
  have hIt : ((t : ℂ) * I) ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  have hrefl := Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * I)
  have hadd : Complex.Gamma ((t : ℂ) * I + 1) = ((t : ℂ) * I) * Complex.Gamma ((t : ℂ) * I) :=
    Complex.Gamma_add_one _ hIt
  have hsinh_ne : Real.sinh (π * t) ≠ 0 := by
    refine Real.sinh_ne_zero.mpr ?_
    have hpi : (0 : ℝ) < π := Real.pi_pos
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 hpi.ne'
    · exact ht h2
  have hsin : Complex.sin ((π : ℂ) * ((t : ℂ) * I)) = (Real.sinh (π * t) : ℂ) * I := by
    have h : (π : ℂ) * ((t : ℂ) * I) = ((π * t : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h, Complex.sin_mul_I]
    norm_cast
  have hprod : Complex.Gamma (1 + (t : ℂ) * I) * Complex.Gamma (1 - (t : ℂ) * I)
      = ((π * t / Real.sinh (π * t) : ℝ) : ℂ) := by
    have hcomm : Complex.Gamma (1 + (t : ℂ) * I)
        = ((t : ℂ) * I) * Complex.Gamma ((t : ℂ) * I) := by
      rw [← hadd]
      congr 1
      ring
    have hIne : ((Real.sinh (π * t) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsinh_ne
    rw [hcomm, mul_assoc, hrefl, hsin]
    have hcancel : ((t : ℂ) * I) * ((π : ℂ) / (((Real.sinh (π * t) : ℝ) : ℂ) * I))
        = ((t : ℂ) * (π : ℂ)) / ((Real.sinh (π * t) : ℝ) : ℂ) := by
      field_simp
    rw [hcancel]
    push_cast
    ring
  have hconj : Complex.Gamma (1 + (t : ℂ) * I)
      = (starRingEnd ℂ) (Complex.Gamma (1 - (t : ℂ) * I)) := by
    have hstar : (starRingEnd ℂ) (1 - (t : ℂ) * I) = 1 + (t : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [← hstar, Complex.Gamma_conj]
  rw [hconj] at hprod
  have hnorms := congrArg (fun z : ℂ => ‖z‖) hprod
  simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs] at hnorms
  rw [sq, hnorms, abs_of_pos (pi_mul_div_sinh_pos ht)]

/-! ## The archimedean factor -/

/-- **The archimedean factor of the functional equation is bounded below on the line
`Re s = −1`.** -/
theorem one_add_sq_le_cosh_sq_mul_gamma (t : ℝ) :
    1 + t ^ 2 ≤ Real.cosh (π * t / 2) ^ 2 * ‖Complex.Gamma (2 - (t : ℂ) * I)‖ ^ 2 := by
  have hgamma2 : Complex.Gamma (2 - (t : ℂ) * I)
      = (1 - (t : ℂ) * I) * Complex.Gamma (1 - (t : ℂ) * I) := by
    have h : (2 : ℂ) - (t : ℂ) * I = (1 - (t : ℂ) * I) + 1 := by ring
    rw [h]
    refine Complex.Gamma_add_one _ ?_
    intro hzero
    have hre : ((1 : ℂ) - (t : ℂ) * I).re = 1 := by simp
    rw [hzero] at hre
    norm_num at hre
  have habs : ‖(1 : ℂ) - (t : ℂ) * I‖ ^ 2 = 1 + t ^ 2 := by
    have h : ((1 : ℂ) - (t : ℂ) * I) = Complex.mk 1 (-t) := by
      apply Complex.ext <;> simp
    rw [h]
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _)]
    simp [Complex.normSq_apply]
    ring
  have hnorm : ‖Complex.Gamma (2 - (t : ℂ) * I)‖ ^ 2
      = (1 + t ^ 2) * ‖Complex.Gamma (1 - (t : ℂ) * I)‖ ^ 2 := by
    rw [hgamma2, norm_mul, mul_pow, habs]
  rw [hnorm]
  rcases eq_or_ne t 0 with rfl | ht
  · have hg : Complex.Gamma (1 - ((0 : ℝ) : ℂ) * I) = 1 := by
      norm_num [Complex.Gamma_one]
    rw [hg]
    norm_num
  rw [norm_Gamma_one_sub_mul_I_sq ht]
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hdouble : Real.sinh (π * t) = 2 * Real.sinh (π * t / 2) * Real.cosh (π * t / 2) := by
    have h := Real.sinh_two_mul (π * t / 2)
    rw [show 2 * (π * t / 2) = π * t by ring] at h
    rw [h]
  have hune : (π * t / 2) ≠ 0 :=
    div_ne_zero (mul_ne_zero hpi.ne' ht) two_ne_zero
  have hsinh_half : Real.sinh (π * t / 2) ≠ 0 := Real.sinh_ne_zero.mpr hune
  have hcosh_pos : (0 : ℝ) < Real.cosh (π * t / 2) := Real.cosh_pos _
  have hval : Real.cosh (π * t / 2) ^ 2 * (π * t / Real.sinh (π * t))
      = (π * t / 2) * Real.cosh (π * t / 2) / Real.sinh (π * t / 2) := by
    rw [hdouble]
    field_simp
  have hkey := one_le_mul_cosh_div_sinh hune
  have hcosh_sinh : (1 : ℝ) ≤ Real.cosh (π * t / 2) ^ 2 * (π * t / Real.sinh (π * t)) := by
    rw [hval]
    exact hkey
  have hpos : (0 : ℝ) ≤ 1 + t ^ 2 := by positivity
  nlinarith [hcosh_sinh, hpos]


/-! ## The lower bound on the line `Re s = −1` -/

theorem norm_cos_pi_two_sub_mul_I (t : ℝ) :
    ‖Complex.cos ((π : ℂ) * (2 - (t : ℂ) * I) / 2)‖ = Real.cosh (π * t / 2) := by
  have harg : (π : ℂ) * (2 - (t : ℂ) * I) / 2 = (π : ℂ) - ((π * t / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [harg, Complex.cos_pi_sub, Complex.cos_mul_I, norm_neg, ← Complex.ofReal_cosh,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]

theorem sqrt_one_add_sq_le_cosh_mul_gamma (t : ℝ) :
    Real.sqrt (1 + t ^ 2)
      ≤ Real.cosh (π * t / 2) * ‖Complex.Gamma (2 - (t : ℂ) * I)‖ := by
  have hsq := one_add_sq_le_cosh_sq_mul_gamma t
  have hnn : 0 ≤ Real.cosh (π * t / 2) * ‖Complex.Gamma (2 - (t : ℂ) * I)‖ := by
    have := Real.cosh_pos (π * t / 2)
    positivity
  have hle : Real.sqrt (1 + t ^ 2)
      ≤ Real.sqrt ((Real.cosh (π * t / 2) * ‖Complex.Gamma (2 - (t : ℂ) * I)‖) ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow]
    exact hsq
  rwa [Real.sqrt_sq hnn] at hle

/-- **Zeta is bounded below on the line `Re s = −1`**: the functional equation trades the value
there for a value on `Re s = 2`, where the Dirichlet series bounds it, times an archimedean factor
that only grows. -/
theorem norm_riemannZeta_left_line_ge (t : ℝ) :
    Real.sqrt (1 + t ^ 2) / (8 * π ^ 2) ≤ ‖riemannZeta (-1 + (t : ℂ) * I)‖ := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set s : ℂ := 2 - (t : ℂ) * I with hs
  have hsre : s.re = 2 := by
    rw [hs]
    simp
  have hne : ∀ n : ℕ, s ≠ -n := by
    intro n hcon
    have hre : s.re = -(n : ℝ) := by rw [hcon]; simp
    rw [hsre] at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hne1 : s ≠ 1 := by
    intro hcon
    have hre : s.re = 1 := by rw [hcon]; simp
    rw [hsre] at hre
    norm_num at hre
  have hfe := riemannZeta_one_sub hne hne1
  have harg : (1 : ℂ) - s = -1 + (t : ℂ) * I := by
    rw [hs]
    ring
  rw [harg] at hfe
  have hnorm : ‖riemannZeta (-1 + (t : ℂ) * I)‖
      = 2 * (2 * π) ^ (-(2 : ℝ)) * ‖Complex.Gamma s‖ * Real.cosh (π * t / 2)
        * ‖riemannZeta s‖ := by
    rw [hfe]
    have hbase : (0 : ℝ) < 2 * π := by positivity
    have hcpow : ‖((2 * π : ℂ)) ^ (-s)‖ = (2 * π) ^ (-(2 : ℝ)) := by
      have hcast : ((2 : ℂ) * (π : ℂ)) = (((2 * π : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hbase]
      congr 1
      rw [Complex.neg_re, hsre]
    have hcos : ‖Complex.cos ((π : ℂ) * s / 2)‖ = Real.cosh (π * t / 2) := by
      rw [hs]
      exact norm_cos_pi_two_sub_mul_I t
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hcpow, hcos]
    norm_num
  rw [hnorm]
  have hzeta : (1 : ℝ) / 4 ≤ ‖riemannZeta s‖ := by
    refine norm_riemannZeta_ge_of_two_le_re ?_
    rw [hsre]
  have hgamma : Real.sqrt (1 + t ^ 2)
      ≤ Real.cosh (π * t / 2) * ‖Complex.Gamma s‖ := by
    rw [hs]
    exact sqrt_one_add_sq_le_cosh_mul_gamma t
  have hcpowval : (2 * π) ^ (-(2 : ℝ)) = 1 / (4 * π ^ 2) := by
    rw [Real.rpow_neg (by positivity)]
    have h2 : (2 * π) ^ (2 : ℝ) = 4 * π ^ 2 := by
      rw [Real.rpow_two]
      ring
    rw [h2]
    ring
  rw [hcpowval]
  have hsqrtnn : 0 ≤ Real.sqrt (1 + t ^ 2) := Real.sqrt_nonneg _
  have hgnn : 0 ≤ ‖Complex.Gamma s‖ := norm_nonneg _
  have hznn : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  have hcoshnn : 0 < Real.cosh (π * t / 2) := Real.cosh_pos _
  have hstep : Real.sqrt (1 + t ^ 2) * (1 / 4)
      ≤ (Real.cosh (π * t / 2) * ‖Complex.Gamma s‖) * ‖riemannZeta s‖ := by
    have h1 : Real.sqrt (1 + t ^ 2) * (1 / 4)
        ≤ (Real.cosh (π * t / 2) * ‖Complex.Gamma s‖) * (1 / 4) := by
      refine mul_le_mul_of_nonneg_right hgamma (by norm_num)
    have h2 : (Real.cosh (π * t / 2) * ‖Complex.Gamma s‖) * (1 / 4)
        ≤ (Real.cosh (π * t / 2) * ‖Complex.Gamma s‖) * ‖riemannZeta s‖ := by
      refine mul_le_mul_of_nonneg_left hzeta ?_
      positivity
    linarith
  have hpi2 : (0 : ℝ) < 4 * π ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  have hfinal : 2 * (1 / (4 * π ^ 2)) * ‖Complex.Gamma s‖ * Real.cosh (π * t / 2)
      * ‖riemannZeta s‖ * (8 * π ^ 2)
      = 4 * ((Real.cosh (π * t / 2) * ‖Complex.Gamma s‖) * ‖riemannZeta s‖) := by
    field_simp
    ring
  rw [hfinal]
  linarith [hstep]

/-- The reciprocal of zeta is bounded on the line `Re s = −1`. -/
theorem norm_riemannZeta_left_line_ge_const (t : ℝ) :
    (1 : ℝ) / (8 * π ^ 2) ≤ ‖riemannZeta (-1 + (t : ℂ) * I)‖ := by
  have h := norm_riemannZeta_left_line_ge t
  have hone : (1 : ℝ) ≤ Real.sqrt (1 + t ^ 2) := by
    have hle : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_one] at this
  have hpi : (0 : ℝ) < 8 * π ^ 2 := by
    have := Real.pi_pos
    positivity
  have hmono : (1 : ℝ) / (8 * π ^ 2) ≤ Real.sqrt (1 + t ^ 2) / (8 * π ^ 2) := by
    refine div_le_div_of_nonneg_right hone ?_
    exact hpi.le
  linarith

end RHTower

end
