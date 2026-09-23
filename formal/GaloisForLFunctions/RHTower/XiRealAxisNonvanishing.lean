import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# The completed xi function has no real zero

Zeta does not vanish on the real segment `(0,1)`, because the fractional-part representation
`-zeta(s)/s = integral fract(u) u^(-s-1) du` has a strictly positive integrand there.  Together with
the Euler-product nonvanishing to the right of `1`, the value `xi 1 = 1/2`, and the reflection
`xi (1 - s) = xi s`, this gives nonvanishing of `xi` on the whole real axis.

In centered coordinates the real `s`-axis is the imaginary `z`-axis, so the centered function has no
purely imaginary zero.  Consequently a centered zero whose square is real is itself real --- the
reality step behind every folded second-order self-adjoint realization.
-/

open Complex

noncomputable section

namespace RHTower

/-- **The completed xi function has no real zero.**  On `(0,1)` this is the fractional-part
positivity of zeta; to the right of `1` it is the Euler-product nonvanishing; the reflection
`xi (1 - s) = xi s` covers the left. -/
theorem xi_ne_zero_of_real (σ : ℝ) : xi ((σ : ℝ) : ℂ) ≠ 0 := by
  have hhalf : ∀ τ : ℝ, 1 / 2 ≤ τ → xi ((τ : ℝ) : ℂ) ≠ 0 := by
    intro τ hτ
    rcases eq_or_ne τ 1 with rfl | hne
    · rw [show (((1 : ℝ)) : ℂ) = 1 by norm_num, xi_one]
      norm_num
    · have hre : 0 < (((τ : ℝ)) : ℂ).re := by
        rw [Complex.ofReal_re]
        linarith
      have h1 : (((τ : ℝ)) : ℂ) ≠ 1 := by
        intro h
        exact hne (by exact_mod_cast h)
      rw [Ne, xi_eq_zero_iff hre h1]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact riemannZeta_ne_zero_of_ofReal_mem_Ioo (by linarith) hlt
      · refine riemannZeta_ne_zero_of_one_le_re ?_
        rw [Complex.ofReal_re]
        linarith
  rcases le_or_gt (1 / 2 : ℝ) σ with hge | hlt
  · exact hhalf σ hge
  · have hsub : xi ((((1 - σ : ℝ)) : ℂ)) = xi ((σ : ℝ) : ℂ) := by
      rw [show ((((1 - σ : ℝ)) : ℂ)) = 1 - ((σ : ℝ) : ℂ) by push_cast; ring]
      exact xi_one_sub _
    rw [← hsub]
    exact hhalf (1 - σ) (by linarith)

/-- **The centered xi function has no purely imaginary zero.**  In centered coordinates the
imaginary axis is the real `s`-axis, where `xi` never vanishes. -/
theorem XiC_ne_zero_of_imaginary (y : ℝ) : XiC ((y : ℂ) * Complex.I) ≠ 0 := by
  have hval : XiC ((y : ℂ) * Complex.I) = xi (((1 / 2 - y : ℝ)) : ℂ) := by
    rw [XiC]
    congr 1
    rw [mul_assoc, Complex.I_mul_I]
    push_cast
    ring
  rw [hval]
  exact xi_ne_zero_of_real _

/-- **A centered Xi zero with real square is real.**  This is the reality step behind the folded
second-order realization: the folded eigenvalue is `alpha^(2 : ℕ)`, and a self-adjoint realization forces
it real, which forces `alpha` itself real because no purely imaginary point is a zero. -/
theorem XiC_im_eq_zero_of_sq_im_eq_zero {α : ℂ} (hα : XiC α = 0) (hsq : (α ^ 2).im = 0) :
    α.im = 0 := by
  have hprod : α.re * α.im = 0 := by
    have h : (α ^ 2).im = 2 * (α.re * α.im) := by
      rw [pow_two, Complex.mul_im]
      ring
    rw [h] at hsq
    linarith
  rcases mul_eq_zero.mp hprod with hre | him
  · exfalso
    have hform : α = ((α.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hre]
    rw [hform] at hα
    exact XiC_ne_zero_of_imaginary α.im hα
  · exact him

end RHTower
