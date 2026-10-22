import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFunctionCriterion
import GaloisForLFunctions.RHTower.GaussHodgeWeilDeviationMoment
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The exponential zero series for Suzuki's screw kernel

This module proves the identity

```text
G_g(t, u) = ∑_γ m_γ (e^{iγt} - 1)(e^{-iγu} - 1) / γ²,
```

equation (1.9) of Suzuki, *Aspects of the screw function corresponding to the Riemann
zeta-function*, where the sum runs over the zeros of `ξ` in the centered spectral coordinate,
counted with multiplicity.

The identity is unconditional.  The exponentials are controlled by the critical-strip bound
`|Im γ| < 1/2`, which makes each summand `O(‖γ‖^{-2})` and hence summable.  Summing the series
against the reflection `γ ↦ -γ` of the divisor replaces each exponential by a hyperbolic cosine
and produces exactly the combination `-Ψ(t - u) + Ψ(t) + Ψ(u)` defining `G_g`.
-/

open Complex

namespace RHTower
noncomputable section

/-- The exponential zero-series summand of Suzuki's screw kernel. -/
def suzukiScrewExpTerm (t u : ℝ) (q : XiZeroCopy) : ℂ :=
  (Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) *
    (Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1) / xiSpectralPoint q ^ (2 : ℕ)

theorem norm_exp_I_xiSpectralPoint_mul_le (t : ℝ) (q : XiZeroCopy) :
    ‖Complex.exp (I * xiSpectralPoint q * (t : ℂ))‖ ≤ Real.exp (|t| / 2) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have him := abs_xiSpectralPoint_im_lt_half q
  have hre : (I * xiSpectralPoint q * (t : ℂ)).re = -((xiSpectralPoint q).im * t) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have h1 : |(xiSpectralPoint q).im * t| ≤ |t| / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg t, him, abs_nonneg ((xiSpectralPoint q).im)]
  linarith [neg_abs_le ((xiSpectralPoint q).im * t), h1]

theorem norm_suzukiScrewExpTerm_le (t u : ℝ) (q : XiZeroCopy) :
    ‖suzukiScrewExpTerm t u q‖ ≤
      ((Real.exp (|t| / 2) + 1) * (Real.exp (|u| / 2) + 1)) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  have h1 : ‖Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1‖ ≤ Real.exp (|t| / 2) + 1 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one]
    linarith [norm_exp_I_xiSpectralPoint_mul_le t q]
  have h2 : ‖Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1‖ ≤ Real.exp (|u| / 2) + 1 := by
    have hneg : -(I * xiSpectralPoint q * (u : ℂ)) = I * xiSpectralPoint q * ((-u : ℝ) : ℂ) := by
      push_cast; ring
    rw [hneg]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one]
    have := norm_exp_I_xiSpectralPoint_mul_le (-u) q
    rw [abs_neg] at this
    linarith
  rw [suzukiScrewExpTerm, norm_div, norm_mul, norm_pow, mul_one_div]
  gcongr

theorem summable_suzukiScrewExpTerm (t u : ℝ) :
    Summable (fun q : XiZeroCopy => suzukiScrewExpTerm t u q) :=
  Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left
      ((Real.exp (|t| / 2) + 1) * (Real.exp (|u| / 2) + 1)))
    (fun q => norm_suzukiScrewExpTerm_le t u q)

/-- The exponential pair identity behind the reflection symmetrization. -/
theorem screw_exp_pair_identity (w a b : ℂ) (hw : w ≠ 0) :
    (Complex.exp (w * a) - 1) * (Complex.exp (-(w * b)) - 1) / (-w ^ (2 : ℕ))
      + (Complex.exp (-(w * a)) - 1) * (Complex.exp (w * b) - 1) / (-w ^ (2 : ℕ))
      = 2 * (-((Complex.cosh ((a - b) * w) - 1) / w ^ (2 : ℕ))
          + (Complex.cosh (a * w) - 1) / w ^ (2 : ℕ) + (Complex.cosh (b * w) - 1) / w ^ (2 : ℕ)) := by
  rw [Complex.cosh, Complex.cosh, Complex.cosh]
  rw [show ((a - b) * w) = w * a - w * b by ring, show (a * w) = w * a by ring,
      show (b * w) = w * b by ring]
  rw [Complex.exp_sub, show (-(w * a - w * b)) = w * b - w * a by ring, Complex.exp_sub,
      Complex.exp_neg, Complex.exp_neg]
  have hX : Complex.exp (w * a) ≠ 0 := Complex.exp_ne_zero _
  have hY : Complex.exp (w * b) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

theorem suzukiScrewExpTerm_add_reflect (t u : ℝ) (q : XiZeroCopy) :
    suzukiScrewExpTerm t u q + suzukiScrewExpTerm t u (xiZeroCopyReflectEquiv q) =
      2 * (-xiScrewDivisorTerm (t - u) q + xiScrewDivisorTerm t q + xiScrewDivisorTerm u q) := by
  have hrefl : xiSpectralPoint (xiZeroCopyReflectEquiv q) = -xiSpectralPoint q :=
    xiSpectralPoint_reflect q
  have hwne : I * xiSpectralPoint q ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (xiSpectralPoint_ne_zero q)
  have hkey := screw_exp_pair_identity (I * xiSpectralPoint q) (t : ℂ) (u : ℂ) hwne
  have hsq : xiSpectralPoint q ^ (2 : ℕ) = -(I * xiSpectralPoint q) ^ (2 : ℕ) := by
    rw [mul_pow, Complex.I_sq]; ring
  have hcast : ((t - u : ℝ) : ℂ) = (t : ℂ) - (u : ℂ) := by push_cast; ring
  simp only [suzukiScrewExpTerm, xiScrewDivisorTerm, hsq, hrefl, hcast]
  rw [show ((-xiSpectralPoint q : ℂ)) ^ (2 : ℕ) = -(I * xiSpectralPoint q) ^ (2 : ℕ) by
    rw [neg_pow, mul_pow, Complex.I_sq]; ring]
  rw [show I * -xiSpectralPoint q * (t : ℂ) = -(I * xiSpectralPoint q * (t : ℂ)) by ring,
    show -(I * -xiSpectralPoint q * (u : ℂ)) = I * xiSpectralPoint q * (u : ℂ) by ring]
  exact hkey

/-- **The exponential zero series for Suzuki's screw kernel** (Su22, equation (1.9)).
Unconditional: the strip bound alone controls the exponentials, and the divisor's reflection
symmetry converts the symmetrized exponential sum into the cosine series defining `Psi`. -/
theorem suzukiScrewKernel_eq_tsum (t u : ℝ) :
    suzukiScrewKernel t u = ∑' q : XiZeroCopy, suzukiScrewExpTerm t u q := by
  have hsum := summable_suzukiScrewExpTerm t u
  have hsumr : Summable (fun q : XiZeroCopy =>
      suzukiScrewExpTerm t u (xiZeroCopyReflectEquiv q)) :=
    hsum.comp_injective xiZeroCopyReflectEquiv.injective
  have hrefl : ∑' q : XiZeroCopy, suzukiScrewExpTerm t u (xiZeroCopyReflectEquiv q)
      = ∑' q : XiZeroCopy, suzukiScrewExpTerm t u q :=
    xiZeroCopyReflectEquiv.tsum_eq _
  have hdouble : (2 : ℂ) * ∑' q : XiZeroCopy, suzukiScrewExpTerm t u q
      = ∑' q : XiZeroCopy,
          (suzukiScrewExpTerm t u q + suzukiScrewExpTerm t u (xiZeroCopyReflectEquiv q)) := by
    rw [hsum.tsum_add hsumr, hrefl]; ring
  have hrhs : ∑' q : XiZeroCopy,
      (suzukiScrewExpTerm t u q + suzukiScrewExpTerm t u (xiZeroCopyReflectEquiv q))
      = 2 * (-xiScrewDivisor (t - u) + xiScrewDivisor t + xiScrewDivisor u) := by
    rw [tsum_congr (fun q => suzukiScrewExpTerm_add_reflect t u q), tsum_mul_left]
    congr 1
    rw [xiScrewDivisor, xiScrewDivisor, xiScrewDivisor]
    rw [Summable.tsum_add
        (((xiScrewDivisorTerm_summable (t - u)).neg).add (xiScrewDivisorTerm_summable t))
        (xiScrewDivisorTerm_summable u),
      Summable.tsum_add ((xiScrewDivisorTerm_summable (t - u)).neg)
        (xiScrewDivisorTerm_summable t),
      tsum_neg]
  have hker : suzukiScrewKernel t u =
      -xiScrewDivisor (t - u) + xiScrewDivisor t + xiScrewDivisor u := by
    have h1 := ofReal_suzukiPsi_eq_xiScrewDivisor_all (t - u)
    have h2 := ofReal_suzukiPsi_eq_xiScrewDivisor_all t
    have h3 := ofReal_suzukiPsi_eq_xiScrewDivisor_all u
    have hkernel : suzukiScrewKernel t u =
        ((-suzukiPsi (t - u) + suzukiPsi t + suzukiPsi u : ℝ) : ℂ) := by
      simp [suzukiScrewKernel, suzukiScrewG]
    rw [hkernel]
    push_cast
    rw [h1, h2, h3]
  have hcancel : ∑' q : XiZeroCopy, suzukiScrewExpTerm t u q
      = -xiScrewDivisor (t - u) + xiScrewDivisor t + xiScrewDivisor u := by
    have h2 : (2 : ℂ) * ∑' q : XiZeroCopy, suzukiScrewExpTerm t u q
        = 2 * (-xiScrewDivisor (t - u) + xiScrewDivisor t + xiScrewDivisor u) := by
      rw [hdouble, hrhs]
    exact mul_left_cancel₀ (by norm_num) h2
  rw [hker, hcancel]

end
end RHTower
