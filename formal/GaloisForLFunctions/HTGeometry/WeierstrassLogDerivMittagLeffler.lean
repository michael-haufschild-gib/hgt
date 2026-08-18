import GaloisForLFunctions.HTGeometry.MittagLefflerHalfPlaneApproximation
import GaloisForLFunctions.HTGeometry.WeierstrassFactorizationTheorem
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

/-!
# The logarithmic derivative of a Weierstrass product is a Mittag-Leffler series

The genus-`n` elementary factor at `a n` has

```text
logDeriv (fun z => weierstrassFactor n (z / a n)) z = (z / a n)^n / (z - a n)
                                                    = 1/(z - a n) - Q n z ,
Q n z = - (sum_{j<n} z^j (a n)^{n-1-j}) / (a n)^n ,
```

with `Q n` a polynomial, hence entire, and the remainder bounded by `2^{-n} * 2/‖a n‖` on the disc
of radius `‖a n‖/2`.  Termwise logarithmic differentiation of the locally uniformly convergent
product therefore exhibits `logDeriv (weierstrassGenusProduct a)` as a Mittag-Leffler series with
simple poles of residue one at the zeros.

Combined with `exists_entire_approx_sq_mittagLeffler` this gives the Arakelyan step for the
logarithmic derivative of any prescribed-divisor realization.
-/

noncomputable section

open Metric Filter Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The derivative of the `n`-th Weierstrass factor of a product. -/
theorem hasDerivAt_weierstrassGenusFactorAt (a : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    HasDerivAt (weierstrassGenusFactorAt a n)
      (-((z / a n) ^ n) * Complex.exp (weierstrassLog n (z / a n)) * (1 / a n)) z := by
  have h1 : HasDerivAt (fun w : ℂ => w / a n) (1 / a n) z := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id z).div_const (a n)
  exact (hasDerivAt_weierstrassFactor n (z / a n)).comp z h1

/-- **The logarithmic derivative of the `n`-th factor.** -/
theorem logDeriv_weierstrassGenusFactorAt {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (n : ℕ) {z : ℂ}
    (hz : z ≠ a n) :
    logDeriv (weierstrassGenusFactorAt a n) z = (z / a n) ^ n / (z - a n) := by
  have han : a n ≠ 0 := hane n
  have hzan : z - a n ≠ 0 := sub_ne_zero.mpr hz
  have hone : (1 : ℂ) - z / a n ≠ 0 := by
    intro h
    apply hzan
    field_simp at h
    linear_combination -h
  have hexp : Complex.exp (weierstrassLog n (z / a n)) ≠ 0 := Complex.exp_ne_zero _
  rw [logDeriv_apply, (hasDerivAt_weierstrassGenusFactorAt a n z).deriv,
    weierstrassGenusFactorAt, weierstrassFactor]
  field_simp
  ring

/-- The polynomial correction attached to the `n`-th factor. -/
def weierstrassMittagLefflerCorrection (a : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  -(∑ j ∈ Finset.range n, z ^ j * (a n) ^ (n - 1 - j)) / (a n) ^ n

theorem differentiable_weierstrassMittagLefflerCorrection (a : ℕ → ℂ) (n : ℕ) :
    Differentiable ℂ (weierstrassMittagLefflerCorrection a n) := by
  unfold weierstrassMittagLefflerCorrection
  exact ((Differentiable.fun_sum fun j _ =>
    (differentiable_id.pow j).mul (differentiable_const _)).neg).div_const _

/-- **The `n`-th factor's logarithmic derivative in Mittag-Leffler form.** -/
theorem logDeriv_weierstrassGenusFactorAt_eq {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (n : ℕ) {z : ℂ}
    (hz : z ≠ a n) :
    logDeriv (weierstrassGenusFactorAt a n) z
      = 1 / (z - a n) - weierstrassMittagLefflerCorrection a n z := by
  have han : a n ≠ 0 := hane n
  have hzan : z - a n ≠ 0 := sub_ne_zero.mpr hz
  have hanpow : (a n) ^ n ≠ 0 := pow_ne_zero _ han
  have hgeom : (∑ j ∈ Finset.range n, z ^ j * (a n) ^ (n - 1 - j)) * (z - a n)
      = z ^ n - (a n) ^ n := geom_sum₂_mul z (a n) n
  rw [logDeriv_weierstrassGenusFactorAt hane n hz, weierstrassMittagLefflerCorrection]
  rw [div_pow, div_sub_div_eq_sub_div, eq_div_iff hzan] at *
  field_simp
  linear_combination (z - a n) * hgeom + hgeom

end GaloisForLFunctions.HTGeometry

end
