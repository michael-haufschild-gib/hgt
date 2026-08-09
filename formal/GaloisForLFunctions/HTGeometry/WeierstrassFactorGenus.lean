import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The Weierstrass elementary factor of arbitrary genus

`E_g(z) = (1 - z) exp(∑_{r=1}^{g} z^r/r)` is the factor from which canonical products of genus `g`
are assembled.  The exponential polynomial is chosen exactly so that the logarithmic derivative
collapses:

`E_g'(z)/E_g(z) = -z^g/(1 - z)`.

The `g` lowest-order terms of `-1/(1-z)` are cancelled by the derivative of the exponential
polynomial, which is the truncated geometric series; only the tail `-z^g/(1-z)` survives.  That
collapse is what makes the logarithmic derivative of a canonical product a sum of terms decaying
like the `(g+1)`-st power, and hence what produces the inverse-power asymptotic tail of a power
canonical product.

* `GaloisForLFunctions.HTGeometry.weierstrassE`;
* `GaloisForLFunctions.HTGeometry.hasDerivAt_weierstrassE`;
* `GaloisForLFunctions.HTGeometry.logDeriv_weierstrassE`;
* `GaloisForLFunctions.HTGeometry.tsum_inverse_power_expansion`.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The Weierstrass elementary factor of genus `g`. -/
noncomputable def weierstrassE (g : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp (∑ r ∈ Finset.range g, z ^ (r + 1) / ((r : ℂ) + 1))

@[simp] theorem weierstrassE_zero_eq_one (g : ℕ) : weierstrassE g 0 = 1 := by
  rw [weierstrassE]
  simp

/-- The exponential polynomial differentiates to the truncated geometric series. -/
theorem hasDerivAt_weierstrassPoly (g : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => ∑ r ∈ Finset.range g, w ^ (r + 1) / ((r : ℂ) + 1))
      (∑ r ∈ Finset.range g, z ^ r) z := by
  have hterm : ∀ r ∈ Finset.range g,
      HasDerivAt (fun w : ℂ => w ^ (r + 1) / ((r : ℂ) + 1)) (z ^ r) z := by
    intro r _
    have hne : ((r : ℂ) + 1) ≠ 0 := by
      have : ((r : ℂ) + 1) = ((r + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this]
      exact Nat.cast_ne_zero.2 (Nat.succ_ne_zero r)
    have hbase := (hasDerivAt_pow (r + 1) z).div_const ((r : ℂ) + 1)
    have hval : ((r + 1 : ℕ) : ℂ) * z ^ (r + 1 - 1) / ((r : ℂ) + 1) = z ^ r := by
      have hcast : ((r + 1 : ℕ) : ℂ) = (r : ℂ) + 1 := by push_cast; ring
      rw [hcast]
      simp only [Nat.add_sub_cancel]
      field_simp
    rw [hval] at hbase
    exact hbase
  have hsum := HasDerivAt.sum hterm
  have hfun : (∑ i ∈ Finset.range g, fun w : ℂ => w ^ (i + 1) / ((i : ℂ) + 1))
      = fun w : ℂ => ∑ r ∈ Finset.range g, w ^ (r + 1) / ((r : ℂ) + 1) := by
    funext w
    rw [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

/-- The derivative of the elementary factor. -/
theorem hasDerivAt_weierstrassE (g : ℕ) (z : ℂ) :
    HasDerivAt (weierstrassE g)
      (Complex.exp (∑ r ∈ Finset.range g, z ^ (r + 1) / ((r : ℂ) + 1))
        * (-1 + (1 - z) * ∑ r ∈ Finset.range g, z ^ r)) z := by
  have hlin : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub 1
  have hexp := (hasDerivAt_weierstrassPoly g z).cexp
  have hmul := hlin.mul hexp
  refine hmul.congr_deriv ?_
  ring

/-- **The logarithmic derivative of the elementary factor collapses.** -/
theorem logDeriv_weierstrassE (g : ℕ) {z : ℂ} (hz : z ≠ 1) :
    logDeriv (weierstrassE g) z = -z ^ g / (1 - z) := by
  have hsub : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have hgeom : (∑ r ∈ Finset.range g, z ^ r) = (z ^ g - 1) / (z - 1) := geom_sum_eq hz g
  have hzsub : z - (1 : ℂ) ≠ 0 := sub_ne_zero.2 hz
  have hEne : weierstrassE g z ≠ 0 := by
    rw [weierstrassE]
    exact mul_ne_zero hsub (Complex.exp_ne_zero _)
  rw [logDeriv_apply, (hasDerivAt_weierstrassE g z).deriv, weierstrassE, hgeom]
  rw [mul_comm ((1 : ℂ) - z) (Complex.exp _)]
  rw [mul_div_mul_left _ _ (Complex.exp_ne_zero _)]
  field_simp
  ring

/-- **The inverse-power expansion of a factor's logarithmic-derivative term.**  Outside the closed
unit disc the term expands in *descending* powers starting at `t^g`: this is the expansion that
produces the inverse-power asymptotic tail of a canonical product, since `t = x/n^s` is large
exactly for the finitely many `n` with `n^s < x`. -/
theorem tsum_inverse_power_expansion (g : ℕ) {t : ℂ} (ht : 1 < ‖t‖) :
    t ^ (g + 1) / (1 + t) = ∑' j : ℕ, (-1 : ℂ) ^ j * t ^ g * (t⁻¹) ^ j := by
  have ht0 : t ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at ht
    linarith
  have hinv : ‖(-t⁻¹)‖ < 1 := by
    rw [norm_neg, norm_inv, inv_lt_one_iff₀]
    right
    exact ht
  have hgeo : ∑' j : ℕ, (-t⁻¹) ^ j = (1 - (-t⁻¹))⁻¹ := tsum_geometric_of_norm_lt_one hinv
  have hterm : ∀ j : ℕ, (-1 : ℂ) ^ j * t ^ g * (t⁻¹) ^ j = t ^ g * (-t⁻¹) ^ j := by
    intro j
    rw [neg_pow]
    ring
  have h1t : (1 : ℂ) + t ≠ 0 := by
    intro hcon
    have hval : t = -1 := by linear_combination hcon
    rw [hval, norm_neg, norm_one] at ht
    linarith
  have hinvval : ((1 : ℂ) - -t⁻¹)⁻¹ = t / (1 + t) := by
    have hrw : (1 : ℂ) - -t⁻¹ = (1 + t) / t := by
      field_simp
      ring
    rw [hrw, inv_div]
  rw [tsum_congr hterm, tsum_mul_left, hgeo, hinvval]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
