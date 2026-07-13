import Mathlib

/-!
# Infinite-prime shadows degenerate to the logarithmic generator

The raw shadow of `x^(1/P)` at an infinite hyperinteger `P` is `1`.  The first renormalized
shadow is `log x`.  This is the exact standard limit underlying the nonstandard-language claim.
-/

namespace RHTower

noncomputable section

open Filter Topology

/-- The raw infinitesimal-power shadow is trivial on every positive standard real. -/
theorem infinitePrimeShadow_tendsto_one {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t : ℝ => x ^ t) (nhds 0) (nhds 1) := by
  have h := Real.continuousAt_const_rpow (b := 0) hx.ne'
  rw [show (1 : ℝ) = x ^ (0 : ℝ) by rw [Real.rpow_zero]]
  exact h

/-- The first nontrivial renormalized shadow is the logarithmic generator.  With `t=1/P`, this is
`P * (x^(1/P)-1) -> log x`. -/
theorem infinitePrimeRenormalizedShadow_tendsto_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t : ℝ => (x ^ t - 1) / t)
      (nhdsWithin 0 {0}ᶜ) (nhds (Real.log x)) := by
  have hderiv : HasDerivAt (fun t : ℝ => x ^ t) (Real.log x) 0 := by
    convert (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_rpow hx using 1
    norm_num
  simpa [div_eq_inv_mul] using hderiv.tendsto_slope_zero

end
end RHTower
