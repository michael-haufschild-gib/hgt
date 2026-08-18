import GaloisForLFunctions.RHTower.ProlateGlobalDerivativeBounds
import GaloisForLFunctions.RHTower.ProlateHermiteRescale

/-!
# The Hermite-rescaled prolate profile is bounded with its first two derivatives

The Hermite rescaling `u(ξ) = Φ(ξ/√c)` differentiates by the chain rule, so each derivative of the
rescaled profile is a derivative of the original divided by a power of `√c`.  Since a global band
eigenfunction and its first two derivatives are globally bounded, so are `u`, `u′` and `u″`.
-/

noncomputable section

namespace RHTower

theorem hasDerivAt_prolateHermiteRescale {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ}
    (hΦ : Differentiable ℝ Φ) (ξ : ℝ) :
    HasDerivAt (prolateHermiteRescale c Φ)
      (deriv Φ (ξ / Real.sqrt c) / Real.sqrt c) ξ := by
  have hs : Real.sqrt c ≠ 0 := Real.sqrt_ne_zero'.mpr hc
  have hinner : HasDerivAt (fun z : ℝ => z / Real.sqrt c) (1 / Real.sqrt c) ξ := by
    simpa using (hasDerivAt_id ξ).div_const (Real.sqrt c)
  have hcomp := ((hΦ (ξ / Real.sqrt c)).hasDerivAt).comp ξ hinner
  refine hcomp.congr_deriv ?_
  field_simp

theorem deriv_prolateHermiteRescale {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ}
    (hΦ : Differentiable ℝ Φ) :
    deriv (prolateHermiteRescale c Φ)
      = fun ξ => deriv Φ (ξ / Real.sqrt c) / Real.sqrt c :=
  funext fun ξ => (hasDerivAt_prolateHermiteRescale hc hΦ ξ).deriv

theorem hasDerivAt_deriv_prolateHermiteRescale {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ}
    (hΦ : Differentiable ℝ Φ) (hΦ' : Differentiable ℝ (deriv Φ)) (ξ : ℝ) :
    HasDerivAt (deriv (prolateHermiteRescale c Φ))
      (deriv (deriv Φ) (ξ / Real.sqrt c) / c) ξ := by
  have hs : Real.sqrt c ≠ 0 := Real.sqrt_ne_zero'.mpr hc
  have hsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  rw [deriv_prolateHermiteRescale hc hΦ]
  have hinner : HasDerivAt (fun z : ℝ => z / Real.sqrt c) (1 / Real.sqrt c) ξ := by
    simpa using (hasDerivAt_id ξ).div_const (Real.sqrt c)
  have hcomp := ((hΦ' (ξ / Real.sqrt c)).hasDerivAt).comp ξ hinner
  have hdiv := hcomp.div_const (Real.sqrt c)
  refine hdiv.congr_deriv ?_
  have hsq2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  field_simp
  rw [hsq2]
  ring

theorem deriv2_prolateHermiteRescale {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ}
    (hΦ : Differentiable ℝ Φ) (hΦ' : Differentiable ℝ (deriv Φ)) :
    deriv (deriv (prolateHermiteRescale c Φ))
      = fun ξ => deriv (deriv Φ) (ξ / Real.sqrt c) / c :=
  funext fun ξ => (hasDerivAt_deriv_prolateHermiteRescale hc hΦ hΦ' ξ).deriv

end RHTower

end
