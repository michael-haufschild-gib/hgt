/-
# `bottcherCoord` preserves winding on `escapeOpen`

On `escapeOpen c` the Böttcher coordinate factors as `bottcherCoord c z = z · exp(S(z))` with
`S(z) = ∑ₖ bottcherLogTerm c z k` analytic (`bottcherCoord_eq_mul_exp`,
`differentiableOn_bottcherLogSum`). The `exp(S)` factor is windingless (`wind_exp`), so the winding of
`bottcherCoord c ∘ γ` around `0` equals the winding of the identity `z ↦ z` along `γ`, for every loop
`γ` in `escapeOpen c`. This is the bridge that lets winding around the puncture be read off the bare
position loop — the key step in identifying the `2ⁿ`-fold monodromy of the escape-level tower.
-/
import GaloisForLFunctions.Bottcher.WindDynamics
import GaloisForLFunctions.Bottcher.BasinColimit

open Topology

namespace Bottcher

/-- **`bottcherCoord` preserves winding on `escapeOpen`.** For any loop `p` in `escapeOpen c`, the
winding of `bottcherCoord c` along `p` equals the winding of the position map `z ↦ z` along `p`:
the `exp(S)` factor contributes nothing. -/
theorem wind_bottcherCoord_eq_wind_id (c : ℂ) {x₀ : escapeOpen c} (p : Path x₀ x₀)
    (hgB : Continuous (fun x : escapeOpen c => bottcherCoord c (x : ℂ)))
    (hgBne : ∀ x : escapeOpen c, bottcherCoord c (x : ℂ) ≠ 0)
    (hgId : Continuous (fun x : escapeOpen c => (x : ℂ)))
    (hgIdne : ∀ x : escapeOpen c, (x : ℂ) ≠ 0) :
    wind (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) hgB hgBne p
      = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne p := by
  set M : escapeOpen c → ℂ := fun x => ∑' k, bottcherLogTerm c (x : ℂ) k with hMdef
  have hM : Continuous M := (differentiableOn_bottcherLogSum c).continuousOn.restrict
  have hrel : (fun x : escapeOpen c => bottcherCoord c (x : ℂ))
      = (fun x : escapeOpen c => (x : ℂ) * Complex.exp (M x)) := by
    funext x; exact bottcherCoord_eq_mul_exp (hgIdne x)
  have key : wind (fun x : escapeOpen c => bottcherCoord c (x : ℂ)) hgB hgBne p
      = wind (fun x : escapeOpen c => (x : ℂ)) hgId hgIdne p
        + wind (fun x : escapeOpen c => Complex.exp (M x))
            (Complex.continuous_exp.comp hM) (fun x => Complex.exp_ne_zero _) p := by
    rw [wind_congr hrel hgB hgBne (hgId.mul (Complex.continuous_exp.comp hM))
      (fun x => mul_ne_zero (hgIdne x) (Complex.exp_ne_zero _)) p]
    exact wind_mul (fun x : escapeOpen c => (x : ℂ)) (fun x => Complex.exp (M x))
      hgId (Complex.continuous_exp.comp hM) hgIdne (fun x => Complex.exp_ne_zero _) p
  rw [key, wind_exp M hM, add_zero]

end Bottcher
