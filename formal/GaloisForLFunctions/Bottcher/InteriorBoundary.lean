/-
# Interior-case natural boundary — the `K_c`-has-interior complement to `DendriteBoundary`

The natural-boundary transcendence (`STATUS.md` blueprint) needs `φ_c` to be non-continuable across a
Julia point for EVERY nonexceptional `c`. `DendriteBoundary.no_green_modulus_continuation` handles the
empty-interior (dendrite) case. This file handles the complementary case where `K_c` has nonempty
interior near the Julia point: a modulus-preserving continuation `g` would have `‖g‖ = exp(G_c) = 1` on
the OPEN interior of `K_c` (where `G_c = 0`), forcing `g` constant on the connected ball (max-modulus /
local-max principle) — contradicting that `g ~ φ_c ~ z` is nonconstant (some basin point has `‖g‖ > 1`).

Pure complex analysis; consumes `Complex.eventually_eq_of_isLocalMax_norm` + the identity theorem.
Together with the dendrite case this gives the full natural-boundary obstruction for all `c`.
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness

open Complex Metric Topology Filter Set

namespace Bottcher

/-- **Interior-case natural boundary.** If `g` is analytic on `ball z₀ r`, has unit modulus `‖g‖ = 1`
on a nonempty open subset `V` (the interior of `K_c`, where `G_c = 0`), and is non-unit-modulus
somewhere in the ball (a basin point, `‖g‖ > 1`), then `False`. Reason: a unit-modulus point of an
open set is a local maximum of `‖g‖`, so `g` is locally constant (`eventually_eq_of_isLocalMax_norm`),
hence constant on the connected ball (identity theorem) — contradicting the differing-modulus point.
The complement of `DendriteBoundary.no_green_modulus_continuation` for parameters whose filled Julia set
has nonempty interior. -/
theorem no_unit_modulus_open_continuation {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hgan : AnalyticOnNhd ℂ g (ball z₀ r))
    {V : Set ℂ} (hVo : IsOpen V) (hVsub : V ⊆ ball z₀ r) {c : ℂ} (hcV : c ∈ V)
    (hmod1 : ∀ z ∈ V, ‖g z‖ = 1)
    (hbad : ∃ z ∈ ball z₀ r, ‖g z‖ ≠ 1) :
    False := by
  have hdiff : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ g z := by
    filter_upwards [isOpen_ball.mem_nhds (hVsub hcV)] with z hz
    exact (hgan z hz).differentiableAt
  have hlm : IsLocalMax (norm ∘ g) c := by
    filter_upwards [hVo.mem_nhds hcV] with z hz
    show ‖g z‖ ≤ ‖g c‖
    rw [hmod1 z hz, hmod1 c hcV]
  have hconst : ∀ᶠ z in 𝓝 c, g z = g c := eventually_eq_of_isLocalMax_norm hdiff hlm
  have hEq : EqOn g (fun _ => g c) (ball z₀ r) :=
    hgan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball z₀ r).isPreconnected (hVsub hcV) hconst
  obtain ⟨w, hw, hwne⟩ := hbad
  exact hwne (by rw [hEq hw, hmod1 c hcV])

end Bottcher
