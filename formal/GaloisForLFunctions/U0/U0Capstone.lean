/-
# The u₀ capstone — the strongest UNCONDITIONAL result, self-contained

This file states the strongest algebraic-independence result on the `u₀` topic that is FULLY
proven right now: no `sorry`, no assumed hypothesis, and the standard axiom set
`[propext, Classical.choice, Quot.sound]` only.  It depends on nothing from the pending q62/Böttcher
lane — only on the committed Böttcher base.

## The four pillars — now all four UNCONDITIONAL

1. **Sharp independence (`u0_boettcher_independence_sharp = window_threshold_sharp`).**
   For every parameter with `‖b‖ > 2+√2`, `u₀` and the Böttcher window branch `φ_b` are
   algebraically independent over `ℂ(z)` (`NoRelation`); and the constant `2+√2` is EXACT —
   at modulus `2+√2` the parameter `−(2+√2)` is obstructed (its filled Julia set meets the closed
   unit disk, killing the window route).  This is the direction-independent threshold.

2. **The viability boundary is a closed set with a certified curve point.**
   The obstructed set `𝒪 = {b : K_b ∩ D̄(0,1) ≠ ∅}` is closed; its frontier — the critical curve
   `ρ` — has a machine-checked point on the ray `arg b ≈ 126.9°` in modulus `[11/5, 22/5]`.  So
   `2+√2` is the MAXIMUM of `ρ` (attained at `arg b = π`); in most directions the window method
   reaches strictly below it.

3. **The m-step branch exists analytically for every viable parameter.**
   Whenever `K_b` avoids the closed unit disk, the branch `ψ = bottcherCoord ∘ f_b^[N]` is analytic
   and nowhere zero on a window disk crossing `|z| = 1` (`exists_mstep_branch`).

4. **Independence over the WHOLE viable region — UNCONDITIONAL** (`u0_mstep_independence`).  For
   EVERY viable parameter, `u₀ ⟂ ψ` over `ℂ(z)` on that window (`MStepIndependence b`).  The last
   input — `ψ`'s transcendence over `ℂ(z)` — is now discharged (`U0PhiMStepFar.psiN_transcendental`)
   by descending `bottcher_transcendental_far` along `f^[N]` on the unpunctured carrier; the open
   mapping theorem for positive-degree polynomials replaces the sharp-threshold derivative
   hypothesis, so no `‖b‖ > 2+√2` and no genericity argument is needed.  This carries independence
   strictly below the sharp threshold, in every direction — witnessed at six concrete parameters of
   modulus `< 2+√2` (`U0MStepInstances.u0_mstep_independence_subthreshold`: `b = 3` and five
   critical-curve slice points at `arg b ≈ 105°…155°`).
-/
import GaloisForLFunctions.U0.U0WindowSharpness
import GaloisForLFunctions.U0.U0ParameterSpace
import GaloisForLFunctions.U0.U0PhiMStep
import GaloisForLFunctions.U0.U0MStepInstances

open Complex Set Metric Bottcher
open U0ParameterSpace U0PhiMStep U0PhiMStepFar U0WindowSharpness

namespace U0Capstone

/-- **Pillar 1 — sharp u₀–Böttcher independence.**  Alias of `window_threshold_sharp`: coverage
`∀ ‖b‖ > 2+√2` paired with an obstruction exactly at `2+√2`. -/
alias u0_boettcher_independence_sharp := window_threshold_sharp

/-- **The u₀ capstone (pillars 2 & 3, unconditional).**  The window-viability boundary is a closed
set with a certified point of the critical curve, and the m-step Böttcher branch exists analytically
on a window crossing the natural boundary for every viable parameter. -/
theorem u0_viability_and_branch_capstone :
    IsClosed Obstructed ∧
    (∃ b : ℂ, b ∈ frontier Obstructed ∧
      b ∈ segment ℝ (⟨-33/25, 44/25⟩ : ℂ) (⟨-66/25, 88/25⟩ : ℂ)) ∧
    (∀ b : ℂ, (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) →
      ∃ (r : ℝ) (N : ℕ), 1 < r ∧
        AnalyticOnNhd ℂ (psiN b N) (ball (0 : ℂ) r) ∧ (∀ z : ℂ, psiN b N z ≠ 0)) :=
  ⟨isClosed_obstructed, exists_frontier_obstructed_on_ray, fun _ hv => exists_mstep_branch hv⟩

/-- **Pillar 4 — unconditional independence over the whole viable region.**  For every parameter
whose filled Julia set avoids the closed unit disk, `u₀` and the m-step Böttcher branch
`ψ = bottcherCoord ∘ f_b^[N]` are algebraically independent over `ℂ(z)` on a window crossing
`|z| = 1` — `MStepIndependence b`.  No threshold hypothesis, no assumed transcendence. -/
theorem u0_mstep_independence_viable {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) : MStepIndependence b :=
  u0_mstep_independence hviab

/-- **The u₀ topic — the full unconditional capstone (pillars 2–4).**  In one axiom-clean statement:
the closed viability boundary with a certified critical-curve point (pillar 2); the analytic m-step
branch for every viable parameter (pillar 3); and — the newly closed gap — UNCONDITIONAL `u₀ ⟂ ψ`
over the ENTIRE viable region, in every direction (pillar 4), witnessed strictly below the sharp
threshold at `b = 3` (`‖b‖ = 3 < 2+√2`).  Pillar 1 (sharp independence with the exact threshold
`2+√2`) is `u0_boettcher_independence_sharp`. -/
theorem u0_topic_capstone :
    -- pillar 2: closed boundary with a certified curve point
    IsClosed Obstructed ∧
    (∃ b : ℂ, b ∈ frontier Obstructed ∧
      b ∈ segment ℝ (⟨-33/25, 44/25⟩ : ℂ) (⟨-66/25, 88/25⟩ : ℂ)) ∧
    -- pillar 3: analytic m-step branch for every viable parameter
    (∀ b : ℂ, (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) →
      ∃ (r : ℝ) (N : ℕ), 1 < r ∧
        AnalyticOnNhd ℂ (psiN b N) (ball (0 : ℂ) r) ∧ (∀ z : ℂ, psiN b N z ≠ 0)) ∧
    -- pillar 4 (UNCONDITIONAL): u₀ ⟂ ψ over the whole viable region
    (∀ b : ℂ, (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) → MStepIndependence b) ∧
    -- witnessed strictly below the sharp threshold
    MStepIndependence (3 : ℂ) :=
  ⟨isClosed_obstructed, exists_frontier_obstructed_on_ray,
    (fun _ hv => exists_mstep_branch hv), (fun _ hv => u0_mstep_independence hv),
    U0MStepInstances.u0_mstep_independence_three⟩

end U0Capstone
