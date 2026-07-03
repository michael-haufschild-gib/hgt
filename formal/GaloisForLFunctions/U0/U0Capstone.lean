/-
# The u₀ capstone — the strongest UNCONDITIONAL result, self-contained

This file states the strongest algebraic-independence result on the `u₀` topic that is FULLY
proven right now: no `sorry`, no assumed hypothesis, and the standard axiom set
`[propext, Classical.choice, Quot.sound]` only.  It depends on nothing from the pending q62/Böttcher
lane — only on the committed Böttcher base.

## The five pillars — now all five UNCONDITIONAL

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

5. **Independence from the whole finite Böttcher tower — UNCONDITIONAL** (`u0_kummer_tower_independence`).
   For every viable parameter and every level `k`, a genuine analytic nowhere-zero branch `χ` on the
   window — a `2^k`-th root of `ψ` (the sub-threshold inverse Böttcher branch `φ_b` carried `k`
   levels down the tower, FE `ψ = φ_b^(2^N)`) — is algebraically independent of `u₀` over `ℂ(z)`.
   The single m-step branch is lifted to its entire `2`-power root tower by a purely algebraic
   Kummer descent (`U0MStepKummer.noRelation_pow_descent`), with the concrete root supplied by the
   simply-connectedness of the window disk (`U0KummerBranch`) — no new transcendence input.
-/
import GaloisForLFunctions.U0.U0WindowSharpness
import GaloisForLFunctions.U0.U0ParameterSpace
import GaloisForLFunctions.U0.U0PhiMStep
import GaloisForLFunctions.U0.U0MStepInstances
import GaloisForLFunctions.U0.U0KummerBranch

open Complex Set Metric Bottcher Filter Topology
open U0ParameterSpace U0PhiLargeCarrier U0PhiLargeDescent U0PhiMStep U0PhiMStepFar
open U0WindowSharpness
open U0MStepBranch U0MeroCarrier

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

/-- **Pillar 5 — independence from the whole finite Böttcher tower (unconditional).**  For every
viable parameter and every level `k`, there is a genuine analytic, nowhere-zero branch `χ` on the
window — a `2^k`-th root of `ψ = bottcherCoord ∘ f_b^[N]`, i.e. the sub-threshold inverse Böttcher
branch `φ_b` carried `k` levels down the tower (FE: `ψ = φ_b^(2^N)`) — that is algebraically
independent of `u₀` over `ℂ(z)`.  Not a single branch but the entire `2`-power root tower, all
independent of `u₀`, all from one algebraic descent (`U0MStepKummer.noRelation_pow_descent`) with no
new analytic input beyond the concrete root lift (`U0KummerBranch`). -/
theorem u0_kummer_tower_independence {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) (k : ℕ) :
    ∃ (r : ℝ) (N : ℕ) (hr : 1 < r) (χ : ℂ → ℂ)
      (hχ : AnalyticOnNhd ℂ χ (ball (0 : ℂ) r)),
      (∀ z, χ z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) r, χ z ^ (2 ^ k) = psiN b N z) ∧
      letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
        (annMB_nonempty hr)
      letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
        (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
          (annMB_infinite hr)).toAlgebra
      NoRelation (RatFunc ℂ)
        (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
          ⟨Germ.coeRingHom (𝓟 (annMB r)) χ, ⟨χ, hχ.mono inter_subset_left, rfl⟩⟩)
        (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
          (u0AnSub annMB_subset_Ext)) :=
  U0KummerBranch.u0_mstep_kummer_branch_independence hviab k

/-- **The full u₀ Böttcher-tower capstone (pillars 1–5).**  This packages the whole
current U0 proof surface in one theorem: the sharp `2+√2` window theorem with its exact
obstruction, the viable-region branch/existence/independence capstone, and the finite
Kummer tower strengthening for every viable parameter and every level.  It introduces no
new proof ingredient; it is the unified formal entry point for the U0 result. -/
theorem u0_full_bottcher_tower_capstone :
    -- pillar 1: sharp window independence plus exact obstruction
    ((∀ b : ℂ, ∀ hb : 2 + Real.sqrt 2 < ‖b‖,
      letI := isDomain_analyticSubring (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
        (annWB_nonempty hb)
      letI : Algebra (RatFunc ℂ) (meroField (annWB b)) :=
        (ratfuncToMero (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
          (annWB_nonempty hb) (annWB_infinite hb)).toAlgebra
      NoRelation (RatFunc ℂ)
        (algebraMap (analyticSubring (annWB b)) (meroField (annWB b)) (phiBAn b hb))
        (algebraMap (analyticSubring (annWB b)) (meroField (annWB b))
          (u0AnSub annWB_subset_Ext))) ∧
    (∃ b : ℂ, ‖b‖ = 2 + Real.sqrt 2 ∧ ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia b)) ∧
    -- pillars 2–4: viable-region structure, m-step branch, and m-step independence
    (IsClosed Obstructed ∧
    (∃ b : ℂ, b ∈ frontier Obstructed ∧
      b ∈ segment ℝ (⟨-33/25, 44/25⟩ : ℂ) (⟨-66/25, 88/25⟩ : ℂ)) ∧
    (∀ b : ℂ, (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) →
      ∃ (r : ℝ) (N : ℕ), 1 < r ∧
        AnalyticOnNhd ℂ (psiN b N) (ball (0 : ℂ) r) ∧ (∀ z : ℂ, psiN b N z ≠ 0)) ∧
    (∀ b : ℂ, (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) → MStepIndependence b) ∧
    MStepIndependence (3 : ℂ)) ∧
    -- pillar 5: every finite Kummer layer of the viable m-step branch
    (∀ b : ℂ, (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) → ∀ k : ℕ,
      ∃ (r : ℝ) (N : ℕ) (hr : 1 < r) (χ : ℂ → ℂ)
        (hχ : AnalyticOnNhd ℂ χ (ball (0 : ℂ) r)),
        (∀ z, χ z ≠ 0) ∧
        (∀ z ∈ ball (0 : ℂ) r, χ z ^ (2 ^ k) = psiN b N z) ∧
        letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
          (annMB_nonempty hr)
        letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
          (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
            (annMB_infinite hr)).toAlgebra
        NoRelation (RatFunc ℂ)
          (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
            ⟨Germ.coeRingHom (𝓟 (annMB r)) χ, ⟨χ, hχ.mono inter_subset_left, rfl⟩⟩)
          (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
            (u0AnSub annMB_subset_Ext))) := by
  refine ⟨u0_boettcher_independence_sharp, u0_topic_capstone, ?_⟩
  intro b hviab k
  exact u0_kummer_tower_independence hviab k

end U0Capstone
