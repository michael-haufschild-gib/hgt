# The u₀ topic — capstone: strongest unconditional result

- **ID:** u0-topic-capstone
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — the closing statement of the u₀ program
- **Axioms:** `[propext, Classical.choice, Quot.sound]` only (no `sorry`, no assumed hypothesis,
  no q62/Böttcher-lane pending dependency — verified by `#print axioms`).
- **File:** `formal/GaloisForLFunctions/U0/U0Capstone.lean`.

## The result (four pillars, ALL unconditional)

**Pillar 1 — sharp independence** (`U0Capstone.u0_boettcher_independence_sharp`, alias of
`U0WindowSharpness.window_threshold_sharp`).  For every parameter with `‖b‖ > 2+√2`, `u₀` and the
Böttcher window branch `φ_b` are algebraically independent over `ℂ(z)` (`NoRelation`), and the
constant is EXACT: at `‖b‖ = 2+√2` the parameter `−(2+√2)` is obstructed (`K_b` meets the closed
unit disk, killing the window route).  This is the direction-independent threshold.

**Pillars 2 & 3 — bundled** (`U0Capstone.u0_viability_and_branch_capstone`):
- the obstructed set `𝒪 = {b : K_b ∩ D̄(0,1) ≠ ∅}` is **closed**, and its frontier (the critical
  curve `ρ`) has a **machine-checked point** on the ray `arg b ≈ 126.9°`, modulus `[11/5, 22/5]`
  — so `2+√2` is the MAXIMUM of `ρ`, attained at `arg b = π`, and the window method reaches
  strictly below it in most directions;
- for **every viable parameter**, the m-step branch `ψ = bottcherCoord ∘ f_b^[N]` is analytic and
  nowhere zero on a window disk crossing the natural boundary `|z| = 1` (`exists_mstep_branch`).

**Pillar 4 — UNCONDITIONAL** (`U0PhiMStepFar.u0_mstep_independence`; bundled in
`U0Capstone.u0_topic_capstone`): `u₀ ⟂ ψ` over `ℂ(z)` for the WHOLE viable region, in every
direction — `MStepIndependence b` for every viable `b`.  `ψ`'s transcendence is discharged
(`psiN_transcendental`) by descending `Bottcher.bottcher_transcendental_far` along `f^[N]` on the
UNPUNCTURED carrier `annMB r` (no q62 dependency).  The former gap — `pMapB_deriv_ne_zero` on
`annMB` — dissolved: `deriv ≠ 0` was only needed for far-image openness, and a positive-degree
polynomial is an open map unconditionally (`Polynomial.isOpenQuotientMap_eval`), so no puncturing
and no `IsConnected (open ∖ finite)` topology lemma is required.  Witnessed strictly below the sharp
threshold at six parameters of modulus `< 2+√2` (`U0MStepInstances`: `b = 3`, five slice points).

## Supporting infrastructure (all this-session, axiom-clean)

- General obstruction engine `U0ObstructionPatterns.filledJulia_meets_unit_disk_preperiodic`
  (subsumes P1/P2/P3), with the exact period-3 parameterization `b = −(σ²+σ+2)`.
- Multi-lobe certificates (`U0LobeInstances`): period-3 at `arg ≈ 111.8°`, 2-cycle in the ring,
  the radial bracket of `∂𝒪`.
- Uniform clearance `U0UniformClearance.exists_uniform_clearance` / `exists_clearance_escapeOpen`.
- Branch-conditional capstone `U0MStepBranch.u0_mstep_independence_of_branch` (engine + descent +
  assembly all discharged generically — only the branch is m-step-specific).
- Parameter-space objects `U0ParameterSpace` (`Obstructed`, `Viable`, `isClosed_obstructed`,
  `PatternRegion`, the conjecture Prop `ObstructedEqClosurePattern` + its easy half, the reducible
  half `obstructed_open_sub_pattern_of_dense` conditional on classical preperiodic-density).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: build + lint green; capstone theorems `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-02 — capstone assembled: sharp independence (banked) + the session's critical-curve,
  parameter-space, and m-step-branch results into one axiom-clean statement, independent of the q62
  lane.  The sole located gap to full viable-region independence is ψ's transcendence
  (punctured-carrier descent port).
