# The deck-charge calculus (Phase A) — additive charge, winding number, argument principle

- **ID:** deck-charge-calculus
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — the Phase-A "reusable formal calculus of root-torsor charges", built to
  exhaustion (additive charge + topological winding number + the argument-principle bridge +
  quadrant-local geometry).
- **Source:** Phase A of `../../rh-monodromy-weight-mismatch/00-apporach-reorientation.md`
  ("Build the deck-charge calculus"), extended through the loop/winding realisation and the
  quadrant-local charge (leads #1–#2). Builds on the pre-existing multiplicative geometric deck
  apparatus (`DeckCocycle`, `DeckMultiZero`, `DeckMonomial`, `AnnulusRootGluing`, `SignatureParity`).
- **Statement:** The obstruction to lifting a nonvanishing holomorphic `f` through `z ↦ z^n` is
  realised as one object in three registers, all built axiom-clean and proven equal:
  the **additive** charge `wCharge n idx ∈ ℤ/n`; the **multiplicative** deck class `deckRed n idx ∈ μ_n`
  (`ℤ/n ≃* μ_n`, `deckIso`); and the **topological** winding number `windingNumber γ ∈ ℤ` of the
  boundary loop, with `windingNumber` around an order-`m` zero `= m` (the local argument principle).

## The Lean certificates (all axiom-clean, lint green, `RHTower` umbrella)

**`DeckChargeCalculus.lean`** — the additive charge.
- `wCharge n idx = (idx : ℤ/n)`; `wCharge_add` (additivity), `wCharge_intMul`/`_nsmul` (power law),
  `wCharge_eq_zero_iff` (`= 0 ↔ n ∣ idx`), `wCharge_sum`, `wCharge_boundary_crossing`,
  `interior_charge_conservation`, `wCharge_tower`/`wCharge_eq_zero_of_le` (dyadic-ladder coherence).
- The spine `ℤ/n ≃* μ_n`: `deckChar`, `deckChar_wCharge` (the additive and multiplicative avatars
  agree), `deckChar_mul`/`_injective`/`_pow_eq_one`, `deckUnitHom`, `deckIso`.
- `exists_root_iff_wCharge_zero`: on any two-chart cover, `wCharge n idx = 0 ↔` a coherent global
  `n`-th root of `f` exists (the vanishing-⟺-root deliverable, additive form).

**`DeckChargeLadder.lean`** — the charge on the ξ ladder.
- `rhLadder_iff_ladderCharge_zero`: `RH_{2^k}` holds iff every right-half ξ-zero carries trivial
  rung-`k` charge — the whole multiplicity-parity ladder read through the additive calculus.
- `wCharge_invisible_below_reflection_depth`: a reflection-symmetric-depth-`k` configuration has
  trivial rung-`j` charge for `j ≤ k` (globally symmetric counts are too coarse — go quadrant-local);
  `wCharge_orbit_first_visible` (a `2^k`-orbit is first seen at rung `k+1`).

**`WindingNumber.lean`** — the integer winding number (mathlib gap, built from the `exp` covering map).
- `exists_contLog` (continuous logarithm on the line, via `Complex.exists_continuousOn_eqOn_exp_comp`
  and `ContractibleSpace ℝ`), `contLog_increment_indep` (branch-independence: two logs differ by a
  locally constant `2πiℤ`-valued function on connected `ℝ`, hence a constant), `windingNumber : ℤ`,
  `contLog_increment` (`L b − L a = 2πi·windingNumber`).
- `windingNumber_mul` (additivity), `windingNumber_pow` (power law), `windingNumber_const`,
  `windingNumber_eq_zero_iff` (`= 0 ↔` the log closes up ⟺ a continuous root exists), and the loop
  charge `loopCharge k γ = windingNumber γ mod 2^k` with `loopCharge_mul`/`_pow`/`_eq_zero_iff`.

**`WindingArgumentPrinciple.lean`** — the local argument principle (the winding = order bridge).
- `windingNumber_center_zero`: the loop `θ ↦ (r·e^{iθ})^m` winds `m` times — a zero of order `m`
  contributes exactly `m`. `windingNumber_circle` (`e^{iθ}` winds once — non-vacuity).
- `loopCharge_center_zero`: the loop deck charge around an order-`m` zero is `wCharge (2^k) m` — the
  topological winding realisation and the algebraic `wCharge` are the **same** observable on the
  local model; `loopCharge_center_zero_eq_zero_iff` (`= 0 ↔ 2^k ∣ m`).

**`RegionCharge.lean`** — the quadrant-local charge (new geometry).
- `regionCharge n S ord R` (charge of the zeros of `S` in a region `R`); `regionCharge_add_compl`
  (region + complement partition the total); `regionCharge_transport` (an order-preserving involution
  swapping two regions makes their charges equal — the FE symmetries move charge between quadrants);
  `regionCharge_klein_equal` (the functional-equation Klein four-group `{s,1−s,s̄,1−s̄}` makes the
  four quadrant charges equal, so the total is `4·q` — blind mod `4`, while the single-quadrant `q`
  is the signal).

**`DeckChargeBridge.lean`** (companion, built by the coordinating GPT agent on this calculus): welds
`ladderCharge` to the geometric `xiDeckCharge`, confirming the two agents' rung conditions are one.

## Approach

The additive charge is the residue `(idx : ℤ/n)`; its laws are the `Int.cast` ring-hom laws, and the
spine `ℤ/n ≃* μ_n` transports `deckRed` along `ZMod.val`. The winding number is genuinely new
infrastructure absent from mathlib: mathlib supplies the branch of logarithm (via the `exp` covering
map `isCoveringMapOn_exp`) but not the integer winding invariant — that is built here, its
well-definedness resting on branch-independence (a continuous `2πiℤ`-valued function on connected `ℝ`
is constant, via `Complex.isClosedEmbedding_intCast` + `IsLocallyConstant`). No carrier or flow is
constructed anywhere: every charge is a property of the *given* zero/loop data — a cocycle/obstruction
invariant, not a propagated quantity (rule 7 — constraint, not flow).

## Verdict — dual gate

**DELIVERED (formalized):** the deck-charge calculus is built to exhaustion in all three registers,
machine-checked, axiom-clean, integrated. Every named Phase-A deliverable — additivity, power law,
vanishing ⟺ root existence, boundary-crossing, homotopy invariance — holds; the additive and
multiplicative faces are one object (`deckIso`); the integer winding number (a mathlib gap) is built
and computes the enclosed order (`windingNumber_center_zero`); the quadrant-local charge and its
FE/conjugation transport are formalized.

**Graded as branch infrastructure:** the individual pieces (cyclic-group iso, elementary charge laws,
the winding number, the local argument principle, region transport) are reduce-to-known complex
analysis / group theory; the value is (i) a mathlib gap genuinely filled (the integer winding number)
and (ii) the *unification* — three realisations of one obstruction proven equal and welded to the ξ
ladder. Significance is proximity to the program: the charge is now a first-class cyclic-group element
with a conservation law, a topological winding realisation, and a quadrant-local refinement.

## Springboards

- **Global argument principle**: `windingNumber_center_zero` is the local case; the winding of `f`
  around a box boundary `= Σ` enclosed orders is the next brick (needs a homotopy/degree argument to
  reduce a general boundary to circles around each zero).
- **Phase E (charge motion)**: `interior_charge_conservation` + `wCharge_boundary_crossing` +
  `regionCharge_transport` are the seeds of the pair-annihilation rule and interior conservation for
  admissible FE-symmetric deformations.
- **Phase F (quadrant-ramified cover)**: `regionCharge_klein_equal` isolates the single-quadrant
  charge `q` as the mod-4-invisible signal — the target a quadrant-ramified cover must detect.

## Log
- 2026-07-07 — built to exhaustion in 3-formalized (5 files, all axiom-clean, lint green, umbrella):
  `DeckChargeCalculus` (additive charge + `ℤ/n ≃* μ_n` + conservation + tower), `DeckChargeLadder`
  (RH ladder in charge form + symmetry-blindness), `WindingNumber` (the integer winding number — a
  mathlib gap — with its full calculus), `WindingArgumentPrinciple` (winding = enclosed order; the
  topological and algebraic charge coincide), `RegionCharge` (quadrant-local charge + FE/conjugation
  transport + Klein-four blindness). The coordinating GPT agent's `DeckChargeBridge` builds on
  `DeckChargeLadder`, confirming both agents' rung conditions are one object.
