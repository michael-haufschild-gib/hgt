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

**`WindingDivisor.lean`** — the argument principle for a divisor (winding = total enclosed order).
- `windingNumber_linear_enclosing`: a zero *anywhere strictly inside* the circle winds it once (its
  linear factor factors as `(r e^{iθ})·u`, `u` a loop in the unit ball about `1`, winding `0` —
  `windingNumber_eq_zero_of_ball1` via `Complex.log` on the slit plane); `windingNumber_prod`
  (winding of a finite product of loops = Σ windings).
- `windingNumber_divisor`: `windingNumber(θ ↦ ∏ᵢ (c + r e^{iθ} − ρᵢ)^{mᵢ}) = Σᵢ mᵢ` — the
  argument principle for a divisor; `loopCharge_divisor`: the boundary-circle deck charge is
  `wCharge (2^k) (Σᵢ mᵢ)` — the topological twin of the algebraic `box_charge_eq_deckRed`.

**`WindingFull.lean`** — the argument principle for a general analytic `f`.
- `windingNumber_nonvanishing_disc`: a factor `g` continuous and nowhere zero on `ball c R` winds `0`
  on any interior circle (branch log on the simply connected disc, `isSimplyConnected_ball`).
- `windingNumber_argument_principle`: for `f = (∏ᵢ (z − ρᵢ)^{mᵢ})·g` on `ball c R` (all `ρᵢ` inside a
  circle of radius `r < R`, `g` nowhere zero), `windingNumber(f∘circle) = Σᵢ mᵢ` — the full argument
  principle in exactly the factored form of `box_charge_eq_deckRed`; `loopCharge_argument_principle`
  = `wCharge (2^k) (Σᵢ mᵢ)`.

**`WindingXi.lean`** — the winding number of ξ is its ladder charge.
- `windingNumber_xi_zero`: instantiating the argument principle on the completed ζ-function `xi` via
  its peeling factorisation `xi = (·−ρ₀)^m·h` (`xi_peel_ball`), the winding number of `xi` around a
  small circle about a zero `ρ₀` is `ord_{ρ₀} xi`. `loopCharge_xi_zero`: the loop deck charge of that
  circle is `ladderCharge k ρ₀` — the winding-number realisation of the `RH_{2^k}` ladder invariant
  (the contour twin of the residue `m_ρ = Res_ρ(xi'/xi)`).
- `windingNumber_xi_disc`/`loopCharge_xi_disc`: the several-zero case, via the tree's multi-zero peel
  `exists_multi_peel_orders` — the winding number of `xi` around a disc collecting a finite zero-set
  `t` is `Σ_{w∈t} ord_w xi`, and the loop deck charge is `wCharge (2^k) (Σ orders)`: the winding
  realisation of the box census charge.

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

- **Argument principle — DONE, through ξ, fully discharged**: `windingNumber_argument_principle`
  handles a general analytic `f = (divisor)·g`; `windingNumber_xi_zero`/`_xi_disc` instantiate it on
  the actual `xi`; `xi_zeros_closedBall_finite` + `windingNumber_xi_circle` discharge `hzeros`
  entirely (finiteness of ξ-zeros in a disc via codiscreteness + compactness, then the peeling radius
  slid into the gap to the next zero-radius): for any zero-avoiding circle, the winding of ξ is the Σ
  of orders of the finitely many zeros strictly inside. `windingNumber_homotopy_invariant` /
  `windingNumber_of_homotopic` give deformation invariance (joint log lift over the contractible
  `ℝ×ℝ`), so a general boundary reduces to a circle.
- Remaining (larger arcs, not this lane's Phase A): the multi-zero peel radius bookkeeping for
  arbitrary enclosing curves, and Phase E/F below.
- **Phase E (charge motion)**: `interior_charge_conservation` + `wCharge_boundary_crossing` +
  `regionCharge_transport` are the seeds of the pair-annihilation rule and interior conservation for
  admissible FE-symmetric deformations.
- **Phase F (quadrant-ramified cover)**: `regionCharge_klein_equal` isolates the single-quadrant
  charge `q` as the mod-4-invisible signal — the target a quadrant-ramified cover must detect.

## Log
- 2026-07-07 — the two hard analytic prerequisites discharged: `WindingXiCircle`
  (`xi_zeros_closedBall_finite` — ξ-zeros finite in a compact disc via codiscreteness + compactness;
  `windingNumber_xi_circle` — the fully-discharged winding of ξ around a zero-avoiding circle = Σ
  enclosed orders, no `hzeros` hypothesis) and `WindingHomotopy`
  (`windingNumber_homotopy_invariant`/`windingNumber_of_homotopic` — deformation invariance via the
  joint log lift over the contractible `ℝ×ℝ`). 10 files, all axiom-clean, sorry-free.
- 2026-07-07 — argument principle carried through to ξ: `WindingFull` (general analytic `f =
  (divisor)·g`, `windingNumber(f∘circle) = Σ mᵢ`, matching `box_charge_eq_deckRed`'s factorisation)
  and `WindingXi` (`windingNumber_xi_zero`/`loopCharge_xi_zero`: the winding number of the actual
  `xi` around a zero is its order / `ladderCharge`). 8 files total, all axiom-clean, lint green.
- 2026-07-07 — built to exhaustion in 3-formalized (6 files, all axiom-clean, lint green, umbrella):
  `DeckChargeCalculus` (additive charge + `ℤ/n ≃* μ_n` + conservation + tower), `DeckChargeLadder`
  (RH ladder in charge form + symmetry-blindness), `WindingNumber` (the integer winding number — a
  mathlib gap — with its full calculus), `WindingArgumentPrinciple` (winding = enclosed order at the
  centre; the topological and algebraic charge coincide), `WindingDivisor` (the argument principle for
  a divisor: winding of `∏ (z−ρᵢ)^{mᵢ}` around a circle = Σ mᵢ, welded to the deck charge),
  `RegionCharge` (quadrant-local charge + FE/conjugation transport + Klein-four blindness). The
  coordinating GPT agent's `DeckChargeBridge` builds on `DeckChargeLadder`, confirming both agents'
  rung conditions are one object.
