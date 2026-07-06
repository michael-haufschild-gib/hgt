# 108 — Fail-fast audit of the incidence/parity route (F1 scale, F2 Davenport–Heilbronn, F3 hagree)

Three pre-registered tests on the route of docs 106–107, run to verdicts. Each was
designed to kill the route quickly if it is structurally unable to discriminate; the
predictions were registered before execution (worklog). Outcome in one line: **the route
survives F1 with a weakened consumer, F2 confirms the producer is arithmetic-blind and
localizes all discrimination at the weld, F3 closes the parity boundary datum as a target
and identifies the anchor as the mirror-symmetry breaker.**

---

## F1 — Scale audit [PROVED HERE, Lean]

Two questions: (i) is the producer's phase-π quantum a real resolution limit, (ii) does the
consumer genuinely need events at all scales `ε → 0`?

### F1a — the quantum is sharp (`EdgeScaleNoGo.lean`)

`short_window_engine_no_events`: for every edge segment with `ρ₀·(b−a) < π` there is a
carrier pair satisfying EVERY hypothesis of the forcing engine — entire, nonvanishing,
rate floor `ρ₀` attained, endpoint orientations agreeing — for which **no member of the
real-ratio pencil vanishes anywhere on the segment**. The witness is the pure phase
carrier `exp(ρ₀(z−σ−ia)+iθₐ)`, `θₐ = (π−ρ₀(b−a))/2`: the phase advances at exactly the
floor rate and never completes a half-turn. With the engine's positive direction (one
event per phase advance `π`, doc 107), the forcing threshold is bracketed at exactly the
phase-π quantum `π/ρ₀`:

- window ≥ `nπ/ρ₀` ⟹ `n` events forced (`exists_edge_events_of_high_edge`);
- window < `π/ρ₀` ⟹ nothing forced (`short_window_engine_no_events`).

At height `τ` on the ζ-carrier the floor is `ρ₀ ≈ ½·log(τ/2π)`, so the quantum
`π/ρ₀ ≈ 2π/log τ` **is the mean zero gap**: the engine's resolution is one mean gap, and
below it the rate floor constrains nothing.

### F1b — the consumer scale drops to ONE isolating annulus (`IsolatingAnnulusRung.lean`)

The rung `rhLadder_of_anchoredLedgers` demanded anchored ledgers at radii `≤ ε` for every
`ε > 0`. Reading its proof: the `∀ε` clause is consumed **once**, at the peel radius of ξ
at the anchor. The peel cofactor is global (`exists_peel` on `Set.univ`), so the
deck-class identity extends to any annulus whose ball is free of other ξ-zeros —
nonvanishing of the cofactor away from the centre IS the isolation hypothesis:

- `xi_peel_isolating_ball` — `ξ = (z−ρ)^m·h`, `h` analytic nonvanishing, on any isolating
  ball;
- `xi_deckClass_annulus_isolating` — the deck class counts the central multiplicity on
  any isolating annulus, no smallness needed;
- `rhLadder_of_isolating_anchoredLedgers` — the rung from ONE isolating annulus per
  off-line zero;
- `rhLadder_one_of_isolating_anchoredEventLedgers` — the event-typed base rung likewise;
- `xi_exists_isolating_radius` — isolating radii exist unconditionally.

### F1 verdict

The producer cannot reach scales below the phase-π quantum (`≈` mean gap), but the
consumer no longer demands them. **The route survives with the weakened consumer**, and
the producer/consumer meeting condition is now a single named comparison:

> **[OPEN CORE] The repulsion clause.** For a hypothetical off-line zero
> `ρ = β+iγ`, does its isolation radius exceed the producer scale:
> `δ_iso(ρ) > π/ρ₀(γ) ≈ 2π/log γ`?

This is a zero-repulsion statement (no other ξ-zero within one mean gap of ρ), i.e. a
locality statement about zero clustering — exactly the lever the scale audit was designed
to surface. Unconditionally false directions are known (zeros cluster below the mean gap
infinitely often on RH-attractor statistics), but the clause is only needed AT a
hypothetical off-line zero, where no gap statistics are established — this is genuinely
open ground, not a known-false shortcut.

---

## F2 — Davenport–Heilbronn stress test [paper]

**Registered prediction:** every producer hypothesis holds for an FE-satisfying,
Euler-product-free carrier with off-line zeros. **Confirmed.**

The test object: the Davenport–Heilbronn function (period-5 coefficient pattern), which
satisfies a Riemann-type functional equation with a degree-1 Γ-factor of conductor 5, has
no Euler product, and has zeros off the critical line — including zeros in the domain of
absolute convergence `σ > 1` (Davenport–Heilbronn 1936).

Hypothesis-by-hypothesis against the abstract terminus
`exists_incidence_edge_events_fluxPaired` and the concrete stack that feeds it:

| hypothesis | ζ-instantiation | D–H instantiation | target's arithmetic used? |
|---|---|---|---|
| `hab, hρ, hU, hmapU` (window geometry) | holds | holds | no |
| `hΛ1, hΛ1ne` (anchor analytic, nonvanishing) | `eulerHeadAnchor P`, any finite prime set | identical — the anchor is OUR inserted factor, independent of the carrier | no |
| `hΛ2, hΛ2ne` (carrier analytic, edge-nonvanishing) | `completedGN`: χ-symmetrized all-ones partial sum × arch factor | same construction with the period-5 coefficients and conductor-5 χ-factor; edge-nonvanishing is carrier data in BOTH cases | no |
| `hfloor` (rate floor) | `stripFloor − eulerHeadBound − B_D` | same three-part split; the D–H Γ-factor has the same `½log τ` Stirling growth (conductor shifts the constant UP) | no |
| `hna, hnb` (endpoints off-axis) | generic position | generic position | no |
| `hagree` (boundary datum) | window-dependent bit | window-dependent bit | no |

The formal tree itself already witnesses this: `gN` is `chiSymmetrize zetaChi
(dirichletPoly N)` — an **all-ones partial sum**; its functional equation
(`chiSymmetrize_one_sub_at`) is proven **generic in the summand `h`**. Nothing ζ-specific
enters the producer at any point; ζ first appears at the consumer (`xi` in
`rhLadder_…`).

### F2 verdict

The producer — anchor, carrier FE, floor, budgets, engine, pairing, parity — is valid for
the whole Davenport–Heilbronn class and therefore **carries no RH content by itself**.
Discrimination can only live at the **weld**: the step (not yet existing, and now known
to be impossible in FE-generic form) that transports edge-pencil events into the anchored
ledger at a putative off-line zero.

> **[PROVED HERE + classical] The D–H filter.** Any weld mechanism that is (a) uniform in
> the FE carrier class and (b) uniform in the ladder rungs `2^k` would prove the full
> ladder for the Davenport–Heilbronn function, forcing it to have no off-line zeros —
> contradicting Davenport–Heilbronn 1936. Hence every weld candidate must break FE-class
> genericity (use the Euler product or the positivity it brings) or rung uniformity.
> This is a mechanical falsifier: run any proposed weld against D–H before investing in
> it.

---

## F3 — the hagree dichotomy [PROVED HERE, Lean: `MirrorEdgeSymmetry.lean`]

Question: is the boundary datum `hagree` (endpoint-orientation agreement of the incidence
carrier on a lateral edge) derivable from the functional equation and Schwarz reality
alone? Both horns are now theorems.

**Blindness horn — mirror-symmetric certificates are free.** For pencil members
equivariant under line reflection `s ↦ 1−s̄` (= even FE ∘ reality):

- `incidence_lineReflection` — the incidence value conjugates under reflection;
- `im_incidence_mirror_edge` — its imaginary part is ODD across the critical line;
- `bandEvent_mirror_iff` / `mirror_orientation_reversal` — band events biject across the
  mirror at the same heights, orientations reversed;
- `mirror_pool_fluxPaired` — an event family pooled over a mirror pair of edges is
  doubled and its flux pairing exists **unconditionally**: a parity certificate over a
  mirror-symmetric contour asserts nothing, whatever the zero configuration;
- `completedGN_lineReflection` / `completedGN_im_mirror_edge` — the concrete carrier is
  equivariant on the strip, so its own (trivial) pencil is mirror-blind.

**Non-derivability horn — the symmetry class does not decide the datum.**
`hagree_not_determined_by_symmetry`: two entire carriers in the same equivariance class
(both even under `s↦1−s`, both Schwarz-real — `cosh(s−½)` and `cosh(2(s−½))`) realise
agreement and disagreement of the endpoint orientations **on the same edge**, all four
endpoint values off the real axis. No derivation from FE + reality alone can output
`hagree`; it is a strictly finer boundary quantity than the symmetry class.

### F3 verdict

Both horns land. `hagree` is re-classified: **not a residual datum to be discharged from
the box symmetry, but the problem in boundary coordinates** — the parity front is closed
as a target and retained as an interface. And one sharpening the critique did not
predict: the **anchor is the mirror-symmetry breaker**. The blindness theorems require
equivariance of BOTH pencil members; `eulerHeadAnchor` is not line-reflection equivariant
(its Euler factors tilt toward `Re s > ½`), so the anchored pencil escapes the
free-pairing argument precisely through the anchor. Whatever parity content the route can
ever extract must flow through the anchor's asymmetry — the finite prime sum is not a
budget nuisance, it is the only non-blind component.

---

## Combined verdict and forward objects

The pre-registered kill criterion — F1 no-weld AND F2 no failing hypothesis — did **not**
fire: F1's second half repaired the scale mismatch (single isolating annulus), so the
route is not certified non-feeding; F2 confirmed blindness of the producer but localized
all future content at the weld rather than killing the interface.

State of the route after the audit:

1. **Producer**: forces events at one per mean gap, arithmetic-blind, valid for the whole
   FE class. Complete and closed as a mechanism.
2. **Consumer**: needs ONE isolating annulus per off-line zero (new, weaker). Complete.
3. **Weld** (open): must use non-FE-generic input (Euler product/positivity) or break
   rung uniformity — the D–H filter is the mechanical test for candidates.
4. **Repulsion clause** (open): `δ_iso(ρ) > 2π/log γ` at a hypothetical off-line zero —
   the locality statement on which producer and consumer scales meet.
5. **Anchor asymmetry** (new): the only mirror-non-blind component; parity content must
   flow through it.

Next generative move: work items 4 and 5 jointly — the anchor's phase tilt
`∑_{p∈P} arg(1−p^{−s})` at an off-line zero is a finite, computable, mirror-odd quantity;
the question whether it can certify the boundary orientation on the isolating annulus of
the zero (rather than on a distant long edge) is exactly where the Euler product meets
the locality scale, and it is a new, concrete object no prior doc has named.
