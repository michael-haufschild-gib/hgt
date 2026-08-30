# Ritt's theorem on Poincaré functions, in Lean

- **ID:** `ritt-poincare-differential-transcendence-formalization`
- **Stage:** 0-backlog
- **Type:** THEOREM (Lean) — a formalization project for a classical theorem, not new mathematics
- **Source:** the shared blocker of the last three cards in
  `2-fully-proven/not_new_scientific_knowledge/04-rg-stochastic-quantum-fields`
- **Statement:** If the Poincaré function `σ` of a rational map `R` of degree at least two at a
  repelling fixed point (`σ(λz) = R(σ z)`, `σ 0 = 0`, `σ' 0 = 1`, `|λ| > 1`) is differentially
  algebraic over `ℂ(z)`, then there are integers `r ≠ 0`, `j` and a nonzero rational `A` with
  `(σ')^r = a z^j A(σ)`.

## Goal

This single implication is what stops `exact-rational-rg-generation-dichotomy`,
`gadc-tree-population-rg-clock-hypertranscendence` and
`noisy-binary-tree-channel-rg-clock-hypertranscendence` from reaching stage 3.  Everything else on
those cards is already unconditional Lean, so proving it closes three cards at once and, more
generally, unlocks every hypertranscendence statement in the corpus that currently cites
Becker–Bergweiler or Ritt.

## What the corpus already owns (do not rebuild)

| Piece | Where |
|---|---|
| Koenigs linearizer, Poincaré germ | `HTGeometry/PoincareFunctionGerm.lean` |
| `Φ` DA `⇔` `κ` DA `⇔` `β` DA | `HTGeometry/RittDichotomy.lean` — `differentiallyAlgebraicOn_poincare_iff_rgBeta` |
| the order-one relation is an ADE (`(4) ⇒ (1)`) | `differentiallyAlgebraicOn_of_rittForm` |
| the cocycle equivalence `(4) ⇔ (5)`, both directions | `HTGeometry/RittCocycle.lean` |
| scaling rigidity behind `(5) ⇒ (4)` | `HTGeometry/ScalingGermRigidity.lean` |
| the positive branch (power family) | `HTGeometry/PowerMapPoincareDA.lean` |
| the negative branch (infinite-divisor obstruction) | `HTGeometry/CocycleDivisorObstruction.lean` |
| coherence of a linearized tower from DA | `HTGeometry/RGTowerCoherence.lean` |

Only `(1) ⇒ (4)` is missing.

## Scope note

`ritt-algebraicity-load-bearing.md` (same folder) fixes the *boundary* of the theorem: it cannot be
extended by replacing the rational base map with an arbitrary differentially algebraic germ.  That
card constrains generalisations; this one is the formalization of the rational statement itself, and
the rational hypothesis is exactly what the two proof routes below use.

## Approach

Two known proofs, neither of whose foundations exist in mathlib.

1. **Value distribution (Bergweiler, Becker–Bergweiler).**  Needs the second main theorem for
   *meromorphic* functions with the `S(r,f)` error term, plus complex-dynamics input (density of
   repelling periodic points) and a normal-families argument.  Corpus status as of 2026-08-30: the
   chain `SecondMainTheoremChain.mul_characteristic_le_sum_logCounting_add_proximity` and
   `SecondMainTheoremEntire.exists_mul_characteristic_le_of_separated_entire` still carry the
   proximity terms explicitly and are stated for *entire* `f`; the logarithmic-derivative estimate
   exists only in the small-growth form
   (`SmallGrowthDerivative.smallGrowth_proximity_logDeriv_isLittleO`).  A Poincaré function is
   meromorphic of finite order but not small growth, so the input is not yet in usable shape.
   **Coordination:** the final `m(r, f'/(f−a)) = S(r,f)` assembly is owned by
   `2-fully-proven/new_scientific_knowledge/universal-first-order-entire-cascade-unit-cost.md`.
   Do not duplicate it; build the finite-order layer on top once it lands.
2. **Parametrized Picard–Vessiot (Di Vizio–Fernandes).**  A Galoisian proof for the `q`-difference
   equation `σ(λz) = R(σ z)`.  mathlib has no Picard–Vessiot theory at all, so this route means
   building differential Galois theory first.

A third, cheaper attack is not available: the elementary divisor argument runs in the `(5)` direction
only, and the transcendence-degree / ultraproduct machinery built for the incoherence card gives
coherence *from* differential algebraicity, never the converse.

## Gates

- [ ] 0 → 1  in-progress: route chosen; the missing analytic input stated as a precise Lean signature
- [ ] 1 → 2  fully-proven: complete paper proof of `(1) ⇒ (4)` written out at formalization grain
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, axioms `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready: not applicable — classical theorem, formalization only

## Log
- 2026-08-30 — created in 0-backlog.  Extracted as the single shared blocker of the last three
  `04-rg-stochastic-quantum-fields` cards after the whole differential-algebra layer around it was
  formalized; see those cards' Lean-status sections and
  `HTGeometry/{RittDichotomy,RittCocycle,ScalingGermRigidity,PowerMapPoincareDA,CocycleDivisorObstruction}.lean`.
