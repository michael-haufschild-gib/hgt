# Positive prime-cube ceiling: source-shape obstruction

- **ID:** CCM-FU-UC1
- **Stage:** 5-failed
- **Type:** UC1 refuted; exact positive survivor formalized
- **Source:** [actual-source PE4](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Scope:** tests a proposed generic proof mechanism; the cube is not the actual divisor source. PE4 and RH remain open.

## Frozen source-shape claim

UC1: a strictly positive unsigned finite prime cube with final signed energy at most its initial diagonal admits some prime order whose every intermediate energy stays below that initial diagonal. This is an independent proposed source-shape implication, with the same literal prime difference and factor-one ceiling. The endpoint bound is granted only to test that implication as strongly as possible. Assuming it for the actual source would already assume SD1, so UC1 is not an independent SD1 producer even if it were true.

## Dependency-closed paper obstruction

Use four prime coordinates 0,1,2,3. At Boolean subset S set `K_e(S)=e+B(S)`, where B is 1 at the empty subset and at each pair `{0,i}` for i=1,2,3; B is 4 at `{1,2,3}`; and B is 0 elsewhere. Every coordinate is strictly positive when e>0.

Eliminating coordinate i replaces `F(S)` by `F(S)-F(S union {i})` on i-free S, and discards the i-containing coordinates. Every first elimination cancels the uniform background exactly. The initial diagonal is `20+16e+16e²`.

For the sparse source B, the six pairs of even-parity occupied vertices have symmetric differences equal to the six coordinate pairs, each contributing positive overlap 2. The four even/odd occupied pairs have symmetric differences equal to the four coordinate triples, each contributing negative overlap -8. Thus after m distinct coordinates have been processed, for m>=1, energy is

`20+2 binom(m,2)-8 binom(m,3)`.

The energy sequence after the first through fourth eliminations is exactly `20,22,18,0`, independently of order. At e=1/16 the initial energy is `337/16`, so every first elimination strictly contracts, every second stage exceeds the initial energy by `15/16`, and the final signed source is zero. This refutes UC1.

## Strongest positive survivor

For the whole family e>=0, an original-diagonal ceiling exists exactly when `e²+e>=1/8`; in that regime every order satisfies it. Below that threshold no order does. This is a complete parameter classification, together with the exact invariant that one prime difference erases a uniform unsigned background. The obstruction identifies separate activation of even pair gains and odd triple cancellation as information not captured by positivity or endpoint energy.

## Formalization and scope

`formal/GaloisForLFunctions/RHTower/PositivePrimeCubeEnergyBarrier.lean` proves the literal finite-coordinate difference operation's constant-background erasure, all four intermediate-energy identities, strict-positive counterexample and sharp parameter classification. In particular, `positivePrimeCube_order_ceiling_iff` characterizes the ceiling for every tuple of distinct coordinates; `positivePrimeCube_strict_counterexample` is a closed counterexample with no hypotheses. The identities also prove zero final energy in every valid order.

The leaf passed `lake env lean GaloisForLFunctions/RHTower/PositivePrimeCubeEnergyBarrier.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PositivePrimeCubeEnergyBarrier.olean`. All nine new public theorems were audited once from a temporary import: only `propext`, `Classical.choice`, and `Quot.sound`; no added axioms. The module is wired into `RHTower.lean`, without building that umbrella or dependencies. Global `scripts/formal_tools.py lint` passed; the declaration index was refreshed. No numerical screen was used for this algebraic family. All constants follow from symbolic source amplitudes and exact overlap counts, not experimental values.

UC1 is closed negatively and its full parameter-family survivor is closed positively in Lean. The literal arithmetic PE4 and SD1 remain open. A source-specific ordering argument needs arithmetic control of intermediate pair and higher-order overlap activation; positivity, first-step contraction and endpoint energy alone do not supply it.
