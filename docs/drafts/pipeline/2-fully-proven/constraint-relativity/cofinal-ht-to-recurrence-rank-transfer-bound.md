# Cofinal HT-to-recurrence rank-transfer bound

- **ID:** `cofinal-ht-to-recurrence-rank-transfer-bound`
- **Stage:** 2-fully-proven
- **Type:** CONDITIONAL THEOREM / NO-SHORTCUT BOUND (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL IMPLICATION]`
  `[HT/PHYSICS BRIDGE] [NO RH CLAIM] [NO LEAN WRITTEN]`
- **Role:** quantifies minimal growth of recurrence carrier needed for no-loss/no-surplus
  realization of neutral-fusion HT law tower.

## Setup

For tail-complete fusion system with `m=|A|`, let

\[
 K_N=E\langle F_{r,z}:0\le r\le N, z\in A\rangle_\partial.
\]

Layer independence gives

\[
 \operatorname{dtrdeg}_{K_0}K_N=Nm.
 \tag{1}
\]

Let recurrence carrier at depth `N` have `D_N` complex levels. Let
`y_1,...,y_(D_N-1)` be projective phase-coordinate trajectories in differential overfield of
`K_0`.

## Theorem: no-loss projective realization forces cofinal carrier growth

Assume no-loss realization supplies `K_0`-differential embedding

\[
 K_N\hookrightarrow
 K_0\langle y_1,\ldots,y_{D_N-1}\rangle_\partial.
\]

Then

\[
 Nm\le D_N-1,
 \qquad
 \boxed{D_N\ge Nm+1.}
 \tag{2}
\]

### Proof

Monotonicity of differential transcendence degree gives

\[
 Nm=\operatorname{dtrdeg}_{K_0}K_N
 \le
 \operatorname{dtrdeg}_{K_0}
 K_0\langle y_1,\ldots,y_{D_N-1}\rangle_\partial
 \le D_N-1,
\]

which is `(2)`. QED.

For simultaneous unit-residue profiles modulo pairwise coprime `q_i`, exact source state size is

\[
 m=\prod_i\varphi(q_i),
 \tag{3}
\]

so carrier must satisfy

\[
 D_N\ge N\prod_i\varphi(q_i)+1.
 \tag{4}
\]

## Consequence

No fixed finite recurrence carrier realizes complete HT fusion tower under stated no-loss
differential-coordinate embedding. Any claimed transfer must use at least one:

1. cofinally growing spectral support;
2. reuse/identification violating no-surplus and explicitly recorded as new relations;
3. nonlinear/non-differential-coordinate carrier with separate proof of independence retention.

This separates unbounded Krylov/wormhole complexity inside fixed large model from source-selected
HT law creation. Matching scalar growth rates does not transfer independent creative directions.

## Hostile audit

1. Theorem is conditional differential-coordinate bound; it does not assert physical recurrence
   carriers admit stated embedding.
2. Infinite-dimensional carrier escapes finite bound but must prove topological independence.
3. Nonlinear or nondifferential encoding requires separate no-loss theorem.
4. Bound is not RH result.

## Lean-return note

No Lean work authorized. If later requested, generic finite-dimensional injection bound is trivial;
substantive formal target is fusion differential-rank statement already publication-ready.

## Log

- 2026-08-08 — hostile HT/recurrence transfer audit; paper implication promoted.
