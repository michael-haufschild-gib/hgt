# Absolute-Euler Squared-Seam Sign Violation

- **ID:** `absolute-euler-squared-seam-sign-violation`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / RH-disproof source target
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOVELTY UNVERIFIED]`
- **Source:** `../2-fully-proven/not_new_scientific_knowledge/seam-log-derivative-weld-identity.md`;
  `../2-fully-proven/not_new_scientific_knowledge/seam-log-markov-pick-rh-equivalence.md`;
  `../3-formalized/not_new_scientific_knowledge/completed-prime-gamma-moment-far-right-asymptotic.md`
- **Statement:** For `w > 1/2`, set
  `F(w)=xiLogDeriv(1/2+w)/w`. There exist `n >= 1` and `w > 1/2` for which
  `(-1)^n ((1/(2w)) d/dw)^n F(w) < 0`.

## Goal

Prove an unconditional violation using only the absolutely convergent Euler source, the
completed rational--Gamma source, and exact analytic inequalities. Such a violation implies
`not RiemannHypothesis`: under RH the centered canonical product gives

`F(w)=2 sum_gamma m_gamma/(w^2+gamma^2)`,

so every displayed alternating squared-coordinate derivative is nonnegative.

The proposed sign violation is stronger than `not RiemannHypothesis`; the converse is not
assumed. The research content is the source-derived negative sign, not the conditional endpoint.

## First Gate

For `n=1`, the witness is the explicit completed logarithmic-derivative inequality

`w * deriv xiLogDeriv (1/2+w) - xiLogDeriv(1/2+w) > 0`.

On `w > 1/2`, both terms have the exact rational--digamma--von-Mangoldt decomposition already
formalized in `XiCollapseDirichletLeg.lean`. This is the smallest source gate to attack before
introducing arbitrary-order differential operators.

## Competing Moves and Discriminator

1. **Compact first gate.** Derive a strict positive lower bound for the first-gate expression on
   a symbolic interval in `w > 1/2`. This would immediately prove `not RiemannHypothesis`.
2. **Compact growing-order gate.** If the first gate is nonpositive, retain a fixed safe base point
   and let `n` grow. The source proof must control the cancellation between the pole leg and the
   von-Mangoldt leg before taking the high jet.
3. **Cofinal coupled gate.** Let both `n` and `w` grow, with a proved coupling selected by a
   saddle inequality for the completed source. This move survives only if low critical-line atoms
   are not automatically dominant in that scaling.

The discriminator is a rigorous source-side asymptotic or one-sided bound for the completed
expression. A move is killed if its proposed main term has the RH-compatible sign or if it merely
renames an existing Stieltjes/Hankel equivalence.

## Current Attack

The existing theorem
`tendsto_scaled_iteratedDeriv_xiLogDeriv_odd` gives the derivative half of the first gate on the
far right. The missing companion is the elementary source asymptotic
`Re xiLogDeriv(x) -> +infinity`. Together they force the first-gate expression to be negative
eventually. This will close the fixed-order far-right move and confine any first-gate witness to a
bounded interval.

After that boundary is formalized, the live attack is the compact gate or a genuinely
growing-order completed-source estimate. No numerical search is part of this card.

## Anti-Theatre Gate

- The seam-log Markov/Pick and Hankel criteria are already RH-equivalent; restating them is not
  progress.
- Complete monotonicity is only a necessary RH shadow, not an equivalent characterization. A
  source-derived negative derivative is useful because it is a one-way disproof certificate.
- Fixed coefficient prefixes, fixed-rank Hankel tests, isolated positive Euler frequencies,
  finite local repairs, and finite half-turn-repaired packets are already excluded by the source
  boundary cards attached to `seam-log-markov-pick-rh-equivalence.md`.
- The rational pole at `s=1` and the zeta logarithmic derivative cancel in the completed object.
  Termwise high-jet estimates that split this cancellation are invalid as an RH argument.

## Open Core

`[OPEN CORE]` Prove a strict negative squared-coordinate derivative, or a negative completed
square test, directly from the absolute Euler plus rational--Gamma source. The proof must preserve
the completed cancellation and cannot use a zero off the critical line as an input.

## Gates

- [x] 0 -> 1 in-progress: source-pure coordinate, unconditional disproof endpoint, competing moves,
  and a falsifying asymptotic discriminator are explicit.
- [ ] Fixed-order far-right boundary proved on paper.
- [ ] Fixed-order far-right boundary formalized in Lean.
- [ ] Strict source-side sign violation proved on paper with no open dependency.
- [ ] Violation formalized and wired to `not RiemannHypothesis` in Lean.

## Log

- 2026-07-17 -- Created under the RH-false goal. The first move is to prove the far-right boundary,
  then attack only compact or growing-order completed-source regimes.
