# Arithmetic identity forcing the unit phase to vanish

- **Stage:** 1-in-progress
- **Type:** independently frozen hypotheses and classification targets
- **RH chain:** full arithmetic remainder -> independently forced unit imaginary part at every zero -> exclusion of off-line zeros. RH remains unproved.

## Source and attempted mechanism

The actual normalized unit remainder is `g_s(1)=conjugate(G(s))`, where

`G(s)=-1/[2*s*(1-s)]-zeta(s)/[s*(s+1)]`.

This identity is already in the Lean corpus. The exact successor recurrence determines differences of remainders; subtracting two candidate solutions leaves a constant. Its asymptotic boundary selects the actual solution but does not yet prove a unit sign law. The new attack tests a concrete analytic identity that would force vanishing at zeros directly, avoiding a tail-to-unit sign inference.

**U1, frozen:** there exists a holomorphic complex function H on the open strip `0<Re(s)<1` such that `Im(g_s(1))=Im(zeta(s)*H(s))` throughout that strip. If independently proved, U1 would force the unit phase to vanish at every strip zero. No H is assumed as a Lean premise for an RH claim.

**U2, independently frozen:** allow separate holomorphic multipliers on finitely many connected open subsets of the strip, each carrying the same identity throughout its domain, and require those domains to cover every positive-height strip zero. This tests whether splitting zeros into finitely many groups could rescue this specific type of identity. It is not a restriction on every possible classwise RH architecture.

## Attack as false and positive classification target

The corpus open-mapping mechanism suggests that `G+zeta*H`, being holomorphic and real-valued on a connected open domain, must be one real constant c. This predicts the exact replacement classification

`zeta(s)*H(s)=c+1/[2*s*(1-s)]+zeta(s)/[s*(s+1)]`.

At a zero, the constant would equal `-1/[2*s*(1-s)]`. Equality of this rational value at two parameters predicts that they are equal or sum to one. Two distinct positive-height zeros cannot sum to one. Thus every domain obeying the proposed identity may contain at most one positive-height zero, including multiple zeros and any exceptional cases. Verify all analytic hypotheses, signs, and denominator exclusions in the current corpus before accepting this argument.

The positive survivor to prove is the exact constant classification and the exhaustive equality cases for the rational zero boundary. If this obstruction closes, preserve both facts in Lean rather than reporting only U1/U2 false. It would show what extra freedom a vanishing identity needs, not prove that all arithmetic identities forcing vanishing are impossible.

## Evidence and scope

Corpus searches: `unit remainder`, `finite recurrence`, `boundary selection`, `recurrence cone`, `backward invariant`, `boundary uniqueness`, `signed transport`, `maximum principle`, `affine recurrence`, `unit discrepancy`, `head tail`, `two zeros`, `infinitely many zeros`, `holomorphic real constant`, `phase factorization`. Actual statements and proofs were inspected with rg and bounded reads, notably ArithmeticPrimeSievePhase, ArithmeticSuccessorCellPhase, ArithmeticMinimumPhaseCompleteness, and HTGeometry.GeometricCDDBoundarySelection. The known existence of multiple critical-line zeros is available in the corpus for falsification; no unproved zero location or simplicity premise is intended.

No computation is needed for the predicted algebraic and analytic obstruction. No novel architecture or literature-absence claim is made. U1 and U2 remain frozen until their exact proofs or refutations are audited.

## Independently frozen local survivor S1

The constant classification predicts an additional constraint, beyond distinct-height separation: any positive-height zero lying in such a domain must be simple and on the critical line. At a zero rho, differentiating `G+zeta*H=c` predicts

`zeta'(rho)*(H(rho)-1/[rho*(rho+1)])=-(1-2*rho)/[2*(rho*(1-rho))^2]`.

The right side is nonzero at positive height. Thus even an infinite collection of these local holomorphic identities would implicitly require simplicity, an additional unproved property of all zeros. Freeze the tangent identity and its consequence independently; they do not weaken U1 or U2. On a zero-free domain, every real c supplies the exact solution `H=(c-G)/zeta`, so the obstruction is not absence of analytic solutions away from zeros. All statements still require Lean audit.

## Independently frozen local survivor S2 and proof plan

**S2:** at a positive-height strip zero rho, a holomorphic germ H satisfying the phase identity throughout a neighborhood of rho exists **if and only if** rho lies on the critical line and is simple. The proposed constructive direction divides the analytic divided difference of `c-G` by the divided difference of zeta, with `c=G(rho)` real. Simplicity makes the latter denominator nonzero near rho. This is an exact local classification, not a simplicity or RH assertion.

- [ ] Derive the source identity, analyticity, constant classification, and exhaustive rational-boundary equality cases in Lean.
- [ ] Prove the tangent identity and both directions of S2, including the removable quotient at rho.
- [ ] Refute U1 and U2 using the corpus's analytic Hardy theorem; preserve the positive classification.
- [ ] Audit leaf builds, axioms, umbrella wiring, and formal lint; update current-state ledgers.
- [ ] Produce an independent head-orientation law and complete the unconditional RH proof. This final goal remains open regardless of the factorization audit.

Adversarial checks: the source is conjugated, so its imaginary part changes sign; a local germ does not imply a global multiplier; a double zero must be handled explicitly; a finite-cover obstruction must cover every chart and every positive-height strip zero. No numerical zero locations or computational certificates enter these proofs.
