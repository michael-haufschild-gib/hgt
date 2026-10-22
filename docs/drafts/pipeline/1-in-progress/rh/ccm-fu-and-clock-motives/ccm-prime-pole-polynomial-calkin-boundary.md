# Joint polynomial Calkin boundary of CCM prime-pole projections

- **ID:** ccm-prime-pole-polynomial-calkin-boundary
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Connes--Consani local-factor pole spaces and the finite-place CCM route
- **Statement:** Every finite family of positive CCM pole-space projections has the joint essential boundary point `(1,...,1)` for all free noncommutative polynomial observables; evaluation there descends to the unique character of the polynomial algebra modulo compact evaluations that sends every local generator to one.

## Goal

Identify an intrinsic, positive essential-boundary structure forced by the local-factor pole geometry, then determine whether it supplies a genuinely new carrier theorem for the semilocal Connes route. The theorem concerns the actual Gauss/local-factor Hardy pole spaces. It does not identify them with the semilocal Sonin spaces and does not claim Weil positivity or RH.

## Gates

- [x] 0 → 1 in-progress: exact cross-scale Gram law, cofinal simultaneous coherence, weak-null boundary, and a concrete operator-algebra target
- [ ] 1 → 2 fully-proven: standalone paper proof and completed primary-literature novelty audit
- [ ] 2 → 3 formalized: all unconditional theorem surfaces imported, narrow build green, axiom report and formal lint pass
- [ ] 3 → 4 publication-ready: dual novelty/significance gate at least 90/100 and standalone paper

## Formal theorem surface

The unconditional Lean chain currently proves:

1. Exact cross-scale CCM pole Gram/Laplace covariance.
2. Cofinal simultaneous approximate alignment for every finite family of positive scales.
3. A common weakly-null unit sequence for the corresponding orthogonal projections.
4. For every free noncommutative polynomial `Q`,
   \[
   Q(P_1,\ldots,P_d)v_n-Q(1,\ldots,1)v_n\longrightarrow0.
   \]
5. The essential-boundary inequality
   \[
   |Q(1,\ldots,1)|\leq \|Q(P_1,\ldots,P_d)\|_{\mathrm{ess}}.
   \]
6. Compact polynomial evaluation forces `Q(1,...,1)=0`.
7. Evaluation at `(1,...,1)` descends to a character of the polynomial quotient by compact evaluations, and this character is uniquely determined by taking value one on every generator.
8. Every free polynomial over an arbitrary index family has a finite-generator presentation. Therefore the character extends algebraically to arbitrary positive scale families, including the complete family of prime logarithms.

The finite capstone is `formal/GaloisForLFunctions/RHTower/CCM/CCMPrimePolePolynomialBoundary.lean`. The arbitrary-family and all-prime capstone is `formal/GaloisForLFunctions/RHTower/CCM/CCMPrimePoleUniversalPolynomialBoundary.lean`.

## Positive Connes-route obligation

The local factors force a coherent joint boundary character rather than merely independent finite-place projections. A successful semilocal/global construction must therefore carry an observable that is nonconstant beyond this boundary character and couples it to the Weil/divisor trace datum. Finite polynomial Calkin information alone lands at the universal boundary point.

## Open core

1. Audit whether this exact joint character for the Connes--Consani prime-pole model appears in the model-space or operator-algebra literature.
2. Determine whether the now-formalized algebraic all-prime character is continuous in a natural completed operator algebra.
3. Prove or refute a source-defined coupling from this boundary character to the actual semilocal Sonin compression or Weil trace.
4. Promote only if the route-specific theorem clears both novelty and significance; the general Weyl-sequence lemma is infrastructure, not novelty.

## Current verdict

`[NOVELTY UNVERIFIED]`. The exact cross-prime coherence and induced all-prime algebraic character appear route-specific. The abstract implication from a common Weyl sequence to an essential-norm bound is classical operator theory. Provisional significance: 90/100 mathematically, pending the primary-literature gate and a precise comparison with completed model-space projection algebras.
