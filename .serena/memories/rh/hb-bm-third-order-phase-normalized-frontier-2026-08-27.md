# HB BM third-order phase-normalized frontier — 2026-08-27

Active pipeline card: `docs/drafts/pipeline/1-in-progress/bm-third-order-peierls-polarized-causal-cut.md`.

## Closed formal infrastructure

- Cubic U(1) covariance no-go: bare imaginary-part positivity cannot be physical; Hermitian modal work is invariant.
- Peierls polarization: mixed self-pairing vanishes for one cyclic action/skew propagator; full causal cut is polarized `++/--`.
- Exact compact-interval polarized BM Green identity and projective causal no-go.
- Complementary horizon branch: genuine hypergeometric factor, radius one, formal/analytic Gauss ODE, actual first/second derivatives, full BM jet.
- Regular horizon branch: genuine actual solution jet.
- Exact horizon basis normalized Wronskian is globally
  `4n + 3 + 2i chi` on `0<z<1`; nonzero on every Xi fibre.
- Exact Cauchy kernel solves homogeneous radial equation and has unit weighted derivative jump at every interior source radius.
- Exact AdS forbidden/source and square-root normalizable branches solve original BM jet.
- Exact AdS normalized Wronskian is globally `-1/2`.
- Conserved cross-Wronskians and Cramer's rule produce radius-independent horizon-to-AdS connection coefficients.
- Exact connection determinant is `-2 * (4n + 3 + 2i chi)`; nonzero on every Xi fibre.

Latest modules:
- `ThetaCuspHawkingBMSecondHarmonicExactWronskianConservation.lean`
- `ThetaCuspHawkingBMSecondHarmonicExactAdSForbiddenSolution.lean`
- `ThetaCuspHawkingBMSecondHarmonicExactAdSNormalizableSolution.lean`
- `ThetaCuspHawkingBMSecondHarmonicExactAdSOuterBasis.lean`
- `ThetaCuspHawkingBMSecondHarmonicExactConnectionMatrix.lean`

Verification:
- direct Lean passes for connection module;
- targeted build passes `11150/11150`;
- representative `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

## Failed routes

- Single-projective/same-branch flux vanishes.
- Monodromy-zero selection is impossible: complementary branch monodromy is nonzero on every Xi fibre.
- Bare cubic imaginary-part positivity is ruled out by phase covariance.

## Exact open core

1. Identify Cramer connection coefficients with physical Gamma/Jost coefficients. Corpus currently lacks Gauss `₂F₁` summation/connection theorem at `z=1`; likely requires building Euler-beta/Gauss infrastructure or endpoint asymptotics.
2. Impose physical horizon and AdS incidence to construct genuine retarded/advanced distributional Green kernels, including counterterm reciprocity.
3. Project literal augmented Einstein `B_aug,C_aug` source and target left-QNM normalization through those kernels.
4. Evaluate phase-invariant polarized horizon-plus-AdS flux.
5. Derive pre-Xi-specialization source-global equality/simultaneous-solvability law forcing flux zero; only then use optical zero locus to force RH.

No unconditional RH proof yet. Continue corpus-first heavy conjecture → hostile attack → prove/fail/pivot loop; always run `scripts/formal_tools.py research "<query>"` before new conjectures.