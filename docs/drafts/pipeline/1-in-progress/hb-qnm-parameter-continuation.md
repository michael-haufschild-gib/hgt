# HB: original QNM frequency continuation

- **Stage:** in progress.
- **Goal:** unconditional RH proof/falsification; open.
- **Frontier map:** read-only.

Chain: literal theta cusp → Xi occurrence → retained spin-two source → original
causal response and physical left-QNM pairing → independent Hawking-clock
extinction → RH.

The complete-source original joint causal response and its operator-domain
Laplace identity are constructed. The next obligation is physical continuation
of that response with its left pairing. Energy-space inversion on the opposite
frequency half-plane does not establish the required causal continuation.

## Closed frequency component

[Original radial Green germs at every Xi QNM](../3-formalized/hb-original-qnm-frequency-germs.md)
records six audited Lean leaves and 25 public theorems. The original Gauss sums
are holomorphic in frequency under explicit local denominator bounds, including
terminating numerator parameters. The original dressed horizon solution and full
connection coefficient are analytic off the real frequency axis; the dressed
normalizable solution is entire at each physical interior radial point.

The actual normalized kernel and both source-weighted Green integrands have
meromorphic germs at every Xi QNM on both branches. The original source amplitudes,
angular coefficients, and fixed smooth-onset correction are retained. Equality to
the original source transform is proved in its convergence chamber. This does not
assert a pole, a nonzero residue, endpoint-integral continuation, or full joint
response continuation.

## Current analytic target

Continue the actual endpoint Green moments. For the horizon moment, retain the
exact factorization of the integrand into `z^w` times the Gauss factor and source
remainder, with the full connection normalization. Prove a parameter-uniform
endpoint Taylor decomposition, integrate the finite Taylor terms with their
actual coefficients, and bound the subtracted remainder in the larger frequency
chamber. Every subtracted coefficient must be restored in the continued formula.
Establish equality with the original convergent integral before identifying any
QNM residue. Handle the outer moment's endpoint separately.

Corpus starting points from broad OR discovery and focused AND searches:
`BarnesSingleZetaContinuation` and `BarnesDoubleZetaDeepContinuation` construct
actual Mellin continuations by analytic-slope Taylor remainders, retained polar
terms, and endpoint integrability. Their fixed-kernel proofs supply techniques;
the BM source depends on frequency, so the required uniformity must be proved.
`HadamardFinitePart` concerns a different real Cauchy kernel and does not itself
supply this continuation.

Then identify the continued moments/spatial pairings with the complete-source
joint causal response and its physical left residue. Full joint angular/metric,
spin-two/AIME identification, and independent Hawking-clock extinction remain
open. Local factor analyticity is not their completion.

No numerical experiment is indicated: coefficient estimates, endpoint remainder
bounds, and complex analytic identities are the relevant proof obligations.
