# MC actual exponential weight: scalar convolution square root

- **ID:** MC-C12.92-root
- **Stage:** 5-failed
- **Type:** NO-GO, unconditional Lean audit complete (2026-10-04, 1005i).
- **Source:** `../3-formalized/mc-exponential-weight-phase-zero.md`.

## Failed proposal

For every t>0, w_t(n)=exp(-nt)/n admits an absolutely summable real Dirichlet-convolution square root. Such a root would make the literal Liouville evaluation a real square and prove its positivity.

## Exact obstruction

The stronger complex-root proposal is false throughout some punctured interval 0<t<delta. The actual weight has a simple bounded completely multiplicative phase zero there. Absolute summability would identify its evaluation with the square of a holomorphic function, forcing derivative zero at every zero.

Lean: `RHTower.LiouvillePrimeBand.exists_small_no_summable_dirichlet_square_root` and `not_all_weights_have_summable_square_roots` in `LiouvilleExponentialWeightNoSquare.lean`. No source, summability, analytic, or RH premise is supplied to these conclusions.

## Strongest positive survivor

For every sufficiently large real T, two fixed prime intervals above T admit unit phases and |z|<1 such that the complete weight source at damping1/T vanishes with nonzero derivative. Every prime power, excluded cofactor, and nonlinear term is retained. Exact theorem: `RHTower.LiouvillePrimeBand.exists_eventually_simple_prime_phase_zero` in `LiouvillePrimeBandSimpleZero.lean`.

New insight: actual cofactor angular separation creates more linear phase capacity than the actual center, while all multiple-band terms are exponentially small. The positive survivor's dependency-closed proof and Lean formalization are complete, including the full real-scale logarithmic center limit. Targeted builds, required direct `lake --old env lean` audits and standard-only axiom audits passed. Imports wired; no umbrella build. Global lint has thirteen unrelated reachability errors, listed in the survivor card.

This retires only the scalar l1 convolution-square construction. It does not refute J_lambda>=0, a sum-of-squares construction, or RH; the literal critical signed-density estimate is still open.
