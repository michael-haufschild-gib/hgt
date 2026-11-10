# Endpoint tangent moment obstructs polynomial scaling

- **ID:** B130-endpoint-tangent-moment
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [Analytic prime smoothing](../2-fully-proven/universal-moving-branch-for-analytic-prime-smoothing.md).

## Statement

Let `Ψ` be analytic on a disc larger than the unit disc, with
`Ψ(0)=1`, `Ψ(1)=-1`, and `Re Ψ′(1)=0`. Write
`Ψ(z)-1=Σ_{k≥1}b_k z^k`. Then

`Q(w)=ζ(2)exp(-Σ_{k≥1}b_k log(w+k))`

agrees with no polynomial on `Re w>0`.

## Mechanism

Taylor convergence gives `Σ b_k=-2` and
`Re Σ k b_k=Re Ψ′(1)=0`. The proposed asymptotic is

`Q(x)=ζ(2)[x²-(Σ k b_k)x+o(x)]` as `x→+∞`.

If `Q` were polynomial, it would be quadratic with purely imaginary
linear coefficient after division by its leading coefficient. Its
roots would have real parts summing to zero. At least one root would
lie in `Re w≥0`, where the exponential formula is analytic and nonzero.

The first moment can be obtained by dominated convergence from
`x log(1+k/x)→k` and `0≤x log(1+k/x)≤k`. This avoids classifying every
negative-integer branch separately.

## Candidate with a regular first shift

Consider

`Φ±(z)=1-4z²+2z⁴ ± 2iz(1-z²)√(2-z²)`.

The square root has an analytic branch on a disc larger than one.
The proposed pair is unimodular on `[0,1]` with common endpoints
`1,-1`. Its mean has coefficients `b₂=-4`, `b₄=2`, suggesting the
mixture profile `ζ(2)(w+2)⁴/(w+4)²`. The first shift is a zero;
the later shift is a pole. Thus cancellation of the first imaginary
coefficient can remove the first branch without producing polynomial
scaling. The pair and its arithmetic realization remain unformalized.

## Arithmetic relevance and boundary

Every finite real affine average of analytic unimodular profiles with
the same endpoints has the endpoint tangent condition. The conjecture
would retain the obstruction when averaging cancels the first imaginary
Taylor coefficient. It supplies a candidate invariant for arithmetic
phase mixtures beyond one common prime profile.

The asymptotic and polynomial exclusion are not yet formalized. An
actual arithmetic mixture still requires its own shifted-prime
expansion and regular-part control; no such family theorem is claimed.
Corpus search found no matching moment obstruction. External novelty
has not been assessed. B130 remains open.
