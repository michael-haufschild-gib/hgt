# BAG prime-window error with arbitrary logarithmic savings

2026-10-06,17az. CLOSED on paper and in Lean as an analytic input.
Full signed hyperbolic-packet formalization remains open.

For every 1/6<θ<1 and every natural k, put δ=X^(θ-1). The actual relative
error |ψ(x+δx)-ψ(x)-δx|/(δx) is integrable on [X,2X] for all sufficiently
large X, and its integral times (log(X²)+2)^k/X tends to zero.
The exceptional-set estimate also permits a shrinking relative tolerance
(log(X²)+2)^(-a), for every natural a, while retaining every logarithmic
saving in the measure of the exceptional set.

Lean: `formal/GaloisForLFunctions/RHTower/ChiCubicPrimeWindowLogRate.lean`,
267 lines, public API:

- `RHTower.tendsto_logPow_volume_psi_short_shrinking` at74.
- `RHTower.chiCubicPrimeWindowError` at131.
- `RHTower.chiCubicPrimeWindowError_logRate` at217.

Paper proof: the existing explicit almost-all bound contains ε^(-2) and a
zero-weight cutoff scaled by ε^(-1). The exact inequality
zeroShortWeight(x,cY)≤c zeroShortWeight(x,Y), c≥1, reduces this to one fixed
zero-weight sum at cost ε^(-3). Choosing the tolerance as an inverse log
power lets the unconditional every-log-power zero-weight decay pay any
specified power. The large-X side condition follows from log powers being
dominated by X^(2θ). On [X,2X], the relative error is bounded by
2(log(X²)+2). Integrate the good-set tolerance plus this full bound on the
bad set. Measurability and integrability are proved explicitly.

Validation: final foreground leaf audit40319,
`/tmp/bag-prime-window-log-rate-clean-17az.log`, exit0 with empty output,
using `lake --old env lean` and explicit olean output. Imported final
axiom audit62949, `/tmp/bag-prime-window-axioms-final-17az.log`, exit0:
all three public declarations use only propext, Classical.choice and
Quot.sound. Mathlib-name scratch audit14887 passed. No new axioms,
admissions, heartbeat increases, full or umbrella builds. Umbrella import
occurs exactly once. Index45570 passed; all three public API rows checked.

Authoritative lint52145 exited1 with367 existing large-file warnings and
three unrelated unreachable modules: RHTower.CCMRestrictedWeilGroundPolynomialStructure,
RHTower.KuznetsovQuadraticPhase, HTGeometry.HilbertSchmidtTraceIdeal.
No finding names the new leaf; global lint is not clean.

Role in BAG: this pays the complete exceptional-set error against the
actual critical hyperbolic kernel once its uniform O_M(1) aggregate
bound and exact averaging identity are formalized. It does not assert
prime-anchor sampling, signed cubic cancellation or RH. The detailed
fixed-integer-radius packet paper proof is in
`../1-in-progress/bag-hyperbolic-phase-cell-cancellation.md`.
