# Continuous factorial producer with exact prime-grid values

- **ID:** signed-prime-polar-grid-preserving-smoothing
- **Stage:** 1-in-progress
- **Type:** PAPER-PROVED / LEAN IN PROGRESS
- **Scope:** Next uncounted signed prime–polar producer package.
- **Statement:** Construct a concrete compact continuous test with exactly the
  factorial bi-null producer's prime-grid values and an unconditional
  O(log N/sqrt(N)) full signed-pairing bound.

## Proposed construction

For N≥1 set ε=1/(4N). For K=N,2N,4N and 1≤λ≤1+ε define
R^λ_K(x)=exp(x/2) Σ_{j=1}^K 1_[0,log(λK/j)](x).
Keep j≤K fixed. Average
W^λ_N=(R^λ_(4N)−4R^λ_(2N)+4R^λ_N)/sqrt(N)
uniformly in λ over [1,1+ε].

An explicit formula for the averaged jth rectangle, on x≥0, is
exp(x/2) clamp((1+ε−j exp(x)/K)/ε,0,1).
Use this clamped expression on all real x when taking the bi-null combination.
For x≤0 every clamp equals 1, so the sums K cancel in the stencil and the result
is exactly zero. Thus global continuity should follow directly from the explicit
finite clamped formula, with no discontinuous extension step. Its support ends
at log(4N+1), where every clamped ramp vanishes.

## Mechanism to verify

For 1≤λ<1+ε, λK lies in [K,K+1). No integer product nj crosses the cutoff.
Hence R^λ_K(log n)=R_K(log n) for every integer n≥1. The exceptional upper
λ endpoint has measure zero, including n=4N+1. Thus the averaged test preserves
every actual prime-grid value exactly, including top value 2 at log(4N).

Finite continuum integration gives
ν(W^λ_N)=(2 B_N−λ C_N)/sqrt(N),
where B_N is the factorial bi-null producer and C_N∈[0,1] its harmonic correction.
The K log λ terms cancel because 4N−4(2N)+4N=0.
The averaged pairing should therefore be

ν(average W_N)=[2 B_N−(1+1/(8N))C_N]/sqrt(N),

with bound [10 log(4N+1)+3+1/(8N)]/sqrt(N).

Size control to audit as part of the same construction: for y=Nλ exp(−x), the
floor stencil floor(4y)−4floor(2y)+4floor(y) takes values 0,1,−2,−1 according
to the quarter containing the fractional part of y. Thus |W^λ_N(x)|≤
2 exp(x/2)/sqrt(N) on [0,log(4N+1)]. Averaging should give a uniform squared
L² upper bound 20. On the fixed explicit band
log(2N+1)<x≤log(4N), the averaged test equals exp(x/2)/sqrt(N), so its squared
L² norm is at least 2−1/N≥1. These bounds would certify that vanishing pairing
is not caused by the producer vanishing in L². Treat all these size claims as
unverified until the endpoint and floor-count details are audited.

## Gates and boundary

- [x] Initial corpus search, including candidates and source arguments.
- [x] Audit endpoint, continuity, support and integration details on paper.
- [ ] Construct the actual C_c test and prove exact grid preservation in Lean.
- [ ] Prove the exact pairing and explicit bound, with no arithmetic assumption.
- [ ] Certify uniform upper and positive lower L² bounds for this concrete family.
- [ ] Direct leaf checks, scratch axioms, umbrella, lint and index.

This would remove a real domain obstruction: the current producer is discontinuous.
The test still has zero origin value and nonzero top value, so it is not an
autocorrelation. No arbitrary-correlation packet estimate or positivity claim follows.
Count only the complete continuous producer and exact arithmetic preservation
package; averaging and interpolation helpers do not count separately.

Dependency-closed paper proof:
`docs/reports/BiScaleUncertainty/SignedPrimePolarContinuousFactorialProducer.md`.
Lean uses the explicit ramp directly: exact endpoint values replace an a.e.
parameter argument; piecewise FTC replaces two-variable Fubini; a finite antitone
alternating-sum bound replaces floor-case enumeration. The squared L² upper
bound can in fact be 16; the planned public bound 20 remains valid.

Search `/tmp/spp8-next-search.json`: partial=false/errors=[]; complete file inventory,
source-only/pending compiler metadata and unmeasured semantic coverage. Retrieved
smooth logarithmic-grid sources, finite-grid extensions, and the current unverified
factorial producer source; no retrieved theorem supplies this common-dilation
construction and exact harmonic correction. Inspect those precedents before code.
