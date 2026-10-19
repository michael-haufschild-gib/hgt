# Complete selected Fermi traces: quadratic valuation-depth conditioning

- **ID:** thim-full-trace-valuation-depth-stability
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `thim-selected-fermi-coefficient-observability.md`;
  `thim-fermi-valuation-observability.md`
- **Statement:** Complete selected Fermi traces control arbitrary finite-horizon
  sieve energy with a quadratic dyadic-depth factor. Explicit finite coefficient
  ramps force quadratic growth along power-of-two horizons; no uniform constant
  independent of the horizon exists.
- **Qualification:** No contribution counted; significance and external novelty
  remain separate from formal verification. Exact optimal physical constants are
  not claimed.

## Objects and exact verified statements

Write s(n)=sieveSeq N c n, J(n)=fermiBoundaryJump N c n, q(n)=1/(n(n+1)).
The complete energies are

`P = sum_(n>=1) q(n)*s(n)^2`,

`Q = sum_(odd n>=1) q(n)*J(n)^2 + sum_(even n>=1) q(2n)*J(2n)^2`.

Both converge for every finite horizon and every real coefficient function.

1. For D=Nat.log 2 N+1, `P <= (D+4)*(D+1)*Q`, unconditionally.
2. Its finite-window precursor controls paired indices below M by selected
   indices below `2^D*M`, with the same factor.
3. For every L>=0, an explicit coefficient function at horizon `2^(L+1)` has
   `P >= L*(L+1)*(2*L+1)/12` and `Q <= 2*L`.
4. For L>0 its selected energy is positive (the first selected even cell
   already contributes 4/5). Hence
   `((L+1)*(2*L+1)/24)*Q <= P` is a nonvacuous quadratic lower bound.
5. There is no real C such that `P(N,c) <= C*Q(N,c)` for all N,c.

The lower bounds are formalized at power-of-two horizons. Together with the
all-horizon upper bound, they establish unavoidable quadratic growth, without
claiming an exact best constant for every individual horizon.

## Dependency-closed paper mechanism

### Upper bound

If 0<d<2^D then divisibility of `2^D*n` and `2^(D+1)*n` by d agrees.
Induct on D, cancelling a factor two for even d and using coprimality for odd d.
The admitted divisors satisfy the strict bound by `Nat.lt_pow_succ_log_self`.
Thus the sieve saturates along each dyadic ray beyond this depth.

The existing even Fermi jump identity then telescopes to

`s(n) = sum_(j=0..D-1) J(2^(j+1)*n)/2^(j+1)
          + 2*J(2^(D+1)*n)/2^(D+1)` for positive even n.

The terminal coefficient squares sum to D+4. Cauchy–Schwarz, the exact
comparison `q(n)/a^2 <= q(a*n)` for a>=1, and an injective pair-index map for
each of D+1 dilations give the finite-window bound. Odd readings already
recover the corresponding sieve values. Existing bounded-sieve and pronic
summability results justify passage to the complete trace.

The earlier odd-ray proposal `(5/4)*(D+2)^2` is larger than the verified
`(D+4)*(D+1)` for the same D; it is not a stronger unresolved result.

### Matching obstruction

For 0<=k<L, let `F(k)=2^(k+1)*(L-k)` and place coefficient columns
`F(k)*(1_(d=2^(k+1))-1_(d=2^(k+2)))`. The horizon includes both endpoints.
Their sieve responses are disjoint valuation shells
`delta_k(n)=1_(2^(k+1) divides n and 2^(k+2) does not divide n)`.
Thus `s(n)=sum_(k<L) F(k)*delta_k(n)`.

On even n, `J(2n)=sum_(k<L) 2^(k+2)*delta_k(n)`; odd readings vanish.
Keeping just the cells n=2^(k+1) in P and using
`(a*x)^2/(a*(a+1)) >= x^2/2` for a>=1 gives the cubic lower bound.
Disjointness removes cross terms in Q. For each shell, drop its exclusion
condition, reindex multiples, and apply
`a^2*q(a*t) <= 2*q(t)` for a,t>=1. Total pronic mass 1 charges at most 2
per shell. This proves Q<=2L. The first even cell proves positivity, and an
Archimedean choice of L contradicts every proposed uniform inverse constant.

## Formal artifacts and verification

- `FermiValuationDepthAndFiniteWindowStability.lean`: saturation, exact finite
  recovery, finite-window stability; three public declarations.
- `FermiCompleteTraceValuationStability.lean`: both total energies,
  summability, complete-trace bound; four public declarations.
- `FermiDyadicRampAndQuadraticTraceLoss.lean`: explicit weight, energy bounds,
  positive trace, quadratic loss, no uniform inverse; five public declarations.

Every named leaf passed `lake --old env lean` source verification. All twelve
public declarations passed `/tmp` axiom audits, depending only on `propext`,
`Classical.choice`, and `Quot.sound`. All six leaves of the broader programme
are wired; index regeneration and `scripts/formal_tools.py lint --check-generated`
passed after the ramp leaf was added.

The ramp proof initially hit the default heartbeat limit while inferring an
implicit function in the existing range-shift theorem. Explicitly supplying
that function resolved it. No heartbeat limit was increased; no umbrella/full
build, numerical experiment, proof hole, or new axiom was used.

## Existing work and search coverage

Reuse, not novelty:

- Existing universal Fermi jumps and dyadic inversion; squarefree saturation;
  initial-prefix observability and Gram determinants; finite observation states.
- `abs_sieveSeq_le_sum_abs` in THIM
  `ShortWindowCorrelationDefectAndIsoStateClassification`.
- `summable_div_pronicSeq_of_bounded` in BVI
  `TruncatedPronicGramMatrixAndFiniteHorizonVonMangoldtApproximation`.
- `sum_Icc_filter_dvd_eq_sum_Icc_div` in THIM
  `CompositeSquarefreeStepAndMultiOctaveL2Energy`.
- RHTower `sum_Icc_eq_sum_range_succ` and `hasSum_pm_reciprocal_weight`.

Their relevant source and compiled-artifact availability were checked. A broad
bounded-sieve search missed the exact existing envelope; exhaustive rg found
it, and exact-name corpus search confirmed it. Retrieval alone is insufficient.

Complete lexical pagination included `sieveSeq pronic` (27), `Fermi logarithmic`
(51), `sieveSeq pow` (56), `sum filter dvd` (34), `sieveSeq sum` (83),
`dyadic pronic` (13), `pronic coercivity` (2), and `sieve inverse` (119).
Relevant endpoint-Haar resolvent and concurrent Ramanujan gap-chain tail
statements concern different operators. The initial deep stability query was
partial; later shell/conditioning queries completed but did not return an
applicable prior theorem. The conditioning snapshot inventoried 74,253 files
while reporting 57,019 compiler entries pending, 2,658 stale, and 2,654
unavailable. Source coverage does not certify compiler applicability.

Searches after writing the ramp returned this programme's own then-unverified
lemmas. Those hits are not prior art or independent evidence.

Zhong-Wei Liao's [Discrete Hardy-type Inequalities](https://arxiv.org/abs/1406.1984)
treats weighted finite summation operators. Its standard two-sided criterion
implies quadratic squared-norm growth for finite unweighted chains (our
specialization). Abstract chain estimates and ramps are prior mathematics.
Significance here must be assessed through the exact arithmetic realization
and physical trace consequence; no external novelty claim follows from search.

## No-go closure and remaining work

The failed uniform-bound route is recorded in
`../5-failed/thim-horizon-uniform-selected-fermi-coercivity.md`. Its positive
survivor is the verified quadratic-depth upper bound with matching growth
order. The earlier four-free support class still has uniform physical constants;
the coefficient-space inverse constant 3/2 concerns a different norm.

A stronger obstruction for nonnegative coefficients is separately recorded in
`thim-nonnegative-fermi-trace-conditioning.md`. Its separate seventh leaf has
passed source and public-axiom audits and is wired. Fresh index regeneration and
global generated lint passed after the concurrent BiScale umbrella was completed.
The stronger cone statement is not asserted by these three leaves.

## Gates

- [x] Precise arithmetic operator and physical norm.
- [x] Dependency-closed paper proof of the stated upper/lower results.
- [x] Unconditional Lean source, public axioms, umbrella wiring, generated lint.
- [ ] Significance and external novelty qualification.

## Log

- 2026-10-18 — Completed source/axiom verification and formal lint; no-go closed
  with its positive quadratic-depth survivor. Qualified programme count remains 0.
