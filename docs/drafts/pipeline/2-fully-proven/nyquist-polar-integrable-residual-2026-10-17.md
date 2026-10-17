# Explicit Nyquist polar producer modulo an integrable residual

- **ID:** nyquist-polar-integrable-residual-2026-10-17
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scope:** Infinite-Grid Tail Rigidity Beyond Trap 5; general signed correlations.
- **Status:** Dependency-closed paper proof complete; Lean audit pending; uncounted.
- **Paper:** `docs/reports/BiScaleUncertainty/NyquistPolarIntegrableResidual.md`
- **Guide:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).

## Positive survivor

For cell I_n=[log n,log(n+1)], n>=1, reuse the existing explicit producer
C_n=nyquistPolarConstant(n). For bounded continuous real H, define

    r_n(H)=integral_I_n H(x)(cosh(x/2)-C_n) dx.

These actual residuals are absolutely summable, with an explicit
uniform tail bound |sum_(n>=N) r_n(H)|<=||H||_infinity/sqrt(N), N>=1.
The residual defines a bounded linear functional, Lipschitz in
the global correlation norm, with a vanishing operator norm on distant tails.

For compactly supported H, the exact actual polar integral decomposition is

    integral_(0,infinity) H(x)cosh(x/2) dx
      = sum_(n>=1) C_n integral_I_n H(x) dx + sum_(n>=1) r_n(H).

The first series is finite for each such H. This locates every discontinuity
of the polar functional in the explicitly produced cell-average term, while the
weight-approximation residual is uniformly controlled independently of support,
energy or source count. Apply the decomposition to actual normalized correlations
and to the diffuse producer after its certificate is complete.

## Paper proof mechanism

Existing pointwise producer error and cell length bounds give

    |r_n(H)| <= ||H||_infinity/(4 n sqrt(n)).

An elementary radical comparison bounds 1/(4 n sqrt(n)) by
1/sqrt(n)-1/sqrt(n+1) for n>=1. Finite telescoping and the vanishing reciprocal
square root then give the full summable tail. The paper checks endpoint conventions,
interval orientation, operator linearity, the infinite sum and exact compact-support
decomposition. Lean must formalize these actual integrals, not an assumed interface.

## Corpus boundary and Trap 10

Search logs: `/tmp/nyquist-integrable-residual-frontier.txt` (one unrelated
factorial-producer tail), `/tmp/nyquist-integrable-residual-nearby.txt` and
`/tmp/nyquist-integrable-residual-nearby-20.txt` (all 37 declarations across five
modules inspected). Existing `ExplicitNyquistPolarAndChebyshevFactorialProducer`
already proves the pointwise cell error, O(n^-2) cell L2 error, consumer residual
and O(N^-1) dyadic L2 sum; none is new here. Existing Euler–Maclaurin quadrature
retains the polar density cost and is a different approximation.

This candidate uses the explicit producer with an unconditional all-tail bound.
It concerns exact cell averages, not point samples or prime-weighted sums. It
does not assert global polar closedness from unweighted trace decay, a Chebyshev
bound, or an arithmetic coercivity inequality. No floor counterterm subtraction.
The scientific target is the stable remainder operator and exact source of polar
escape, rather than another assumed positivity receiver.

## Gates

- [x] Focused prior-corpus search; existing producer identified.
- [x] Dependency-closed paper proof and strongest positive-survivor audit.
- [ ] Exact Lean formalization with actual integrals and explicit bounds.
- [ ] Direct leaves, exhaustive axiom/API checks, umbrella wiring and lint.
- [ ] Count once only if the full connected result adds a substantive tool.

## Strongest paper survivor

The actual all-tail residual is a positive bounded linear functional R_N, with
exact operator norm A_N=sum_(n>=N) integral_I_n (cosh-C_n)<=1/sqrt(N), attained
by the constant function one. It is represented by an actual nonnegative L1
kernel. Compact-source polar integrals split exactly into the explicit weighted
cell-average producer and this stable residual. The diffuse train paper forces
the producer term to diverge under compact correlations and convergent energies;
the new uniformly bounded correction cannot explain that escape. All details,
including absolute summation and endpoint conventions, are proved in the paper.
No new Lean source has been written for this package yet.
