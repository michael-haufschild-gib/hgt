# Prolate arcsine charge is an even-zeta-derivative spectrum

- **ID:** prolate-arcsine-zeta-derivative-transform
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`
- **Statement:** The universal diagonal prime constant in the constrained prolate radial leakage
  law is exactly a positive central-binomial transform of the derivative values
  \(-\zeta'(2),-\zeta'(4),\ldots\).

## The value

The diagonal von Mangoldt contribution in
`constrained-prolate-radial-leakage-divisibility-spectrum.md` is
\[
 \mathcal D
 =-\frac{16}{11\pi}
 \sum_{k=2}^{\infty}\frac{\log k}{k}\arcsin\frac1k.
\]
Put
\[
 c_j=\frac{\binom{2j}{j}}{4^j(2j+1)}.
\]

## Theorem — arcsine/zeta-derivative transform

One has the absolutely convergent identity
\[
 \boxed{
 \sum_{k=2}^{\infty}\frac{\log k}{k}\arcsin\frac1k
 =-\sum_{j=0}^{\infty}c_j\zeta'(2j+2).
 }
\]
Consequently,
\[
 \boxed{
 \mathcal D
 =\frac{16}{11\pi}
 \sum_{j=0}^{\infty}c_j\zeta'(2j+2)<0.
 }
\]

**Proof.**  For \(|u|\leq1\),
\[
 \arcsin u=\sum_{j=0}^{\infty}c_ju^{2j+1},
 \qquad c_j>0.
\]
At \(u=1/k\), every term is nonnegative after multiplication by \(\log k/k\).  Tonelli's
theorem therefore gives
\[
 \sum_{k\geq2}\frac{\log k}{k}\arcsin\frac1k
 =\sum_{j\geq0}c_j
 \sum_{k\geq2}\frac{\log k}{k^{2j+2}}.
\]
For every \(s>1\), termwise differentiation of the zeta Dirichlet series gives
\[
 -\zeta'(s)=\sum_{k\geq2}\frac{\log k}{k^s}.
\]
Substitute \(s=2j+2\).  Absolute convergence follows from the original positive double series;
alternatively, \(c_j=O(j^{-3/2})\) and \(-\zeta'(2j+2)=O(2^{-2j} )\).  Since every
\(\zeta'(2j+2)<0\), the sign of \(\mathcal D\) is strict. \(\square\)

## Analytic family behind the value

For \(\operatorname{Re}s>0\), define the arcsine Dirichlet transform
\[
 \mathcal A(s)=\sum_{k=1}^{\infty}\frac{\arcsin(1/k)}{k^s}.
\]
The same positive-term interchange gives the analytic identity
\[
 \boxed{
 \mathcal A(s)=\sum_{j=0}^{\infty}c_j\zeta(s+2j+1).
 }
\]
Both series converge locally normally on \(\operatorname{Re}s>0\).  Differentiating at \(s=1\)
recovers the prolate charge transform:
\[
 \boxed{
 -\mathcal A'(1)
 =\sum_{k=2}^{\infty}\frac{\log k}{k}\arcsin\frac1k
 =-\sum_{j=0}^{\infty}c_j\zeta'(2j+2).
 }
\]
Thus the diagonal constant is one value of a full analytic zeta-superposition law, not an
isolated series coincidence.

## Consequences

### Positive spectral measure on even derivative values

The weights \(c_j\) are positive and universal.  Thus the absolute diagonal charge
\(-\mathcal D\) is a positive spectral average of the values \(-\zeta'(2j+2)\), with no unknown
zeros and no analytic continuation into the critical strip.

### Sharp elementary bounds

For \(0\leq u\leq1\),
\[
 u\leq\arcsin u\leq\frac\pi2u.
\]
Hence
\[
 \boxed{
 -\zeta'(2)
 \leq
 \sum_{k\geq2}\frac{\log k}{k}\arcsin\frac1k
 \leq
 -\frac\pi2\zeta'(2).
 }
\]
Equivalently,
\[
 \frac{8}{11}\zeta'(2)
 \leq \mathcal D
 \leq
 \frac{16}{11\pi}\zeta'(2),
\]
with both endpoints negative and the inequalities ordered in the displayed direction because
\(\zeta'(2)<0\).

### Numerical certification

The two series independently give
\[
 \sum_{k\geq2}\frac{\log k}{k}\arcsin\frac1k
 =0.9501528656413454591578570027\ldots,
\]
\[
 \mathcal D=-0.4399171643919988701540541126\ldots.
\]
These numbers are verification only; the theorem is the exact transform above.

## Scientific interpretation

The constrained prolate calculation originally presents \(\mathcal D\) as a divisibility sum
over every positive integer.  The transform shows that the same value is a spectrum indexed by
the even archimedean points of zeta.  The equality is an exact bridge between:

1. the radial dilation kernel \(\arcsin(1/k)/k\);
2. the logarithmic arithmetic weight \(\log k\); and
3. the derivative values \(\zeta'(2j+2)\).

It does not assert RH and does not use zero data.  Its value is to put the solved diagonal source
charge into the same special-value language as the zeta side before any off-diagonal or central
correction is considered.

## Novelty audit

The ingredients—arcsine's power series and termwise differentiation of the zeta Dirichlet
series—are classical.  Searches for the exact series, its zeta-derivative expansion, and arcsine
Dirichlet transforms found adjacent rational-zeta-series literature but no matching formula.  The
identity is therefore a candidate-new exact value transform attached to a candidate-new prolate
constant; specialist formula-database review remains required.

- **Novelty estimate:** 0.67.
- **Significance estimate:** 0.72.  The transform is elementary once seen, but it changes the
  mathematical coordinates of the prolate diagonal charge and exposes a positive even-zeta
  derivative spectrum.

## Lean status

Mathlib formalizes differentiation of absolutely convergent `LSeries`, but the required arcsine
power-series theorem is not present in the current toolchain.  A faithful Lean proof should first
add that analytic expansion and then use a nonnegative double-series interchange; no wrapper with
the expansion assumed is added here.

## Gates

- [x] exact transform proved
- [x] convergence and sign proved
- [x] elementary bounds proved
- [x] numerical cross-check
- [ ] arcsine power series added to Lean
- [ ] specialist novelty audit
