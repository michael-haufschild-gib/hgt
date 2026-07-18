# Scale-covariant Bernstein--Abel tomography

- **ID:** `scale-covariant-bernstein-abel-tomography`
- **Stage:** 3-formalized
- **Type:** MASTER THEOREM / INVERSE THEOREM / ABEL SELECTION
- **Scientific status:** `[PROVED] [FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Paper:** [main.tex](../4-publication-ready/prime-arch-abel-susceptibility-selection/main.tex)
- **PDF:** [main.pdf](../4-publication-ready/prime-arch-abel-susceptibility-selection/main.pdf)

## Headline theorem

One scale-covariant positive observation field is simultaneously:

1. globally source-faithful on pointed moment sequences;
2. exactly equal to the square energy of its atomic Bernstein packet;
3. spectrally complete for every real packet exponent `p >= 1`;
4. sharply square-root singular in the quadratic case;
5. exactly selective for the nonnegative-real source radical;
6. normalization-free at first recession order.

Let

```text
a_(N,k)^m(x)
  = binom(N,k) sum_(j=0)^(N-k)
      (-1)^j binom(N-k,j) x^(k+j)m_(k+j),

P_(N,m)(x) = sum_(k=0)^N a_(N,k)^m(x)^2,

Pcal_m(N,R) = P_(N,m)(R^(-1)),
chi_m(R,t) = sum_(N>=0) Pcal_m(N,R)t^N.
```

Assume an atomic representation

```text
m_n = sum_i c_i z_i^n in R,
```

with `sum_i |c_i| < infinity`, bounded injective nodes `z_i -> 0` cofinally, `c_i != 0`,
`m_0 > 0`, and every occupied real node nonnegative.

Put

```text
u_i(R) = z_i/R,
B(R) = sup_i (|u_i(R)| + |1-u_i(R)|),
A(R) = B(R)^(-2),
Delta = sup_i (|z_i| - Re z_i).
```

Then the formal master theorem `scaleCovariantBernsteinAbel_tomography` proves all of the
following.

### 1. Global pointed source chart

For every `N`, the map

```text
J_N(m_0,...,m_N) = ([x^r]P_(N,m)(x))_(0<=r<=N)
```

is a global bijection

```text
(0,infinity) x R^N -> (0,infinity) x R^N.
```

Its triangular law is

```text
[x^0]P_(N,m) = m_0^2,

[x^r]P_(N,m)
  = 2(-1)^r binom(N,r)m_0m_r + Q_(N,r)(m_0,...,m_(r-1)).
```

The inverse is recursive:

```text
m_0 = sqrt(y_0),

m_r = (y_r-Q_(N,r))/(2(-1)^r binom(N,r)m_0).
```

The coordinate Jacobian is lower triangular and

```text
det D J_N(m)
  = (-1)^(N(N+1)/2)(2m_0)^(N+1)
      prod_(r=0)^N binom(N,r) != 0.
```

Therefore the cofinal family `(P_(N,m))_N` recovers the complete pointed moment sequence.

### 2. Literal atomic realization

For every `R > 0`,

```text
Pcal_m(N,R)
  = sum_(k=0)^N |
      sum_i c_i binom(N,k)(z_i/R)^k(1-z_i/R)^(N-k)
    |^2.
```

Thus the finite source chart and the infinite atomic packet are the same observable.

### 3. All real-p spectra

If `R > 2M` and some node is nonreal, the maximal amplitude `B(R)>1` is attained on a nonempty
finite packet. Every complementary amplitude is bounded by one common `beta(R)<B(R)`.

For every real `p >= 1`, if

```text
E_(p,N)(R) = sum_(k=0)^N |A_(N,k)(R)|^p,
```

then

```text
E_(p,N)(R)^(1/N) -> B(R)^p.
```

This is the strengthened theorem missed by the earlier referee: the confocal amplitude is the
complete real-p packet spectrum, not only the quadratic exponent.

### 4. Sharp quadratic half-order and Abel boundary

For `p=2`, the selected finite packet has distinct maximizing ellipse phases. Therefore all
mixed terms are exponentially gapped and only the positive diagonal constants survive:

```text
sqrt(N) Pcal_m(N,R)/B(R)^(2N) -> L(R) > 0,
```

where

```text
L(R) = sum_(u in U_R) |C_R(u)|^2 kappa(u),

kappa(u)
  = pi^(-1/2)
    (1-(|u|-|1-u|)^2/(|u|+|1-u|)^2)^(-1/2).
```

The Abel transfer is exact:

```text
sqrt(1-B(R)^2 t) chi_m(R,t) -> sqrt(pi)L(R)
```

as `t` approaches `B(R)^(-2)` from below.

### 5. Exact radical and confocal recession

Define

```text
delta_R(z) = |z|+|R-z|-R,
D(R) = sup_i delta_R(z_i).
```

The pointwise and envelope collars are

```text
0 <= delta_R(z)-(|z|-Re z) <= M^2/(2(R-M)),

Delta <= D(R) <= Delta + M^2/(2(R-M)).
```

Moreover `D` is nonnegative and antitone, and

```text
B(R) = 1 + D(R)/R.
```

Hence, for every `R>M`,

```text
A(R)=1 iff Delta=0 iff every z_i is nonnegative real.
```

The normalization-free first recessions are

```text
R(B(R)^2-1) -> 2Delta,
R(1-A(R))   -> 2Delta.
```

### 6. Gibbs corollary

For

```text
F(R) = -log A(R),
```

the exact split is

```text
F(R)=2log B(R),
F(R)=0 iff every node is nonnegative real,
R F(R) -> 2Delta.
```

This is a conceptual corollary, not a second main theorem.

## Why this is stronger than the retired fixed-scale paper

The earlier fixed-normalization manuscript was vulnerable to the correct objection that an
arbitrarily narrow Abel collar can be manufactured by increasing the normalization radius.
The present theorem retains the full scale variable. It makes no scientific claim from
`A(R) -> 1`, which holds for every bounded source. The intrinsic statement is instead the exact
recession

```text
R(1-A(R)) -> 2Delta.
```

The rewrite also incorporates the earlier referee's strongest abstract requests:

- the theorem is stated for general absolutely summable atomic sources;
- the false-phase coefficient law is sharp `B^(2N)/sqrt(N)`;
- the Abel boundary has the explicit square-root coefficient;
- every real `p>=1` has exact nth-root spectrum `B^p`;
- the source-side object and atomic weights are displayed explicitly;
- no Connes architecture is claimed to be forced to realize this particular observable.

## Formal theorem ledger

All listed theorem leaves pass the project toolchain directly. The master theorem, Gibbs
corollaries, and dedicated Xi radical capstone depend only on the ordinary logical axioms
`propext`, `Classical.choice`, and `Quot.sound`.

| Mathematical component | Module | Principal theorem |
|---|---|---|
| triangular coefficient law | `RHTower/ScaleCovariantBernsteinPurityJet.lean` | `coeff_bernsteinScalePurityPolynomial_eq_leading_add_lower` |
| explicit global inverse | `RHTower/ScaleCovariantBernsteinPurityChart.lean` | `bernsteinPurityJet_global_pointed_chart` |
| Jacobian and determinant | `RHTower/ScaleCovariantBernsteinPurityJacobian.lean` | `det_bernsteinPurityJetJacobian_ne_zero` |
| atomic observation bridge | `RHTower/ScaleCovariantBernsteinAtomicObservation.lean` | `scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy` |
| generic finite selection | `RHTower/ScaleCovariantBernsteinAtomicSelection.lean` | `exists_positive_halfOrder_atomicBernsteinPacket_of_small_source` |
| inverse-scale confocal selection | `RHTower/ScaleCovariantBernsteinInverseScaleSelection.lean` | `exists_positive_halfOrder_inverseScaleAtomicPacket` |
| all real-p spectra | `RHTower/ScaleCovariantBernsteinRpowSpectrum.lean` | `exists_tendsto_inverseScaleAtomicBernsteinRpowEnergy` |
| confocal recession | `HTGeometry/ConfocalAbelDefectFlow.lean` | `tendsto_mul_one_sub_confocalAbelRadius` |
| single bundled master theorem | `RHTower/ScaleCovariantBernsteinAbelTomography.lean` | `scaleCovariantBernsteinAbel_tomography` |
| Gibbs corollary | `RHTower/ScaleCovariantBernsteinGibbsCorollary.lean` | `tendsto_mul_confocalGibbsFreeEnergy` |
| exact Xi radical chain and recession | `RHTower/ScaleCovariantXiBernsteinAbelCorollary.lean` | `exists_xiScaleCovariantRadical_scale`, `tendsto_mul_xiScaleCovariantGibbsFreeEnergy` |

## Literature boundary

Known parent mechanisms include:

- Hausdorff moment positivity and its RH applications, including Ruiming Zhang,
  [arXiv:2303.09396](https://arxiv.org/abs/2303.09396);
- generic algebraic phase retrieval, including Conca--Edidin--Hering--Vinzant,
  [arXiv:1312.0158](https://arxiv.org/abs/1312.0158);
- classical Bernstein/local-binomial asymptotics and Abelian transfer;
- Connes' trace-formula programme, The Scaling Hamiltonian, Spectral Triples and Zeta-Cycles,
  and Connes--Consani--Moscovici's 2025
  [Zeta Spectral Triples](https://arxiv.org/abs/2511.22755).

The exact combination

```text
one positive scale polynomial
  + global pointed inverse
  + all-p atomic spectrum
  + positive quadratic half-order constant
  + confocal first recession
```

was not located in the targeted comparison. Novelty remains a candidate claim requiring
specialist review.

## RH status

For the pre-aggregated reciprocal-square Xi divisor source, support on `[0,infinity)` is equivalent
to RH. Therefore the exact radical specializes to

```text
RH iff Delta_Xi=0 iff A_Xi(R)=1 iff F_Xi(R)=0
```

for every sufficiently large scale.

Its pointed zeroth moment is the centered curvature

```text
kappa_Xi = Xi_c''(0)/Xi_c(0) > 0,
```

not the distinct endpoint reciprocal moment `2 + gamma_E - log(4pi)`. The positivity is supplied
by the positive theta-kernel representation, and the divisor/source equality is already part of
the formal central-moment bridge.

This does not estimate `Delta_Xi` and is not an RH proof. The scientific theorem is the complete
carrier and recession law, not the final Xi vanishing condition.
