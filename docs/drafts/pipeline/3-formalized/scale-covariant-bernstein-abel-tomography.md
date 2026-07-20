# Scale-covariant Bernstein--Abel tomography

- **ID:** `scale-covariant-bernstein-abel-tomography`
- **Stage:** 3-formalized
- **Type:** MASTER THEOREM / INVERSE THEOREM / ABEL SELECTION
- **Scientific status:** `[PROVED] [FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Paper:** [main.tex](../4-publication-ready/prime-arch-abel-susceptibility-selection/main.tex)
- **PDF:** [main.pdf](../4-publication-ready/prime-arch-abel-susceptibility-selection/main.pdf)

## Headline theorem

One locally observed scale-covariant positive field is simultaneously:

1. source-faithful on every nonempty open scale-coordinate interval;
2. exactly equal to the square energy of its atomic Bernstein packet;
3. spectrally complete for every real packet exponent `p > 0`;
4. sharply square-root singular in the quadratic case;
5. exactly selective for an intrinsic radical/transverse moment-fibre stratum;
6. presentation-rigid at the full confocal field and first recession;
7. reconstructive on every stably exposed conjugation orbit.

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

with `sum_i |c_i| < infinity`, bounded nodes, cofinally vanishing transverse defect
`|z_i|-Re z_i`, `m_0 > 0`, and every occupied real node nonnegative. Repeated nodes, zero fibres,
and fibrewise cancellations are removed by canonical aggregation.

Put

```text
u_i(R) = z_i/R,
B(R) = sup_i (|u_i(R)| + |1-u_i(R)|),
A(R) = B(R)^(-2),
Delta = sup_i (|z_i| - Re z_i).
```

Then the formal master theorem `scaleCovariantBernsteinAbel_tomography` proves all of the
following.

### 1. Local scale-germ and global pointed source chart

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

Therefore the cofinal family `(P_(N,m))_N` recovers the complete pointed moment sequence. More
strongly, equality of all `P_(N,m)` and `P_(N,m')` on any one nonempty open interval already
forces `m=m'`.

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

If `R > M` and some node is nonreal, the maximal amplitude `B(R)>1` is attained on a nonempty
finite packet. Every complementary amplitude is bounded by one common `beta(R)<B(R)`.

For every real `p > 0`, if

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

### 6. Complete admissible-fibre classification

For two arbitrary raw presentations of the same pointed moments, canonical aggregation produces
intrinsic supports `S,S'` satisfying

```text
S has a nonreal node iff S' has a nonreal node,
B_S(R)=B_S'(R) for every common exterior scale,
Delta_S=Delta_S'.
```

In the transverse stratum their positive half-order coefficient is common. If nodes `u in S` and
`u' in S'` expose the common confocal field on a nonempty radius interval, then

```text
Re u = Re u',
|Im u| = |Im u'|.
```

Thus the common positive field reconstructs every stably exposed atom up to the unavoidable
conjugation symmetry.

### 7. Gibbs corollary

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
- every real `p>0` has exact nth-root spectrum `B^p`;
- any nonempty open scale-coordinate interval is source-faithful;
- the radical/transverse stratum and full confocal field are presentation-invariant;
- stable exposed confocal branches reconstruct conjugation orbits;
- the source-side object and atomic weights are displayed explicitly;
- no Connes architecture is claimed to be forced to realize this particular observable.

## Formal theorem ledger

All listed theorem leaves pass the project toolchain directly. The master theorem, Gibbs
corollaries, and dedicated Xi radical capstone depend only on the ordinary logical axioms
`propext`, `Classical.choice`, and `Quot.sound`.

| Mathematical component | Module | Principal theorem |
|---|---|---|
| triangular coefficient law | `RHTower/ScaleCovariantBernsteinPurityJet.lean` | `coeff_bernsteinScalePurityPolynomial_eq_leading_add_lower` |
| local interval source faithfulness | `RHTower/ScaleCovariantBernsteinPresentationRigidity.lean` | `bernsteinScalePurityPolynomial_interval_source_faithful` |
| explicit global inverse | `RHTower/ScaleCovariantBernsteinPurityChart.lean` | `bernsteinPurityJet_global_pointed_chart` |
| Jacobian and determinant | `RHTower/ScaleCovariantBernsteinPurityJacobian.lean` | `det_bernsteinPurityJetJacobian_ne_zero` |
| atomic observation bridge | `RHTower/ScaleCovariantBernsteinAtomicObservation.lean` | `scaleCovariantBernsteinObservation_eq_atomicPacketSquareEnergy` |
| generic finite selection | `RHTower/ScaleCovariantBernsteinAtomicSelection.lean` | `exists_positive_halfOrder_atomicBernsteinPacket_of_small_source` |
| inverse-scale confocal selection | `RHTower/ScaleCovariantBernsteinInverseScaleSelection.lean` | `exists_positive_halfOrder_inverseScaleAtomicPacket` |
| all real-p spectra | `RHTower/ScaleCovariantBernsteinRpowSpectrum.lean` | `exists_tendsto_inverseScaleAtomicBernsteinRpowEnergy` |
| confocal recession | `HTGeometry/ConfocalAbelDefectFlow.lean` | `tendsto_mul_one_sub_confocalAbelRadius` |
| single bundled master theorem | `RHTower/ScaleCovariantBernsteinAbelTomography.lean` | `scaleCovariantBernsteinAbel_tomography` |
| radical/transverse moment-fibre classification | `RHTower/ScaleCovariantBernsteinPresentationRigidity.lean` | `aggregatePresentationFullRigidity_of_common_pointed_moments` |
| exposed branch inverse | `RHTower/ScaleCovariantBernsteinPresentationRigidity.lean` | `exposed_confocal_orbit_eq_of_common_pointed_moments` |
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
one positive field on any open scale interval
  + global pointed inverse
  + all-p atomic spectrum
  + positive quadratic half-order constant
  + intrinsic radical/transverse presentation stratum
  + exposed-orbit inverse
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

## 2026-07-20 publication strengthening: projective bicompletion

The publication theorem is strengthened without adding a second route.  Its analytic completion is
now the exact signed divided-power root

```text
F_(N,m)(T)=sum_(r=0)^N binom(N,r)m_r T^r/r!,
D_N(P)(T)=sum_r (-1)^r [X^r]P T^r/r!,
D_N(P_(N,m))=F_(N,m)^2.
```

The pointed condition `m_0>0` selects the root.  On the chamber

```text
m_0,m'_0 >= mu>0,
||m||_(N,tau),tail, ||m'||_(N,tau),tail <= theta mu,
theta<1,
```

it satisfies the degree-independent stability law

```text
|F_(N,m)(T)-F_(N,m')(T)|
 <= |F_(N,m)(T)^2-F_(N,m')(T)^2|/[2(1-theta)mu]
```

for `|T|<=tau`.

The geometric completion is the maximal Lorentz hull of the common exterior confocal field.  It
admits an exact projective description.  For a source-radius bound `M`, a radius domain `D subset
(M,infinity)`, a nonnegative defect field `d(R)`, Lorentz null coordinates

```text
u(q)=a-x,
v(q)=a+x,
lambda_R(d)=d/(2R+d),
ell_lambda(q)=u(q)+lambda v(q),
```

one has the dependency-closed identity

```text
H_D(R |-> R+d(R)) intersect {a<=M}
 = {q in C : a<=M and
      ell_(lambda_R(d(R)))(q)<=d(R) for every R in D}.       (PB)
```

Indeed `a<=M<R` makes the pointwise projective equivalence

```text
g_R(q)<=R+d iff ell_(lambda_R(d))(q)<=d
```

applicable at every radius, and intersection gives `(PB)`.

For a realized bounded source `S`, put `G_S(R)=sup_(q in S)g_R(q)` and
`D_S(R)=G_S(R)-R`.  The already proved null-support theorem then gives

```text
D_S(R)=h_S(lambda_R(D_S(R))),
```

where `h_S(lambda)=sup_(q in S)ell_lambda(q)`.  This is the unique nonnegative fixed point of
`Phi_(S,R)(d)=h_S(lambda_R(d))`; the operator has the optimal contraction modulus `M/R`, and
support-field perturbation by `epsilon` changes the defect by at most
`epsilon/(1-M/R)`.  Thus the maximal hull is not merely an abstract quotient: its defining
half-spaces are generated by a sharp one-dimensional support dynamics.

Combining the existing local-field bicompletion equivalence with `(PB)` gives the strengthened
single-observable law:

```text
local equality of the positive scale fields
  iff
complete pointed sources agree
  and
maximal bounded projective confocal hulls agree.
```

The all-real-`p` spectrum and square-root Abel boundary remain the spectral selection face of this
same bicompletion.  This closes both manuscript questions that were actually answerable from the
current corpus: analytic inversion has a degree-uniform weighted stability chamber, and geometric
identifiability ends exactly at the maximal hull/exposed-face boundary.  The only remaining scope
question is enlargement of the admissible presentation class itself.

**Paper-proof status:** `[PAPER-PROVED]`.  The divided-power, maximal-hull, fixed-point,
contraction, sharpness, stability, and dimension-free components are already `[LEAN-PROVED]`.
Only the exact bound-aware projective-hull connector `(PB)` remains to be added as a named Lean
corollary before the manuscript rewrite is called complete.

**Formal closure (2026-07-20).**  The bound-aware connector `(PB)` and direct complex-source
specialization are now `[LEAN-PROVED]` in
`HTGeometry/ConfocalNullSupportFixedPoint.lean`:

- `mem_confocalHullOfField_add_defect_iff_nullFunctional_le`;
- `confocalHullOfField_inter_snd_le_eq_projectiveNullHalfspaces`;
- `complexConfocalDefectEnvelope_eq_iff_nullSupport_fixedPoint`.

The edited leaf passes `lake env lean` with no errors.  No aggregate build was run.

## Global duality upgrade (2026-07-20)

The manuscript's geometric branch is now stronger than the projective fixed-point formulation.
For every nonradical bounded Lorentz source, the entire exterior defect graph is exactly the
rational projective image of the admissible null-support graph:

```text
{(R,D_S(R)):R>M}
 = {(h_S(lambda)(1-lambda)/(2lambda),h_S(lambda)):
      0<lambda<1 and h_S(lambda)(1-lambda)/(2lambda)>M}.
```

The radius map is injective on this domain, with inverse
`lambda=D_S(R)/(2R+D_S(R))`.  The complementary radical graph is exactly `{(R,0):R>M}`.
For two presentations of the same exterior field, the selected support trace is therefore common
at every exterior radius, even when unused parts of their raw support functions differ.

This makes the paper's single narrative:

```text
local positive scale field
  -> unique pointed divided-power root
  -> intrinsic exterior confocal field
  <-> admissible null-support graph by a bijective projective chart
  -> maximal Lorentz hull and exposed-face quotient
  -> all-p spectrum and square-root Abel boundary.
```

Every new equality and inverse assertion is unconditional and formalized in
`HTGeometry/ConfocalNullSupportFixedPoint.lean`; the exact leaf check passes.  No broad build was
run.
