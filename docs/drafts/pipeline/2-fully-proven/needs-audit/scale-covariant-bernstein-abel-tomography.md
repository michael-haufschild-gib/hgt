# Scale-covariant Bernstein--Abel tomography

- **ID:** `scale-covariant-bernstein-abel-tomography`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM CANDIDATE / INVERSE THEOREM / ABEL SELECTION
- **Scientific status:** `[PROVED ON PAPER] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Statement:** The positive scale family of Bernstein coefficient purities is triangularly
  complete for every Schwarz-real moment source; for summable discrete sources its Abel boundary
  simultaneously selects a finite square-root packet and generates a monotone confocal defect
  flow whose renormalized unit-radius gap is the intrinsic transverse source defect.

## Goal

Replace the normalization-dependent endpoint collar by one scale-covariant inverse theorem.  The
same observable must do three jobs without importing a zero-derived positive carrier:

1. recover the complete pointed moment source from its positive purity curves;
2. identify the finite atomic packet which creates any subunit Abel boundary;
3. extract a normalization-free transverse defect from the large-scale boundary flow.

For the reciprocal-square Xi source this gives a genuinely source-bearing positive architecture.
It does not estimate the recovered source and therefore does not prove RH.

## Narrative contract for the paper

The paper is about one scale-covariant mechanism, not several adjacent criteria.  Its logical arc
is:

```text
fixed-scale Abel selection has a normalization ambiguity
    -> retain the full dilation variable
    -> the purity scale polynomial becomes a finite triangular source chart
    -> its Abel boundary selects the exposed atomic packet
    -> the same scale flow has the intrinsic residue 2 Delta
    -> exposed derivatives reconstruct the active transverse orbit.
```

Finite purity tomography therefore explains **what information is retained**, Abel selection
explains **which atoms control the boundary**, and confocal recession explains **which part of the
boundary is invariant under normalization**.  The reciprocal-square Xi source is an application
of this single mechanism.  The old fixed normalization, rational collar constants, finite
Hausdorff rectangle, dissipation hierarchy, and unrelated physical carriers are not headline
components of the new paper.

## Exact finite-degree observation

For a real sequence `m=(m_j)_{j>=0}`, a degree `N`, and inverse scale `x`, put

```text
b_(N,k)^m(x)
  = binom(N,k) sum_(j=0)^(N-k) (-1)^j binom(N-k,j) m_(k+j) x^(k+j),

P_(N,m)(x) = sum_(k=0)^N b_(N,k)^m(x)^2.                 (1)
```

Thus `P_(N,m)` is exactly the purity of the Bernstein coefficient vector of the scaled moment
sequence `j |-> x^j m_j`.  Its constant coefficient is `m_0^2`.  For `1<=r<=N`, its coefficient
of degree `r` is

```text
[x^r] P_(N,m)
 = 2 (-1)^r binom(N,r) m_0 m_r + Q_(N,r)(m_1,...,m_(r-1)),       (2)
```

where `Q_(N,r)` is the explicit finite sum of all terms with positive left and right moment
indices.  In particular, no moment of index larger than `r` occurs in `[x^r]P_(N,m)`, and the only
occurrences of `m_r` are the two displayed cross terms with `m_0`.

### Finite triangular phase retrieval

If `m_0` and `m'_0` are positive, then

```text
P_(N,m) = P_(N,m')  iff  m_j=m'_j for every j<=N.         (3)
```

Without the orientation `m_0>0`, equality determines the prefix up to the unavoidable common
sign.  Equality of the scale curves on any nonempty open interval is enough, because both sides
are polynomials.  Consequently the cofinal family `(P_(N,m))_N` determines the full oriented real
moment sequence.

More strongly, define the low-order purity-jet map

```text
J_N(m_0,...,m_N)=([x^r]P_(N,m))_(0<=r<=N).                 (3a)
```

Then

```text
J_N : (0,infinity) x R^N -> (0,infinity) x R^N            (3b)
```

is a global real-analytic triangular diffeomorphism.  Its inverse starts with
`m_0=sqrt((J_N(m))_0)` and then solves `(2)` successively for `m_r`.  Its Jacobian is

```text
det D J_N(m)
 = (-1)^(N(N+1)/2) (2m_0)^(N+1)
     prod_(r=1)^N binom(N,r),                              (3c)
```

so the source chart has no interior critical locus.  This gives a quantitative local-stability
starting point; no stability bound uniform as `m_0` approaches zero is claimed.

This is the first new theorem target.  It is not generic frame phase retrieval: one scalar
polynomial at degree `N` reconstructs the entire length-`N+1` prefix because the Bernstein
dilation is triangular at infinite radius.

## Discrete source and Abel field

Let `I` be countable and let

```text
mu = sum_(i in I) c_i delta_(z_i)
```

satisfy:

- `sum_i |c_i| < infinity`;
- the coordinate family is bounded and tends to zero cofinally;
- equal coordinates have first been aggregated and every occupied aggregate is nonzero;
- `m_n=sum_i c_i z_i^n` is real for every `n`;
- every occupied real coordinate is nonnegative;
- `m_0>0`.

For a positive radius `R`, write

```text
u_i(R)=z_i/R,
beta_i(R)=|u_i(R)|+|1-u_i(R)|,
B(R)=sup_i beta_i(R),
A(R)=B(R)^(-2).                                           (4)
```

Let `Pi_n(R)=P_(n,m)(1/R)` and

```text
chi_R(t)=sum_(n>=0) Pi_n(R)t^n.                            (5)
```

For every `R>2M` with `B(R)>1`, the supremum in `(4)` is attained on a finite
nonempty coordinate packet.  Distinct occupied maximal coordinates have distinct maximizing
Bernstein ellipse phases: the only other equal-phase possibility is the reflection
`u=1-conj(v)`, excluded once all `|u|<1/2`.  Hence the mixed packet is exponentially gapped.
The standard diagonal identity and the gapped complement then give

```text
Pi_n(R) ~ L(R) B(R)^(2n)/sqrt(n),  L(R)>0,                 (6)

sqrt(1-B(R)^2 t) chi_R(t) -> sqrt(pi)L(R)                  (7)
```

as `n->infinity` and `t` increases to `A(R)`.  The maximal diagonal has the exact finite kernel

```text
sum_(u in U_R) |C_R(u)|^2 /
  (sqrt(1-B(R)^2 t) sqrt(1-D_u(R)^2 t)),                   (8)

D_u(R)=|u|-|1-u|,                                         (9)
```

and the complete remainder vanishes after multiplication by `sqrt(1-B(R)^2t)`.

## Confocal defect flow

Let `M=sup_i |z_i|` and, for `R>M`, define

```text
delta_R(z)=|z|+|R-z|-R,
D(R)=sup_i delta_R(z_i),
Delta=sup_i (|z_i|-Re z_i).                               (10)
```

Then

```text
B(R)=1+D(R)/R.                                            (11)
```

The function `D` is nonnegative and nonincreasing.  More sharply,

```text
Delta <= D(R) <= Delta + M^2/(2(R-M)),                    (12)
```

so `D(R)` decreases to `Delta`.  It follows that the exact Abel radii increase to one and

```text
R(B(R)^2-1) -> 2 Delta,
R(1-A(R))   -> 2 Delta.                                   (13)
```

Thus `Delta` is the normalization-free transverse defect left after the artificial collar has
been removed.

If one conjugacy orbit `{z,conj(z)}`, with `Im z != 0`, uniquely exposes the upper envelope on an
open radius interval, then the active branch

```text
f(R)=R+D(R)=|z|+|R-z|                                    (14)
```

recovers that orbit locally.  With `p=f'(R)`, `q=f''(R)>0`,

```text
s=(1-p^2)/q,
Re z=R-sp,
|Im z|=s sqrt(1-p^2).                                    (15)
```

The boundary coefficient `L(R)` then recovers the squared norm of the aggregated weight of the
exposed orbit after division by the explicit positive row constant.

## Proposed single master theorem

The **scale-covariant Bernstein--Abel tomography theorem** is the conjunction of:

1. finite triangular reconstruction `(2)--(3)`;
   equivalently, the global purity-jet coordinate theorem `(3a)--(3c)`;
2. exact finite square-root selection `(6)--(9)` for every sufficiently large false phase;
3. the monotone confocal defect flow `(10)--(13)`;
4. exposed-orbit reconstruction `(14)--(15)`.

For the reciprocal-square Xi source, the moment orientation is fixed by `m_0>0`, the cofinal
purity field retains the complete normalized prime--Gamma moment sequence, and

```text
RH iff Delta=0
   iff A(R)=1 for every sufficiently large R.              (16)
```

Equation `(16)` is an application of the master theorem, not its scientific content and not an
RH proof.

## Proof plan and dependency audit

1. Expand the Bernstein basis and prove `(1)`.
2. Collect the coefficient of `x^r`.  The degree constraint is `2k+a+b=r`.  If one moment index
   equals `r`, then necessarily `k=0` and `{a,b}={0,r}`; all remaining indices are `<r`.  This
   proves `(2)` and induction proves `(3)`.
3. Use cofinite convergence `z_i->0` to isolate the finite superunit maximal packet.  Aggregate
   equal coordinates before energy formation.
4. Use Bernstein ellipse phase rigidity.  Equal amplitude and equal phase give either equal
   coordinates or `u=1-conj(v)`; the latter is impossible when both norms are `<1/2`.
5. Apply the exact diagonal central-binomial kernel and the strict mixed-mode gap.  Absolute
   summability and a uniform submaximal amplitude control the infinite complement, yielding
   `(6)--(9)`.
6. For `R_2>R_1`, the triangle inequality gives
   `|R_2-z| <= (R_2-R_1)+|R_1-z|`, hence every `delta_R(z)` and then `D(R)` is nonincreasing.
7. Put `z=x+iy`.  Since `R>M`, rationalization gives

   ```text
   0 <= |R-z|-(R-x)
      = y^2/(|R-z|+R-x)
      <= M^2/(2(R-M)).                                    (17)
   ```

   Taking suprema proves `(12)`, and elementary algebra proves `(13)`.
8. Differentiate `(14)` on an exposed interval.  If
   `s=|R-z|`, then `p=(R-Re z)/s` and `q=(Im z)^2/s^3`.
   Hence `1-p^2=(Im z)^2/s^2=sq`, proving `(15)`.

## Hostile attacks

1. **Sign ambiguity.**  Purity is invariant under `m |-> -m`.  The theorem must state projective
   sign recovery unless `m_0>0` is part of the pointed source.
2. **Complex moments.**  Positive real scale alone does not recover arbitrary complex phases.
   The main theorem is restricted to Schwarz-real moments.  A complex phase-dilation extension is
   a possible strengthening, not a paper claim yet.
3. **Moment indeterminacy.**  Recovering all holomorphic moments need not recover an arbitrary
   global measure.  The theorem claims the moment source; atomic divisor recovery is claimed only
   for exposed branches, unless an independent determinacy/meromorphic-continuation hypothesis is
   added.
4. **Reflection collision.**  A general equal-amplitude packet can contain reflected equal-phase
   coordinates.  The theorem uses the large-radius regime `R>2M`, where this collision is
   impossible.
5. **Tied maxima.**  Formula `(15)` applies only on an interval with one exposed conjugacy orbit.
   Isolated ties and permanently hidden atoms are not reconstructed by the boundary envelope.
6. **Weight overclaim.**  Purity loses phase.  The boundary coefficient recovers an aggregate
   squared weight norm, not arbitrary individual complex weights.
7. **Normalization artifact.**  The raw collar still narrows as `R` grows.  Only the renormalized
   limit `Delta` and the complete scale field are claimed invariant.
8. **RH overclaim.**  The theorem recovers the Xi moment carrier and measures its transverse
   defect.  It supplies no unconditional estimate forcing that defect to vanish.

## Internal parent results already complete

- `PrimeArchBernsteinNormalizationDependence.lean` proves that one fixed collar is not intrinsic.
- `FiniteBernsteinCoordinatePacketAsymptotic.lean` proves finite gapped-packet half-order
  asymptotics.
- `FiniteBernsteinDiagonalSquareRootDecomposition.lean` proves the exact diagonal kernel.
- `XiBernsteinPuritySquareRootDecomposition.lean` proves the fixed endpoint Xi decomposition.
- `PrimeArchBernsteinAbelSharpSelectionMaster.lean` proves the old fixed-scale sharp selection.

The new work is the triangular inverse theorem, the scale-covariant confocal flow, exposed-orbit
inverse geometry, and their exact coupling to the already proved Abel selector.

## Preliminary external parent audit

- Generic finite-dimensional phase retrieval reconstructs vectors from intensity frames and has
  algebraic injectivity criteria (Conca--Edidin--Hering--Vinzant).  It does not state the
  triangular Bernstein dilation identity `(2)`.
- Binomial transforms and Bernstein coefficient identities are classical.
- Prony reconstruction and finite atomic moment inversion are classical and are not claimed here.
- Square-root transfer from `n^(-1/2)` coefficients is standard singularity analysis.
- Searches through 2026-07-18 did not locate the exact combination of a scalar Bernstein-purity
  scale polynomial, cofinal moment reconstruction, confocal Abel defect flow, and exposed-atom
  boundary inversion.  This is not a novelty proof; specialist audit remains required.

## Gates

- [x] 0 -> 1: source-pure statement, exact attack list, internal parent map
- [ ] complete primary-literature comparison and specialist novelty audit
- [x] close the general mixed-packet and infinite-complement paper proof
- [x] prove the triangular inverse theorem on paper
- [x] prove the confocal monotonicity, uniform limit, and exposed-orbit inverse on paper
- [x] hostile counterexample pass against every quantifier
- [x] 1 -> 2: dependency-closed paper proof and honest novelty classification
- [ ] formalize the exact theorem in Lean without new axioms
- [ ] targeted leaf build and ordinary-axiom audit
- [ ] replace the old manuscript by one single-master-theorem paper
- [ ] render the PDF and perform a journal-referee audit

### Formalization ledger (2026-07-18)

- `ScaleCovariantBernsteinPurityJet.lean`: exact scale polynomial, literal purity evaluation,
  antidiagonal coefficient law, corrected `r=0` base, pointed jet injectivity, and open-interval
  tomography.  **Leaf check passed.**
- `ConfocalAbelDefectFlow.lean`: pointwise amplitude identity, monotonicity, sharp collar,
  supremal flow, convergence to `Delta`, and both first-order recession laws.  **Leaf check passed
  through the recession theorems.**  Exact unit-boundary selection was added after the shared
  compiler freeze and awaits the next compiler lease.
- `ConfocalExposedOrbitTomography.lean`: derivative and reconstruction source has been written.
  **Awaiting verification after the shared compiler freeze.**
- Still missing: the explicit global inverse/analytic-chart theorem and its actual Jacobian
  determinant; the generic atomic master wrapper connecting the existing finite-packet Abel
  theorems to the new scale flow; the reciprocal-square Xi specialization; final ordinary-axioms
  audit and umbrella/index wiring.

## Log

- 2026-07-18 -- created in Stage 1 after the old fixed-normalization manuscript failed novelty
  review.  The target was strengthened from exposed-envelope recovery alone to complete
  scale-purity moment tomography plus a monotone normalization-free Abel defect flow.

## Complete paper proof

The proof below fixes the quantifiers used by the master theorem.  Replace the original index set
by the set of occupied coordinate fibres, and replace the weights on each fibre by their sum.
Thus the coordinate map is injective and every weight is nonzero.  This changes neither the moments
nor any Bernstein coefficient.

### Lemma 1 (scaled Bernstein expansion)

For `0<=k<=N`, expansion of `X^k(1-X)^(N-k)` gives

```text
b_(N,k)^m(x)
 = binom(N,k) sum_(j=0)^(N-k)
     (-1)^j binom(N-k,j)m_(k+j)x^(k+j).
```

**Proof.**  Apply the moment functional of the scaled sequence `j |-> x^j m_j` to
`binom(N,k)X^k(1-X)^(N-k)` and use the binomial theorem.  Terms with `k>N` are absent.  This is
exactly `(1)`.  `square`

### Lemma 2 (triangular purity coefficient)

For `0<=r<=N`, the full coefficient formula is

```text
[x^r]P_(N,m)
 = (-1)^r sum_{
       0<=k<=N, 0<=a,b<=N-k, 2k+a+b=r}
     binom(N,k)^2 binom(N-k,a)binom(N-k,b)
     m_(k+a)m_(k+b).                                      (18)
```

The constant coefficient is `m_0^2`.  For `r>0`, the only summands in `(18)` containing `m_r`
are the distinct terms `(k,a,b)=(0,r,0)` and `(0,0,r)`.

**Proof.**  The constant term comes only from `k=a=b=0` and is `m_0^2`.  For positive `r`,
multiply the two finite sums in Lemma 1.  A term indexed by `(k,a,b)` has degree
`(k+a)+(k+b)=2k+a+b` and sign `(-1)^(a+b)=(-1)^r`.  If `k+a=r`, the degree equation gives
`k+b=0`, hence `k=b=0` and `a=r`; the other case is symmetric.  Every remaining moment index is
strictly smaller than `r`.  Separating the two exceptional terms proves `(2)`.  `square`

### Theorem 3 (global purity-jet coordinates)

For every `N`, the map `J_N` in `(3a)` is a real-analytic diffeomorphism from
`(0,infinity) x R^N` onto itself, with Jacobian `(3c)`.  On the domain `m_0!=0` without a chosen
orientation, the full purity polynomial determines `m` up to common sign.

**Proof.**  The zeroth output is `m_0^2`, so on the pointed chamber its unique inverse is
`m_0=sqrt(y_0)`.  Suppose `m_0,...,m_(r-1)` have been recovered.  Lemma 2 writes

```text
y_r=2(-1)^r binom(N,r)m_0m_r+Q_(N,r)(m_1,...,m_(r-1)),
```

and its displayed coefficient of `m_r` is nonzero.  This uniquely and analytically recovers
`m_r`.  The same recursion constructs a preimage for every `(y_0,...,y_N)` with `y_0>0`, proving
global bijectivity and analyticity of the inverse.

The Jacobian is lower triangular.  Its diagonal is `2m_0` in degree zero and
`2(-1)^r binom(N,r)m_0` in degree `r>=1`.  Multiplication gives `(3c)`.  If orientation is not
fixed, the zeroth coefficient gives `|m'_0|=|m_0|`; multiply one source by the resulting common
sign and apply the pointed theorem.  Equality on an open scale interval implies equality of the
two finite polynomials, hence equality of their coefficient jets.  `square`

### Lemma 4 (finite maximal packet)

Assume the discrete-source hypotheses and fix `R>2M`.  If `B(R)>1`, there are a finite nonempty
coordinate set `U_R`, a number `beta` with `1<beta<B(R)`, and aggregated weights `C_R(u)!=0` such
that

```text
|u|+|1-u|=B(R)  for u in U_R,
|u|+|1-u|<=beta for every occupied u outside U_R.          (19)
```

**Proof.**  Since `z_i->0` cofinally, `u_i=z_i/R->0`, so the amplitudes tend cofinally to one.
Choose one amplitude strictly larger than one.  Above its value only finitely many coordinates
occur; the supremum is therefore the maximum of a nonempty finite set.  The complement is the
union of a finite strictly submaximal set and a cofinite tail lying below `(1+B(R))/2`.  Taking the
larger of those two strict bounds gives `beta`.  `square`

### Lemma 5 (strict mixed-mode separation at large scale)

Distinct points of `U_R` have distinct maximizing Bernstein ellipse phases.  Consequently, for
each distinct `u,v in U_R` there is `gamma_(u,v)<B(R)^2` such that the reflected cross moment is
bounded by `gamma_(u,v)^n`.

**Proof.**  A real occupied coordinate is nonnegative by hypothesis.  Because `R>M`, such a
coordinate lies in `[0,1]` after normalization and has amplitude one; hence every member of the
superunit packet is nonreal.  Bernstein ellipse rigidity says that two nonreal coordinates of
equal amplitude and equal maximizing phase obey either `u=v` or `u=1-conj(v)`.  The second
alternative contradicts `|u|,|v|<1/2`, because then
`|1-conj(v)|>=1-|v|>1/2`.  Thus distinct coordinates have distinct phases.

At every unit-circle point the norm of their reflected product is at most `B(R)^2`, and equality
would force both individual affine modes to attain their maxima at that same phase.  This has just
been excluded.  Continuity and compactness of the unit circle give a uniform strict maximum
`gamma_(u,v)<B(R)^2`.  The normalized circle-integral formula for the cross moment transfers the
pointwise bound to `gamma_(u,v)^n`.  `square`

### Theorem 6 (finite square-root Abel selection)

Under the hypotheses of Lemma 4,

```text
sqrt(n) Pi_n(R)/B(R)^(2n) -> L(R)>0,                       (20)
```

the exact Abel radius is `A(R)=B(R)^(-2)`, and `(7)--(9)` hold.

**Proof.**  Write the degree-`n` coefficient vector as `d_n+r_n`, where `d_n` is the finite
packet from `U_R` and `r_n` is its complement.  Polarized Parseval expands the energy of `d_n`
into diagonal and mixed reflected moments.  The diagonal row at `u` satisfies

```text
sqrt(n) E_n(u)/B(R)^(2n) -> c(u)>0,
```

with the explicit constant `c(u)=bernsteinAffineRowHalfOrderConstant(u)`.  Lemma 5 makes every
mixed term exponentially smaller.  Therefore

```text
sqrt(n)||d_n||_2^2/B(R)^(2n)
 -> sum_(u in U_R)|C_R(u)|^2c(u)=L(R)>0.                  (21)
```

Let `W=sum_i|c_i|`.  Formula `(19)` bounds the complement's circle transform pointwise by
`W beta^n`.  Parseval gives `||r_n||_2^2<=W^2 beta^(2n)`.  Cauchy--Schwarz bounds the cross energy
between `d_n` and `r_n` by their norm product.  After multiplication by
`sqrt(n)/B(R)^(2n)`, both the complement energy and the cross energy tend to zero because
`beta/B(R)<1`.  This proves `(20)` for the complete source.

The nonnegative coefficients and `(20)` give exact exponential exponent `B(R)^2` and therefore
the exact power-series radius `A(R)`.  The classical central-binomial identity gives the diagonal
generating function `(8)`.  Abel transfer of `(20)` gives `(7)`.  The diagonal has the same limit
by `(21)`, so their difference, the complete remainder, vanishes at the square-root scale.  All
series converge absolutely at interior points by the strict exponential bound.  `square`

### Lemma 7 (the unit phase)

If `B(R)=1`, then the exact purity exponent is one and the exact Abel radius is one.

**Proof.**  Every occupied normalized coordinate lies on `[0,1]`, so every affine row has unit
amplitude.  Absolute summability gives an exponential upper bound with every base larger than one.
On the other hand the Bernstein coefficients sum to `m_0`; Cauchy--Schwarz gives

```text
Pi_n(R)>=m_0^2/(n+1).
```

Since `m_0>0`, the lower exponential exponent is one.  `square`

### Theorem 8 (monotone confocal defect flow)

For `R>M`, equations `(11)--(13)` hold, `D(R)` is nonnegative and nonincreasing, `B(R)` is
nonincreasing, and `A(R)` is nondecreasing to one.

**Proof.**  Multiplying the amplitude by `R` gives

```text
R beta_i(R)=|z_i|+|R-z_i|=R+delta_R(z_i),
```

and taking suprema proves `(11)`.  The reverse triangle inequality gives
`|R-z|>=R-Re z`, hence

```text
delta_R(z)>=|z|-Re z>=0.
```

For `R_2>R_1`, the triangle inequality gives

```text
|R_2-z|<=R_2-R_1+|R_1-z|,
```

so `delta_(R_2)(z)<=delta_(R_1)(z)` and the supremum is nonincreasing.

Write `z=x+iy`.  Since `R>M`, both terms in the denominator below are positive, and

```text
delta_R(z)-(|z|-x)
 = |R-z|-(R-x)
 = y^2/(|R-z|+R-x).
```

The numerator is at most `M^2`; each denominator summand is at least `R-M`.  This proves the
uniform bound `(12)` after taking suprema.  Hence `D(R)->Delta`.

Because `D` is nonnegative and nonincreasing, so is `D(R)/R`; `(11)` makes `B` nonincreasing and
`A=B^(-2)` nondecreasing.  Finally

```text
R(B^2-1)=2D+D^2/R,

R(1-A)=(2D+D^2/R)/(1+D/R)^2.
```

The bounded convergence `D(R)->Delta` proves both limits in `(13)`.  `square`

### Theorem 9 (exposed-orbit inversion)

Assume one nonreal conjugacy orbit is the unique maximizing orbit throughout an open interval.
Then `(14)--(15)` recover that orbit, and the leading Abel coefficient recovers its aggregate
squared weight norm.

**Proof.**  On the interval the supremum is the single smooth branch
`f(R)=|z|+sqrt((R-x)^2+y^2)`, where `z=x+iy` and `y!=0`.  Put
`s=sqrt((R-x)^2+y^2)`.  Direct differentiation gives

```text
p=(R-x)/s,  q=y^2/s^3.
```

Thus `1-p^2=y^2/s^2=sq`, proving `(15)`.  Conjugation is the only remaining ambiguity.  In the
square-root coefficient `(21)`, conjugate coordinates have the same known row constant.  Division
by that constant recovers the sum of the squared norms of their nonzero aggregate weights.
`square`

### Corollary 10 (reciprocal-square Xi source)

The reciprocal-square Xi divisor source satisfies all hypotheses after equal coordinates are
aggregated.  Its pointed scale-purity field determines every normalized prime--archimedean moment,
and `(16)` holds.

**Proof.**  The reciprocal-square weights are absolutely summable and tend cofinally to zero; the
moments are real by functional-equation and Schwarz symmetry; equal-coordinate fibres add copies
of the same nonzero reciprocal-square weight; and the zeroth moment is positive.  A real
reciprocal-square coordinate occurs exactly for a critical-line zero and is then positive.
Therefore Theorems 3, 6, 7, and 8 apply.

The intrinsic defect vanishes exactly when every reciprocal-square coordinate is positive real,
which is equivalent to every Xi zero lying on the critical line.  If it vanishes, `B(R)=1` for all
`R>M`; if it is positive, `(12)` and the pointwise strict triangle inequality give `B(R)>1` for
every `R>M`.  Hence `(16)`.  `square`

## Paper-proof status after hostile pass

- The finite purity-jet theorem is dependency-closed.
- The atomic selection theorem explicitly aggregates fibres, excludes the reflected phase
  collision by `R>2M`, and controls the complete infinite complement.
- The defect flow has an exact uniform error bound, not only a pointwise limit.
- The exposed inverse is orbitwise and recovers only the weight norm visible to purity.
- The Xi corollary is an equivalence/reconstruction statement, not a vanishing estimate.

The theorem is now `[PROVED ON PAPER] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`.  It is ready for an
independent literature/specialist audit and exact Lean formalization; it is not yet eligible for
Stage 2 because the novelty classification has not been independently closed.

## Focused primary-literature comparison (2026-07-18)

1. Conca--Edidin--Hering--Vinzant, *An algebraic characterization of injectivity in phase
   retrieval*, ACHA 38 (2015), 346--356, studies recovery of a complex vector up to phase from
   generic frame intensities and proves the `4M-4` generic complex bound.  It does not use a
   Bernstein dilation, a scalar purity polynomial, or the triangular coefficient chart `(3a)`.
2. Chen--Cheng--Sun, *Phase retrieval of complex and vector-valued functions*, develops phase
   retrieval from norms of vector-valued linear measurements and characterizes the associated
   trivial ambiguities.  This is the closest general parent for interpreting purity as norm data.
   It does not state the global Bernstein purity-jet diffeomorphism or the confocal Abel flow.
3. Classical binomial-transform and Bernstein-basis theory supplies Lemma 1.  Classical phase
   retrieval supplies the surrounding inverse-problem language.  Neither parent contains the
   coefficient isolation in Lemma 2 as an identified global chart on moment space.
4. Ruiming Zhang, *An Application of Hausdorff Moment Problem* (arXiv:2303.09396), derives
   Hausdorff-moment positivity criteria for root location and RH-type equivalences.  It is direct
   prior art for the fixed-sign/Hausdorff lane, but not for scale-purity inversion, half-order Abel
   singularity selection, or the normalization-free defect flow.
5. The central-binomial square-root transfer and finite dominant-mode singularity analysis used in
   Theorem 6 are classical analytic-combinatorics parents.  No novelty is assigned to those steps
   in isolation.
6. Connes--Consani--Moscovici, *Zeta Spectral Triples* (arXiv:2511.22755), constructs finite
   self-adjoint prime-cutoff operators and reports numerical spectral and determinant convergence;
   rigorous convergence of the normalized determinants to Xi remains the proposed RH-bearing
   step.  The present theorem supplies an independent source-observability statement and makes no
   claim that a Connes construction must realize this particular observable.
7. Focused searches for inverse upper envelopes of confocal distance-sum curves, Bernstein
   coefficient norm phase retrieval, binomial-transform purity inversion, and moment recovery from
   scale-dependent Bernstein energies did not locate Theorem 3, Theorem 8, or their conjunction.
   Search failure is evidence for a candidate, not proof of priority.

**Novelty verdict.**  The square-root singularity analysis and phase-retrieval framing are
`[PARENT/BRIDGE]`.  The exact global purity-jet coordinate theorem, its explicit nowhere-zero
Jacobian, and its coupling to the monotone confocal Abel defect flow remain
`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [SPECIALIST AUDIT REQUIRED]`.
