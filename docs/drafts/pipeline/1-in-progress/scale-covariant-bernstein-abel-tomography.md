# Scale-covariant Bernstein--Abel tomography

- **ID:** `scale-covariant-bernstein-abel-tomography`
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE / INVERSE THEOREM / ABEL SELECTION
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
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

## Exact finite-degree observation

For a real sequence `m=(m_j)_{j>=0}`, a degree `N`, and inverse scale `x`, put

```text
b_(N,k)^m(x)
  = binom(N,k) sum_(j=0)^(N-k) (-1)^j binom(N-k,j) m_(k+j) x^(k+j),

P_(N,m)(x) = sum_(k=0)^N b_(N,k)^m(x)^2.                 (1)
```

Thus `P_(N,m)` is exactly the purity of the Bernstein coefficient vector of the scaled moment
sequence `j |-> x^j m_j`.  Its coefficient of degree `r<=N` is

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

For every sufficiently large `R` with `B(R)>1`, the supremum in `(4)` is attained on a finite
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
- [ ] close the general mixed-packet and infinite-complement paper proof
- [ ] prove the triangular inverse theorem on paper
- [ ] prove the confocal monotonicity, uniform limit, and exposed-orbit inverse on paper
- [ ] hostile counterexample pass against every quantifier
- [ ] 1 -> 2: dependency-closed paper proof and honest novelty classification
- [ ] formalize the exact theorem in Lean without new axioms
- [ ] targeted leaf build and ordinary-axiom audit
- [ ] replace the old manuscript by one single-master-theorem paper
- [ ] render the PDF and perform a journal-referee audit

## Log

- 2026-07-18 -- created in Stage 1 after the old fixed-normalization manuscript failed novelty
  review.  The target was strengthened from exposed-envelope recovery alone to complete
  scale-purity moment tomography plus a monotone normalization-free Abel defect flow.
