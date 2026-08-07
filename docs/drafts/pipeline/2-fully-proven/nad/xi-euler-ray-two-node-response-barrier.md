# Xi Euler-Ray Two-Node Response Barrier

- **ID:** `xi-euler-ray-two-node-response-barrier`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / positive survivor of the signed-Jordan-mass no-go
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[INTERNAL NOVELTY AUDITED] [EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** the squared centered Xi canonical product; the open critical strip; the
  source-derived zero-height gap; the infinitesimal real Euler-ray index law
- **Lean targets:** `RHTower/XiSquaredEulerRayTwoPointPositivity.lean`,
  `RHTower/XiSquaredEulerRayFullResponse.lean`, and
  `RHTower/XiSquaredEulerRayCubicAmplification.lean`

## Headline theorem

Put

```text
X(z) = xi(1/2+z),
Q(x) = X'(x)/X(x),
J(x,y) = (Q(x)+Q(y))/(x+y),       x,y>0.                (1)
```

Then, unconditionally,

```text
x |-> Q(x)/x  is strictly decreasing,
x |-> x*Q(x)  is strictly increasing,                 (2)
```

and for every `0<x<y`,

```text
det [[J(x,x),J(x,y)],[J(y,x),J(y,y)]] > 0.             (3)
```

In particular every one-node and every two-node matrix of the infinitesimal real Euler-ray
kernel is positive definite.  Combined with the exact negative-index law for `J`, this implies:

```text
not RH  ->  the least negative Euler-response detector has at least three nodes. (4)
```

This lower bound is sharp for each individual transverse orbit.  If `c>0`, then the response
kernel of that one orbit has negative determinant on **every** three distinct positive nodes.
Thus its minimal detector cardinality is exactly three.

Thus the signed boundary decomposition does have an unconditional response-correlation
cancellation, but only through detector order two.  The open RH content starts at a genuinely
three-node correlation; no one-node or two-node control of the Jordan pieces can reach it.

## 1. One squared-zero orbit

Let `rho=sigma+i*gamma` be a Xi zero and write

```text
delta = sigma-1/2,
t = gamma^2-delta^2,
c = 4*delta^2*gamma^2.                                  (5)
```

The critical strip gives `delta^2<1/4`.  The unconditional source height theorem gives
`gamma^2>41/2`.  Hence

```text
t>0,  c>=0,  c<t^2.                                     (6)
```

Indeed `4*delta^2<1`, so `c<gamma^2=t+delta^2<t+1/4`, while `t>20`; therefore `c<t^2`.

The conjugate pair of squared centered zeros contributes, up to its positive multiplicity, the
real response atom

```text
H_(t,c)(u) = (t+u)/((t+u)^2+c),       u>=0.              (7)
```

For `0<=u<v`, direct denominator clearing gives

```text
H(u)-H(v)
 = (v-u)*((t+u)*(t+v)-c)
   / ((((t+u)^2+c)*((t+v)^2+c))) > 0,                  (8)
```

because `(t+u)*(t+v)>t^2>c`.  A second exact identity is

```text
v*H(v)-u*H(u)
 = (v-u)*(t*(t+u)*(t+v)+c*(t+u+v))
   / ((((t+u)^2+c)*((t+v)^2+c))) > 0.                  (9)
```

Therefore every orbit atom is strictly decreasing, while its radial multiple `u*H(u)` is
strictly increasing.

## 2. Assembly over the Xi divisor

The even entire function `X` has the genus-zero product in the squared variable.  Pairing a
squared zero with its complex conjugate gives the locally uniformly and absolutely convergent
expansion

```text
G(u) := Q(sqrt(u))/sqrt(u)
      = sum_orbits 2*m_orbit*H_(t,c)(u),      u>0.       (10)
```

The summands and multiplicities are positive.  Xi has zeros, so the sum is nonempty.  Equations
`(8)` and `(9)` pass through the absolutely convergent sum and yield

```text
G(u)>G(v)>0,
u*G(u)<v*G(v),                         0<u<v.            (11)
```

Putting `u=x^2`, `v=y^2` proves `(2)` because

```text
Q(x)/x = G(x^2),
x*Q(x) = x^2*G(x^2).                                   (12)
```

No RH hypothesis occurs: the transverse squared-zero charge `c` may be nonzero.  The only
geometric input is the unconditional chamber `c<t^2`.

## 3. Exact response-correlation factorization

Write `A=Q(x)` and `B=Q(y)`.  Clearing the positive denominator `x*y*(x+y)^2` gives the identity

```text
J(x,x)*J(y,y)-J(x,y)^2
 = ((y*A-x*B)*(y*B-x*A)) / (x*y*(x+y)^2).               (13)
```

The first factor is positive by the first monotonicity in `(2)`:

```text
y*A-x*B = x*y*(Q(x)/x-Q(y)/y) > 0.                      (14)
```

The second is positive by the second monotonicity:

```text
y*B-x*A = y*Q(y)-x*Q(x) > 0.                            (15)
```

Equations `(13)`--`(15)` prove `(3)`.

This is the precise positive statement left by the signed-Jordan no-go.  The individual
off-line quartet has a positive-minus-negative Krein decomposition, but its negative coordinate
cannot dominate on one or two real Euler nodes.  The response correlation cancels it exactly
through order two.  At three nodes the determinant has a new independent degree of freedom, so
the cancellation no longer follows from the two radial monotonicities.

## 4. Minimal detector order

The existing infinitesimal Euler-ray index law states

```text
ind_-(J) = total multiplicity of Xi zeros with Re(rho)>1/2. (16)
```

If RH fails, `(16)` produces a finite principal matrix with a negative direction.  Equations
`(2)`--`(3)` show that no principal matrix of order one or two has such a direction.  Hence its
order is at least three, proving `(4)`.

The conclusion is not that every three-node matrix detects RH failure.  A previously proved
protected matrix at squared nodes `{0,1,4}` is positive unconditionally.  The new theorem is the
sharp universal lower bound on detector cardinality; the remaining problem is to characterize or
control the first genuinely three-node source correlation.

## 5. Exact single-orbit three-node sharpness

For one orbit write

```text
K_(t,c)(x,y)
 = [x H_(t,c)(x^2)+y H_(t,c)(y^2)]/(x+y).              (18)
```

Put

```text
D(x)=(x^2+t)^2+c.                                       (19)
```

Direct complex-pair clearing gives the polynomial congruence

```text
D(x)D(y)K_(t,c)(x,y)
 =(xy+t)(x^2+t)(y^2+t)
   +c(x^2-xy+y^2+t).                                    (20)
```

The right side is the evaluation kernel of the coefficient form, in the monomial basis
`(1,x,x^2,x^3)`,

```text
B_(t,c)=
[[t(t^2+c), 0,       t^2+c, 0],
 [0,          t^2-c, 0,     t],
 [t^2+c,      0,     t,     0],
 [0,          t,     0,     1]].                        (21)
```

Its even and odd `2 by 2` blocks both have negative determinant:

```text
det B_even=-c(t^2+c),
det B_odd=-c,
det B=c^2(t^2+c).                                       (22)
```

For three nodes `0<x<y<z`, set

```text
e1=x+y+z,  e2=xy+xz+yz,  e3=xyz,
Delta=(y-x)(z-x)(z-y),                                  (23)

Phi_(t,c)
 =(t^2+c)*(c-(e2-t)^2-t*e1^2+2*e1*e3)-t*e3^2.          (24)
```

The null vector of the `3 by 4` Vandermonde evaluation matrix is
`(-e3,e2,-e1,1)`.  Applying the codimension-one Cauchy--Binet identity to `(21)` gives

```text
det (K_(t,c)(x_i,x_j))_(i,j=1)^3
 = c*Delta^2*Phi_(t,c)
   / (D(x)D(y)D(z))^2.                                  (25)
```

The sign of `Phi` is forced without estimating the nodes.  For positive `x,y,z`, the elementary
Maclaurin inequalities needed here are

```text
e1^2>=3e2,
e2^2>=3e1e3.                                            (26)
```

Consequently

```text
c-(e2-t)^2-t*e1^2+2e1e3
 <= c-(e2-t)^2-3te2+(2/3)e2^2
  = c-t^2-te2-(1/3)e2^2
  < 0                                                    (27)
```

because `c<t^2`, `t>0`, and `e2>0`.  Equation `(24)` now gives `Phi_(t,c)<0`.  If the orbit is
transverse, `c>0`; all remaining factors in `(25)` are positive.  Therefore

```text
det (K_(t,c)(x_i,x_j))_(i,j=1)^3 < 0                   (28)
```

for every three distinct positive nodes.

This sharpens `(4)` at the atomic level:

```text
critical-line orbit (c=0): positive rank at most two;
off-line orbit (c>0):      first negative detector order exactly three. (29)
```

The full Xi kernel is a sum of all orbit kernels, so `(28)` does not by itself make its
three-node determinant negative: positive critical-line packets and other transverse packets can
mask one orbit under a fixed triple.  The remaining RH problem has therefore become an exact
cross-orbit selection/cancellation question at exterior degree three, rather than an unspecified
signed-mass estimate.

## 6. Exact cross-orbit masking and amplification law

Fix three ordered positive nodes and let `A` be the three-by-three response matrix of one orbit.
Let `B` be any fixed background matrix, in particular the complete Xi response with that copy
removed.  Write `M(A;B,B)` for the mixed determinant coefficient with one row from `A` and two
rows from `B`, summed over the three row placements.  Multilinearity gives the exact cubic
identity

```text
det(B+lambda A)
 = det(B) + lambda M(A;B,B) + lambda^2 M(B;A,A)
   + lambda^3 det(A).                                      (30)
```

For an off-line orbit, `(28)` says `det(A)<0`.  Put

```text
C = |det(B)| + |M(A;B,B)| + |M(B;A,A)|.                   (31)
```

For `lambda>=1`, the three lower-degree terms in `(30)` are at most `lambda^2 C`.  Therefore

```text
C < -lambda det(A)
  -> det(B+lambda A) <= lambda^2(C+lambda det(A)) < 0.     (32)
```

In particular the explicit threshold

```text
L = max(1, C/(-det(A)))                                   (33)
```

has the property that `det(B+lambda A)<0` for every `lambda>L`.  Applied with
`B=K_full-A`, this proves:

```text
cross-orbit masking of an off-line self-cubic is finite-amplitude only. (34)
```

This is the strongest exact positive classification of the mixed-cubic obstruction found here.
It does **not** authorize selecting a zero orbit.  To turn `(34)` into RH, the completed Euler
source must produce a source-pure transverse aperture whose relative weight on every hypothetical
entering orbit becomes unbounded while the residual mixed budget stays fixed or lower order.
The finite differential-rank and positive Gram theorems from HTGeometry do not supply that
zero-side amplifier: they prove that the source has enough independent finite directions, but the
missing infinite completion is precisely the map from those directions to the Xi orbit weights.

The source-side geometry of that map is now exact.  At prime-power valuation layer `r=e+1`, the
normalized transverse coefficient satisfies

```text
Lambda(p^r)(1-p^(-ra))/(r(log p)^2)
  = integral_0^a exp(-r(log p)t)dt.                       (35)
```

Thus all prime/valuation columns are Laplace samples of interval vectors `1_[0,a]`, whose Gram is
the Brownian kernel `min(a,b)`.  This is also the kernel of the established Xi boundary relative
trace.  Hence the candidate completion is no longer unspecified: it is a Brownian--Laplace
source-to-Hardy map.  To close `(34)`, that map must still be proved source-defined and
nonexpansive against the Euler-pole boundary density, and its action must be shown to create the
required relative transverse orbit weight.  Equation `(35)` supplies the common Hilbert geometry;
it does not select a divisor orbit or prove the cubic amplification.

## 7. Relation to the physical-cutoff Jordan no-go

The fixed-cutoff low/high Jordan split is not physical: complementary alias coefficients rejoin
before the common response is evaluated.  The invariant corrected response instead leaves the
positive aperture defect, whose vanishing rate is RH-equivalent.  Thus direct total-variation
control of either signed half is the wrong target.

The theorem here is the strongest noncircular correlation salvage found after that no-go:

```text
signed orbit packet
  -> full Euler response
  -> automatic 1-node and 2-node positivity
  -> first unresolved response charge is 3-node.        (17)
```

It does not bound the RH-equivalent aperture defect and does not prove complete positivity.

## 8. Novelty boundary

The internal corpus was searched for the two monotonicities in `(2)`, the determinant
factorization with their Xi chamber discharge, and the conclusion that the first negative
Euler-ray detector has order at least three.  No matching statement was found.  The nearest
parents are:

- the generalized Nevanlinna/Krein--Langer negative-index law, which gives the total negative
  index but no Xi-specific lower bound on the cardinality of a negative principal detector;
- the squared-Xi `{0,1,4}` three-point protected chamber, which treats one fixed Toeplitz matrix;
- the half-unit Cauchy seam no-go, whose two-node scalar seam is indefinite but is not the full Xi
  response.
- `DetectorOrderClassification.lean`, whose "order two" concerns vanishing order of a
  holomorphic height-fibre reader.  It is not the cardinality of a principal Euler-response
  matrix and neither statement implies the other.

The result may normalize to a specialized consequence of classical Hurwitz-stable or Stieltjes
function theory.  No external literature search was performed, in accordance with the
no-Googling research constraint.  Therefore the external novelty label remains explicitly
unverified and publication novelty must not be claimed yet.

## Lean scope

The two Lean leaves formalize:

1. the exact identities `(8)`, `(9)`, and `(13)`;
2. the abstract response-correlation theorem;
3. the unconditional Xi orbit chamber `(6)` from live strip and height theorems;
4. strict one- and two-node positivity for every nonempty finite Xi orbit packet;
5. the exact three-node factorization `(25)` and strict negativity `(28)` for every transverse
   orbit;
6. absolute summability over the complete multiplicity-exact Xi divisor;
7. the exact analytic normalization
   `xi'(1/2+x)/(x xi(1/2+x)) = sum_q Re (x^2+a_q^2)^(-1)` for `x>0`;
8. strict radial monotonicity and strict two-node positivity for the actual infinite Xi response;
9. the exact mixed-discriminant expansion `(30)` and finite-amplitude masking theorem `(32)`--`(34)`.
10. the all-valuation Brownian--Laplace factorization `(35)`, projective collapse, and oriented
    first contact grade in `XiTransversePrimeSourceProjectiveTangent.lean`.

The first leaf is the dependency-closed finite algebraic core.  The second leaf performs the full
analytic promotion through the already formalized Xi Hadamard/relative-resolvent connector.  It
does not infer three-node negativity for the sum: the mixed exterior-cubic masking terms remain
the exact open core.

## Gates

- [x] Direct signed-Jordan route retired using the physical response-joining law.
- [x] Positive correlation survivor stated exactly.
- [x] Per-orbit chamber derived without zero computation.
- [x] Both strict radial monotonicities proved by exact identities.
- [x] Two-node determinant factorized and signed.
- [x] Minimal detector order deduced from the exact index law.
- [x] Single transverse orbit proved to have detector order exactly three.
- [x] Internal novelty search found no duplicate.
- [ ] External parent-theory and literature novelty audit.
- [x] Full infinite-sum Lean promotion from the finite-packet core.
- [x] Mixed exterior-cubic masking expanded and finite-amplitude amplification formalized.

## Log

- 2026-07-19 -- Extracted the two-node response barrier as the positive survivor of the physical
  cutoff Jordan-mass obstruction.  The decisive new factorization is `(13)`: the two response
  directions are exactly the strict decrease of `Q(x)/x` and strict increase of `x*Q(x)`.
- 2026-07-19 -- Promoted the finite packet to the complete multiplicity-exact Xi divisor in Lean.
  The relative-resolvent identity fixes the normalization with no factor-of-two ambiguity, and
  the full analytic response inherits the strict two-node barrier unconditionally.
- 2026-07-19 -- Expanded the first unresolved three-node charge into its two mixed discriminants
  and negative atomic self-cubic.  Cross-orbit masking is now proved to be finite-amplitude; the
  exact remaining RH object is a source-pure unbounded transverse amplifier, not another generic
  Jordan-mass or finite-field estimate.
- 2026-07-19 -- Used the full transverse HT source hierarchy to identify its canonical completion
  geometry: normalized valuation-layer coefficients are Laplace samples of Brownian interval
  vectors, and their `min` Gram is the same kernel as the Xi boundary relative trace.  The open
  amplifier is now a specific source-to-Hardy contraction/weight-transfer theorem.
