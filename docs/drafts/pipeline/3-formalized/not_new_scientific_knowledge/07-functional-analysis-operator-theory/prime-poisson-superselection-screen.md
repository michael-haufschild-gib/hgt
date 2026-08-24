# Prime Poisson states form a superselection screen at the critical line

- **ID:** `prime-poisson-superselection-screen`
- **Stage:** 3-formalized / needs independent audit
- **Type:** THEOREM (paper); source-carrier theorem
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** the normalized full prime density matrix and its Bohr spectral measure
- **Lean:** `GaloisForLFunctions.HTGeometry.PrimePoissonSuperselectionScreen`
- **Statement:** The trace-class prime density states on `Re(s)>1/2` have canonical product-Poisson
  spectral measures on the infinite prime torus.  These normal states converge at `Re(s)=1/2` to
  singular states.  Functional-equation-reflected states have the same measure class exactly on
  the critical line, while two distinct heights on that line give mutually singular measures.

## Purpose

This theorem replaces the misleading picture of a trace-class joint density that loses rank at a
zero.  The prime density is rank one everywhere it exists.  The genuine change of quality is a
change of representation class:

```text
Re(s)>1/2:  one normal Haar-sector containing every height,
Re(s)=1/2:  singular, mutually disjoint height sectors,
reflection: the two sectors coincide only on the self-dual line.
```

Thus the critical line is a superselection screen.  Interference is not forced onto it by an
uncertainty inequality; coherent comparison of the two reflected prime descriptions exists only
there.  The theorem does not prove that every completed-zeta zero supplies such a coherent
comparison.

## Prime Poisson states

Let

```text
T^P = product_(p prime) S^1
```

with product Haar probability `m`.  For `a` in the open unit disk, let `nu_a` be harmonic measure
with Poisson density

```text
d nu_a(z) = P_a(z) dm_1(z),
P_a(z) = (1-|a|^2)/|z-a|^2,       |z|=1.
```

For `s=sigma+it` with `sigma>0`, put

```text
a_s(p)=p^(-conj(s))
```

and define the product probability

```text
mu_s = tensor_p nu_(a_s(p)).
```

This product exists for every `sigma>0`; no infinite density relative to Haar is asserted at this
point.  For a rational prime character

```text
q=A/B,  gcd(A,B)=1,
z^q = product_p z_p^(v_p(A)-v_p(B)),
```

the Poisson moment formula gives

```text
integral z^q d mu_s = A^(-conj(s)) B^(-s).
```

In particular the absolute value is `(AB)^(-sigma)`.  These moments retain the off-diagonal phase
coherence that the particle probabilities discard.

## Local Hellinger lemma

`[PROVED]` There are `r_0 in (0,1)` and constants `0<c<C` such that whenever
`|a|,|b|<=r_0`,

```text
c |a-b|^2
  <= 1 - integral_(S^1) sqrt(P_a P_b) dm_1
  <= C |a-b|^2.                                      (1)
```

### Proof

Define

```text
Phi(a)=sqrt(P_a) in L2(S^1,m_1).
```

On every closed disk of radius strictly below one, the denominators are uniformly separated from
zero.  Differentiation under the norm therefore shows that `Phi` is continuously Frechet
differentiable as a map from the two-real-dimensional disk to `L2`.  At the origin,

```text
D Phi(0)[h](z)=Re(conj(z)h),
||D Phi(0)[h]||_2^2=|h|^2/2.                          (2)
```

Choose `r_0` so small that

```text
||D Phi(a)-D Phi(0)|| <= 1/(2 sqrt(2))
```

for `|a|<=r_0`.  Integrating the derivative along the segment from `b` to `a` and using (2) gives
two constants `0<c_1<C_1` with

```text
c_1|a-b| <= ||Phi(a)-Phi(b)||_2 <= C_1|a-b|.
```

Finally,

```text
||Phi(a)-Phi(b)||_2^2
  = 2 - 2 integral sqrt(P_a P_b) dm_1.
```

Squaring the preceding bounds proves (1).  QED.

## Product-measure classification

`[PROVED]` Let `a=(a_p)` and `b=(b_p)` be two disk-valued prime sequences tending to zero, and put

```text
mu_a=tensor_p nu_(a_p),
mu_b=tensor_p nu_(b_p).
```

Then

```text
mu_a and mu_b are equivalent
  iff
sum_p |a_p-b_p|^2 < infinity;                         (3)
```

otherwise they are mutually singular.

### Proof

Every one-prime pair is mutually absolutely continuous because its Poisson densities are strictly
positive.  Kakutani's product-measure dichotomy says that the products are equivalent exactly when

```text
product_p H_p > 0,
H_p = integral sqrt(P_(a_p) P_(b_p)) dm_1,
```

and otherwise they are mutually singular.  Since `a_p,b_p -> 0`, all but finitely many pairs lie in
the disk from the local lemma.  There `1-H_p` is comparable to `|a_p-b_p|^2`.  The elementary
criterion

```text
product_p H_p>0 iff sum_p (1-H_p)<infinity
```

for `H_p in (0,1]` tending to one now gives (3).  QED.

## The normal-to-singular transition

`[PROVED]` For `sigma>0`,

```text
mu_s is equivalent to Haar m
  iff
sigma>1/2.                                             (4)
```

Indeed Haar is the product with every disk parameter equal to zero, so (3) reduces (4) to

```text
sum_p |a_s(p)|^2 = sum_p p^(-2 sigma) < infinity,
```

which holds exactly when `2 sigma>1`.

For `sigma>1/2`, the normalized prime vector

```text
Psi_s = zeta(2 sigma)^(-1/2) (n^(-s))_(n>=1)
```

belongs to `l2(N)`.  Its Bohr transform is

```text
F_s(z)
  = zeta(2 sigma)^(-1/2) sum_n n^(-s) z^kappa(n)
  = product_p
      (1-p^(-2 sigma))^(1/2)/(1-p^(-s)z_p).
```

Consequently

```text
d mu_s = |F_s|^2 dm.                                   (5)
```

Thus `mu_s` is exactly the wave spectral measure of the full rank-one density
`|Psi_s><Psi_s|`, not a replacement built from its diagonal.

For fixed `t`, cylinder moments show

```text
mu_(sigma+it) -> mu_(1/2+it) weak-star
as sigma decreases to 1/2.                             (6)
```

Cylinder functions are uniformly dense in `C(T^P)`, so moment convergence proves (6) for every
continuous function.  By (4), the limiting measure is singular to Haar.  The trace-class vector
therefore does not converge to another Haar-space density matrix; it converges as a state to a
singular GNS sector.

## Reflection selects exactly the wall

Let

```text
tau(s)=1-conj(s).
```

`[PROVED]` For `0<Re(s)<1`,

```text
mu_s and mu_(tau(s)) are equivalent
  iff
Re(s)=1/2.                                             (7)
```

At `Re(s)=1/2`, `tau(s)=s`, so the measures are equal.  Suppose `sigma<1/2`.  The reverse triangle
inequality gives

```text
|a_s(p)-a_(tau(s))(p)|
  >= p^(-sigma)-p^(-(1-sigma))
  = p^(-sigma)(1-p^(-(1-2 sigma)))
  >= c_sigma p^(-sigma),
```

where `c_sigma=1-2^(-(1-2 sigma))>0`.  Hence the square-distance sum dominates a positive multiple
of `sum_p p^(-2 sigma)`, which diverges because `2 sigma<1`.  Equation (3) makes the measures
mutually singular.  The case `sigma>1/2` follows by reflection symmetry.  QED.

This is the exact superselection statement: off the wall, the two completed perspectives are
disjoint representations rather than two coherent paths in one representation.

## Distinct critical heights are distinct sectors

`[PROVED]` If `t!=u`, then

```text
mu_(1/2+it) is mutually singular to mu_(1/2+iu).        (8)
```

By (3), it is enough to prove divergence of

```text
sum_p |p^(-1/2+it)-p^(-1/2+iu)|^2
  = 2 sum_p (1-cos((t-u)log p))/p.                     (9)
```

Put `lambda=t-u!=0`.  The classical de la Vallee Poussin remainder in the prime number theorem
implies convergence of

```text
sum_p p^(-1-i lambda).                                 (10)
```

For completeness, write the partial sum as the Stieltjes integral

```text
integral_(2-)^x y^(-1-i lambda) d pi(y).
```

With

```text
pi(y)=Li(y)+O(y exp(-c sqrt(log y))),
```

the main term becomes, after `v=log y`,

```text
integral_(log 2)^(log x) exp(-i lambda v)/v dv,
```

which converges by Dirichlet's test.  Integration by parts makes the error absolutely convergent,
because it is bounded by a constant times

```text
integral_2^infinity exp(-c sqrt(log y)) dy/y < infinity.
```

Taking real parts in (10) shows that

```text
sum_(p<=x) cos(lambda log p)/p
```

has a finite limit.  Euler--Mertens gives

```text
sum_(p<=x) 1/p = log log x + O(1).
```

Therefore (9) diverges, and Kakutani's dichotomy proves (8).  QED.

The vertical coordinate is not an evolution inside one critical representation.  Every height is
its own singular prime-phase sector.  A completed-zeta zero, if realized as a physical defect, must
be an internal defect of the sector at that same height.

## Height flow becomes outer at the screen

For `h in R`, let the arithmetic Kronecker rotation be

```text
R_h(z)_p = p^(ih) z_p.
```

Up to the harmless sign fixed by the Fourier convention,

```text
(R_h)_* mu_(sigma+it) = mu_(sigma+i(t+h)).              (11)
```

`[PROVED]` For `sigma>1/2`, this action is spatial in the Haar representation.  All measures in
(11) are equivalent to Haar, and the Radon--Nikodym square-root formula gives the usual Koopman
unitary between their `L2` realizations.

`[PROVED]` At `sigma=1/2`, every `h!=0` sends the state to a mutually singular state by (8).
Therefore no unitary in one critical GNS representation can implement the height translation: such
a unitary would make the original and translated representations quasi-equivalent.  Height is an
outer motion between sectors, not a Hamiltonian evolution inside one sector.

There is nevertheless an exact dephasing law.  For every `sigma>0`,

```text
(1/(2T)) integral_(-T)^T mu_(sigma+it) dt
  -> Haar                                                   (12)
```

weak-star.  Indeed the Fourier coefficient at `q=A/B` is a fixed amplitude times

```text
(1/(2T)) integral_(-T)^T exp(it log(A/B)) dt,
```

which tends to zero unless `A=B`; cylinder functions are dense.

For `sigma>1/2`, the corresponding density matrices satisfy the stronger particle-dephasing law

```text
(1/(2T)) integral_(-T)^T |Psi_(sigma+it)><Psi_(sigma+it)| dt
  -> diag(n^(-2 sigma)/zeta(2 sigma))                      (13)
```

in trace norm.  To prove (13), first truncate `Psi` to finite support.  On the resulting finite
matrix, every off-diagonal entry is multiplied by the same oscillatory average as in (12), hence
vanishes.  The finite-rank convergence is therefore in trace norm.  Approximation of `Psi` in
`l2`, together with contractivity of time averaging and dephasing on trace class, passes the result
to the full density.

Equations (12)--(13) make the wave--particle statement literal.  Height coherence gives the wave
state; averaging over the screen destroys all unequal-number phases and leaves the particle law.
At the critical line the individual wave states survive only as disjoint singular sectors, while
their averaged shadow is Haar.

## Phase-twist criterion

Let `chi` be completely multiplicative and unimodular.  Replacing `n^(-s)` by `chi(n)n^(-s)`
rotates the local disk parameters.  The same theorem gives the exact criterion

```text
mu_(s,chi) ~ mu_(s,1)
  iff
sum_p p^(-2 sigma)|chi(p)-1|^2 < infinity.             (14)
```

For `sigma>1/2`, every such twist stays in the Haar measure class.  At the wall, a twist with

```text
sum_p |chi(p)-1|^2/p = infinity
```

enters a disjoint sector.  Thus the phase information erased by all local-unitary invariants of the
density matrix reappears at the critical transition as a measure-class invariant.  Equation (14)
does not show that every prescribed-divisor Helson twist is disjoint; that is a separate arithmetic
question.

## Consequence for the screen conjecture

`[PROVED RECUT]` A trace-class density is not the wall object.  Trace-class prime densities exist
only in the normal bulk `Re(s)>1/2`, where all their Poisson spectral measures lie in one Haar
measure class.  The screen is the singular weak-star boundary family

```text
{mu_(1/2+it) : t in R},
```

whose members are pairwise disjoint superselection sectors.

Accordingly, the RH route has two logically separate layers.

1. **Kinematic layer, closed here.** Reflected prime descriptions admit one common sector only on
   `Re(s)=1/2`; distinct heights remain separated.
2. **Source layer, open.** Construct from the Euler--Gamma/theta completion an observable or
   correspondence in the sector `mu_(1/2+it)` whose nontrivial defect is equivalent to
   `xi(1/2+it)=0`, and prove that every complex zero of `xi` produces one of these sector defects.

The second clause is essential.  Merely restricting `xi` to the line would discard hypothetical
off-line analytic zeros rather than exclude them.

## Novelty and significance verdict

The proof uses known parent results: the Poisson kernel, the Bohr transform, Kakutani's product
measure dichotomy, compact-group dephasing, Euler--Mertens, and the prime number theorem with its
classical zero-free-region remainder.  Exact searches across infinite-polytorus harmonic measure,
Dirichlet-series Bohr lifts, product Poisson measures, and Riesz-product equivalence did not locate
this assembled zeta statement.  Nevertheless every mathematical step is a direct specialization
or composition of those parents.  It therefore fails the novelty gate and is classified
`[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`.

Its route significance is already concrete:

- it identifies a canonical non-trace-class wall state rather than postulating one;
- it upgrades the scalar normalizability threshold to an exact representation-class transition;
- it proves that height itself becomes superselected at the wall;
- it makes the Helson phase gauge visible through measure class; and
- it removes the false requirement that one trace-class joint density persist off the wall and
  then lose rank at a zero.

It does not prove RH and does not construct the completion-locked defect observable.

## Gates

- [x] 0 -> 1: product-Poisson state, measure-class criterion, reflection, height, and twist tests
  stated exactly
- [x] 1 -> 2: complete paper proof with all analytic inputs explicit
- [x] parent novelty audit: exact assembled statement not located, but direct Kakutani--Bohr--PNT
  derivation fails the novelty gate
- [x] significance audit: substantive new carrier for this route, but no zero-to-sector descent and
  therefore no RH advance
- [x] 2 -> 3: exact unconditional Lean formalization, reusable outer-factor/Bohr infrastructure,
  targeted leaf build, and axiom audit complete

## References to audit

- S. Kakutani, *On equivalence of infinite product measures*, Annals of Mathematics 49 (1948).
- H. Hedenmalm, P. Lindqvist, and K. Seip, *A Hilbert space of Dirichlet series and systems of
  dilated functions in L2(0,1)*, Duke Mathematical Journal 86 (1997).
- Classical Euler--Mertens and de la Vallee Poussin prime-number theorems.
