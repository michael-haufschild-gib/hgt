# Finite-jet Page transition for two incompatible projective horizons

- **ID:** `projective-horizon-finite-jet-page-transition`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ALGEBRAIC COMPLEMENTARITY LAW
- **Scientific status:** `[PROVED ON PAPER] [FORMAL CORE COMPLETE] [NOVELTY PROVISIONAL]`
- **Parents:** `projective-horizon-one-sided-depth-transition`,
  `projective-horizon-all-depth-cusped-building`
- **Lane:** source-pure hypertranscendental geometry; physical-information interpretation

## Claim

Let `x` be differentially transcendental over a characteristic-zero constant field `C`, write

```text
x_j = delta^j x,
y_j = delta^j (x^-1),
J_N = C(x_0,...,x_N),
O_(m,n;N) = C(x_m,...,x_N,y_n,...,y_N),
```

where `m,n>=1` and `m,n<=N+1`. Then

```text
trdeg_C O_(m,n;N)
  = min(N+1, (N+1-m)+(N+1-n)).                         (1)
```

Equivalently, the unobserved transcendence degree and the number of independent algebraic
compatibility relations among the displayed observables are

```text
hidden(m,n;N)    = max(0,m+n-N-1),
relations(m,n;N) = max(0,N-m-n+1).                      (2)
```

Thus the finite-order observation map has an exact static Page-type transition at

```text
N_Page = m+n-1.                                         (3)
```

Before `(3)`, each added derivative removes one hidden source degree. At `(3)`, the two horizon
packets have exactly `N+1` algebraically independent coordinates and determine the full `N`-jet
up to a generically finite ambiguity. After `(3)`, no hidden transcendence remains and every added
order contributes one new compatibility relation.

The later theorem `projective-horizon-one-step-postcritical-rigidity` completes the degree profile
omitted here: the critical ambiguity has degree `choose(m+n,m)` and full symmetric monodromy,
while at the very next order the observation map is birational and remains so at every later order.

The parameter `N` is derivative resolution, not time. No carrier or propagation law is introduced.

## Proof core

Use exponential Taylor coordinates

```text
X(t)=sum_(j>=0) x_j t^j/j!,
Y(t)=X(t)^-1=sum_(j>=0) y_j t^j/j!.
```

The coordinates `x_0,...,x_N` are algebraically independent by differential transcendence. The
raw horizon contributes `N+1-m` independent rows. It remains to compute the rank supplied by the
reciprocal rows modulo `dx_m,...,dx_N`.

Linearize inversion at the formal jet

```text
X_*(t)=exp(-t/2),    Y_*(t)=exp(t/2).
```

Since `dY=-Y^2 dX`, at this jet

```text
d y_j = -sum_(k=0)^j choose(j,k) d x_k.                 (4)
```

For any `r`, the consecutive minor with rows `j=n,...,n+r-1` and columns `k=0,...,r-1` is

```text
P_(n,r) = (-choose(n+i,k))_(0<=i,k<r).                  (5)
```

The unsigned shifted Pascal matrix has determinant one. Indeed, at shift zero it is lower
unitriangular, and Pascal's recurrence gives

```text
P^+_(n+1,r)=P^+_(n,r) U_r,
```

where `U_r` is upper unitriangular. Hence

```text
det P_(n,r)=(-1)^r != 0.                                (6)
```

Take

```text
r=min(m,N+1-n).
```

The minor `(5)` is available because its columns are among the unobserved low raw modes and its
rows are among `y_n,...,y_N`. Therefore the full observation Jacobian has rank

```text
(N+1-m)+min(m,N+1-n)
  = min(N+1,2N-m-n+2).                                  (7)
```

The coordinate count gives the matching upper bound. The characteristic-zero Jacobian criterion
promotes `(7)` to algebraic independence of a maximal observable subset, proving `(1)`. Subtracting
the rank from the ambient and displayed-coordinate counts gives `(2)`.

## Projective covariance

The raw/reciprocal pair is the normal form of every ordered pair of distinct scalar projective
horizons. Choose a constant Mobius coordinate

```text
z=(a x+b)/(c x+d)
```

sending the two labels to infinity and zero. Nondegeneracy gives

```text
z_j = phi'(x_0) x_j + R_j(x_0,...,x_(j-1)),              (8)
```

with `phi'(x_0) != 0`. The triangular rational transformation `(8)` is birational on every finite
jet space, so `z_0,...,z_N` remain algebraically independent and preserve transcendence rank.
Applying `(1)` to `z` and `z^-1` proves the same law for the original pair. Hence the critical
resolution depends only on the two depths `(m,n)`, not on the chosen labels or affine chart.

## Physical meaning

Two incompatible projective horizons behave as a finite-resolution algebraic secret-sharing
system. Neither observer is privileged and the pair has no dynamical coupling. Their apparent
information release is instead a theorem about how two static constraint charts overlap:

```text
hidden source freedom  ->  critical finite ambiguity  ->  redundant compatibility law.
```

The infinite-tail theorem is the `N -> infinity` endpoint: the join is the complete source field,
while the depth-two meet collapse says no nonconstant datum is common to both charts. The finite
law explains how those two limiting statements coexist.

## RH impact

For an unconditionally hypertranscendental source such as Riemann zeta, `(1)--(3)` apply to its
formal scalar jet and any reciprocal projective chart. This supplies an exact finite-order
observability threshold. It does not identify zeros: target translation leaves all positive
horizons unchanged. Consequently the law can organize a future arithmetic marking but cannot by
itself imply RH.

## Novelty audit

Jet bundles, prolonged projective actions, reciprocal derivative formulae, Pascal matrices, and
Jacobian criteria are classical separately. A targeted search found adjacent work on algebraic
differential invariants and jet/prolongation spaces, but no statement of the horizon-pair
transcendence-rank law `(1)`, its sharp threshold `(3)`, or the hidden-to-relation exchange `(2)`.
Novelty therefore remains provisional pending expert literature audit.

The phrase “algebraic Page curve” is already used by Gomez for a time-parametrized family of finite
type-II_1 factors and Murray--von Neumann relative dimension
([arXiv:2403.09165](https://arxiv.org/abs/2403.09165)). That theory is not the theorem here: `(1)`
has no operator algebra, state, entropy, evaporation, or time parameter. “Page-type” describes only
the exact exchange between hidden dimension and relation redundancy as derivative resolution
crosses `(3)`. Likewise, Richardson's “reciprocal Pascal matrix” is the Hadamard inverse of a
symmetric Pascal matrix ([arXiv:1405.6315](https://arxiv.org/abs/1405.6315)); it is not the
reciprocal-jet Jacobian `(5)`.

## Lean verification

The module

```text
formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonPageTransition.lean
```

formalizes:

1. the shifted Pascal recurrence as multiplication by an upper-unitriangular matrix;
2. `det(choose(n+i,k))=1` for every shift and size;
3. the reciprocal linearization determinant `(-1)^r` and its nonvanishing;
4. the maximal-rank formula and exact hidden/relation balance;
5. simultaneous vanishing of both counts at `N=m+n-1`.

A targeted leaf build succeeds. The axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`; there are no project axioms or placeholders. The paper-level use of the
characteristic-zero Jacobian criterion remains stated in this card rather than encoded as a new
general algebraic-geometry library in Lean.
