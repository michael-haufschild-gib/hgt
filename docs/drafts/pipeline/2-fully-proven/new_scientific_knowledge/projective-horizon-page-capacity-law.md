# Projective horizon capacity law in every rank

- **ID:** `projective-horizon-page-capacity-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / HIGHER-RANK FINITE-JET COMPLEMENTARITY
- **Scientific status:** `[PROVED ON PAPER] [FORMAL DETERMINANT CORE COMPLETE] [NOVELTY PROVISIONAL]`
- **Parent:** `projective-horizon-finite-jet-page-transition`
- **Lane:** source-pure projective hypertranscendence; physical-information interpretation

## Theorem

Let `X` be a differential-generic projective source in `P^d`, `d>=1`, over a characteristic-zero
constant field `C`. Choose two distinct hyperplane horizons and observe complete affine-coordinate
jet packets through order `N`, starting at positive depths `m` and `n`. If `O_(m,n;N)` is their
joint observation field, then

```text
trdeg_C O_(m,n;N)
  = d min(N+1, (N+1-m)+(N+1-n)).                         (1)
```

The exact hidden-source and compatibility-relation dimensions are therefore

```text
hidden_d(m,n;N)    = d max(0,m+n-N-1),
relations_d(m,n;N) = d max(0,N-m-n+1).                  (2)
```

The critical derivative resolution remains

```text
N_Page=m+n-1,                                            (3)
```

independent of projective dimension. Dimension changes the capacity of the transition, not its
location: every derivative step transfers exactly `d` algebraic degrees from hidden freedom to
observable rank before `(3)`, and creates exactly `d` independent compatibility relations per step
after `(3)`.

## Normal form

Any ordered pair of distinct hyperplanes is projectively equivalent to

```text
H_a={a=0},    H_b={b=0}
```

in homogeneous coordinates `(a,b,w_1,...,w_(d-1))`. On their common domain, use the two affine
charts

```text
(p,u)=(b/a,w/a),
(q,v)=(a/b,w/b).
```

Their transition is the static birational law

```text
(q,v)=(p^-1,p^-1 u).                                    (4)
```

No source flow or observer connection is introduced.

## Maximal-rank proof

The raw chart contributes `d(N+1-m)` independent jet coordinates. Modulo their differentials,
there are `dm` low source directions. Put

```text
r=min(m,N+1-n).
```

It suffices to exhibit a nonzero `dr`-square Jacobian minor from the first `r` reciprocal-chart
orders and the first `r` low orders in every channel.

Linearize `(4)` at the formal jet

```text
p(t)=exp(-t),    u(t)=0.                                 (5)
```

Then

```text
dq = -exp(2t) dp,
dv_alpha = exp(t) du_alpha.                              (6)
```

Consequently the chosen minor is block diagonal. Its longitudinal block is

```text
L_(n,r)=(-choose(n+i,k) 2^(n+i-k))_(0<=i,k<r),           (7)
```

and each of the `d-1` transverse blocks is

```text
T_(n,r)=(choose(n+i,k))_(0<=i,k<r).                     (8)
```

Weighted Pascal recurrence gives

```text
det L_(n,r)=(-1)^r 2^(rn),
det T_(n,r)=1.                                           (9)
```

Thus the full determinant is `(-1)^r 2^(rn)`, nonzero in characteristic zero. The observation
Jacobian has rank

```text
d[(N+1-m)+min(m,N+1-n)]
  = d min(N+1,2N-m-n+2).                                (10)
```

Coordinate count supplies the matching upper bound, and the Jacobian criterion proves `(1)`.
Subtracting `(10)` from ambient and displayed dimensions proves `(2)`.

## Physical interpretation

The theorem gives a source-pure horizon capacity law. Projective dimension `d` is the exact number
of independent algebraic information channels. The critical surface `(3)` is universal, while the
amount of information hidden or redundantly encoded on either side is extensive in `d`.

This is only an algebraic analogue of an area/channel law. It does not assert a Hilbert space,
entropy, quantum state, spacetime, black-hole evaporation, or physical time. Its content is the
exact finite-resolution rank theorem `(1)--(2)`.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonPageTransition.lean` proves

```text
exponentialPascalMatrix_det:
  det(choose(n+i,k) q^(n+i-k)) = q^(rn)

projectiveLongitudinalLinearizationMinor_det:
  det L_(n,r) = (-1)^r 2^(rn)
```

and proves nonvanishing of the longitudinal block. The unweighted determinant theorem in the same
module supplies every transverse block. Block-diagonal multiplication and the factor `d` in
`(1)--(2)` are retained as the elementary paper layer. A targeted leaf build and scratch axiom
audit pass; no full build was run.

## Novelty audit

Classical jet/prolongation theory, projective chart transitions, binomial derivative laws, and
Pascal matrices are prior art. Chen's Pascal map concerns contact of Hermitian vector bundles
([arXiv:2111.14570](https://arxiv.org/abs/2111.14570)); Doria--Hassanzadeh--Simis use Jacobian dual
rank to characterize birational maps ([arXiv:1101.0197](https://arxiv.org/abs/1101.0197)). Neither
source states the two-horizon observation rank `(1)`, its hidden/relation exchange `(2)`, or the
dimension-extensive capacity law. Targeted searches found no exact collision. Novelty remains
provisional pending expert audit.

## RH impact

The scalar case `d=1` applies to the unconditionally free zeta jet and gives the earlier finite
observability threshold. Higher rank could organize simultaneous projective packets of several
arithmetic functions, but it adds no zero-level marking. Translation-gauge blindness still blocks
an RH implication unless arithmetic source data distinguish the zero fiber.
