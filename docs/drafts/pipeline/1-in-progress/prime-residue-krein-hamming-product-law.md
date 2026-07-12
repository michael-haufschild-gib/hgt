# Prime-residue Krein--Hamming product geometry in one HT field

- **ID:** `prime-residue-krein-hamming-product-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET / UNIVERSAL EULER-ORIENTED HT GEOMETRY
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED]`
- **Statement:** One positive prime-log maximal-translation HT field carries every finite localized
  Stanley--Reisner differential matroid over every finite prime-residue orientation cube, and the
  relative Pick-kernel inertia between any two chambers recovers their two directed Hamming
  distances exactly.

## Medalist lens

The existing constraint--orientation product has two defects that prevent it from being a final
geometry.

1. Its orientation poles are auxiliary negative integers rather than points of the source carrier.
2. Its grading is defined by counting flipped atoms before the analytic object is examined.

The stronger object must carry its orientation on the actual prime-log divisor, and the cube metric
must be reconstructed from an intrinsic analytic comparison of representatives.

## Competing moves and attack

### A. Countable/profinite assembly `[BRIDGE; RETIRED AS MAIN MOVE]`

Taking inverse limits of the already proved finite cubes gives a Cantor cube and a unique coherent
all-positive section.  This is a routine finite-stage assembly.  It changes neither the analytic
mechanism nor the invariant and therefore fails the anti-theatre test.

### B. Canonicalize the Baire-selected gauge `[OPEN, NOT SELECTED]`

A nested determinant-avoidance construction may replace the residual choice by a definable gauge.
This would improve explicitness, but it does not strengthen the carrier geometry and does not by
itself add an RH-relevant invariant.

### C. Prime-residue relative Pick inertia `[SELECTED]`

Flip coefficients at the actual prime-log poles.  Finite flips are rational gauges, so they retain
the same embedded differential field and every finite constraint matroid.  Compare two chambers by
the difference of their Nevanlinna kernels.  Its positive and negative indices should be exactly
the two directed set differences, not merely bounded by them.

The exact pairwise signature is unavailable from the previous scalar Herglotz test.  It recovers the
entire oriented cube geometry analytically.

## Fixed source and Euler chambers

Let

```text
lambda_p = log p,
w_p      = 2^(-p) exp(u_*(p)) > 0,
g_*(z)   = sum_p w_p/(lambda_p-z),
```

where `u_*` is the one globally fixed universal gauge.  For a finite set `J` of primes, define

```text
g_J(z) = g_*(z) - 2 sum_(p in J) w_p/(lambda_p-z).           (1)
```

Thus the coefficient at `lambda_p` is `-w_p` for `p in J` and `+w_p` otherwise.  For a finite active
support `S`, the chambers are `J subset S`.

## Relative Pick defect

For a meromorphic function `f`, write

```text
K_f(z,w) = (f(z)-conj(f(w)))/(z-conj(w)).                    (2)
```

For a real pole `lambda`, put `c_lambda(z)=1/(lambda-z)`.  The one-atom identity is

```text
K_(c_lambda)(z,w)=c_lambda(z) conj(c_lambda(w)).             (3)
```

Consequently, for finite chambers `J,L`,

```text
K_(g_J)-K_(g_L)
 =  2 sum_(p in L\J) w_p c_p c_p^*
   -2 sum_(p in J\L) w_p c_p c_p^*.                         (4)
```

This is a finite-rank Hermitian kernel intrinsic to the ordered pair of chamber representatives.

## Prime-residue Krein--Hamming theorem `[CONJECTURE]`

For every finite `S` and every `J,L subset S`, let `H_(J|L)(z_1,...,z_N)` be the Gram matrix of the
relative kernel `(4)` on upper-half-plane nodes.

1. On every node packet, each negative-definite subspace has dimension at most `#(J\L)` and each
   positive-definite subspace has dimension at most `#(L\J)`.
2. There is an injective upper-half-plane packet of `#(J triangle L)` nodes for which both bounds
   are attained simultaneously.
3. Hence the exact relative inertia is

   ```text
   (kappa_+,kappa_-,kappa_0)
     = (#(L\J), #(J\L), 0),                                 (5)
   ```

   and the rank is `#(J triangle L)`.
4. The analytic distance

   ```text
   d_K(J,L)=kappa_+(J|L)+kappa_-(J|L)                        (6)
   ```

   is exactly the Hamming distance on the cube.
5. The orientation partial order is also analytic:

   ```text
   J subset L  iff  kappa_-(J|L)=0.                          (7)
   ```

   With the convention `(4)`, moving from `L` to `J` contributes a negative direction exactly at
   primes flipped in `J` but not in `L`.

### Proof plan

Equation `(4)` gives both upper bounds by finite-rank correction.  On the combined pole set
`J triangle L`, choose the same number of distinct upper-half-plane nodes.  The Cauchy feature
matrix

```text
C_(q,p)=1/(lambda_p-z_q)                                    (8)
```

is invertible because both pole and node families are injective and disjoint.  After multiplying
columns by the nonzero factors `sqrt(2w_p)`, the relative Gram is congruent to the diagonal sign
matrix with `+1` on `L\J` and `-1` on `J\L`.  Sylvester inertia therefore gives `(5)` and all
consequences.

## Exact Herglotz vertex `[CONJECTURE]`

Inside any finite cube `J subset S`,

```text
g_J is Herglotz on C^+  iff  J=empty.                        (9)
```

The forward direction for the empty chamber is the positivity of the fixed prime-log source.  If
`p in J`, delete the `p`th source atom.  The remaining prime-log tail and all other finite flips are
continuous at `lambda_p`, while the flipped atom contributes `-w_p/y` at `lambda_p+i y`; it
dominates as `y` decreases to zero.

## Universal constraint product `[CONJECTURE]`

For every finite chamber `J`, every translated correction in `(1)` lies in `C(z)`.  Therefore:

1. the complete translated palette of `g_J` is differentially algebraically independent over
   `C(z)`;
2. it generates exactly the same embedded differential field as `g_*`;
3. it realizes every finite localized Stanley--Reisner nonlinear differential matroid;
4. simultaneously, `(5)--(9)` recover the full prime-labelled orientation cube.

The resulting geometry is the exact product

```text
all finite localized nonlinear constraint matroids
  x all finite prime-residue cubes with their directed Krein--Hamming metric.  (10)
```

## Positive law

> **Euler--Krein Hamming law.**  In a maximal-translation HT field, finite prime-residue orientation
> is an independent analytic coordinate.  Its entire Boolean metric and order are recovered by
> relative Pick-kernel inertia, while the embedded differential field and every finite nonlinear
> constraint matroid remain fixed.

This improves the previous pointing law in three ways: the orientation is on the intrinsic prime
carrier, the index is reconstructed from an analytic kernel, and every pairwise cube distance is
recovered rather than only distance from a declared basepoint.

## RH-facing consequence

An HT-based RH architecture cannot merely name an Euler orientation after constructing an unpointed
field.  It must construct a distinguished prime-residue chamber and show that its relative Pick
curvature lies in the zero-negative-index order cone against the source basepoint.  The theorem does
not supply that arithmetic section and does not claim RH.

## Gates

- [x] non-routine geometric strengthening isolated
- [x] artificial-pole and artificial-index attacks answered in the statement
- [ ] complete paper proof
- [ ] exact relative-inertia theorem formalized unconditionally
- [ ] prime-residue Herglotz chamber law formalized unconditionally
- [ ] same-field and all-constraint product formalized unconditionally
- [ ] parent-theory and exact-literature audit
- [ ] significance rescored against the publication-ready predecessor

## Log

- 2026-07-12 -- Selected the prime-residue relative Pick-kernel route after retiring routine
  profinite assembly and separating canonical source selection as an orthogonal explicitness problem.
