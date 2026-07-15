# Critical projective-horizon multiplicity is binomial

- **ID:** `projective-horizon-critical-binomial-multiplicity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / EXACT CRITICAL-FIBER ENUMERATION
- **Scientific status:** `[PROVED ON PAPER] [FORMAL CORE COMPLETE] [NOVELTY PROVISIONAL]`
- **Parents:** `projective-horizon-finite-jet-page-transition`,
  `projective-horizon-page-capacity-law`
- **Lane:** source-pure hypertranscendental geometry; enumerative topology

## Theorem

Let `m,n>=1`, put `L=m+n` and `N=L-1`, and let

```text
X(t)=x_0+x_1 t+...+x_N t^N
```

be the truncated ordinary Taylor jet of a differential-generic scalar. Let

```text
Y(t)=X(t)^-1 mod t^L.
```

The critical two-horizon observation map is

```text
Phi_(m,n): X |->
  (x_m,...,x_N, y_n,...,y_N).                            (1)
```

Over an algebraically closed characteristic-zero field, `(1)` is dominant and generically etale
of degree

```text
deg Phi_(m,n) = choose(m+n,m).                           (2)
```

Thus a generic critical observation has exactly `choose(m+n,m)` distinct compatible source jets.
The count is symmetric in the two depths.

For a differential-generic source in any `P^d`, with complete affine-coordinate packets at two
distinct hyperplane horizons, the critical degree is still `(2)`. Projective dimension multiplies
the subcritical hidden dimension and supercritical relation codimension, but the transverse
channels are generically linear and add no critical finite ambiguity.

## 1. Generic finiteness and separability

The finite-jet Page theorem gives a square Jacobian at `N=m+n-1`. Its reciprocal Pascal minor is
nonzero, so `(1)` is dominant and generically finite. In characteristic zero the same nonzero
Jacobian gives a nonempty etale locus. Hence the generic geometric fiber is reduced; its cardinality
equals the intersection degree computed below.

Changing from exponential derivative coordinates to ordinary Taylor coefficients only rescales
coordinates by nonzero factorials and does not change degree.

## 2. Biprojective compactification

Fix generic observed tails

```text
P(t)=sum_(i=m)^(L-1) p_i t^i,
Q(t)=sum_(j=n)^(L-1) q_j t^j.
```

Write the unknown low pieces as

```text
A(t)=sum_(i=0)^(m-1) a_i t^i,
B(t)=sum_(j=0)^(n-1) b_j t^j.
```

The fiber equations are the `L` coefficient equations

```text
(A+P)(B+Q)=1 mod t^L.                                   (3)
```

Homogenize the two variable blocks separately with coordinates `alpha,beta`:

```text
X_h=A+alpha P,
Y_h=B+beta Q,
X_h Y_h=alpha beta mod t^L.                              (4)
```

The variables `(alpha,a_0,...,a_(m-1))` give `P^m`; the variables
`(beta,b_0,...,b_(n-1))` give `P^n`. Every one of the `L` equations `(4)` is a divisor of bidegree
`(1,1)`.

Under the Segre embedding

```text
P^m x P^n -> P((C^(m+1)) tensor (C^(n+1))),
([A],[B]) |-> [A tensor B].                               (S)
```

each bilinear coefficient equation becomes a linear hyperplane. Thus the compactified critical
fiber is a codimension-`m+n` linear section of the rank-one tensor variety. The binomial number in
`(2)` is equivalently the degree of this Segre variety.

## 3. No fiber escapes to infinity

Assume the generic open conditions

```text
p_m != 0,    q_n != 0.                                  (5)
```

If `alpha=0` and `beta!=0`, then `X_h=A` is a nonzero polynomial of degree below `m`, while `Y_h`
has nonzero coefficient `beta q_n` at order `n`. Their lowest nonzero product coefficient occurs
strictly below `m+n=L`, contradicting `(4)`. The case `beta=0`, `alpha!=0` is symmetric. If both
homogenizing coordinates vanish, `deg A<m` and `deg B<n`, so their lowest nonzero product
coefficient again occurs below `L`. Hence the compactified generic fiber has no boundary point.

This exclusion is not a heuristic dimension count: it is the valuation identity

```text
ord_t(A B)=ord_t A+ord_t B.                              (6)
```

## 4. Intersection number

The Chow ring of `P^m x P^n` is

```text
Z[H_1,H_2]/(H_1^(m+1),H_2^(n+1)).
```

The complete intersection `(4)` has class

```text
(H_1+H_2)^(m+n).                                        (7)
```

Its degree is the coefficient of `H_1^m H_2^n`, namely

```text
coeff_(H_1^m H_2^n) (H_1+H_2)^(m+n)
  = choose(m+n,m).                                       (8)
```

Generic finiteness makes the intersection proper; the boundary exclusion places all of `(8)` in
the affine jet fiber; generic etaleness makes all points simple. This proves `(2)`.

## 5. Higher-rank transverse uniqueness

In projective normal coordinates the chart transition is

```text
(p,u) |-> (p^-1,u/p).
```

Once a longitudinal solution `p` in a generic critical fiber is fixed, every transverse pair of
tails gives a square linear convolution system for the low coefficients of `u` and `u/p`. The
transverse Pascal determinant is one on a nonempty open set, so each longitudinal solution has one
transverse lift. Repeating channels changes neither the generic degree nor `(2)`.

## Topological meaning

The same integer satisfies

```text
choose(m+n,m) = chi(Gr(m,m+n)),                          (9)
```

the Euler characteristic of the complex Grassmannian, equivalently the number of its Schubert
cells or monotone lattice paths across an `m x n` rectangle. Equation `(9)` is an exact equality of
the critical multiplicity with a classical topological charge. This proof does not yet construct a
canonical identification between individual generic fiber points and Schubert cells; such an
identification would require a controlled degeneration and is not claimed.

Physically, `(2)` is a static critical microstate count. No probability measure or entropy is
introduced, although the logarithm of `(2)` could be used only after choosing such extra data.

There is also an exact quantum-kinematic interpretation. Projective rank-one tensors are precisely
separable bipartite pure states; this use of the Segre variety is standard in quantum information
([Heydari](https://arxiv.org/abs/quant-ph/0506043)). Hence the critical horizon microstates are
isolated separable states satisfying `m+n` linear compatibility observables. This statement adds no
inner product, Born rule, Hamiltonian, time evolution, or claim that a hypertranscendental function
is literally a quantum system. It identifies the exact algebraic state variety selected by the
constraint theorem.

## Lean verification

The module

```text
formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonCriticalMultiplicity.lean
```

formalizes:

1. the outer-product tensor and vanishing of all its `2 x 2` minors;
2. factorization of every bilinear compatibility equation through a linear tensor pairing;
3. the exact low-coefficient survival theorem implied by `(6)`;
4. exclusion of an all-zero truncated product on each boundary face;
5. the Chow coefficient `(8)` as `criticalHorizonMultiplicity`;
6. positivity and symmetry of the multiplicity.

It imports the already formalized nonzero critical Jacobian minor. A targeted leaf build and
scratch axiom audit pass with only `propext`, `Classical.choice`, and `Quot.sound`. No full build was
run. The general multiprojective Bezout theorem and generic-etale theorem are used at paper level
rather than reimplemented as a project-local algebraic-geometry library.

## Novelty audit

Formal-series inversion, multiprojective Bezout, Schubert-cell enumeration, and generic etaleness
are classical. Multihomogeneous Bezout numbers count isolated solutions in products of projective
spaces (for an adjacent reference, [Malajovich--Meer](https://arxiv.org/abs/cs/0405021)). Targeted
searches of jet/prolongation, Padé, reciprocal-series, Cremona, and multihomogeneous literature found
no theorem identifying the generic critical tail-observation degree `(2)`, its all-rank stability,
or its role as the finite-jet transition multiplicity of a hypertranscendental horizon pair.
Novelty remains provisional pending expert audit.

## RH impact

For the free Riemann-zeta jet, the theorem gives the exact number of generic finite jets compatible
with two critical reciprocal horizon packets. It remains a generic observation theorem and is
invariant under target translations of the underlying positive-jet geometry. It does not select
zeta's zero fiber and therefore does not imply RH. A useful arithmetic application would have to
show how an Euler marking resolves or orients the binomial critical fiber.
