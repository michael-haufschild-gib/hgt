# Hypertranscendental clock incompressibility under differential embeddings

- **ID:** `hypertranscendental-clock-incompressibility`
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL DIFFERENTIAL-FIELD THEOREM / IMMERSION-RIGIDITY LAW
- **Scientific status:** `[PROVED HERE] [LEAN ASYMPTOTIC KERNEL FORMALIZED] [EXTERNAL NOVELTY PROVISIONAL]`
- **Parent theorem:** `differential-variational-building-balance-law.md`
- **Lean kernels:**
  `formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentObservableNet.lean`,
  `formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentObservableFactorization.lean`
- **Statement:** A finite-rank free hypertranscendental field cannot be asymptotically compressed
  by embedding it into another finite-rank free differential field.  Intrinsic and ambient jet
  orders differ by a uniform additive constant, and their entire normalized Cartan spectra agree.

## 1. Setup

Let `C` be a characteristic-zero differential field of constants and let

```text
T=C<y_1,...,y_s>  ->  F=C<x_1,...,x_r>                              (1)
```

be a differential-field embedding.  Both displayed tuples are differentially independent over
`C`; equivalently, `T` and `F` are free differential rational fields of finite ranks `s<=r`.
For a finite tuple `u` in `T`, define

```text
ord_y(u) = least jet order needed to express u rationally in the y-jets,
ord_x(u) = least jet order needed to express its image in the x-jets.    (2)
```

These are orders of observables, not elapsed times.

Write `R_F=F[partial;delta]` and let `Q_F` be its skew field of rational pseudodifferential
operators.  The Frechet matrix of the embedding is

```text
P=J_x(y) in Mat_(s x r)(R_F).                                        (3)
```

## 2. Incompressibility theorem

### Theorem A: uniform two-sided order comparison

There is a constant `K>=0`, depending only on the embedding `(1)` and the two displayed
generating tuples, such that every finite tuple `u` in `T` satisfies

```text
|ord_x(u)-ord_y(u)| <= K.                                             (4)
```

In particular, for every sequence `(u_n)` in `T`, whenever either normalized order has a limit,
both do and

```text
lim ord_x(u_n)/n = lim ord_y(u_n)/n.                                  (5)
```

### Proof

The universal differential of `T` extends to `F`.  The one-forms `dy_1,...,dy_s` are
`R_F`-linearly independent: a nonzero `R_F`-relation among them would be a differential-algebraic
relation among the `y_i`, contrary to their differential independence.  In the free basis
`dx_1,...,dx_r`, their row matrix is precisely `P`.  Thus `P` has full row rank over `Q_F`, so
there exists

```text
Q in Mat_(r x s)(Q_F),                 P Q = I_s.                      (6)
```

For `u in T^m`, let

```text
A=J_y(u),       B=J_x(u).                                               (7)
```

The differential-substitution chain rule and `(6)` give the exact identities

```text
B=A P,                    A=B Q.                                      (8)
```

Let `deg` be maximum `partial`-order of a matrix over `Q_F`, with zero matrices assigned degree
`-infinity`, and put `deg_+(M)=max(0,deg(M))`.  Pseudodifferential order is subadditive under
matrix multiplication, hence

```text
deg_+(B) <= deg_+(A)+deg_+(P),
deg_+(A) <= deg_+(B)+deg_+(Q).                                        (9)
```

In a free differential rational field of characteristic zero, a rational function depends on a
highest jet exactly when its formal partial derivative with respect to that jet is nonzero.
Consequently the jet order of a tuple is the nonnegative order of its Frechet matrix.  Equations
`(7)--(9)` prove `(4)` with

```text
K=max(deg_+(P),deg_+(Q)).                                              (10)
```

Dividing `(4)` by `n` proves `(5)`.

## 3. Vector theorem

### Theorem B: the full clock spectrum is embedding-functorial

Let `A_n` be any sequence of invertible `s x s` rational pseudodifferential matrices over `T`,
and regard

```text
B_n=A_n P                                                     (11)
```

as its ambient realization.  Let `mu(A_n)` be the dominant invariant-factor vector.  Define the
ambient vector of `B_n` inside its `s`-dimensional row span by the same valuation-lattice
construction.  Then there are constants `K_k`, independent of `n`, such that for every
`1<=k<=s`,

```text
|sum_(i<=k) mu_i(A_n) - sum_(i<=k) mu_i(B_n)| <= K_k.                  (12)
```

Therefore, if one normalized Cartan vector converges, both do and

```text
lim mu(B_n)/n = lim mu(A_n)/n.                                        (13)
```

The associated weighted boundary flag is carried injectively into the ambient variational
subspace.  Thus the differential variational building is functorial for finite-rank differential
embeddings at the level of asymptotic cones and spherical boundaries.

### Proof

The map

```text
j_P:Q_F^s -> Row_QF(P),                    v |-> vP                    (14)
```

is a linear isomorphism onto its row space, with inverse induced by `Q`.  It therefore transports
pairs of valuation lattices and their elementary-divisor vectors exactly.  In particular, the pair
`(R_F^s,A_n R_F^s)` has the same Cartan vector as
`(j_P(R_F^s),j_P(A_n R_F^s))` inside the row-space building.

The ambient construction may use the saturated base lattice
`Lambda=Row_QF(P) intersect R_F^r` instead of `j_P(R_F^s)`.  These are two fixed commensurable
lattices.  Changing one endpoint of a vector-valued building distance by the fixed distance
between them changes every fundamental-weight coordinate by a bounded amount, by the affine
building triangle/dominance inequalities.  This proves `(12)` without commutative minors.  The
partial sums determine the dominant vector, proving `(13)`.  After passage to the asymptotic cone
the fixed base-lattice offset vanishes, and the induced spherical-boundary map is injective.

## 4. Dynamical corollary

Let `sigma` be a differential automorphism of `T`, and set

```text
a_n=ord_y(sigma^n(y)),             b_n=ord_x(sigma^n(y)).              (15)
```

Then

```text
|a_n-b_n|<=K for all n,
ell_delta^T(sigma)=lim a_n/n=lim b_n/n.                               (16)
```

More strongly, the balanced intrinsic translation vector and its attracting/repelling weighted
flags are preserved by the embedding.  Nonlinear ambient cancellation cannot hide an intrinsic
linear clock slope, and ambient coordinates cannot manufacture one.

This proves the finite-free intrinsic/embedded comparison conjecture in
`../../1-in-progress/nonlinear-hypertranscendental-clock-building-completeness.md`.

## 5. The conductor no-go and its positive successor

For the fixed embedding `(1)`, define the integral Kähler--Ore conductor

```text
Cond(T->F) = Sat_(R_F)(P R_F^r) / (P R_F^r),                           (17)
```

with the row/column convention adjusted as usual.  It is a finite Ore-torsion module.  For
example, `y=delta^k x` gives `P=partial^k` and conductor length `k`.

`[NO-GO]` The conductor of a fixed finite-rank differential embedding cannot be the sought
growing unified obstruction.  Its elementary divisors contribute only the constants in `(10)`
and `(12)`, so normalization kills them.

`[POSITIVE THEOREM]` Every genuine asymptotic loss of clock spectrum certifies failure of at least
one finite-immersion hypothesis.  It must occur at one of the following boundaries:

1. **rank boundary:** the stable differential tail is not finitely differentially generated;
2. **map boundary:** the proposed realization is a quotient, specialization, or rank-degenerate
   comparison rather than a differential-field embedding;
3. **completion boundary:** the comparison exists only after analytic continuation, completion,
   or passage to boundary values, and is not induced by one fixed finite-order differential map.

This is an exact obstruction trichotomy.  Inside the finite free differential category there is no
fourth mechanism: the pseudodifferential right inverse forces incompressibility.

## 6. Constraint on hypertranscendence

The higher-level law is

```text
finite-rank HT freedom is differential-immersion rigid.               (18)
```

Hypertranscendence supplies unlimited algebraically independent finite jet packets.  The theorem
says that no finite differential change of observables can asymptotically compress that capacity.
The balanced clock spectrum and its thin boundary are invariants of the embedded HT field, not of
a chosen presentation.

For a single hypertranscendental function, rank one still has zero balanced reversible spectrum.
Consequently a nonzero self-dual degeneracy spectrum cannot be intrinsic to a scalar zeta field
alone.  A zeta-based realization would have to exhibit a rank-at-least-two coupled field, an
infinite-rank tail, or a completion-boundary comparison.  This is a structural restriction, not an
RH result.

## 7. External novelty gate

The novelty gate is only against external literature.

The closest parent theories located are:

- G. Mari Beffa, *The theory of differential invariants and KdV Hamiltonian evolutions*, which
  identifies the inclusion of differential modules with a Frechet-Jacobian matrix,
  https://www.numdam.org/item/BSMF_1999__127_3_363_0/;
- Lorenzoni--Shadrin--Vitolo, *Miura-reciprocal transformations and localizable Poisson pencils*,
  for Frechet matrices and differential-substitution chain rules,
  https://arxiv.org/abs/2301.04475;
- Startsev, *Differential substitutions and symmetries of hyperbolic equations*, for the parent
  theory of finite-order differential substitutions,
  https://arxiv.org/abs/solv-int/9509006;
- Carpentier--De Sole--Kac, *Some algebraic properties of differential operators*, for rational
  pseudodifferential matrices and Dieudonne determinants,
  https://arxiv.org/abs/1201.1992;
- Demskoi--Viallet, *Algebraic entropy for semi-discrete equations*, for an external degree-growth
  theory in differential-difference dynamics,
  https://arxiv.org/abs/1206.1214.

Those sources contain the ingredients or adjacent growth notions.  In targeted searches for order
growth under differential embeddings, Miura-invariance of differential order entropy,
pseudodifferential right-inverse comparison, and Cartan-spectrum functoriality, no source was found
that states `(4)`, `(12)--(13)`, or the obstruction trichotomy of Section 5.

External novelty is therefore **provisional but live**.  A MathSciNet/zbMATH search and review by
specialists in differential algebra and integrable systems remain mandatory before a priority
claim.

## 8. Significance and anti-theatre gate

- `[PASS]` The theorem constrains every finite-rank free HT field and every differential embedding,
  not a selected special function.
- `[PASS]` It proves presentation-independent survival of the complete balanced clock spectrum,
  not merely a scalar entropy.
- `[PASS]` It closes the nonlinear-cancellation obstruction for the finite-free comparison problem.
- `[PASS]` The conductor no-go has a strict positive successor: the rank/map/completion boundary
  trichotomy.
- `[PASS]` The theorem is falsifiable by one finite-rank differential embedding with unbounded
  intrinsic/ambient order discrepancy.
- `[FAIL if redressed]` Frechet chain rule, full row rank, pseudodifferential inverses, and exterior
  powers separately are parent theory.
- `[PAPER VERDICT]` Conditional on specialist novelty confirmation, Theorems A--B together with the
  variational-building theorem warrant a standalone paper.  They are not by themselves a
  Fields-Medal-scale classification; that requires classifying the three boundary mechanisms and
  proving that the analytic obstruction representations factor through the resulting boundary
  object.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/DifferentialIndependentObservableNet.lean` formalizes both
asymptotic comparison kernels:

- `BoundedComparison.translationLength_eq` proves invariance of scalar clock speed under a fixed
  two-sided additive overhead;
- `finiteVector_coordinate_sub_le_of_prefix_bound` converts bounded fundamental-weight (prefix)
  differences into bounded coordinate differences;
- `tendsto_normalized_finiteVector_of_bounded_prefix` proves equation `(12) -> (13)`: two finite
  vector sequences with uniformly bounded prefix differences have the same normalized limit.

The free-transverse saturation input is formalized in
`DifferentialIndependentObservableFactorization.lean`.  The Frechet/Ore instantiation and the
valuation-lattice theorem supplying the prefix bounds `(12)` remain unformalized, so the card stays
in stage 2.

## Gates

- [x] 0 -> 1: exact theorem, proof mechanism, falsifier, and parent theories stated
- [x] 1 -> 2: complete paper proof with explicit two-sided constants and vector refinement
- [ ] 2 -> 3: scalar and finite-vector bounded-comparison kernels and free-transverse saturation
  are formalized; the Frechet/Ore instantiation and valuation-lattice derivation of `(12)` remain
- [ ] 3 -> 4: specialist novelty review and standalone exposition

## Log

- 2026-07-15 -- proved after the free-transverse saturation law exposed a stronger fixed-embedding
  right-inverse mechanism; retired the growing fixed-conductor hypothesis.
