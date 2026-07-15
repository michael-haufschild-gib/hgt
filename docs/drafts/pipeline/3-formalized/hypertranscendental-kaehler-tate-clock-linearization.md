# The hypertranscendental jet tower has a canonical Kähler--Tate clock linearization

- **ID:** `hypertranscendental-kaehler-tate-clock-linearization`
- **Stage:** 3-formalized
- **Type:** GENERAL HT THEOREM / SOURCE-POINTED IND--PRO GEOMETRY
- **Scientific status:** `[PROVED ON PAPER] [LEAN-FORMALIZED] [NOVELTY PROVISIONAL]`
- **Parent:** `../3-formalized/hypertranscendental-clock-observable-boundary.md`
- **Statement:** The one-way rational jet tower of a pointed hypertranscendental element has a
  canonical filtered Kähler module whose clock principal symbol is the unilateral shift through
  rank-one boundary lines. Its discrete associated graded and full algebraic dual form a
  canonical self-dual elementary Tate object.

## Setup

Let

```text
(C,0) ⊆ (F,delta) ⊆ (E,delta)
```

be differential fields of characteristic zero, with `C` contained in the constant field of
`F`. Let `x in E` be hypertranscendental over `F`, put

```text
j_n=delta^n x,
P_infinity=F(j_0,j_1,...),
Omega=Omega_(P_infinity/C).                                (1)
```

The point `x` is part of the datum. This is essential: the unpointed differential field is blind
to affine translation and cannot select a zero fibre.

Let `Omega_F` denote the image of
`P_infinity tensor_F Omega_(F/C)` in `Omega`. Define the increasing clock filtration

```text
W_N=Omega_F + sum_(0<=n<N) P_infinity d(j_n),
L_N=W_(N+1)/W_N.                                           (2)
```

## The Kähler clock theorem `[PROVED]`

There is a canonical decomposition

```text
Omega = Omega_F direct_sum
        direct_sum_(n>=0) P_infinity d(j_n).               (3)
```

Consequently every `L_N` is a one-dimensional `P_infinity`-vector space, intrinsically attached
to the field interval `P_N ⊆ P_(N+1)`. It is generated in jet coordinates by the class of
`d(j_N)`, but the line itself does not depend on a rational coordinate chosen for that simple
transcendental extension.

The derivation `delta` induces the Lie derivative on Kähler one-forms,

```text
Lie_delta(a db)=delta(a) db + a d(delta b).                (4)
```

It satisfies

```text
Lie_delta(W_N) ⊆ W_(N+1).                              (5)
```

Therefore its degree-one principal symbol is well defined:

```text
sigma_N : L_N -> L_(N+1),
sigma_N([omega])=[Lie_delta(omega)].                       (6)
```

For every `N`,

```text
sigma_N(a [d(j_N)])=a [d(j_(N+1))].                       (7)
```

Hence every `sigma_N` is a canonical `P_infinity`-linear isomorphism. The lower-order coefficient
term `delta(a)d(j_N)` disappears in the next associated-graded quotient; the only principal clock
term is `a d(j_(N+1))`.

## Proof

Hypertranscendence makes the complete jet family `(j_n)_(n>=0)` algebraically independent over
`F`. Thus `P_infinity` is the fraction field of the polynomial algebra

```text
F[X_0,X_1,...].                                           (8)
```

Kähler differentials of the polynomial algebra over `C` split as the base-changed module of
`F/C` differentials plus the free module on `dX_n`. Localization from the polynomial algebra to
its fraction field preserves Kähler differentials and this direct sum. Transport through the
evaluation isomorphism `X_n |-> j_n` proves `(3)`. Equations `(2)` and `(3)` prove that each
successive quotient `L_N` is a line.

Because `delta` kills `C`, formula `(4)` is well defined on the Kähler presentation. The differential
algebra law gives `delta(F) ⊆ F` and `delta(j_n)=j_(n+1)`. Hence `(4)` sends the base summand to
itself and sends

```text
a d(j_n) |-> delta(a)d(j_n)+a d(j_(n+1)),                 (9)
```

which proves `(5)`. If a representative of a class in `L_N` is changed by an element of `W_N`,
its Lie derivative changes by an element of `W_(N+1)`, so `(6)` is well defined. Reducing `(9)`
modulo `W_(N+1)` gives `(7)`, and `(7)` proves bijectivity. `QED`

## Canonical Tate completion

Put

```text
I_x=direct_sum_(N>=0) L_N,
P_x=product_(N>=0) L_N^dual.                              (10)
```

Finite support makes the evaluation pairing

```text
<a,p>=sum_N p_N(a_N)                                      (11)
```

well defined and identifies `P_x` with the full algebraic dual of `I_x`. The clock symbols
`sigma_N` assemble into the forward shift `S_x` on `I_x`; their duals assemble into the backward
shift `B_x` on `P_x`. They obey

```text
<S_x a,p>=<a,B_x p>,                                      (12)

0 -> I_x ->S_x I_x -> L_0 -> 0,
0 -> L_0^dual -> P_x ->B_x P_x -> 0.                      (13)
```

Thus

```text
T_x=P_x direct_sum I_x                                   (14)
```

with the skew evaluation form is a self-dual elementary Tate object. The two exact sequences in
`(13)` say that the infinite clock has one boundary line: forward cokernel and backward kernel are
dual faces of the same seam.

The construction is functorial for differential-field embeddings preserving `C`, `F`, and the
pointed element `x`: such a map carries `j_n` to `j_n`, commutes with the universal differential
and with `(4)`, preserves `W_N`, and intertwines every `sigma_N`.

## Scientific meaning

This theorem resolves the first structural contradiction in the unified-field program:

- hypertranscendence forbids every backward field map;
- self-dual obstruction theory requires a backward face;
- Kähler linearization supplies that face by duality, not by retracting the field.

The resulting object is static. `delta` orders observables and defines a principal symbol; it is
not interpreted as physical time or a generative flow.

The theorem also makes the phrase

```text
infinite algebraic clock capacity concentrated on a thin constraint boundary
```

literal: the capacity is the countable family of independent lines `L_N`, while the clock index
at each cut is the single dual pair `coker(S_x)=L_0` and `ker(B_x)=L_0^dual`.

## Affine-calibration theorem `[PROVED AND LEAN-FORMALIZED]`

The vector Tate clock is not yet the constrained source object. Relative Kähler differentials
erase base-valued translations exactly. For every `c in F` and every `n`,

```text
d_F(delta^n(x+c))=d_F(delta^n x).                         (16)
```

If `a in F` is derivation-constant, then for every `b in F`,

```text
d_F(delta^n(a x+b))=a d_F(delta^n x).                     (17)
```

Thus the complete Kähler flag and its Tate completion retain tangent capacity but not affine
calibration. Translation changes the clock reading without changing a single cotangent clock
observable; constant rescaling changes every graded line by one common unit and hence gives an
isomorphic uncalibrated Tate clock. Neither a vector Tate object nor its projectivization can
recover the source normalization.

This is a fourth structural no-go, paired with a positive replacement. The source object must be
an **affine self-dual Tate clock**: a torsor `A_x` modeled on `T_x`, together with a calibrated
source section and a self-dual Lagrangian lattice. Its linear tangent object is the canonical
`T_x`; its affine section carries precisely the origin and unit erased by `(16)`--`(17)`.

## What is parent theory and what may be new

The following are parent ingredients:

- the Kähler differential module of a purely transcendental field;
- localization/base change for Kähler differentials;
- Lie derivative on one-forms;
- Ind, Pro, and elementary Tate objects;
- Sato Grassmannians, lattice index, dimension torsors, and determinant gerbes.

The candidate-new theorem package is the canonical passage

```text
pointed HT jet tower
  -> filtered Kähler clock with rank-one graded symbol
  -> self-dual Tate boundary object,                              (15)
```

together with the no-backward-field theorem which makes the Ind--Pro variance necessary rather
than optional. Targeted searches found no exact construction connecting a hypertranscendental
jet filtration to a self-dual Tate object through the principal symbol of the Kähler Lie
derivative. This is a provisional absence claim, not a priority claim.

Primary parent anchors:

- Braunling, Groechenig, and Wolfson, `Tate Objects in Exact Categories`,
  https://arxiv.org/abs/1402.4969;
- Previdi, `Sato Grassmannians for generalized Tate spaces`,
  https://arxiv.org/abs/1002.4863;
- Braunling, Groechenig, Heleodoro, and Wolfson, `On the normally ordered tensor product and
  duality for Tate objects`, https://arxiv.org/abs/1709.07962;
- the generalized-differentials and parameterized-prolongation parents already audited in the
  clock-observable-boundary card.

## Unified-obstruction consequence `[CONJECTURE]`

The theorem constructs the universal self-dual tangent boundary but not the source-specific
calibration. A constrained HT source must next define an affine self-dual Tate torsor `A_x`, a
calibrated Lagrangian lattice `Lambda_x`, and a distinguished determinant section. Only then can
the proposed dictionary be tested:

| Representation | Required image of the same Tate datum |
|---|---|
| boundary conditions | lattices in the Sato Grassmannian of `T_x` |
| spectral incompleteness | nontransversality of `Lambda_x` with the reference lattice |
| continuation/monodromy | descent and determinant-gerbe holonomy of `Lambda_x` |
| positivity failure | Hermitian orientation of the self-dual lattice pair |
| compactness escape | image of the lattice class in a Calkin/corona realization |

The rows are proof obligations. Generic Tate theory already relates lattice index, determinant,
and duality; new science requires the same source-selected `Lambda_x` to factor through actual
analytic constructions.

## Lean status

`HypertranscendentalClockBoundary.lean` now formalizes:

- algebraic independence and fresh transcendence of every jet layer;
- linear independence of all universal jet Kähler covectors over the full rational jet field;
- exact finite clock erosion;
- nonexistence of a total algebra homomorphism from a transcendental clock step back to its base;
- exact affine translation blindness and constant-scaling covariance of every relative Kähler
  jet covector;
- the universal Ind forward shift and Pro backward shift;
- the exact rank-one range/kernel descriptions;
- shift/coshift adjointness under the restricted evaluation pairing.

`HypertranscendentalKaehlerClockSymbol.lean` formalizes the remaining Kähler-clock layer:

- the absolute decomposition `(3)` into the base-differential image and the free countable jet
  covectors, including injectivity of the base-change map;
- the universal Kähler connection induced by a derivation preserving the base and its
  specialization to the full hypertranscendental jet field;
- the exact formula `(4)` and preservation `(5)` of the intrinsic absolute filtration;
- identification of each preceding cut with the kernel of its top-coordinate map and
  surjectivity of that coordinate, which gives the canonical one-dimensional successive layer;
- canonical coordinate equivalences for the homogeneous clock lines and the principal-symbol
  isomorphism `(6)`--`(7)`;
- equality of the intrinsic Kähler Lie operator with the transported free-clock operator and
  equality of the principal symbol with the next homogeneous Lie projection;
- invariance of the base-differential summand and compatibility of absolute-to-relative
  reduction with the Kähler connection.

The new module was compiled once because its `.olean` was absent, then verified directly:

```text
lake build +GaloisForLFunctions.HTGeometry.HypertranscendentalKaehlerClockSymbol
lake env lean GaloisForLFunctions/HTGeometry/HypertranscendentalKaehlerClockSymbol.lean
```

No full build or broad lint was run.

## Gates

- [x] no-backward-field theorem proved and formalized
- [x] coordinate-free Kähler boundary lines defined
- [x] Kähler direct-sum decomposition proved on paper
- [x] filtered Lie derivative and rank-one principal shift proved on paper
- [x] self-dual Tate completion and exact clock index proved on paper
- [x] universal algebraic shift/coshift skeleton formalized in Lean
- [x] infinite Kähler jet-covector independence formalized in Lean
- [x] affine-origin blindness and constant-unit covariance formalized in Lean
- [x] primary Tate-theory collision audit completed
- [x] base-summand Kähler decomposition and principal symbol formalized in Lean
- [ ] independent differential-algebra and Tate-category specialist audit
- [ ] actual source-selected affine torsor, calibration, and self-dual lattice constructed
- [ ] three analytic obstruction representations proved to preserve one source class
