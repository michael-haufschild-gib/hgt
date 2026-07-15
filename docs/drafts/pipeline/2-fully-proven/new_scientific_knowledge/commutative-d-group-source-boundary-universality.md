# Commutative D-group source-boundary universality

- **ID:** `commutative-d-group-source-boundary-universality`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / abstract formal core open
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every finite family of observables valued in a finite-dimensional commutative
  algebraic `D`-group and translated by an arbitrary, possibly noncommuting source family has a
  completely linear source-boundary differential polymatroid.  The sharp kernel carries no hidden
  hypertranscendental rank.

## Setup

Let `C -> K -> L` be a tower of ordinary differential fields of characteristic zero, with `C` a
field of differential constants.  Let

```text
tau_i   : K ~= K,
sigma_i : L ~= L                                      (i in I)
```

be compatible differential-field automorphisms.  Assume that every `sigma_i` fixes `C` and that
the common fixed field in `L` is exactly `C`.  No multiplication law or pairwise commutativity is
assumed for the source family.

Let `(G,s)` be a connected commutative algebraic `D`-group of dimension `d` over `C`, with
algebraic logarithmic derivative

```text
ell_s : G(L) -> Lie(G)(L).
```

Choose a `C`-basis of `Lie(G)`.  Let `g_a in G(L)` and `a_(i,a) in G(K)` satisfy

```text
sigma_i(g_a) = a_(i,a) * g_a.                          (1)
```

Write

```text
z_(a,j)       = coordinate_j(ell_s(g_a)),
omega_(i,a,j) = coordinate_j(ell_s(a_(i,a))).          (2)
```

The logarithmic derivative is a differential-rational group homomorphism because `G` is
commutative.  Equivariance and (1) therefore give

```text
sigma_i(z_(a,j)) = z_(a,j) + omega_(i,a,j).             (3)
```

Define the simultaneous source boundary

```text
Q_Sigma(K) = K^I / {(tau_i(k)-k)_i : k in K},
V_Sigma(K) = Q_Sigma(K) tensor_(C[D]) C(D).             (4)
```

## Theorem A: logarithmic linearization preserves all differential rank

For every finite set `S` of observable labels, let

```text
F_S = K<coordinates of g_a : a in S>_D,
E_S = K<z_(a,j) : a in S, 1 <= j <= d>_D.
```

Then

```text
dtrdeg_K F_S = dtrdeg_K E_S.                            (5)
```

### Proof

Every coordinate of `ell_s(g_a)` is differential rational in the coordinates of `g_a`, so
`E_S subset F_S`.  Conversely, each `g_a` is a solution over `E_S` of the first-order algebraic
differential system

```text
ell_s(Y) = ell_s(g_a).                                  (6)
```

Thus every coordinate of `g_a` is differentially algebraic over `E_S`; hence `F_S/E_S` is
differentially algebraic and (5) follows.  This argument is independent of genericity of the
points.

## Theorem B: complete source-boundary rank formula

For every finite `S`,

```text
dtrdeg_K F_S
  = dim_(C(D)) span{[omega_(a,j)] : a in S, 1 <= j <= d}
      in V_Sigma(K).                                    (7)
```

Equivalently, the full coordinate family of the `g_a`, `a in S`, is differentially dependent
beyond rank `r` exactly to the extent that the boundary classes in (7) have linear rank `r`.
In particular, it is differentially dependent if and only if there are operators

```text
P_(a,j)(D) in C[D], not all zero,
```

and one `k in K` such that for every source direction `i`,

```text
tau_i(k)-k
  = sum_(a,j) P_(a,j)(D) omega_(i,a,j).                 (8)
```

### Proof

Equation (3) places the scalar coordinate family `z_(a,j)` under the arbitrary-family additive
Ostrowski theorem.  That theorem identifies every differential dependence among the `z_(a,j)`
with exactly one simultaneous coboundary relation (8), and identifies every subfamily rank with
the dimension of the corresponding span in (4).  Theorem A transfers that rank, subset by
subset, from the logarithmic coordinates back to the `G`-valued points.  This proves (7) and (8).

Changing the `C`-basis of `Lie(G)` applies an invertible constant matrix to all coordinates, so
the rank in (7) is intrinsic.

## Corollary: the sharp kernel is not a hidden HT reservoir

Let

```text
G^sharp = ker(ell_s).
```

Every point of `G^sharp` satisfies the first-order algebraic differential equation
`ell_s(Y)=0`, hence is differentially algebraic over the field of definition.  More generally,
every fibre of `ell_s` is a differential-algebraic torsor under `G^sharp` and has differential
transcendence degree zero over its image point.  Therefore:

```text
all hypertranscendental rank of a commutative D-group source primitive
is visible in its logarithmic source boundary; none is stored in G^sharp. (9)
```

The sharp kernel may retain finite-rank model-theoretic, isogeny, or embedding information.  It
cannot supply an additional hypertranscendental-capacity term.

## Linearization-horizon dichotomy

The theorem gives a sharp boundary for the proposed unified theory.

`[NO-GO]` A finite-dimensional commutative algebraic `D`-group cannot produce genuinely nonlinear
hidden hypertranscendence.  Its nonlinear group geometry and sharp fibres are
differential-algebraic decoration over a complete linear source-boundary invariant.

`[POSITIVE THEOREM]` This is not merely a failure: every such presentation admits an exact and
intrinsic nonlinear-to-linear collapse (7), for arbitrary noncommuting source families and every
finite subfamily simultaneously.

Consequently, any hypertranscendental phenomenon not classified by (7) must cross at least one
of the following horizons:

1. no faithful finite-dimensional commutative `D`-group presentation exists;
2. the logarithmic derivative has nontrivial adjoint twisting because the group is
   noncommutative;
3. the correct envelope is genuinely infinite-dimensional or pro-algebraic;
4. the source action is not by base-field increments.

This locates the next unknown object: it is not a mysterious extra radical inside the
commutative theory, but the obstruction to commutative finite-dimensional logarithmic
linearization itself.

## Bold successor: curved source-boundary conjecture

`[CONJECTURE]` Every finite-source hypertranscendental observable has a minimal differential
Tannakian source envelope.  Its logarithmic derivative is an affine local system

```text
sigma_i(z) = Ad(a_i) z + ell_s(a_i),                    (10)
```

and its complete differential-algebraic polymatroid is determined by a localized twisted
source-cohomology object together with the Tannakian tensor relations of the adjoint local
system.  The commutative theorem is exactly the flat trivial-adjoint case.

The universal nonlinear invariant is then the adjoint holonomy/curvature of (10), not an
additional collection of jets.  Continuation and monodromy should be direct realizations of this
holonomy; positivity, spectral completeness, and boundary-condition uniqueness should be
polarized realization conditions on the same twisted object.

**Falsifier:** two faithful minimal source envelopes with the same twisted source-cohomology and
the same Tannakian tensor relations but different differential-algebraic rank functions, or a
finite-source observable admitting no minimal envelope even up to pro-algebraic equivalence.

## Novelty gate

Classical inputs:

- Buium--Pillay algebraic `D`-groups and logarithmic differential equations;
- the homomorphism identity for the logarithmic derivative of a commutative `D`-group;
- the fact that `G^sharp` is the kernel of a first-order logarithmic differential equation;
- one-operator Kolchin--Ostrowski and parameterized differential-Galois rank theorems.

New candidate surface:

- an arbitrary, possibly noncommuting family of compatible source automorphisms;
- one simultaneous base coboundary in every source direction;
- the complete rank function for every finite family of `G`-valued points;
- the exact elimination of the sharp kernel as a possible hidden HT-capacity layer.

No checked source states (7)--(9) in this arbitrary-source form.  This is affirmative evidence,
not a proof of absence; specialist and bibliographic review remain required.

## Significance and anti-theatre gate

- `[PASS]` The theorem strictly contains the split `G_a^r x G_m^s` theorem.
- `[PASS]` It classifies a complete differential polymatroid, not one dependence.
- `[PASS]` It kills a proposed radical layer and replaces it with a stronger exact theorem.
- `[PASS, PROVISIONAL]` The arbitrary-source theorem surface was not located in the parent
  literature.
- `[OPEN]` A concrete analytic example whose minimal source envelope has nontrivial adjoint
  holonomy.
- `[PARTIAL FORMALIZATION]` The exact singleton logarithmic-linearization and simultaneous
  coboundary criterion are formalized in `SourceLogarithmicBoundary`; algebraic `D`-groups
  themselves are absent from current Mathlib.
- `[FAIL if oversold]` The proof is short once classical `D`-group logarithmic geometry and the
  project additive theorem are imported.  It is significant progress, not a Fields-Medal result.

## RH pressure test `[CONJECTURE]`

If zeta's relevant source envelope were commutative and finite-dimensional, Theorem B would force
all of its hypertranscendental capacity into an ordinary linear boundary module; a genuinely
nonlinear common obstruction spectrum could not come from a hidden Manin/sharp layer.  The live
hypothesis is therefore that the common RH obstruction, if real, is the polarized degeneracy
spectrum of a nontrivial twisted/pro-source envelope.  This is a research hypothesis, not an RH
result.

## References checked

- A. Buium, *Differential Algebraic Groups of Finite Dimension*, 1992.
- D. Bertrand, *Algebraic D-groups and non-linear differential Galois theory*, 2009 notes.
- D. Bertrand and A. Pillay, *A Lindemann--Weierstrass theorem for semi-abelian varieties over
  function fields*, JAMS 23 (2010), 491--533.
- C. Hardouin and M. F. Singer, *Differential Galois Theory of Linear Difference Equations*,
  Math. Ann. 342 (2008), 333--377.

## Log

- 2026-07-15 -- The commutative `D`-group conjecture collapsed to the exact rank theorem; the
  proposed character-invisible HT radical was ruled out and replaced by the linearization-horizon
  dichotomy.
