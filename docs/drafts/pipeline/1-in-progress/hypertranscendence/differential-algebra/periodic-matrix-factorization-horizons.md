# Before There Was Time: hypertranscendence horizons from periodic matrix factorizations

- **ID:** `periodic-matrix-factorization-horizons`
- **Stage:** 1-in-progress
- **Type:** THEOREM / MATRIX FACTORIZATION / HYPERTRANSCENDENCE / QFT
- **Scientific status:** `[CONIC CASE PAPER-PROVEN] [LEAN IN PROGRESS] [NOVELTY PROVISIONAL]`
- **Paper lane:** *Before There Was Time: Matrix Factorizations as Holographic Descendants*

## 1. Periodic factorization principle `[CONJECTURE -- GENERAL]`

Let `V` be a finite law space and let `F` be a homogeneous horizon equation.  Suppose a graded
state module carries a periodic linear operator pencil `T(c)` such that after `p` grade-raising
steps

```text
T(c)^p = F(c) S^p,                                                    (1)
```

where `S` is the grade shift and the intermediate cyclic states are nonzero off `F=0`.  Then a
root state has finite orbit when `F(c)=0` and an infinite linearly independent orbit when
`F(c)≠0`.  Passing to the symmetric observable algebra turns the linear state action into field
derivations, so `F=0` is the exact complete ordinary differential-algebraicity horizon of one
observable.

Equation `(1)` is a dynamical form of a matrix factorization.  It replaces the free-word tail by
a finite-rank periodic descendant sector.

## 2. The conic construction `[PAPER-PROVEN]`

Take `V=K^3` and

```text
F(c0,c1,c2)=c0*c2-c1^2.
```

Define two linear `2×2` pencils

```text
M(c) = [[c0,c1],[c1,c2]],
N(c) = [[c2,-c1],[-c1,c0]].                                          (2)
```

They satisfy

```text
N(c)M(c)=M(c)N(c)=F(c) I_2.                                          (3)
```

On the graded state space `⊕_(n≥0) K^2`, let `T(c)` shift one grade, applying `M(c)` from even to
odd grades and `N(c)` from odd to even grades.  Then

```text
T(c)^2=F(c) S^2.                                                      (4)
```

Starting from `(1,0)` in grade zero, `F(c)=0` kills the orbit after two steps.  If `F(c)≠0`, every
orbit vector is nonzero and lies in a new grade, hence the complete orbit is linearly independent.
The induced symmetric-algebra derivations therefore have exact horizon `F=0`.

## 3. The factorization forces maximal commutator rank `[PAPER-PROVEN]`

Write `T(c)=c0*T0+c1*T1+c2*T2`.  On every even grade the three basic commutators act by

```text
[T0,T1] =  2 E21,
[T0,T2] =  E22-E11,
[T1,T2] = -2 E12.                                                     (5)
```

These matrices are linearly independent in characteristic zero.  Hence

```text
Λ²(K^3) -> End(⊕ K^2),      ei∧ej |-> [Ti,Tj]
```

is injective.  The periodic conic realization has commutator rank three, even though the
line-contact lower obstruction only forces rank at least two.

This does not prove that rank two is impossible for every conic realization.  It proves that the
canonical linear matrix factorization lands at the maximal endpoint and suggests that higher
prolongation, not line contact alone, may raise the true minimum.

## 4. Why this is scientifically different

The universal free-word theorem realizes arbitrary horizons with an infinite branching tail.
The conic theorem realizes a nonlinear horizon with only two internal states per grade and period
two.  Hypertranscendence is produced by infinite grade depth, not by increasing transverse state
rank.

This creates a bridge to hypersurface singularity theory: matrix factorizations, maximal
Cohen--Macaulay modules, and periodic resolutions become finite-memory generators of exact
hypertranscendence horizons.  The new classification problem is:

```text
Which projective schemes admit finite-rank periodic horizon realizations,
and what commutator ranks are forced by their factorization categories?              (6)
```

## 5. QFT meaning `[CONJECTURE]`

Matrix factorizations are standard algebraic objects in Landau--Ginzburg models and D-brane
categories.  Here the same periodic structure generates a complete hypertranscendence boundary.
The finite internal packet is a candidate pretemporal descendant sector; the projective equation
is the holographic horizon; and the coefficient-operator commutators are its algebraic quantum
incompatibility channels.

This is not yet a physical QFT.  A star representation, Hilbert completion, domains, state,
positivity, and locality remain external.  The block-shift construction is nevertheless much
closer to an analytic operator model than the free rational-word field.

## 6. Novelty and parent gate

Known ingredients not claimed as novelty:

- Eisenbud matrix factorizations and two-periodic resolutions;
- Clifford modules for nondegenerate quadrics;
- matrix factorizations in Landau--Ginzburg models and D-brane categories;
- symmetric-algebra derivations induced by linear state actions.

Exact searches found no source using a periodic matrix factorization to realize the exact
varying-derivation ordinary hypertranscendence horizon of one observable, or relating its
factorization category to minimal law-commutator rank.  This is an absence-of-hit result, not a
priority certificate.

Dangerous comparison points:

- D. Eisenbud's matrix-factorization/periodic-resolution theory;
- Landau--Ginzburg matrix-factorization categories;
- support varieties and stable support sets over complete intersections;
- determinantal representations of projective hypersurfaces.

## 7. RH impact

The construction supplies a finite-memory architecture that an arithmetic horizon model could in
principle use instead of a free tail.  No completed `L`-function is currently equipped with the
required periodic factorization, so this is a model class and source filter rather than an RH
proof step.

## 8. Lean route

1. Formalize alternating two-step linear pencils and the identity `(3)`.
2. Formalize the graded block-shift operator and prove `(4)`.
3. Prove exact linear-independence/dependence of the root orbit.
4. Lift the state action to symmetric-algebra derivations and prove the exact conic horizon.
5. Prove the commutator matrices `(5)` give an injective exterior symbol.
6. Axiom-audit and narrow-build the final theorem surface.
