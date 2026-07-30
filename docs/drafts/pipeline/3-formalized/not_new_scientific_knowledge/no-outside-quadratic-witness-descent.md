# A source-natural triangle witness descends through the orientation square

- **ID:** `no-outside-quadratic-witness-descent`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / SOURCE-QUOTIENT BRIDGE
- **Status:** `[PAPER-PROVED] [LEAN-PROVEN] [CLASSICAL MATHEMATICS]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/triangle-fact-orientation-transmutation.md`
- **Existing analytic dependency:**
  `formal/GaloisForLFunctions/HTGeometry/EvenEntireSquareFactor.lean`
- **Existing positive dependency:**
  `source-odd-positivity-square-law.md`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/NoOutsideQuadraticWitnessDescent.lean`
- **Statement:** Every entire scalar reporter invariant under relabeling of the unlabeled triangle
  residual factors through the squared orientation coordinate.

## Goal

Determine the first scalar information that a closed source can publish after its automorphisms
forbid a nonzero orientation value. The result must distinguish an exact quotient theorem from
the physical conjecture that this quotient is quantum probability or spacetime.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and attack
- [x] 1 → 2 fully-proven: dependency-closed proof `[PROVED HERE]`
- [x] 2 → 3 formalized: exact connector theorem, target build, axiom audit
- [ ] 3 → 4 publication-ready: not independently publication-grade

## Setup

Let \(O\cong\mathbb C\) be the complexified orientation line of the unlabeled empty triangle.
The source transposition \(\tau=(01)\) acts by

\[
\tau a=-a.
\tag{QW1}
\]

Let \(\iota:O\to M_3(\mathbb C)\) send \(a\) to the oriented triangle residual with coefficient
\(a\). Let

\[
\mathcal R:M_3(\mathbb C)\longrightarrow\mathbb C
\]

be a scalar reporter invariant under every source relabeling:

\[
\mathcal R(\sigma\cdot X)=\mathcal R(X).
\tag{QW2}
\]

Its restriction to the residual line is

\[
r(a)=\mathcal R(\iota(a)).
\tag{QW3}
\]

## Theorem: no-outside quadratic witness descent

`[PROVED HERE]`

Assume \(r\) is entire. Then:

1. \(r\) is even;
2. the orientation square
   \[
   q(a)=a^2
   \tag{QW4}
   \]
   is unchanged by the source transposition; and
3. there is an entire function \(R:\mathbb C\to\mathbb C\) such that
   \[
   r(a)=R(a^2)
   \qquad\text{for every }a\in\mathbb C.
   \tag{QW5}
   \]

Thus every regular scalar fact obtainable from the unchosen orientation line is a reading of its
quadratic quotient coordinate.

### Proof

The triangle transmutation theorem gives

\[
\tau\cdot\iota(a)=\iota(-a).
\]

Source invariance `(QW2)` therefore implies

\[
r(-a)
=\mathcal R(\iota(-a))
=\mathcal R(\tau\cdot\iota(a))
=\mathcal R(\iota(a))
=r(a).
\tag{QW6}
\]

Hence \(r\) is even. Also \((-a)^2=a^2\), so `(QW4)` is source invariant. The
even-entire square-factor theorem constructs an entire \(R\) by retaining the even Taylor
coefficients of \(r\) and halving their indices. It proves \(R(a^2)=r(a)\) without choosing a
global square-root branch. This is `(QW5)`. \(\square\)

## Exact interpretation

The theorem upgrades the triangle no-selection result:

```text
unlabeled source
  -> orientation residual a transforms as a ↦ -a
  -> no nonzero source-natural linear orientation value
  -> every entire source-natural scalar reporter reads only a².
```

The square is not selected because it is aesthetically simple. It is the quotient coordinate
through which every entire scalar reporter of this sign residual descends.

The existing source-odd positivity theorem supplies an independent compatible wall:

1. a nonzero positive-semidefinite law cannot itself be source odd;
2. a source-odd transfer \(D\) has positive source-even reciprocal squares
   \(D^\dagger D\) and \(DD^\dagger\).

Together the two exact results say:

```text
source symmetry forbids publishing the odd value;
regular invariant observation descends through a square;
positive observation survives as a reciprocal Gram square.
```

## Hostile boundaries

This theorem does **not** prove:

- that physical reporters must be entire;
- that \(a^2\) is a probability, norm, metric, or causal interval;
- that a real sign quotient generates complex scalars, a dagger, or positivity;
- that a scalar square uniquely becomes the Hermitian matrix square \(X^\dagger X\);
- that a Gram cone is physically spacetime;
- that comparison of neighboring square roots yields gravity or gauge forces; or
- that the law has a continuum dynamics or observable prediction.

The analytic factorization is established invariant theory in one variable. The source-specific
gain is only the exact dependency chain from the unlabeled self-witness triangle to its quadratic
public quotient.

## Strongest physical conjecture exposed

`[CONJECTURE — NOT SCIENTIFIC KNOWLEDGE]`

> **The universe has no outside. Reality must witness itself. What it cannot choose, it must
> square.**

Mathematical open core:

> Prove that iterative source-only promotion upgrades the scalar sign quotient \(a^2\) uniquely to
> a positive Hermitian reciprocal square, and that compositional comparison of its local square
> roots uniquely yields quantum probability, \(3+1\) causal spacetime, gravity, and exactly the
> Standard Model gauge sectors.

The first sentence is public language. Only `(QW1)`--`(QW5)` are proved.

## Lean certificate

`[LEAN-PROVED]`

Exact declarations:

- `TriangleRelabelInvariantReporter`
- `triangleResidualReport`
- `triangleOrientationQuadraticWitness`
- `triangleOrientationQuadraticWitness_neg`
- `triangleResidualReport_even`
- `triangleResidualReport_exists_entire_squareFactor`

Foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/NoOutsideQuadraticWitnessDescent.lean
lake build GaloisForLFunctions.HTGeometry.NoOutsideQuadraticWitnessDescent
```

The final target build completed all 8,657 jobs. `#print axioms` reports only project-baseline
`propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-07-30 — combined triangle orientation transmutation with even-entire square descent.
- 2026-07-30 — isolated quadratic public quotient as exact source-symmetry consequence.
- 2026-07-30 — kept sign square, Hermitian positive square, and physical spacetime interpretation
  as three distinct layers.
- 2026-07-30 — formalized source-invariant reporter evenness and entire square descent; direct
  check, final target build, and axiom audit passed.
