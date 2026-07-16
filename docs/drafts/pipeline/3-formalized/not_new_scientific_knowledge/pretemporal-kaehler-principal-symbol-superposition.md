# Before There Was Time: Kähler principal-symbol superposition

- **ID:** `pretemporal-kaehler-principal-symbol-superposition`
- **Stage:** 3-formalized
- **Type:** CONJECTURE / DIFFERENTIAL ALGEBRA / PRINCIPAL-SYMBOL THEOREM
- **Scientific status:** `[TWO-DIRECTION THEOREM LEAN-PROVEN] [KNOWN PARENT LOCATED]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [FINITE-FAMILY PACKAGING OPEN]`
- **Paper lane:** *Before There Was Time: The Holographic Horizon and the Collapse of Commuting Laws*

## Theorem proved here

Let `K ⊆ L` be fields of characteristic zero, let `δ_i : L → L` be a finite family of pairwise
commuting `K`-derivations, and fix `x ∈ L`.  For `c = (c_i) ∈ K^ι`, write

```text
D_c = Σ_i c_i δ_i.
```

The two-direction theorem is

```text
(∀ i, x is ordinarily differential-algebraic over K for δ_i)
  → (∀ c, x is ordinarily differential-algebraic over K for D_c).       (1)
```

Equivalently, for a pairwise commuting law space the ordinary differential-algebraic directions
of one observable form a vector subspace.  The two-direction addition theorem is the irreducible
core; scalar closure is already known.

## General principal-symbol engine `[LEAN-PROVEN FOR TWO DIRECTIONS]`

Put `Ω = Ω[L/K]` and `ω = d x`.  Every `δ_i` induces the Kähler connection

```text
∇_i(a db) = δ_i(a) db + a d(δ_i b).
```

Pairwise commutation of the derivations should imply pairwise commutation of the connections.
Ordinary differential algebraicity in direction `i` is equivalent to a monic finite recurrence

```text
∇_i^(m_i) ω ∈ span_L {∇_i^r ω : r < m_i}.                  (2)
```

The principal-symbol theorem proves that `(2)` in two coordinates traps the full mixed
connection orbit in the finite rectangle

```text
span_L {∏_i ∇_i^(a_i) ω : 0 ≤ a_i < m_i}.                  (3)
```

Hence its dimension is at most `∏_i m_i`.  Every directional orbit
`ω, ∇_c ω, ∇_c² ω, ...` lies in `(3)`, so its first `1 + ∏_i m_i` members are linearly dependent.
Kähler independence then gives `(1)` with a uniform finite order bound.

This is stronger than the current first-prolongation obstruction: it is a complete involutivity
theorem for one observable and every finite commuting pencil.

## Why this is the physical theorem

`[CONJECTURE]` In a pretemporal observable algebra, commuting law directions behave like compatible
kinematic choices before a time ray is selected.  The theorem would say that finite generative law
in each coordinate cannot produce a hypertranscendental generic superposition: commuting laws
collapse together.  A nonlinear holographic dependence horizon for one observable would therefore
certify at least one of noncommutativity, multi-observable syzygies, nonlinear/layer-dependent
action, or a genuinely singular gauge/BRST prolongation.  No cosmological or QFT identification is
claimed without an independently constructed observable algebra and constraint centralizer.

## Counterexample attacks

The statement must be tested against:

1. singular differential equations whose separant vanishes at the chosen solution;
2. coefficients not fixed by the complementary derivations;
3. positive characteristic, where Kähler dependence need not detect algebraic dependence;
4. noncommuting derivations, where arbitrary projective horizons are already realizable;
5. infinitely many law directions, where the finite-rectangle bound is unavailable;
6. several observable roots, where syzygies may retain nonlinear horizon geometry.

The Kähler-connection proof is designed to survive items 1 and 2 without division by a separant.
Items 3--6 are expected sharp boundaries, not defects in the finite characteristic-zero theorem.

## Novelty and anti-theatre gate

The following are classical and are not novelty claims: Kähler criteria for algebraic
independence, Lie derivatives on differentials, commuting derivations, Ore-module recurrences,
Kolchin dimension polynomials, characteristic sets, Janet--Riquier/Spencer involutivity, and finite
codimension of a monomial complete intersection.

An exact parent has been located.  Joris van der Hoeven, *Computing with D-algebraic power series*,
Proposition 24, proves for finitely many pairwise commuting partial derivations that separate
D-algebraicity is equivalent to finite transcendence degree of the complete mixed differential
algebra.  The proof uses minimal Ritt-rank equations, nonzero separants, and the same finite
multi-index rectangle.  Proposition 33 then explicitly applies arbitrary constant linear
combinations of the partial derivations under monomial transformations.  This removes the
superposition statement and finite-rectangle mechanism from the novelty surface.

The Lean theorem is still useful: it is field-theoretic rather than restricted to power series,
derives the rectangle through Kähler connections without dividing by separants, and exposes the
rank bound `≤ m n`.  Those are formal and expository improvements, not field-shattering new
mathematics.  This card must therefore move to `not_new_scientific_knowledge` after the formal
verification gate.

The positive successor is a curvature theorem outside the commuting parent: quantify how the
secant failures of a nonlinear ordinary-DA horizon force and reconstruct nonzero commutator data on
the observable-generated differential field.  Merely taking the contrapositive of superposition is
also bridge material; the new theorem must recover more than the fact that some bracket is nonzero.

## RH impact

This is not an RH theorem.  It would impose a strong source filter: any one-function completed-`L`
model whose arithmetic law directions commute has either an entirely linear ordinary-DA horizon or
must expose additional roots, curvature/noncommutativity, or singular gauge data.  It cannot by
itself locate zeros or supply an RH source producer.

## Lean route

1. [DONE] Prove Kähler connections commute when their base derivations commute.
2. [DONE] Formalize the two-operator semilinear finite-rectangle theorem and rank bound.
3. [DONE] Derive monic Kähler recurrences from failure of algebraic independence of each pure jet.
4. [DONE] Prove the two-direction differential-algebraic addition theorem.
5. Induct over a finite family and obtain the product bound.
6. Deduce that the full ordinary-DA direction horizon is a submodule.
7. [DONE] Run an isolated target build, formal lint, and axiom audit before moving this card.

No theorem may assume the desired directional dependence, finite mixed transcendence degree, or an
invariant finite-dimensional mixed state space.

## Lean surface and verification

`formal/GaloisForLFunctions/HTGeometry/CommutingKaehlerPrincipalSymbol.lean` proves:

- `kaehlerLieDifferential_commute`;
- `exists_pos_kaehlerLie_recurrence`;
- `kaehlerMixedJet_mem_rectangle`;
- `finrank_kaehlerJetRectangle_le`;
- `commutingDerivations_superposition`.

The file contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.  Direct
elaboration and the isolated module build pass.  The formal lint passes.  The axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound` for all five public theorems.
