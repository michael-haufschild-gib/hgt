# Projective constraint topology has a sharp Hurwitz phase transition at 1/42

- **ID:** `projective-hurwitz-one-over-forty-two-phase-transition`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (Lean 4; classical geometric inputs exposed explicitly)
- **Scientific status:** `[PAPER PROOF COMPLETE] [HURWITZ ARITHMETIC 1/42 GAP FORMALIZED; GEOMETRIC EXISTENCE STILL WITNESSED] [NOVELTY UNVERIFIED]`
- **Depends on:** `projective-constraint-topological-capacity-phase-law`
- **Statement:** The least topology density capable of supporting an integral hyperbolic
  projective constraint is exactly `1/42`.  Below that density projective rank is impossible.  At
  the threshold, arithmetic `(2,3,7)` correspondence surfaces of unbounded degree preserve a
  minimal rank-three projective groupoid and saturate the capacity law.

## The theorem

Let `X` be a compact smooth curve of genus `g`, and let a degree-`D` finite map from `X` to a
projective orbifold sphere support a terminal integral hyperbolic projective connection.  Then

```text
D <= 42(2g-2)=84(g-1).                                    (1)
```

Equivalently,

```text
(2g-2)/D >= 1/42.                                         (2)
```

The bound is attained at every torsion-free finite cover of the `(2,3,7)` orbifold:

```text
D = 42(2g-2).                                              (3)
```

Let `Q_237` be the rational Schwarzian projective connection of the hyperbolic triangle
uniformizer.  Then:

1. the Kummer projective groupoid of `Q_237` is minimal;
2. it contains no tensor or affine positive-order subgroupoid;
3. the arithmetic commensurator of `Delta(2,3,7)` produces algebraic spans

   ```text
   X_n => P1_(2,3,7)                                      (4)
   ```

   of unbounded degree with equal pullbacks of `Q_237` along both legs;
4. the surfaces in `(4)` satisfy equality `(3)`.

Thus `1/42` separates two regimes:

```text
topology density < 1/42  => no integral hyperbolic projective phase;
topology density = 1/42  => minimal projective phase exists at unbounded degree. (5)
```

## Proof

The projective topological-capacity theorem gives

```text
D epsilon <= 2g-2                                        (6)
```

for a compact source.  For an integral hyperbolic sphere orbifold, the Hurwitz gap is

```text
epsilon>=1/42,                                            (7)
```

with equality only at signature `(2,3,7)`.  Combining `(6)--(7)` proves `(1)--(2)`.

Now let `H` be a torsion-free subgroup of index `D` in the orientation-preserving triangle group
`Delta(2,3,7)`.  The three target fibres have `D/2`, `D/3`, and `D/7` points, with ramification
contributions `D/2`, `2D/3`, and `6D/7`.  Riemann--Hurwitz gives

```text
2g-2=-2D+D/2+2D/3+6D/7=D/42,                              (8)
```

which proves `(3)`.

The projective monodromy of the hypergeometric triangle equation is `Delta(2,3,7)`.  This group is
non-elementary and therefore has no finite orbit on `P1`.  An algebraic solution of the associated
Riccati equation would have finitely many analytic branches permuted by monodromy, producing such
a finite orbit.  Hence the Riccati equation has no algebraic solution.  The projective Kummer
minimality criterion implies claims 1--2.

Takeuchi's classification and the explicit quaternionic construction identify `(2,3,7)` as an
arithmetic triangle group.  For any commensurator element `a`, choose a torsion-free subgroup

```text
H subset Delta intersect a^(-1)Delta a.                   (9)
```

The triangle Hauptmoduls `t(tau)` and `t(a tau)` descend to the two maps in `(4)`.  Their
Schwarzian pullbacks agree because `a` is Mobius.  Arithmeticity makes the commensurator dense;
the intersection indices are unbounded.  Equation `(8)` applies to every torsion-free refinement,
proving claims 3--4 and `(5)`.

## Strong positive content

The theorem is not only the no-go `(1)`.  It constructs the phase on the boundary and proves:

- exact attainability of the universal constant;
- unbounded relational degree at that density;
- preservation of a minimal, genuinely rank-three projective constraint;
- exact genus accounting, with no hidden capacity.

The positive phase is the compact Hurwitz analogue of modular Hecke correspondences, but it is
more economical: `1/42` is the absolute integral hyperbolic minimum.

## Physical/topological meaning

Negative orbifold curvature has an exact topological storage price.  A compact relational surface
must create at least one unit of `2g-2` for every `42` sheets.  The Hurwitz phase packs projective
information at exactly that density, so `1/42` is a quantized critical density rather than a loose
estimate.

This is a static phase transition in constraint topology.  It is not a thermodynamic limit,
Hamiltonian phase transition, quantum state, time evolution, or black-hole entropy law.  The
mathematical content is the equality between projective curvature excess and extensive surface
topology.

## Meaning for hypertranscendence

`Q_237` is a finite-order projective constraint, not a hypertranscendental function.  It identifies
the sharp last finite-rank phase.  A scalar rational HT tail on fixed `P1` cannot retain this phase;
it collapses to the parabolic tensor current.  A growing relational surface can retain it exactly
at density `1/42`.  Genuine hypertranscendence lies beyond this boundary and cannot be modeled by
an unbudgeted finite-rank projective carrier.

## Novelty and significance gate

The Hurwitz bound, triangle uniformization, arithmeticity of `(2,3,7)`, commensurator
correspondences, and projective Kummer minimality are established ingredients.  The candidate new
result is their conjunction with the nonautonomous scalar-tail no-go: the same `1/42` is proved to
be both the universal collapse threshold and the attained critical density of an irreducible
relational projective phase.

No checked source states that functional--relational phase theorem.  The classical ingredients
make the proof concise once the question is posed, so novelty and medal-level significance remain
unverified.  A specialist audit is required in arithmetic triangle groups, Schwarzian
correspondences, D-groupoids, and orbifold projective structures.

Primary parents include:

- Takeuchi, *Arithmetic triangle groups*, J. Math. Soc. Japan 29 (1977), 91--106;
- Elkies, *Shimura curves for level-3 subgroups of the `(2,3,7)` triangle group*,
  [arXiv:math/0409020](https://arxiv.org/abs/math/0409020);
- Arenas Tirado--Blazquez-Sanz--Casale, projective Kummer minimality,
  [arXiv:2309.07829](https://arxiv.org/abs/2309.07829).

## RH impact audit

Any compact arithmetic-correspondence architecture proposed for RH must pay at least the
`1/42` topology density if it is to retain a minimal projective constraint.  A claimed compact
rank-three mechanism below that density is impossible.  Equality rigidly points toward a
Hurwitz-triangle architecture.

No common pullback of an RH-sensitive zeta projective connection, no critical-line orientation,
and no zero-exclusion theorem is known.  The result is a sharp design and falsification criterion,
not an RH proof step.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/NonautonomousProjectiveTailCollapse.lean` formalizes:

- `hurwitzGap_degree_add_eightyFour_le_genus`;
- `hurwitzTriangle_projectiveCapacity_exact`;
- `hurwitzTriangle_projectiveCapacity_saturates`;
- `hurwitzProjectiveStorage_order_iff`.

`formal/GaloisForLFunctions/HTGeometry/ProjectiveConstraintTopologicalCapacityPhase.lean`
formalizes the complete sharp-phase implication.  The triangle uniformization, common pullback,
arithmetic commensurator, and Kummer-minimality parents are represented without axioms by
`HurwitzProjectiveSurvivalWitness`; Lean then proves exact `1/42` storage, strict degree/genus
ordering, unbounded genus, and persistent irreducibility in the combined phase-separation theorem.

`formal/GaloisForLFunctions/HTGeometry/HurwitzTriangleSumBound.lean` now formalizes the **arithmetic
Hurwitz `1/42` gap** itself — previously an exposed classical input — unconditionally:

- `hurwitz_triple_sum_le (hp : 1 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (hsum : 1/p+1/q+1/r < 1) :`
  `1/p+1/q+1/r ≤ 41/42` — the sharp reciprocal-sum bound for hyperbolic ordered signatures, by
  finite reduction to `p ∈ {2,3}`, then `q`, then `r` bounded by the hyperbolic hypothesis;
- `hurwitz_euler_defect_ge : 1/42 ≤ 1 − (1/p+1/q+1/r)` — the equivalent orbifold Euler-defect form,
  i.e. the gap `ε ≥ 1/42`;
- `hurwitz_signature_237_sum`, `hurwitz_signature_237_defect` — the `(2,3,7)` equalities
  `1/2+1/3+1/7 = 41/42` and defect `= 1/42`, so the bound is sharp;
- `hurwitz_triple_sum_le_symm` — the same bound for *unordered* positive triples (via sorting), the
  form needed for "least density over all signatures";
- `hurwitz_ordered_eq_237` / `hurwitz_ordered_sum_eq_iff` — the **uniqueness of the minimizer**:
  on a hyperbolic ordered signature, `1/p+1/q+1/r = 41/42 ↔ (p,q,r) = (2,3,7)`, formalizing the
  card's "equality only at signature `(2,3,7)`".

`#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only.  Still an exposed input: the
geometric correspondence between hyperbolic sphere orbifolds and integer signatures (Riemann--Hurwitz
and surface existence), which the `HurwitzProjectiveSurvivalWitness` continues to carry.

## Gates

- [x] universal lower-density theorem proved
- [x] exact positive `(2,3,7)` saturation proved
- [x] minimal projective survival proof supplied
- [x] arithmetic unbounded-correspondence construction supplied
- [x] arithmetic core formalized in Lean
- [x] complete Hurwitz survival implication formalized from explicit classical-input witnesses
- [ ] broad specialist parent audit
- [ ] internal construction of triangle groups, covers, and Kummer minimality

## Log

- 2026-07-24 -- Formalized the arithmetic Hurwitz `1/42` gap unconditionally in
  `GaloisForLFunctions.HTGeometry.HurwitzTriangleSumBound` (`hurwitz_triple_sum_le`,
  `hurwitz_euler_defect_ge`, and the `(2,3,7)` sharpness witnesses), discharging the reciprocal-sum
  bound `1/p+1/q+1/r ≤ 41/42` that was previously an exposed classical input. Axioms clean; module
  builds and is wired into the HTGeometry umbrella. Remaining exposed input: the geometric
  orbifold-to-signature correspondence carried by `HurwitzProjectiveSurvivalWitness`.
- 2026-07-24 -- Extended the arithmetic Hurwitz result to its full form: the symmetric (unordered)
  bound `hurwitz_triple_sum_le_symm` and the minimizer uniqueness
  `hurwitz_ordered_eq_237` / `hurwitz_ordered_sum_eq_iff` (`1/p+1/q+1/r = 41/42 ↔ (2,3,7)`),
  formalizing "equality only at (2,3,7)". Axioms clean; module builds.

## Audit — the survival witness carries no geometry `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/HurwitzSurvivalWitnessInhabited.lean` constructs
`natHurwitzProjectiveSurvivalWitness : HurwitzProjectiveSurvivalWitness ℕ` and proves
`nonempty_hurwitzProjectiveSurvivalWitness` (axioms `propext`, `Classical.choice`, `Quot.sound`).

Two consequences follow, and they cut both ways.

1. Every theorem quantified over a `HurwitzProjectiveSurvivalWitness` is non-vacuous.
2. The structure's `commonPullback` and `irreducible` fields are arbitrary predicates, and its only
   numerical constraints are `degree i = 42(2·genus i − 2)` and unboundedness of `degree`.  An
   explicit integer family satisfies them.  Therefore the witness expresses **no** geometric fact
   about correspondence surfaces, and the gate "complete Hurwitz survival implication formalized
   from explicit classical-input witnesses" does not carry the card's statements `(3)`–`(5)`.

What *is* unconditional is the arithmetic: `hurwitz_triple_sum_le`, `hurwitz_euler_defect_ge`,
`hurwitz_ordered_sum_eq_iff` (the `1/42` gap and its uniqueness at `(2,3,7)`) and
`hurwitzTriangle_projectiveCapacity_exact` (Riemann--Hurwitz equation `(8)`, from the three fibre
counts to `D = 42(2g−2)`).

The open formalization obligation is therefore sharper than the card previously recorded: construct
`Δ(2,3,7)` as a group, produce torsion-free finite-index subgroups of unbounded index, and derive
the fibre-count hypotheses of `hurwitzTriangle_projectiveCapacity_exact` from that construction.
Until then the card is not eligible for Stage 3.
