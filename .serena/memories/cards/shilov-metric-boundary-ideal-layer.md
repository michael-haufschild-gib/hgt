# Shilov card: the metric boundary-ideal layer is now Lean

Card `spectral-boundary-migration-shilov-exactness` (stage 2).  Its "next attack" was
"formalize analytic local-envelope layer over compiled literal Roos sequence".  Done, in
`GaloisForLFunctions.HTGeometry.ShilovLocalBoundaryIdeal`
(namespace `GaloisForLFunctions.HTGeometry.ShilovLocal`).

## The idea that makes it formalizable without operator systems

Mathlib has no operator systems, Shilov ideals, C*-envelopes or boundary representations, and the
card says so.  But the card's own proof of `(9)` — the *representation-free maximality check* —
never uses boundary representations.  It uses only the metric universal property:

    IsBoundaryIdeal S J  :=  ∀ s ∈ S, ∀ j ∈ J, ‖s‖ ≤ ‖s - j‖

i.e. the quotient `A → A/J` is isometric on `S` (`isBoundaryIdeal_iff_le_infDist`).  Everything the
card needs is then elementary.  The index type of the tower section is arbitrary, so instantiating
it at (stage × matrix size) gives the completely isometric statements for free.

## Contents

- calculus: `.mono`, `isBoundaryIdeal_bot`, `.topologicalClosure`, `isBoundaryIdeal_sSup`,
  `exists_maximal_isBoundaryIdeal` (Zorn), `isClosed_of_isGreatest_isBoundaryIdeal` — the Shilov
  ideal is closed automatically, so closedness is never a hypothesis.
- `localIdeal p J = ⨅ i, (J i).comap (p i)` = `J^∞`; `mem_localIdeal_iff_mkQ_eq_zero` is the
  injectivity of `Θ` in `(7)`.
- **`localIdeal_isGreatest` = the card's `(9)`**: stage-greatest ⟹ locally greatest.  This closes
  the gap the card attributes to Joiţa (whose proof gives only coordinate inclusion).
- links: `escapeFree_iff_exists_descent`, `isBoundaryIdeal_comap`,
  `isBoundaryIdeal_map_of_quotient`, `map_le_of_isGreatest`.  The kernel condition
  `ker α ≤ J_A` is exactly where escape can fail — the theorem locates the obstruction.
- `exists_coherent_lift` = the recursive lifting of `(10)`, bottom stage.  Cast-free because the
  recursion is `upLift : ∀ n, {x : A n // x ∈ J n}` with the *bottom* prescribed; prescribing a
  general stage forces `A (n + k)` casts, so state general stages via the shifted tower instead.
- `le_localIdeal_of_closure_le`: coordinate inclusion alone already gives `H ⊆ J^∞`.
- `isClosed_localIdeal`, `isClosed_localIdeal_of_isGreatest`: the local envelope is separated.
- `diagonalRep`, `ker_diagonalRep`, `injective_liftQ_diagonalRep` = the card's `(12)`, the faithful
  local representation.  Lives in a purely algebraic section (`TowerAlgebraic`) — `localIdeal` was
  moved there too, since only module structure is needed; the metric statements sit in
  `TowerMetric`.

## The reduction that matters
`isBoundaryIdeal_iff_norm_mkQ` proves the metric definition IS isometry of the quotient map on `S`
(via `QuotientAddGroup.norm_mk`, which applies verbatim to `Submodule` quotients).  Then
`isBoundaryIdeal_sup` / `IsBoundaryIdeal.sup_of_quotient` (transitivity),
`isGreatest_of_maximal_of_sup_closed`, `exists_isGreatest_isBoundaryIdeal` give:
**Shilov ideal exists ⟸ boundary ideals are closed under joins.**  Join-closure is the ONLY thing
Hamana/Arveson still has to supply; everything else about the Shilov ideal is now elementary.
(Zorn alone gives only *maximal*, and join-closure is exactly the gap between maximal and
greatest — it genuinely fails for bare normed spaces.)

## Commutative model — `ShilovCommutativeBoundary.lean`
`isBoundaryIdeal_vanishingIdeal_iff`: for compact Hausdorff `X`, `S ⊆ C(X,ℂ)` and closed `F`,
the vanishing ideal of `F` is a boundary ideal iff `F` computes the sup-norm of every `s ∈ S`.
Forward direction is Urysohn (`exists_continuous_zero_one_of_isClosed`, needs `T2Space` for
normality); cut `s` by a function that is 1 on `F` and 0 where `‖s‖ ≥ (r+‖s‖)/2`.
Trap: define `IsBoundarySet` quantifying only over `0 ≤ r`, else `F = ∅` makes the iff false.
Import trap: `Mathlib.Analysis.Complex.Basic` is what supplies `NormedField ℂ` —
`Mathlib.Analysis.RCLike.Basic` does NOT.

## Classical boundary theory now in `ShilovCommutativeBoundary.lean`
- `isBoundarySet_sInter_of_directed` — directed intersections of closed boundaries are boundaries
  (compactness / finite intersection property: `IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed`).
- `exists_minimal_isBoundarySet` — hence a MINIMAL closed boundary exists (`zorn_superset`).
  Shilov's theorem = uniqueness of it, which needs the algebra structure and is NOT proved.
- `IsBoundarySet.peakPoint_mem`, `closure_setOf_isPeakPoint_subset` — every closed boundary
  contains every peak point.  Forced lower half of the Shilov boundary.
- `isBoundaryIdeal_sup_of_isBoundarySet_inter` — join-closure in the commutative model reduces to
  intersection-closure of boundary SETS.
Trap: `by_contra` on a `Set.Nonempty` of an image element leaves `(fun F => F ∩ T) F` un-beta-reduced,
so `rw` fails; construct the witness with the anonymous constructor instead, which whnfs.

## The single remaining input
`shilovBoundary S := ⋂₀ {closed boundaries}`.  Proved chain, all unconditional:
  closure of peak points is a boundary          (Bishop / Choquet — IMPORTED, not proved)
    ⇒ `isBoundarySet_inter_of_isBoundarySet_closure_peakPoints`  (binary intersection-closure)
    ⇒ `isLeast_shilovBoundary`                  (Shilov boundary is least)
    ⇒ `isBoundaryIdeal_sup_of_isBoundarySet_inter`  (join-closure of boundary ideals)
    ⇒ `exists_isGreatest_isBoundaryIdeal`       (Shilov IDEAL exists)
    ⇒ `localIdeal_isGreatest`                   (the card's (9))
`shilovBoundary_eq_closure_peakPoints` identifies it outright in that case.
Do NOT try to prove binary intersection-closure directly for uniform algebras: the classical proof
needs Rossi's local maximum modulus principle, and reconstructing it from memory is how you get a
wrong proof.  Reduce to the peak-point statement instead.

## NO-GO: joins genuinely fail in the metric category
`not_isBoundaryIdeal_sup_axes` — sup-normed plane, S = diagonal, J₁ = x-axis, J₂ = y-axis: both are
boundary ideals, their join is everything.  Hence
`not_exists_isGreatest_isBoundaryIdeal_diagLine`: no greatest boundary ideal.  So the hypothesis of
`exists_isGreatest_isBoundaryIdeal` is NOT removable and the C*/Choquet import is NECESSARY.
As a function system this is the constants inside `C({1,2})` — non-separation is what breaks it, so
SEPARATION is the load-bearing classical hypothesis.

`isBoundaryIdeal_sup_iff` — transitivity is an EQUIVALENCE: `J₁ ⊔ J₂` boundary ↔ image of `J₂` is
boundary in `A/J₁`.  So iterating quotients restates the join problem, never weakens it.  Do not
try to bootstrap join-closure that way.

mathlib has Krein-Milman (lemma + theorem) but NOT Milman's converse and NOT Bauer's maximum
principle; the corpus has no Choquet theory.  The state-space route needs all three built first.

## Already in the corpus — do not rebuild
`ShilovBoundaryMigrationDefect.escapeDetectionEquiv` is the card's `(16)`, and
`derivedLimitOne_subsingleton_of_surjective` there is the Mittag--Leffler vanishing (with
`inverseDifference_surjective`).  Checking this first saved rebuilding both.

## Still external
Operator systems, C*-covers, boundary representations.  What remains is identifying the metric
universal property above with the Hamana/Arveson construction.
