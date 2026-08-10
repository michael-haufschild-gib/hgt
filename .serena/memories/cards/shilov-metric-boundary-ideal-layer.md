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
- `exists_coherent_lift` = the recursive lifting of `(10)`, bottom stage.
- **`exists_coherent_lift_at` (ShilovStableImage) = ARBITRARY stage** — the earlier "bottom stage
  only" caveat is dead.  Above the stage: `Nat.leRec` (`upLiftAt`); below: `downTo`; glue with
  `downTo_shift`.  All indices literal.  Use `simp only [dif_pos/dif_neg ...]` not `rw` — the `dite`
  in the assembled function is not beta-reduced for `rw`.
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

## Derived acyclicity is NOT formal — `ShilovDerivedNonvanishing.lean`
The defect module had onto-bonds ⇒ lim¹=0 and a never-onto tower WITH lim¹=0.  Missing direction now
built: `polyTower_nonsurjective_and_nonvanishing` — stages all `𝕜[X]`, bonds all `X * ·`; the Roos
equation `xₙ - X·xₙ₊₁ = 1` forces `x₀` to have coefficient 1 in every degree.  So non-surjectivity
and derived vanishing are independent in BOTH directions and the card's `(12f)` cannot follow from
the tower axioms.
`ShilovLocal.eq_bot_of_isLocalBoundaryIdeal` formalizes the load-bearing step of the card's proof of
(12f): stagewise-trivial Shilov ideals + jointly injective coordinates ⇒ only local boundary ideal
is ⊥.  Remaining import: local envelope UNIQUENESS.
Trap: `Submodule.mem_bot` takes `R` explicitly — `(Submodule.mem_bot 𝕜).mpr`.

## Algebraic deficit formula — `ShilovDeficitEnvelopeFormula.lean`
`deficitPreimageEquiv : RelativeQuotient (Js ⊔ ker f) (Jt.comap f) ≃ₗ DeficitDefect f Js Jt`,
i.e. `J_T/α(J_S) ≅ α⁻¹(J_T)/(J_S + ker α)`.  Proof = `Submodule.comap_map_eq` (comap f (map f p) =
p ⊔ ker f) + `quotKerEquivOfSurjective`.  **Zero escape is NOT needed** — the card assumes it but
the equivalence holds for every surjective link; escape-freeness only makes the left side literally
`J_T/α(J_S)`.  `deficitFree_iff_comap_le`: deficit freedom ⟺ `α⁻¹(J_T) ⊆ J_S + ker α`.
Note `RelativeQuotient L M := ↥M ⧸ L.comap M.subtype` — NO `⊓ M`; state kernels in that exact shape
or `quotEquivOfEq` will not typecheck.

## What envelope uniqueness actually adds — GENERATION, not minimality
`inf_eq_bot_of_isBoundaryIdeal`: a boundary ideal meets the system trivially (take s = j, get
‖j‖ ≤ 0).  Hence `eq_bot_of_isBoundaryIdeal_top`: if the system IS the ambient space, the Shilov
ideal is automatically ⊥.  So S is always its own cover with trivial Shilov ideal, and minimality
alone cannot characterise the envelope.  Any future formalization of the card's (12f) must carry
the GENERATION hypothesis (cover generated by S as a C*-algebra) explicitly — the card's proof step
"B has trivial local Shilov ideal" is provably not sufficient by itself.

## Idempotence + the uniqueness/existence split
`isBoundaryIdeal_quotient_eq_bot` — quotienting by the GREATEST boundary ideal leaves a cover with
no nonzero boundary ideal.  Proof is `IsBoundaryIdeal.sup_of_quotient` (transitivity) + greatestness.
So the abstract construction is idempotent and `A/J_S` is genuinely minimal.
`Generates` / `eq_of_eqOn_generates` (`AlgHom.ext_of_adjoin_eq_top`): generation buys UNIQUENESS of
the envelope comparison map outright.  So envelope uniqueness = elementary half (uniqueness, from
generation) + the whole difficulty (existence, from Hamana).  Attack existence, never uniqueness.

## Stable image filtration — `ShilovStableImage.lean`
**Use `Nat.leRec`, not gap recursion.**  `downTo bond (h : n ≤ m) : A m →ₗ A n` via
`Nat.leRec LinearMap.id (fun _ ih => ih.comp (bond k))` keeps every index literal, so BOTH
`downTo_succ` (peel at top) and `downTo_shift` (peel at bottom) are provable with zero transport.
Defining it as `A (n+k) →ₗ A n` by recursion on k gives only the top identity and forces the
propositional rewrite `(n+1)+k = n+(k+1)` — that was a dead end; do not redo it.
`reach bond n m h := range (downTo bond h)`, `reach_antitone`, and `map_bond_reach`
(`bond n (reach (n+1) m) = reach n m`) — the cross-stage identity Mittag-Leffler needs.
`HasStableImages` = ML.  Both corpus extremes are ML (`hasStableImages_of_surjective`,
`_of_zero_bond`); `polyTower_nonsurjective_and_nonvanishing` is a tower that never stabilises.
DONE: `inverseDifference_surjective_of_eventually_zero` — eventually-zero transitions ⇒ lim¹ = 0.
`trans bond n j` = composite extended by zero below the diagonal; correction sum
`∑_{j ∈ Ico n (K n)} trans n j (b j)`; `partialSum_eq_of_le` (truncation point irrelevant) +
`partialSum_sub` (telescopes in ONE step via `trans_shift`).  Strictly generalizes
`derivedLimitOne_subsingleton_of_zero_bond` (case K n = n+1).
DONE: full Mittag-Leffler — `inverseDifference_surjective_of_hasStableImages` /
`derivedLimitOne_subsingleton_of_hasStableImages`.  DIRECT proof, no six-term sequence and no
quotient tower: `map_bond_stable` (stable images form a sub-tower with ONTO bonds, from
`map_bond_reach` + stability), the correction sum solves the Roos equation up to the stable part
(two truncations differ by stable elements), and the corpus's `inverseDifference_surjective`
corrects the residue inside the sub-tower.  Both corpus extremes are now corollaries
(`..._of_surjective_via_stable`, `..._of_zero_bond_via_stable`).
Traps: the corpus module has `variable (A : ℕ → Type v)` EXPLICIT — call `restrictedBond A bond ...`
and `inverseDifference_surjective A ...`.  `linear_combination` needs a CommSemiring; on module
elements use `rw [← h]; abel` or a `show ... from by abel` rewrite.

## Prescribed deficits + ML is NOT necessary — `ShilovPrescribedDeficit.lean`
Tower of tails: `supportedAbove 𝕜 D n` = sections of `D` vanishing below n, bonds = inclusions.
`prescribedCokernelEquiv`: n-th cokernel ≅ `D n` (evaluation at n).
`inverseDifference_surjective_prescribed`: Roos difference ONTO — correction section
`∑_{j ∈ Ico n (k+1)} (b j) k` is finite in every coordinate.
`prescribed_deficit_and_derived_vanishing` = Theorem E's linear core: ARBITRARY prescribed link
deficits coexist with lim¹ = 0.
**Consequence: Mittag-Leffler is STRICTLY sufficient.**  This tower's reaches are the tails, which
never stabilise, yet lim¹ = 0.  So do NOT try to prove (12f) by establishing ML for Shilov towers —
that is strictly stronger than needed and is the wrong invariant.

## The (12f) import, in final form
`surjective_of_isClosed_range_of_generates`: a hom whose RANGE IS CLOSED and contains a
topologically generating set is onto (`Algebra.adjoin_le` + `Subalgebra.topologicalClosure_minimal`).
Θ's injectivity is `mem_localIdeal_iff_mkQ_eq_zero`.  So (12f) needs exactly:
**closed range + generation** — NOT minimality (disproved), NOT Mittag-Leffler (disproved as
necessary), NOT the algebraic comparison (uniqueness is free from generation).  `surjective_of_isometry_of_generates` / `bijective_of_isometry_of_generates`: an ISOMETRIC hom from
a complete algebra has closed range (`Isometry.isClosedEmbedding.isClosed_range`), so with
generation it is bijective.  mathlib HAS `NonUnitalStarAlgHom.isometry` (injective *-hom of
C*-algebras is isometric) and `.norm_map`.  Θ is injective, so ONLY GENERATION remains for (12f).
Important: mathlib has NO C*-quotient, so there is no closed-range theorem for general *-homs —
use the injective case, which is all Θ needs.
`mem_of_coordinatewise_approx`: simultaneous approximation of finitely many coordinates from a
CLOSED set puts the point in it (build the sequence with ε = 1/(m+1), `tendsto_pi_nhds`,
`IsClosed.mem_of_tendsto` — do NOT pass its filter by name `l`, it is not named that).
The closure is essential: the algebraic analogue is FALSE — `A n = 𝕜^n` with truncations, the
finitely-supported coherent sequences surject onto every coordinate but are not everything.
`simultaneous_approx_of_stagewise` (ShilovStableImage) supplies that hypothesis from SINGLE-STAGE
density, given CONTRACTIVE bonds: `downTo_coherent` (earlier coordinates are composites of a later
one) + `norm_downTo_le` (composites of contractions are contractions) ⟹ `norm_sub_le_of_coherent`.
Same ε, no operator-norm bookkeeping.  Contractivity is automatic for C*-quotient maps.

## Generation assembled — `ShilovLocalComparison.lean`
`isClosed_coherent` + `coherent_mem_of_stagewise_dense` / `coherent_subset_of_stagewise_dense`:
a CLOSED set of coherent families that is dense at each SINGLE stage contains every coherent family.
So generation for Θ reduces to "each stage system is dense in its stage envelope".
Traps: `LinearMap.continuous_of_bound` does NOT exist — use
`LipschitzWith.of_dist_le_mul ... |>.continuous`.  `isClosed_eq` needs T2, so this module uses
`NormedAddCommGroup` (seminormed is not enough); the upstream propagation lemmas stay seminormed.

## Already in the corpus — do not rebuild
`ShilovBoundaryMigrationDefect.escapeDetectionEquiv` is the card's `(16)`, and
`derivedLimitOne_subsingleton_of_surjective` there is the Mittag--Leffler vanishing (with
`inverseDifference_surjective`).  Checking this first saved rebuilding both.

## Still external
Operator systems, C*-covers, boundary representations.  What remains is identifying the metric
universal property above with the Hamana/Arveson construction.

## Choquet boundary built; peak-point hypothesis retired (2026-08-10)

`isLeast_shilovBoundary`'s `hinter` and `shilovBoundary_eq_closure_peakPoints`'s
`hb` are discharged/replaced by
`ChoquetBoundaryFunctionSystem.lean` (+ `BauerMaximumPrinciple.lean`,
`MilmanExtremePoints.lean`):

- `isBoundarySet_choquetBoundary` — no hypotheses on S at all;
- `choquetBoundary_subset_of_isBoundarySet` — unital + self-adjoint + separating;
- `isLeast_shilovBoundary_of_functionSystem`,
  `shilovBoundary_eq_closure_choquetBoundary`.

`hb` with the strict `IsPeakPoint` is FALSE for non-metrizable X — do not try to
prove it.

## Shilov ideal + commutative C*-envelope built (2026-08-10)

`ShilovIdealCommutative.lean`, `CStarEnvelopeCommutative.lean`.
Maximality of the Shilov ideal is UNCONDITIONAL (closed ideals of C(X) are
vanishing ideals — mathlib `idealOfSet_ofIdeal_isClosed`); only "it is itself a
boundary ideal" needs the function-system hypotheses.

NEXT capstone: C*_e(A(K)) = C(ext K), i.e. identify the Choquet boundary of the
affine continuous functions on a compact convex K with ext K.

## Capstone done: C*_e(A(K)) = C(closure (ext K)) (2026-08-10)

`AffineFunctionSystemEnvelope.lean`. Key simplification: evaluation on A(K) is
affine, so the state body equals the *range* of evalPoint (range is convex and
compact) — no hull, no closure. Extreme points then transport by injectivity +
affineness, giving choquetBoundary (A K) = ext K.
