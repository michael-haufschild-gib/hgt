# Height one preserved in both directions — the divisor map is well defined and onto (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(stage 2; the local model is hypothesis-free).

## Added to `GaloisForLFunctions/HTGeometry/PrimeDivisorLyingOver.lean`

- `under_height_eq_one_of_height_eq_one [Algebra.HasGoingDown R S]` — the prime **below** a prime
  divisor is a prime divisor.

With `height_eq_one_of_comap_height_eq_one` (the converse, from incomparability) and
`exists_heightOne_comap_eq` (lying over), height one is preserved in both directions, so the
card's `F : prime divisors → prime divisors` is **well defined and onto**.

Proof: for prime `q' < under R p`, going down (`Ideal.exists_ideal_lt_liesOver_of_lt`) lifts to
`P < p` with `P` lying over `q'`; `height p = 1` forces `P = ⊥` hence `q' = ⊥`.  So
`height (under R p) ≤ 1`; the lower bound is `eq_bot_of_comap_eq_bot`.

mathlib pieces: `Algebra.HasGoingDown` (class, `Mathlib/RingTheory/Ideal/GoingDown.lean`, with
`instance of_flat`), `Ideal.exists_ideal_lt_liesOver_of_lt`, `Ideal.LiesOver` (field `.over`).
**`GoingDown.lean` is a separate import from `GoingUp.lean`** — `Algebra.HasGoingDown` is unknown
without it.

## Card lineage: 8 modules, all axiom-clean

`RamificationPoleFixedPoint`, `EigenvolumeRamificationSystem`, `TameEisensteinDifferentExponent`,
`TopExteriorPowerDeterminant`, `LocalRamificationOrderLaw`, `RingOrdRamification`,
`DivisorSupportFinite`, `PrimeDivisorLyingOver`.

Every hypothesis of the abstract system is discharged: `hlaw` (`ramificationShiftLaw_frac`),
`1 ≤ e` (`one_le_ord_map_uniformizer`, needs **locality**), `hfin`
(`finite_heightOneSupport_frac`), surjectivity (`exists_heightOne_comap_eq`), well-definedness of
`F` (`under_height_eq_one_of_height_eq_one`).

## Next brick

Assemble the capstone: instantiate `eigenvolumeOrder_eq_neg_one_of_someRamified` at the concrete
ring-theoretic datum, giving Theorem A's conclusion with no free hypotheses.  **Friction to
expect:** the card's dynamics is a *self-map* `φ : B →+* B`, but all the lemmas are stated for
`Algebra R S` with `algebraMap`.  Instantiating needs `letI := φ.toAlgebra`, which collides with
the existing `Algebra B B` identity instance — plan to either restate the needed lemmas for a bare
`RingHom` with `RingHom.IsIntegral`, or carry the `letI` through the statement.

After that, only the scheme-level passage remains (rational top form = coframe top wedge;
`AlgebraicGeometry.ord` pullback law; `AlgebraicCycle` is a mathlib stub).

## Repo hazard

Lint gate reports another agent's unwired untracked `HTGeometry.ConnectedNetworkRecurrenceLaw`.
Different such module every iteration today; always `git status` first.
