# Gamma pipeline: 24/26 cards moved to stage 3 (2026-08-07)

`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/gamma/` had 26 cards.  24 are now in
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/gamma/` (new subfolder), each with a
`## Stage-3 Lean certificate` block naming the exact declarations.

**Verification actually performed** (do not redo): 623 Lean modules referenced by the cards were
imported into one scratch file and `#print axioms` run on 2214 resolved declarations — every one
reports exactly `[propext, Classical.choice, Quot.sound]` (5 depend on no axioms).  Plus
`scripts/formal_tools.py lint`: no `sorry`/`admit`/`axiom`/`opaque`/`unsafe` anywhere in the tree.

**Card text was massively stale.**  Several cards still said "Lean proof open" / "Verification gate
(blocked)" / "interfaces absent from the tree" while the capstones existed and were axiom-clean.
Always check the repo, never the card prose.  Notable examples:
- all-order structural matroid: capstone is `multipleEllipticGammaProperFacePackets_diffIndepOn` +
  `multipleEllipticGammaCompleteDifferentialMatroid(_rationalBase/Rank)` +
  `differentialAlgebraicOver_xApply_iff_mem_veroneseIdeal` +
  `differentialAlgebraicOver_translateGammaProduct_iff_mem_veroneseIdeal`.
- Barnes annihilator (A) = `differentialAlgebraicOver_diffTranslateApply_barnesSource_iff`.
- The two "Verification gate (blocked)" pole cards: the duplicate-declaration blocker is long gone.

## New Lean built this session (RHTower, all umbrella-registered, all axiom-clean)

- `GammaCoPoissonSoninQuadrantSection.lean` — the co-Poisson quadrant card `(GS1)`--`(GS18)`.
- `GammaCoPoissonSoninQuadrantCharge.lean` — `(GS19)`--`(GS23)`, the escape exponent = centered Xi
  divisor charge.
- `GammaCoPoissonSoninQuadrantReflected.lean` — the same below the critical line by cosine transport.
- `GammaCoPoissonSoninQuadrantSyzygy.lean` — the two-path commutator `(7)`, the torsion `(18)`, the
  rank-one flat gauge invariant `(21)`.

Key reusable facts discovered:
- The **Burnol Sonine/co-Poisson layer is enormous** (421 modules named Burnol*/Sonin*/CoPoisson*).
  `soninExtendedSpace`, `burnolCoPoissonSourceSpace`, `burnolCoPoissonQuotientSpace`,
  `burnolCoPoissonQuotientProjection`, `burnolExtendedSoninEvaluationVector` with its Riesz identity,
  `soninMellinEvaluation_evenDilation` (exact character `r^(w-1/2)`),
  `BurnolCoPoissonAnnihilatorPoint`, `coe_burnolCoPoissonQuotientEvaluationVector_eq_of_annihilator`.
- `⟪·,·⟫_ℂ` on `evenSubspace` elaborates through `WithCStarModule.instCStarModuleComplex.toInner`,
  so generic mathlib `inner_smul_left`/`inner_conj_symm` do **not** `rw`.  Use `simp` (it matches up
  to instances), or route through corpus lemmas / `Submodule.starProjection_inner_eq_zero`.
- `T_j^- = J T_j^+ J` for the cosine involution `J`; that is what transports the whole quadrant
  section to the left half of the strip.

## The one remaining analytic input (task #4)

`gamma-copoisson-sonin-full-quotient-flatness-syzygy` equation `(2)`
(`T_j^+T_{j+1}^- = T_j^-T_{j+1}^+` on the whole quotient) needs exactly

    closure (span {confluent evaluators at co-Poisson annihilator points}) = burnolCoPoissonQuotientSpace b

i.e. **Burnol's completeness theorem**.  The corpus's
`isCyclicFamily_burnolCoPoissonQuotientEvaluationFamily` (span over *all* regular points is dense)
is NOT a substitute: the proved syzygy `coPoissonQuotientCommutator_ladderKernel_offDivisor` shows
`K_j y_{w,j+2}` is exactly the nonzero source-defect expression at a general `w`, and `(2)` is
*equivalent* to that expression vanishing identically.  So no finite-level rearrangement works.

The other open card, `irrational-elliptic-gamma-pointed-bi-anomaly-fracture`, needs the gerbe half
`(11)`--`(12)`: the Felder--Henriques--Rossi--Zhu group--Cech cochain on the explicit invariant
cover and the Dixmier--Douady computation identifying its class with the generator of `H^3(E,Z)`.
Everything else on that card is already unconditional Lean.
