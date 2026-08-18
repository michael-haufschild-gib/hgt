# Two `other` cards promoted to Stage 3 on 2026-08-18

Ledger `docs/drafts/pipeline/1-in-progress/other-stage3-closure-ledger.md` ticked for both;
see `mem:nsk-other/stage3-sweep-ledger-2026-08-13` for the running queue.

## `abelian-multiplication-tail-manin-horizon`

Whole chain `(2)`–`(9)` Lean-proved, axiom-clean, wired into `GaloisForLFunctions.HTGeometry`.

New modules (all under `formal/GaloisForLFunctions/HTGeometry/`):

```
AffineZariskiClosureOver              zariskiZeroLocusOver / zariskiVanishingIdealOver /
                                      zariskiClosureOver / IsZariskiClosedOver / ZariskiDenseOver
                                      + Galois connection, universal property, idempotence,
                                      arbitrary intersections, finite unions, density monotonicity
ManinKernelKolchinClosure             kolchinClosureOver_eq_of_zariskiDense_of_minimal
                                      kolchinClosureOver_iUnion_eq_of_zariskiDense_of_minimal
                                      eq_maninKernel_of_kolchinClosure_of_zariskiDense (subgroup form)
                                      iInf_differentialTranslationFixedField_eq_maninKernel
                                      isKolchinClosedOver_constantPoints (Corollary D)
ManinMapQuotientCoordinates           derivationClosed_differentialTranslationFixedField
                                      invariant_iff_factorsThrough_of_fibre_eq_orbit
                                      iInf_differentialTranslationFixedField_eq_maninCoordinateField
AbelianTailUniversalScaling           differentialJet_zsmul, algebraicIndependent_const_smul,
                                      DifferentialIndependent.zsmul, differentialAdjoin_range_zsmul,
                                      multiplicationTailScaling(+_jet/_source/_deriv/_naturality),
                                      multiplicationTail_noHair
AbelianManinHorizonNoHair             multiplicationTail_noHair_of_maninCoordinates
AbelianManinHorizonTheorem            stableRangeCore_eq_maninDeckFixedField_eq_maninCoordinates
                                      stableRangeCore_eq_maninCoordinates_of_finiteDeckDegree
                                      stableRangeCore_free_of_maninCoordinates
AbelianVarietyMultiplicationGaloisLevel
                                      map_abelianVarietyMultiplicationFunctionFieldPullback_pow_top_eq_fixedField
AbelianVarietyManinHorizonTail        abelianVarietyMultiplicationTail_eq_maninCoordinates
```

Seven classical inputs stay as explicit hypotheses, never axioms: finite étale degree data of `[m]`,
Kolchin-closed element stabilizers, the three Manin-kernel properties, Zariski density of the
primary torsion, invariance of the Manin coordinates, the differential rational quotient theorem,
and (Theorem B) differential independence of the Manin coordinates.

**Reusable pattern.** `differentialIndependentAdjoinAlgEquiv` (already in the tree) turns any
"dynamics on a free differential field is universal" claim into two steps: build the endomorphism by
conjugating the labelled equivalence, then prove intertwining by `IntermediateField.adjoin_algHom_ext`
on jets. Only extra ingredient needed was `differentialAdjoin_range_zsmul`.

## `active-quasi-abelian-palette-exact-ht-dimension-classification`

New modules:

```
ActiveQuotientSplitModel              splitCompactLattice(+_injective/_snd)
                                      ambientFaithful_not_activeFaithful_not_free
                                      splitElliptic_ambientFaithful_activeTrivial  (concrete E × ℂ*)
                                      splitModel_capacity_spectrum
ActiveQuasiAbelianPaletteHierarchy    ActiveQuasiAbelianFacetPresentation.toQuasiAbelianFacetCertificate
                                      + latticeClass_injective, QuasiAbelianPalette,
                                      quasiAbelianPaletteDimension_le_activeQuasiAbelianPaletteDimension
ToruslessActiveCollapse               activeFaithful_iff_faithful_of_compactShadow_eq_bot
                                      quasiAbelianPaletteDimension_eq_activeQuasiAbelianPaletteDimension_of_lift
```

**The separation gate is now sharp.** On a facet presentation with trivial compact shadow the active
quotient is injective, so active faithfulness ⟺ plain faithfulness; the pencil quotient `ℂ*` is
torusless, so the invariants agree on the whole periodic-pencil class. Therefore
`qaDim(Δ) < aqaDim(Δ)` requires a complex where *every* minimal quasi-Abelian palette has a facet
whose period quotient carries a positive-dimensional compact complex subtorus meeting the facet
lattice. Start any future separation attempt from that reduction.

Still named as global operations in the dimension equality `(8)`: `extract` (full-HT period
extraction) and `assemble` (localized Stanley–Reisner/Baire). All-order facet jet ampleness is *not*
a hypothesis — it is discharged from each facet's positive Abe tower.

## Traps hit

- `{κ ι : Type*}` fails to parse in a file that opens `CategoryTheory`/`MonObj`; rename the binders.
- Do not re-sort `GaloisForLFunctions/HTGeometry.lean`; its import block is only partially sorted and
  a full sort produces a ~1000-line diff that collides with other agents. Insert single lines.
- Another agent's import (`LocalNakayamaMonogenic`) was already sitting uncommitted in that umbrella;
  always diff the umbrella against HEAD before rewriting it.
