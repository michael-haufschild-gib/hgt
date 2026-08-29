# Stage-3 sweep ledger — 04-rg-stochastic-quantum-fields (17 cards)

Goal: unconditional Lean for every proven theorem on every card; promote to `3-formalized`.
Rules: no hypotheses wrapping unproven input; no umbrella builds; `lake env lean` for checking,
`lake build <module>` only for final audit; `#print axioms` only on new capstones.

| # | Card | Remaining Lean obligation | Status |
|---|---|---|---|
| 1 | thermodynamic-divisor-charge-finite-ancestor-or-boundary-index | DONE — `RHTower/ThermodynamicBoundaryIndexCarrier.lean` | **PROMOTED** |
| 2 | balanced-causal-fracture-torsor-classification | DONE — AIIIGramFibreTorsor, HermitianConeStrictConvexity, ColorGramGlobalTrivialization, ColorGramTrivializationSmoothness, HermitianSymmetricDimensionBalance | **PROMOTED** |
| 3 | common-profile-boolean-anchor-curvature | DONE — `CommonProfileAnchorResponseMobius`, `CommonProfilePoissonVacuum`, `CommonProfileVacuumJoin`, `CommonProfileGlobalCurvatureJoin`, `CommonProfileDefectBound` | **PROMOTED** |
| 4 | coherence-graph-volume-recurrence-exponent-law | DONE — `RootedForestShear`, `CircleChordBall`, `CoherenceGraphVolumeLaw`, `CoherenceGraphRecurrenceExponent` | **PROMOTED** |
| 5 | schwarzian-projective-erosion-tower | DONE over an arbitrary differential base — `DifferentialFieldLocus`, `FreeFamilyJetShift`, `SchwarzianFamilyCoordinates`, `SchwarzianProjectiveErosionTower` | **PROMOTED** |
| 6 | bbm-pullback-completion-purely-continuous-law | pullback completion unitary + reducing-subspace lemma + dilation a.c. | TODO |
| 7 | q-geometric-generalized-free-field-hypertranscendence | moments, positivity, self-similarity, Hankel, + ADH q-difference dichotomy | TODO |
| 8 | ultrametric-thermal-mahler-hypertranscendence | (3) constraint + uniqueness (done?), non-rationality, HT | TODO |
| 9 | ultrametric-one-loop-resolvent-hypertranscendence | (5),(9),(10) coefficientwise (claimed done), HT | TODO |
| 10 | reciprocal-q-ladder-kallen-lehmann-field | pushforward positivity, (13), (15), HT, de Sitter clock (21),(22) | TODO |
| 11 | de-sitter-ultrametric-detailed-balance-hypertranscendence | (5),(8),(9) + DA-invariance under w=exp(-a/H) | TODO |
| 12 | gadc-tree-population-rg-clock-hypertranscendence | algebra formalized; HT classification remains | TODO |
| 13 | noisy-binary-tree-channel-rg-clock-hypertranscendence | algebra formalized; HT classification remains | TODO |
| 14 | exact-rational-rg-generation-dichotomy | Poincare/Ritt DA dichotomy, cocycle equivalence | TODO |
| 15 | exact-rg-clock-hypertranscendence-equivalence | clock/beta DA equivalence | TODO |
| 16 | rg-tower-differential-incoherence-obstruction | coherence obstruction via Boshernitzan-Rubel | TODO |
| 17 | erosion-threshold | backbone + 19a + 19b assembly | TODO |

## Log
- 2026-08-29 — ledger created; all 17 cards read; named modules confirmed present in tree.
- 2026-08-29 — cards 1 and 2 promoted.
- 2026-08-29 — card 3 promoted.  `(CG1)`, arithmetic `(CG2)`, `(PF1)` by Poisson summation on the
  root progressions, `(CG3)`, `(CG4)`, `(CG6)`, `(CG8)`, `(SG10)`, and an exact `(SG9)` replacing the
  `<<_(A,rho)` notation.  Reused the corpus's `ChenGuptaLiAffinePoisson` layer (affine Poisson +
  `stdAddChar` bridge) rather than rebuilding it; the ℤ residue-class decomposition
  `Int.sumByResidueClasses` was the missing piece.  Also proved that the common-profile hypothesis
  is realizable (`exists_schwartz_interpolating`), so `(CG3)`--`(CG6)` are not vacuous.
- 2026-08-29 — card 5 promoted: the whole tower now lives over an arbitrary characteristic-zero
  differential base.  The route that worked: never ascribe a `Derivation ℚ`/`Derivation ℤ` type at a
  concrete `FractionRing` (the `Module ℚ`/`Module ℤ` instances of the Ore localization are not
  defeq to `Algebra.toModule`); instead phrase every statement with the `Differential` postfix `′`
  and use the two locus constructions of `DifferentialFieldLocus`.
- 2026-08-29 — card 4 promoted: `(1)` two-sided volume law, `(2)` minimax exponent, `(3)` almost-sure
  exponent (Borel--Cantelli over rational exponents), and the full rank-zero boundary
  (`volume = 1`, `universalDeadline = 1`, `firstReturn = 1`) are unconditional in Lean.

## Blocker analysis (2026-08-29)

Shared external theorems that gate whole groups of cards:

| Needed theorem | Cards blocked |
|---|---|
| Adamczewski--Dreyfus--Hardouin rational-or-hypertranscendental dichotomy for linear `q`-difference and Mahler equations | 7, 8, 9, 10, 11 |
| Ritt / Becker--Bergweiler classification of Schroeder, Abel and Poincare functions of rational maps | 12, 13, 14 |
| Boshernitzan--Rubel coherent families + Bergweiler's solution of Rubel's problem | 16 |
| Differentially algebraic germ category with analytic local inversion | 14, 15, 16 |
| Unbounded self-adjoint operator theory (resolvent, reducing subspaces, a.c. spectrum) | 6 |
| Selberg CLT and the abscissa/coboundary backbone | 17 |

Self-contained builds (no external import needed):

| Card | Build |
|---|---|
| 3 | arithmetic `B_(c,r,h)` reduction, physical-profile identities, protected-anchor row identity, an exact statement for `(SG9)` |
| 4 | forest-coordinate volume law, minimax exponent, a.e. exponent, rank-zero boundary |
| 5 | Schwarzian tower over a family: level independence, strict descent, depth law, trivial intersection |

Corpus assets found for card 5: `FreeCoordinateField.lean` (free rational coordinate field,
`mem_freeCoordinateField_iff`, coordinate derivations, common kernel), `FreeDifferential*`
(free jet field, translation and scaling automorphisms), `ProjectiveHorizonSchwarzian*`
(single-generator Schwarzian coordinate system, `schwarzianBasisEquiv`,
`algebraicIndependent_schwarzianSystem`), `DifferentialTranscendenceDegree.lean`,
`DifferentialIndependence.lean`.  The remaining work is the family (`A x N`-indexed) version of
the Schwarzian coordinate change and the tower built from it.

## Card 5 design (Schwarzian projective erosion tower)

Ambient object: `FreeCoordinateRationalField C (ι × ℕ)` with the family jet-shift derivation
`(a, m) ↦ (a, m+1)`.  This is `K<Y_a : a ∈ ι>`, the card's `F_0`.

1. `freeFamilyJetShift` — family jet-shift derivation and `Differential` instance (new module
   `FreeFamilyJetShift.lean`), mirroring `ProjectiveHorizonFreeJetReciprocalTail.freeJetShift`.
2. `schwarzianFamily a = schwarzian (familyJet a 0)`; substitution
   `Φ (freeCoordinate (a, m)) = differentialJet m (schwarzianFamily a)`, built from
   `freeCoordinateBasisEval` at the family `(a,m) ↦ differentialJet m (𝔖_a)` once that family is
   proved algebraically independent.
3. `Φ` intertwines the derivation: the locus where `Φ (f′) = (Φ f)′` is an intermediate field
   containing every coordinate, and coordinates generate everything
   (`freeCoordinateField_univ`).
4. `F n := (Φ^[n]).fieldRange`; `F (n+1) ≤ F n` from `Φ^[n+1] = Φ^[n] ∘ Φ`.
5. **Depth key lemma** `Φ g ∈ lowField (k+3) → g ∈ lowField k`, where
   `lowField k = freeCoordinateField C (ι × ℕ) {p | p.2 < k}`; iterate to
   `Φ^[n] g ∈ lowField (3n + k) → g ∈ lowField k`, hence `F n ⊓ lowField (3n) = ⊥`.
6. Consequences: depth law (item 3), strict descent (item 2, using
   `Y^[n] ∈ lowField (3n+1) \ C`), trivial intersection (item 4, since every element lies in
   `lowField N` for some `N` by `exists_finset_mem_freeCoordinateField`).
7. Level independence (item 1) from differential transcendence degree: `F n` is generated by the
   `|ι|`-family `Y^[n]`, and `F 0` is differentially algebraic over `F n` through the Schwarzian
   relation `2 q' q''' − 3 (q'')² − 2 s (q')² = 0`.
8. Item 5 (translation orbits) is the same statement for `ι` a translation orbit; the Schwarzian
   tower commutes with the index relabelling.

## Card 5 residue: exact obstruction (2026-08-29)

`HTGeometry/RationalDerivationTools.lean` is built and green: `ratOfIntDerivation`,
`derivationEqualizerSubfield`, `derivation_eq_of_agree_on_algebraMap`, `derivationStableOf`,
`adjoin_le_derivationStableOf`, `derivationIntertwinerOf`.  These are the base-derivation-tolerant
replacements for `derivationStable` and the intertwiner used in the tower.

The single remaining obstruction is instance plumbing, not mathematics: building
`Differential (FractionRing (MvPolynomial (ι x N) C))` from
`differentialPolynomialOverDerivation` via `fractionRingDerivation` hits a
`Module Q (FractionRing ...)` diamond (`OreLocalization.instModuleOfIsScalarTower` versus
`Algebra.toModule`).  Two routes to try next:

1. build the derivation at base `Z` with `Ring.toIntAlgebra` on both the polynomial ring and its
   fraction field, supplying `IsScalarTower Z P F` by hand;
2. define the derivation on the fraction field directly by `Derivation.mk'` on `IsFractionRing.mk'`
   representatives with the quotient rule, bypassing `fractionRingDerivation`.

Once the instance exists, the three tower modules need `[Differential C]` added and the four uses of
`derivationStable`/`derivationIntertwiner` swapped for the `...Of` variants.

## Card 4 reconnaissance (2026-08-29)

The corpus's `FiniteQuantumObserverGraph*` lane proves a *continuous-time* first-return law with
exponent `(r-1)/2` (`HasUniversalFiniteObserverFirstReturnLaw`), where `r = Fintype.card
(graphNonRoot G)` and `card_graphNonRoot` gives `r = |V| - c(G)`.  The card's law is the
*discrete-time* one with exponent `r`, so it is a different theorem sharing the machinery.

Reusable pieces found:

- torus model `Fin d → UnitAddCircle` with `volume`, phases `fourier 1 (x j)`
  (`ProjectiveWeightedCoherence.lean`);
- `pivotDifferenceEquiv` — the measure-preserving pivot coordinate change, the template for the
  forest coordinate change;
- `projectiveWaterBox`, `volumeReal_projectiveWaterBox`,
  `norm_fourier_one_sub_one_le_two_pi_mul_norm` — circle chord/box estimates
  (`ProjectiveWeightedTargetVolumeLower.lean`);
- `graphComponentRoot`, `graphNonRoot`, `card_graphNonRoot`, `graphRootChordEnergy` and the
  two-sided comparability `observerPhaseEnergy_rootChordEnergy_comparable`
  (`FiniteQuantumObserverGraphMetricEquivalence.lean`);
- `measureReal_torusProjectiveWeightedCoherenceTarget_zsmul_preimage` — every nonzero integer clock
  preserves the target measure, the discrete-time avoidance engine
  (`ProjectiveWeightedCoherenceAvoidance.lean`);
- `ae_hasUniversalFiniteObserverFirstReturnLaw` — the almost-every-spectrum template.

Still to build for card 4: a spanning forest with parent map and path length, the forest
coordinate change as a measure-preserving torus automorphism, the exact two-sided volume law `(1)`,
the discrete minimax exponent `(2)`, the Borel--Cantelli almost-every exponent `(3)`, and the
rank-zero boundary `(4)`.

## Card 4 progress (2026-08-29)

Built and green, all axiom-clean:

- `RHTower/RootedForestShear.lean` — `RootedForest` (parent, depth, strict descent, roots fixed),
  the forest shear as an additive automorphism `shearEquiv`, its continuity and
  `measurePreserving_shear`, the forest graph and the walk chord bound
  `norm_sub_le_walk_length_mul`.
- `RHTower/CircleChordBall.lean` — `chordBall`, squeezed between metric balls by the two-sided
  chord estimate; `ofReal_le_volume_chordBall` (`δ/π ≤ ·`) and `volume_chordBall_le` (`· ≤ δ/2`),
  matching the card's circle constants exactly.
- `RHTower/CoherenceGraphVolumeLaw.lean` — `graphChordEnergy`, `ForestChart` (parent edge per
  nonroot plus a forest walk per graph edge), `ForestChart.constant` = `K_F`,
  `graphChordEnergy_le_of_shear_le`, `shear_le_of_graphChordEnergy_le`, the forest box and its
  volume, and the capstone `volume_graphChordEnergy_sublevel_bounds`, which is exactly the card's
  `(1)`.  The rank-zero boundary is `graphChordEnergy_eq_zero_of_rank_zero` and
  `volume_graphChordEnergy_sublevel_eq_one_of_rank_zero`.

Remaining for card 4:

1. integer-clock invariance of the sublevel target (mirror
   `measureReal_torusProjectiveWeightedCoherenceTarget_zsmul_preimage`);
2. the Dirichlet pigeonhole upper deadline in forest coordinates (mirror
   `exists_graphRelativeEnergy_phase_approximation`);
3. the minimax exponent `(2)` from 1 + 2 and the volume law;
4. the Borel--Cantelli almost-every exponent `(3)`.

## Card 4: next steps, precisely (2026-08-29)

`RHTower/CoherenceGraphRecurrenceExponent.lean` is built and green: `energyTarget`,
`measure_energyTarget_zsmul_preimage` (integer-clock Haar invariance via
`Measure.measurePreserving_zsmul`), `energyHitUnion`, `measure_energyHitUnion_le`, and
`exists_avoiding_energyTarget` — the minimax *lower* half, which converts the volume law into
"`N` is not a universal deadline once `N · vol(target) < 1`".

Remaining:

1. **Pigeonhole upper deadline.**  Reuse
   `RHTower.exists_fin_simultaneous_integer_approximation_quantitative`
   (`CCMPrimePoleFiniteCoherence.lean`: common denominator at most `(Q+1)^d`, every coordinate
   within `1/(Q+1)` of an integer).  Apply it to the `rank`-many reals given by representatives of
   the nonroot forest chords `T.shear x v`; use `AddCircle.norm_eq` (`‖(y : AddCircle 1)‖ =
   |y − round y|`) to convert the approximation into `‖T.shear ((n : ℤ) • x) v‖ ≤ 1/(Q+1)`, then
   `norm_fourier_one_sub_one_le_two_pi_mul_norm` and `graphChordEnergy_le_of_shear_le`.  Needs
   `T.shear ((n : ℤ) • x) = (n : ℤ) • T.shear x`, which is `map_zsmul` on `shearEquiv`.
2. **Minimax exponent `(2)`** from 1 and `exists_avoiding_energyTarget` plus the two-sided volume
   law: define `IsUniversalDeadline` and the least such `N`, then take logarithms.
3. **Almost-every exponent `(3)`**: first Borel--Cantelli against `ε_n = n^(-1/r-γ)` using
   `measure_energyTarget_zsmul_preimage` and the upper volume bound, then intersect over positive
   rational `γ` and combine with the deadline of step 1.
