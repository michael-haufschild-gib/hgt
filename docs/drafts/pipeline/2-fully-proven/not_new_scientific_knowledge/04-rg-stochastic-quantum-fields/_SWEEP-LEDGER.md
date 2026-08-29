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
| 6 | bbm-pullback-completion-purely-continuous-law | DONE — `SelfAdjointResolvent`, `PullbackCompletion`, `DilationSpectralType`, `ResolventCompactness`, `BBMPullbackCompletionVerdict`, `DilationGeneratorNoPointSpectrum` | **PROMOTED** |
| 7 | q-geometric-generalized-free-field-hypertranscendence | the card's whole declared Lean boundary is ALREADY formalized in `HTGeometry/GeometricKallenLehmannResponse.lean` (moment formula, positivity, self-similarity + uniqueness, Hankel determinants, escape from finite spectral width).  Sole gates: the ADH dichotomy for the first-order inhomogeneous `q`-difference equation, and the generalized-free-field/Wightman construction of items 1--2 | GATED ON ADH |
| 8 | ultrametric-thermal-mahler-hypertranscendence | coefficient spectrum, `(w)`-coordinate constraint and formal-power-series uniqueness already in `HTGeometry/UltrametricThermalMahler.lean`; sole gate is ADH (Mahler case) | GATED ON ADH |
| 9 | ultrametric-one-loop-resolvent-hypertranscendence | the card's coefficientwise target is already formalized (see the promoted `ultrametric-resolvent-susceptibility-constraint` card); sole gate is ADH | GATED ON ADH |
| 10 | reciprocal-q-ladder-kallen-lehmann-field | the card itself records that the finite constraint infrastructure is already in the corpus; gates are the infinite-soliton theorem, analytic Källén--Lehmann reconstruction and ADH | GATED ON ADH |
| 11 | de-sitter-ultrametric-detailed-balance-hypertranscendence | `UltrametricThermalMahler.lean`, `FiniteKMSDetailedBalance.lean` and `UltrametricThermalTruncation.lean` already carry the constraint, uniqueness, detailed balance and the next-shell residual; gates are ADH and the theorem that an invertible differentially algebraic change of the independent variable preserves hypertranscendence | GATED ON ADH + DA CHANGE OF VARIABLE |
| 12 | gadc-tree-population-rg-clock-hypertranscendence | the card's whole declared Lean boundary is already formalized in `HTGeometry/GADCTreePopulationRG.lean` (Bloch action, transition matrix, parameter gap, rational family, multiplier, endpoints); the HT half is a corollary of the Becker--Bergweiler/Fernandes classification.  Its two open gates are future programmes, not theorems of the card | GATED ON BECKER--BERGWEILER |
| 13 | noisy-binary-tree-channel-rg-clock-hypertranscendence | the card's declared Lean boundary is already formalized in `HTGeometry/BetheHolographicIsingRG.lean`; the HT half is the same external classification.  Its three open gates are future programmes | GATED ON BECKER--BERGWEILER |
| 14 | exact-rational-rg-generation-dichotomy | needs the unconditional analytic Poincaré theorem and Ritt's theorem (Di Vizio--Fernandes give a Galoisian proof); nothing of the card is formalizable without them | GATED ON RITT |
| 15 | exact-rg-clock-hypertranscendence-equivalence | needs analytic logarithm branches, local compositional inversion and a differentially algebraic germ category; the card itself refuses a hypothesis wrapper | GATED ON DA GERM CATEGORY |
| 16 | rg-tower-differential-incoherence-obstruction | needs analytic local inversion, differential-algebraic transitivity and the Boshernitzan--Rubel uniform closure theorem | GATED ON BOSHERNITZAN--RUBEL |
| 17 | erosion-threshold | the backbone `Re = 1/2` is the abscissa of a.s. convergence is already formalized (`RHTower/RandomEulerObservableAbscissa.lean`, `measure_coordSeriesConverges_randomEulerTerm_eq_one_iff`); 19a is split to its own card.  Remaining formalizable: the second-moment law `V(sigma)` and `Var(Re L) = V/2`.  The headline G19 is NOT proven on paper — the card's own `1 -> 2` gate is open — so it is not a formalization obligation | PARTIAL: BACKBONE DONE, VARIANCE LAW OPEN, HEADLINE NOT PAPER-PROVED |

## Log
- 2026-08-29 — ledger created; all 17 cards read; named modules confirmed present in tree.
- 2026-08-29 — cards 1 and 2 promoted.
- 2026-08-29 — card 6 promoted.  New unbounded-operator layer that mathlib lacks: the resolvent
  theorem for self-adjoint `LinearPMap`s, the reducing-subspace lemma, the resolvent as a bounded
  operator with its adjoint, and the compactness exclusions (`R* R` has a norm-attaining
  eigenvector, which the two resolvent equations turn into an eigenvector of the operator; the
  second resolvent identity transports that to bounded perturbations).  The dilation generator is
  built from the corpus's own logarithmic-Jacobian and Mellin--Fourier unitaries and the corpus's
  `maximalRealL2Mul_isSelfAdjoint`.
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

## Log addendum — unbounded operator layer

`HTGeometry/SelfAdjointResolvent.lean` is the unbounded self-adjoint layer that card 6 needs and
that mathlib does not have.  Proved: a self-adjoint `LinearPMap` is its own formal adjoint; its
diagonal form is real; `|Im z| * ‖x‖ ≤ ‖A x - z x‖`; injectivity of `A - z` at nonreal `z`;
reality of every eigenvalue; closed range (antilipschitz on the closed graph); trivial orthogonal
complement of the range (via the adjoint characterization); hence bijectivity of `A - z`; and the
reducing-subspace lemma `mem_of_shiftedMap_eq` — a self-adjoint restriction to a closed subspace
forces the ambient resolvent to preserve that subspace.  What remains for card 6 is the
pullback-completion unitary and the absolutely continuous spectrum of the dilation generator.

## Card-by-card gate map (2026-08-29)

Six cards are promoted (1--6).  Of the remaining eleven, **every card's own declared unconditional
Lean boundary is already formalized in the corpus** except card 14, 15, 16 (which declare none) and
card 17's variance law.  What blocks promotion is in each case a named external theorem:

| External theorem | Cards |
|---|---|
| Adamczewski--Dreyfus--Hardouin rational-or-hypertranscendental dichotomy | 7, 8, 9, 10, 11 |
| Becker--Bergweiler / Fernandes classification of Poincaré, Schröder, Böttcher and Abel functions | 12, 13 |
| Ritt's theorem and the analytic Poincaré theorem (Di Vizio--Fernandes Galoisian proof) | 14 |
| Differentially algebraic germ category with analytic local inversion | 15, 16 |
| Boshernitzan--Rubel coherent families + Bergweiler's solution of Rubel's problem | 16 |
| the second-moment/variance law of the random Euler product | 17 |

## ADH gate: the corpus already owns most of the machinery (2026-08-29)

Cards 7--11 share one gate, the Adamczewski--Dreyfus--Hardouin rational-or-hypertranscendental
dichotomy.  A corpus survey shows the difference-Galois layer needed for it is largely built:

- `HTGeometry/DifferenceSystemPicardVessiot.lean` — existence of Picard--Vessiot rings for linear
  difference systems;
- `HTGeometry/DifferencePicardVessiotConstants.lean` — no new constants;
- `HTGeometry/DifferenceGaloisRepresentation.lean` — faithful difference Galois representation;
- `HTGeometry/ParameterizedPicardVessiotExistence.lean`,
  `HTGeometry/ParameterizedGaloisRepresentation.lean`,
  `HTGeometry/ParameterizedDifferenceGalois.lean` — the Hardouin--Singer parameterized theory that
  ADH actually uses;
- `HTGeometry/SourceLogarithmicBoundary.lean` —
  `automorphismFamily_hypertranscendental_of_no_logIncrement_jet_telescoping`: absence of a
  simultaneous jet telescoper forces hypertranscendence, for the *multiplicative* case
  `sigma x = b x`;
- `HTGeometry/AutomorphismFamilyOstrowski.lean` — the additive (Ostrowski) counterpart;
- `HTGeometry/DifferenceHyperexponentialRiccati.lean`, `HTGeometry/MultiQDifference.lean`.

The cards' equations are first order inhomogeneous with *constant* homogeneous coefficient:
card 7's `R - a·rho R = r` is `sigma R = a^{-1} R - a^{-1} r`.  So the ADH specialization needed is
the inhomogeneous first-order case with hyperexponential homogeneous part, which is exactly what
the two telescoping theorems above are shaped for.  The next step on this gate is to state and
prove that specialization and then discharge the telescoping hypothesis for each card's explicit
inhomogeneity.

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

## ADH gate: the executable route (cards 7-11)

The Adamczewski-Dreyfus-Hardouin dichotomy is *not* needed in full.  For a first-order
inhomogeneous q-difference equation the corpus's own differential Ostrowski criterion
(`AutomorphismFamilyOstrowski.automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping`)
gives hypertranscendence directly, once three things are supplied.  Card 7 is the model case:
`R - a·rho R = r`, `rho f(z) = f(bz)`, `r = (1-a)/(1-z)`, `0 < a,b < 1`.

**Step 1 (twist).**  Let `s := -log a / log b` and `h := z^s`, so `rho h = b^s h = a^{-1} h`.
Then `u := R/h` satisfies the *additive* equation `rho u = u - r/h`, whose increment lies in
`K := C(z)(h)`.  `h` is differentially algebraic over `C(z)` (`delta h = s h`), so
hypertranscendence of `u` over `K` gives hypertranscendence of `R` over `C(z)`.

**Step 2 (ambient with constant invariants).**  Take `L := HahnSeries R C` with the dilation
`sigma := hahnDilation chi_b`, `chi_b(g) = b^g`, and the derivation `delta := hahnGrade id`
(the Euler operator `z d/dz`).  Since `0 < b < 1`, `b^g = 1` forces `g = 0`, so the
sigma-invariants of `L` are exactly the constants: this discharges the `hfixed` hypothesis that
every existing corpus reduction (double sine included) still carries.
*Built*: `HTGeometry/HahnDilation.lean` — `hahnDilation`, `hahnGrade`, `hahnDerivation`,
`hahnDifferential`, `hahnScale_hahnGrade`, `hahnDilation_eq_self_iff_single`,
`exists_single_of_hahnDilation_eq_self`, plus the missing two-sided `coeff_mul_of_support_subset`.

**Step 3 (no telescoper).**  `delta^j(r/h) = ((delta - s)^j r)/h`, so a constant-coefficient jet
character of the increment is `Q(r)/h` with `Q` a nonzero constant-coefficient operator; the
`h`-adic coefficient at `h^{-1}` of `tau k - k` for `k` in `C(z)(h)` is `a·rho(k_{-1}) - k_{-1}`.
So the telescoping hypothesis reduces to the **twisted** dilation coboundary equation
`a·rho(k) - k = Q(r)` over `C(z)`.  Since `r = cotModel c - c` with `c = -(1-a)/2`, `Q(r)` is a
nonzero Euler combination of the cotangent model plus a constant, which has a pole at `1` and no
other pole on the orbit `b^Z`.
*Built*: `HTGeometry/TwistedDilationOrbitObstruction.lean` —
`not_twistedDilationTelescoped_of_unique_multOrbit_pole` and
`not_twistedDilationTelescoped_eulerCombination_cotModel`, both from the existing
`not_telescoped_of_unique_orbit_pole_gen` two-jump argument.

**Remaining for card 7.**  (i) the base field: `K = RatFunc (RatFunc C)` with
`twoCylinderDifferential s` (corpus-owned) and the two-variable dilation `k(z,h) -> k(bz,a^{-1}h)`;
(ii) its embedding into `L` (`z -> single 1 1`, `h -> single s 1`), injective when `s` is
irrational; (iii) the `h`-adic coefficient extraction of step 3; (iv) the multiplicatively
dependent case `s = -p/q`, where instead `K = C(w)`, `w = z^{1/q}`, `h = w^{-p}`, and the
obstruction is the *untwisted* one on the `q` distinct orbits of the `q`-th roots of unity.
