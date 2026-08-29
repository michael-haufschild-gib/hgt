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

### ADH gate: build state

Landed and umbrella-wired (all clean under `lake env lean`, no warnings):

1. `HTGeometry/HahnDilation.lean` — Hahn series carry a dilation `hahnScale`/`hahnDilation` for
   every exponential character of the value group, a grading `hahnGrade` with the Leibniz rule and
   the resulting `hahnDerivation`/`hahnDifferential`, the coefficient twist `hahnTwist`, the
   coefficientwise operator `hahnCoeffMap` with its Leibniz rule, the coefficient ring map
   `hahnMapRingHom`, and all the commutation laws between them.  The two headline facts are
   `hahnDilation_eq_self_iff_single` and `exists_single_of_hahnDilation_eq_self`: a faithful
   character forces the invariants to be the constants.  Also `coeff_mul_of_support_subset`
   (mathlib has only the one-sided versions).
2. `HTGeometry/TwistedDilationOrbitObstruction.lean` — `γ k(qX) - k(X) = r` has no rational
   solution when `r` has a single pole on the orbit `p₀ q^Z`, and the cotangent-model corollary.
3. `HTGeometry/TwistedRatFuncLaurent.lean` — the twisted dilation `ratFuncTwist φ q` of `K(X)`
   (coordinate scaled by `q`, coefficients moved by `φ`), its Laurent expansion
   `algebraMap_ratFuncTwist`, and the descent `exists_twistedCoboundary_of_ratFuncTwist`: a
   constant that is a twisted coboundary in `K(X)` is already one in `K`.
4. `HTGeometry/QDifferenceLaurentModel.lean` — the ambient field `k((z))((h))` with the dilation
   `z ↦ bz`, `h ↦ a⁻¹h` (`qDilation`) and the derivation `δz = z`, `δh = sh` (`qDerivation`,
   `qDifferential`), their commutation, and `exists_C_C_of_qDilation_eq_self`: **the invariants are
   the constants whenever `bᵐ = aⁿ` forces `m = n = 0`.**  This is the `hfixed` hypothesis that
   every previous corpus reduction (double sine included) had to carry.

Remaining for card 7, in order: (a) `qEmbed : k(z)(h) → k((z))((h))` and its intertwining with the
dilations (needs only the two compatibilities `algebraMap ∘ ratFuncScale = innerDilation ∘
algebraMap` and the constant expansion, both instances of `algebraMap_ratFuncTwist`); (b) the
derivation compatibility `DifferentialAlgebra` (Euler operator versus Euler grading, by the
agreeing-Leibniz-operators argument, polynomials first, then the quotient rule); (c) the response
`R` as an element of `k((z))` with its functional equation, `u := R h⁻¹`, and the increment
`-r h⁻¹`; (d) `hnot` via (3) + (2); (e) the multiplicatively dependent case `aⁿ = bᵐ`, where the
base is the ramified `k(w)`, `w = z^{1/n}`, and the obstruction is the untwisted one on the `n`
distinct orbits of the `n`-th roots of unity.

### ADH gate: the criterion is closed (generic multiplier pair)

`HTGeometry/QDifferenceInhomogeneousHT.lean` now proves, unconditionally,

> `hypertranscendentalOver_of_qDifference_cotModel` — let `a, b` be nonzero elements of a
> characteristic-zero field with `bᵐ = aⁿ` only for `m = n = 0`, let `r = cotModel cc + γ₀` with
> `cc ≠ 0`, and let `R` be a Laurent series with `R - a·R(bz) = r`.  Then `R` is differentially
> transcendental over `k(z)` for the Euler derivation.

This is the `q`-difference case of the Adamczewski–Dreyfus–Hardouin dichotomy in the shape the
five cards need, and it is proved from the corpus's own differential Ostrowski criterion rather
than imported.  The chain, with the modules that carry it:

| Step | Module |
|---|---|
| Hahn dilations, gradings, twists, invariants | `HahnDilation` |
| twisted orbit obstruction `γk(qX) − k(X) = r` | `TwistedDilationOrbitObstruction` |
| Laurent descent of a twisted coboundary | `TwistedRatFuncLaurent` |
| ambient `k((z))((h))`, its dilation and derivation, invariants = constants | `QDifferenceLaurentModel` |
| base `k(z)(h)` and its embedding | `QDifferenceRatFuncEmbedding` |
| Euler operator = Laurent grading, in one and two variables | `QDifferenceEulerCompat` |
| the Ostrowski criterion instantiated in the model | `QDifferenceOstrowski` |
| jets of `−r/h`, no telescoper, the shift identity, the transfer | `QDifferenceInhomogeneousHT` |

Choosing `δ h = 0` (legitimate: any derivation commuting with the dilation may be used) removes the
shifted-operator binomial that the naive `h = z^s` normalization would need — the jets of the
increment are then literally the Euler jets of `r` divided by `h`.

**What card 7 still needs.**  (i) `(1−a)/(1−z) = cotModel(−(1−a)/2) + (1−a)/2`; (ii) the corpus's
`geometricKallenLehmannResponse` (a `PowerSeries ℝ`) transported to `LaurentSeries ℂ` with its
self-similarity identity in the form `R − a·R(bz) = r`; (iii) the equivalence of hypertranscendence
for `z d/dz` and for `d/dz`; (iv) the propagator transfer `G(−1/z) = −z R(z)`; (v) the
multiplicatively *dependent* case `aⁿ = bᵐ`, where the whole argument runs in the single ramified
variable `w = z^{1/n}` (no second coordinate is needed, since `h = w^{−m}` is already rational) and
the only new ingredient is that a nonzero constant-coefficient Euler combination of a function with
a simple pole at `ζ` has a pole there — the pole-order-increases-by-one lemma.

### Card 7: the response is Lean-hypertranscendental (generic multipliers)

`HTGeometry/GeometricKallenLehmannHypertranscendence.lean` closes the card's own headline for every
multiplicatively independent multiplier pair:

> `hypertranscendentalOver_qDifferenceSolution` — for `a, b ≠ 0` with `bᵐ = aⁿ` only trivially, and
> `w ≠ 0`, the unique Laurent solution of `R − a·R(bz) = w/(1−z)` is differentially transcendental
> over `k(z)` for the Euler derivation.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Supporting: `qDifferenceSolution` (coefficientwise solution), `qDifferenceSolution_spec` (it solves
the equation), `qDifferenceSolution_unique` (there is no other Laurent solution — so the corpus's
`geometricKallenLehmannResponse` *is* this series once transported to a field), and
`no_resonance_of_multIndependent` (`a bᵐ ≠ 1`), plus the identification
`w/(1−z) = cotModel(−w/2) + w/2`.

Card 7's residue is now exactly: the multiplicatively dependent case, the Euler-versus-`d/dz`
transfer (the corpus's `ClockChangeTriangular.isHypertranscendentalOver_clockRescale_iff` is the
tool — it needs a bridge between `IsDifferentiallyAlgebraicOver` and `DifferentialAlgebraicOver`),
the transport of the real response to `LaurentSeries ℂ`, and the propagator substitution.

### The one-variable engine, and card 10's headline

Two more modules, both umbrella-wired, both auditing to the standard three axioms:

* `HTGeometry/SimplePoleEulerCombination.lean` — the Euler operator preserves regularity
  (`regularAt_ratFuncEulerOp`, `regularAt_eulerCombination`); the principal part of a quotient with
  a single linear factor splits off (`exists_regularAt_sub_principalPart`); and **a nonzero
  constant-coefficient Euler combination of a rational function with a simple pole at any `p₀ ≠ 0`
  has a pole there** (`not_regularAt_eulerCombination_simplePole`).  This generalizes the corpus's
  cotangent-model computation, which was tied to a pole at `1` with the specific numerator
  `c(X+1)`; the general case follows by splitting off the principal part and dilating the
  coordinate.
* `HTGeometry/QDifferenceLaurentOneVariable.lean` — when the multiplier of the homogeneous equation
  is a *power of the dilation parameter*, no second coordinate is needed: `k((w))` with `w ↦ βw`
  already has constant invariants (`exists_C_of_innerDilation_eq_self`), the criterion instantiates
  (`differentialIndependent_of_oneVariable_primitive`), and
  **`hypertranscendentalOver_of_monomialTwist`** concludes hypertranscendence from a simple-pole
  increment with a single pole on its orbit.

`HTGeometry/ReciprocalQLadderHypertranscendence.lean` applies it to **card 10**:

> `hypertranscendentalOver_qLadderResolvent` — every Laurent solution of `R(x) − β·R(βx) = 1/(1+x)`
> with `β` not a root of unity is differentially transcendental over `k(x)`.

That is the card's `(13) ⟹ (16)`, and it is *shorter* than the card's own route: the card passes
through the product `P_r` and the Riccati transfer `(14)–(17)`, which are not needed — the
inhomogeneous equation is attacked directly.

**Card type map for the ADH group.**  Cards 7 and 10 are `q`-difference (dilation `z ↦ bz`) and are
now served.  Cards 8, 9 and 11 are **Mahler** (`z ↦ z^p`): there the natural ambient is the Hahn
field with `ℚ`-exponents, where `z ↦ z^p` *is* an automorphism and the invariants are again the
constants (an invariant would have an infinite descending support).  But no nonzero grading
commutes with it — additive maps are `ℚ`-linear, so `μ(pγ) = pμ(γ) = μ(γ)` forces `μ = 0` — and the
Euler derivation instead satisfies `δσ = p·σδ`.  The corpus's criterion needs commutation, and the
short proof of `automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping`
reduces to the *algebraic* independence criterion through `σ(δⁿx) = δⁿx + δⁿb`; in the twisted case
this becomes `σ(δⁿx) = p^{-n}(δⁿx + δⁿb)`, an affine action with a nonconstant multiplier per jet.
So cards 8, 9, 11 need the twisted-commutation form of the criterion, which is the parameterized
Galois content of ADH proper.  That is the next construction.

### Card 10 promoted; the Euler/ordinary bridge; card 7's propagator

**Card 10 is at stage 3.**  Its file now carries a Lean-status table and lives in
`3-formalized/not_new_scientific_knowledge/04-rg-stochastic-quantum-fields/`.  Everything the card
proves is formalized except the two inputs it itself quotes (the Gesztesy--Karwowski--Zhao soliton
spectrum and the Källén--Lehmann/Wightman reconstruction): the reciprocal mass sequence and its
strict growth, the logarithmic counting bound and local finiteness, the affine constraint with its
unique one-sided solution, hypertranscendence of the response for both derivations, the geometric
de Sitter principal-series frequencies, and the Mahler-clock identity.

New since the last entry:

* `HTGeometry/EulerOrdinaryDerivationBridge.lean` — **differential algebraicity over `k(z)` is the
  same notion for `z d/dz` and for `d/dz`.**  Both directions, by the finite-transcendence-degree
  criterion: the differential field generated for one derivation is closed under the other because
  the two differ by a unit of the base field.  This is what lets a card whose claim is about the
  ordinary derivative be discharged by a criterion that is natural for the Euler operator.
* `HTGeometry/ReciprocalQLadderMassSpectrum.lean` — the mass sequence, the counting bound, the
  de Sitter frequencies, the Mahler clock.
* `QDifferenceInhomogeneousHT.hypertranscendentalOver_of_qDifference_simplePole` — the two-variable
  criterion now accepts *any* simple-pole inhomogeneity, not just the cotangent model.
* `GeometricKallenLehmannHypertranscendence.propagatorGerm_equation` and
  `hypertranscendentalOver_propagatorGerm` — **card 7's item 4**: reciprocal inversion
  `G(-1/z) = -z R(z)` turns the response equation into the same shape with multiplier `a/b` and a
  reflected pole, so the criterion applies again; no transport lemma is needed.
* `HTGeometry/RamifiedLaurentTransfer.lean` — the substitution `z = w^q` on Laurent series and on
  rational functions, its compatibility with dilations (`β^q ↦ β`) and with the Euler operator
  (multiplication by `q`), and the rescaled derivation for which the ramification is a
  *differential* homomorphism.

Card 7's residue is now only the multiplicatively dependent case: given `a^q = b^p` with `p, q`
coprime, Bezout gives `β = a^u b^v` with `β^q = b` and `β^p = a`, so the one-variable engine applies
in the ramified coordinate; what remains is to transport hypertranscendence back along `ramify`,
for which the pieces above are in place.

### Card 7 promoted — the ADH gate is fully internal

**Card 7 is at stage 3**, for *every* pair `0 < a, b < 1`, and for both derivations.  The chain:

* `MultiplicativeDependenceRoot.multIndependent_or_commonRoot` — two reals in `(0,1)` are either
  multiplicatively independent or both integer powers of one positive real.  The relation lattice
  is the kernel of `(m,n) ↦ m log b − n log a`, hence generated by a primitive vector, and Bézout
  turns `a^q = b^p` into `β = aᵘbᵛ` with `β^q = b`, `β^p = a` — integer exponents only.
* Independent case: the two-variable model (`hypertranscendentalOver_of_qDifference_simplePole`).
* Dependent case: `RamifiedLaurentTransfer` — the substitution `z = w^q` intertwines the dilation
  by `β^q` with the dilation by `β`, multiplies the Euler operator by `q`, and carries rational
  functions to rational functions; `hypertranscendentalOver_of_ramifiedMonomialTwist` then applies
  the one-variable engine, and `hypertranscendentalOver_of_ramify` transports the conclusion back.
* `EulerOrdinaryDerivationBridge` supplies the card's own Euler-versus-`d/dz` step.
* The propagator (item 4) needs no new criterion: reciprocal inversion is a dilation followed by
  multiplication by the coordinate, and `differentialAlgebraicOver_innerDilation` (new) plus the
  differential-adjoin argument carry hypertranscendence across
  (`hypertranscendentalOver_propagatorGerm_of_response`).
* `geometricResponseLaurent_equation` transports the corpus's real `PowerSeries` response into
  complex Laurent series and verifies the card's constraint `(7)` there, using the identification
  of `w/(1−z)` with the geometric series.

**Status: 8 of 17 promoted.**  The nine remaining cards split as: 8, 9, 11 need the *Mahler*
criterion (`z ↦ z^p`, twisted commutation `δσ = pσδ` — the obstruction is recorded above); 12, 13
need the Becker–Bergweiler/Fernandes classification; 14 needs Ritt plus the analytic Poincaré
theorem; 15, 16 need a differentially algebraic germ category with analytic local inversion (16
also Boshernitzan–Rubel); 17 needs the second-moment law of the random Euler product, and its own
`1 → 2` gate is open on paper.

### The Mahler lane: the model, and the reduction that makes the criterion apply

`HTGeometry/MahlerHahnModel.lean` starts the lane for cards 8, 9 and 11.  On Hahn series with
**rational** exponents the substitution `w ↦ w^p` is a ring automorphism (`mahlerHom`, exponents
stretched by `p`), and

> `eq_C_of_mahlerHom_eq_self` — **its only fixed series are the constants.**

The proof is not the diagonal argument used for dilations: `w ↦ w^p` does not act by scalars.  A
fixed series has `f(γ/p) = f(γ)` for every exponent, so a nonzero exponent generates an infinite
strictly decreasing chain in the support — `γ/pⁿ ↓ 0` for `γ > 0`, `γ·pⁿ ↓ −∞` for `γ < 0` — which
a Hahn support cannot contain.

**The reduction that makes the corpus's criterion apply.**  The Mahler pair does not commute:
`δσ = p·σδ`, so the jets satisfy `σ(δⁿu) = p^{-n}(δⁿu + δⁿb)` — affine with a multiplier depending
on the jet, which the pure-shift criterion cannot accept.  The fix is a *single* twisting element:
adjoin `h` with `σh = p^{-1}h` and `δh = 0` (the second is forced: `δh = λh` and the twisted
commutation give `p^{-1}λ = λ`).  Then `vₙ := δⁿu / hⁿ` satisfies `σvₙ = vₙ + δⁿb/hⁿ` — pure
shifts, for the whole jet family at once — and the corpus's *algebraic* independence criterion
applies to `(vₙ)`, giving algebraic independence of `(δⁿu)` over `K(h)`, hence differential
transcendence over `K`.  Adjoining `h` does not spoil the invariants: `σf = pⁿf` in the Hahn field
forces `f = 0` for `n ≠ 0` by the same support argument.

What remains in this lane: the adjunction `K(h)` with its `σ`, `δ`; the jets-to-shifts reduction;
the criterion instantiation; and the non-telescoping obstruction, which for these cards is the
statement that `λ·y(w^p) − y(w) = ρ` has no *rational* solution — the formal solution's
coefficients are supported on the lacunary set `{p^k}` with geometrically growing values, which no
rational function has.

### Mahler lane: model, base, derivation and the jets-to-shifts law are built

`MahlerHahnModel` and `MahlerRatFuncEmbedding` now carry, all unconditional and umbrella-wired:

| Theorem | Content |
|---|---|
| `eq_C_of_mahlerHom_eq_self`, `eq_zero_of_mahlerHom_eq_smul` | `w ↦ w^p` on rational-exponent Hahn series fixes only constants and has **no eigenvectors at all** |
| `exists_C_C_of_mahlerDilation_eq_self` | in `HahnSeries ℤ (HahnSeries ℚ k)` with `w ↦ w^p`, `h ↦ p⁻¹h`, **the invariants are the constants** |
| `embDomain_comp` | composition law for `HahnSeries.embDomain` (missing in mathlib) |
| `laurentToHahn`, `laurentToHahn_ramify` | Laurent series inside the Hahn field; stretching integer exponents *is* the Mahler substitution |
| `mahlerBaseDilation`, `mahlerEmbed`, `mahlerEmbed_mahlerBaseDilation` | the base `k(w)(h)`, its Hahn expansion, and the restriction property |
| `hahnQEuler`, `hahnQEuler_mahlerHom` | the Euler derivation and the twisted commutation `δσ = p·σδ` at the coefficient level |
| `mahlerDifferential`, `mahlerAmbientDeriv_mahlerDilation` | the ambient derivation and its twisted commutation |
| **`mahlerDilation_deriv_iterate`** | `σδⁿ = p^{-n}δⁿσ` — the jet-scaling law |
| **`mahler_twistedJet_shift`** | dividing the `n`-th jet by `hⁿ` cancels `p^{-n}`: the whole jet family becomes **simultaneous additive primitives**, which is exactly what the corpus's algebraic-independence criterion consumes |
| `ratFuncToHahn_eulerOp` | the Euler operator of `k(w)` is the Hahn grading |

Remaining in this lane: the base derivation compatibility (the analogue of `qEmbed_twoCylDerivation`
for `mahlerEmbed`), the criterion instantiation, and the non-telescoping obstruction — for cards 8,
9 and 11 the latter is that `λ·y(w^p) − y(w) = ρ` has no rational solution, the formal solution
being supported on `{p^k}` with geometrically growing coefficients.

### Mahler lane: the criterion is instantiated and the obstruction is proved

The lane turned on one observation: the Euler derivation `θ` and the Mahler substitution `σ` obey
`θσ = p·σθ`, but the twisting coordinate satisfies `σ(h⁻¹) = p·h⁻¹`, so **`δ := h⁻¹·θ` commutes
with `σ` exactly**.  With that derivation the corpus's automorphism-family criterion applies
verbatim — no jet rescaling, no operator binomial.

| Module | Content |
|---|---|
| `MahlerPerfectBase` | the ramified tower `k(w^{1/pⁿ})` inside the Hahn field, its union (the `p`-perfect rational base `F`), and `σ|F` as an **automorphism** — the smallest base on which the substitution is invertible |
| `MahlerPerfectEmbedding` | general twisted dilation `ratFuncTwistEquiv` of `K(h)`; the two-variable base `F(h)`, its substitution, and the Hahn expansion; the base substitution is the restriction of the ambient one |
| `MahlerPerfectDerivation` | the Euler operator preserves every ramified level (`p^{-n}` times the level Euler operator), hence the perfect base is a differential field |
| `MahlerCommutingDerivation` | `δ = h⁻¹·θ`, its Leibniz rule, and **`σδ = δσ`** |
| `MahlerPerfectDifferentialBridge` | `F(h)` is a differential subfield for `δ`; the coefficient derivation is the restriction of the ambient one |
| `MahlerOstrowski` | `σ` as a ring automorphism of the ambient (inverse substitution `w ↦ w^{1/p}`), constants, and **`differentialIndependent_of_mahler_primitive`** — the Ostrowski criterion in the Mahler model |
| `MahlerRationalNoTelescoper` | **a rational solution of `λ·z(w^p) − z(w) = ρ` is a polynomial** (the reduced denominator would divide its own `p`-fold expansion), and the lacunary coefficient descent: for `ρ = a·w^N + b·w^{pN}` a solution exists **iff `λa + b = 0`** |
| `MahlerIncrementJets` | jets of an increment `A·h⁻¹`: the twisting coordinate is a constant of `δ`, so `δʲ(A·h⁻¹) = (θʲA)·h^{−(j+1)}` |
| `MahlerPerfectNoTelescoper` | **`no_perfectBase_telescoper`**: `p^m·σ(z) − z ≠ a·w + b·w^p` in the perfect base whenever `p^m a + b ≠ 0` — every element is rational at some level, and the level equation is the one just ruled out |

For the three cards the increment is `−((p−2)w + w^p)·h⁻¹`, whose `j`-th jet contributes
`a = −c(p−2)`, `b = −c·p^j` at multiplier `λ = p^{j+1}`; the resonance is
`λa + b = −c·p^j·(p−1)² ≠ 0`, so the telescoper is excluded for every `p ≥ 2`.

### Thermal Mahler card PROMOTED; the next q-difference gate

`ultrametric-thermal-mahler-hypertranscendence` is at stage 3: the germ, its Mahler equation,
rigidity, irrationality, hypertranscendence over `k(w)` for the Euler derivation, the rational
closed form of the spectral zeta series, and the DA/HT reporter split are all Lean-proved
(`MahlerTraceGerm`, `MahlerTraceCard`, `UltrametricSpectralZeta`).

**Next: `ultrametric-one-loop-resolvent-hypertranscendence`.**  Its equation

```text
Q(x) = (p−2)/(x+1)^m + 1/(x+p)^m + p^(1−m) Q(x/p)
```

is a *q*-difference equation with `q = 1/p`.  Multiplying by the monomial `z^(m−1)` — an
eigenvector of the dilation with eigenvalue `p^(1−m)` — turns it into a pure shift
`σu = u − ρ·z^(m−1)` in the **one-variable** Laurent model already built for cards 7 and 10, so
the criterion applies with no second coordinate.

The obstruction is *not* the unique-orbit pole lemma: the two poles `−1` and `−p` lie in the same
multiplicative orbit.  What is needed is the **orbit-mass obstruction**: writing `A_n` for the
coefficient of the top-order pole of `k` at the orbit point `q^n a`, the coboundary equation gives
`γq^(−d)A_(n+1) − A_n = B_n`, and summing against the weights `λ^n`, `λ = γq^(−d)`, telescopes to

```text
Σ_n λ^n B_n = 0     for every rational coboundary.
```

For the resolvent increment the top-order coefficients sit at `n = 0` (the point `−1`) and
`n = −1` (the point `−p`), with values `(p−2)(m)_J(−1)^(m−1)` and `p^J(m)_J(−p)^(m−1)`, and
`λ = p^(m+J)`; the weighted sum is

```text
(m)_J(−1)^(m−1)·[(p−2) + 1/p] = (m)_J(−1)^(m−1)(p−1)²/p ≠ 0,
```

the **same `(p−1)²` resonance** that closed the Mahler lane.  So the card reduces to formalizing
the orbit-mass obstruction (top-order pole coefficients via translation + Laurent expansion, the
`ratFuncAddTranslationCompHom` substitution, and the finite telescoping sum) plus the Euler-jet
pole calculus `δ^J[(x+c)^(−m)] = c^J(m)_J(x+c)^(−m−J) + lower order`.

### The orbit-mass obstruction is built

`RationalPolePart` and `EulerPolePartCalculus` now carry a complete principal-part calculus for
rational functions, all unconditional:

| Theorem | Content |
|---|---|
| `polePart` | the coefficient of `(x−c)^(−d)`, read off the Laurent expansion at the origin of the translate; additive, and `polePart (a·g) = a·polePart g` |
| `polePart_eq_zero_of_regularAt`, `polePart_eq_zero_of_regularAt_mul_pow` | principal parts vanish at regular points, and above the pole order |
| `finite_support_polePart_multOrbit` | along a multiplicative orbit only finitely many principal parts are nonzero |
| `polePart_ratFuncScale` | the dilation law `polePart (g(qx)) c d = q^(−d)·polePart g (qc) d` |
| **`no_dilationTelescoper_of_orbit_mass`** | **the obstruction**: for a coboundary the `λ`-weighted sum of top-order principal parts along an orbit telescopes to zero, so an inhomogeneity whose two adjacent top-order parts have nonzero weighted sum is not a coboundary |
| `polePart_eulerOp`, `polePart_eulerOp_iterate` | the Euler operator acts on the expansion at `c` as `(t+c)d/dt`; the `J`-th jet multiplies the top part by `∏_{i<J} −c(m+i)` and raises the order by `J` |
| `polePart_top_of_repr` | the top part from an explicit regular representation |

This replaces the unique-orbit-pole lemma in the case that matters for the one-loop resolvent card,
where the two poles `−1` and `−p` lie in one orbit.
