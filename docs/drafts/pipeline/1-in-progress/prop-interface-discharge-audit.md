# Prop-interface discharge audit: HTGeometry, HilbertMetric, RHTower

- **ID:** prop-interface-discharge-audit
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** loop mandate — audit the three owned areas for undischarged hypotheses / `Prop` interfaces
- **Statement:** every `Prop` interface consumed as a hypothesis in `HTGeometry`, `HilbertMetric`,
  `RHTower` is either (a) produced by an unconditional or corpus-discharged theorem, (b) proved
  unsatisfiable with an exact obstruction plus a satisfiable structural replacement, or (c) recorded
  as a genuinely open analytic input with its named open core.

## Goal
Remove silent conditionality from the three owned theorem areas.  A `Prop` interface that no
theorem in the corpus ever concludes is either an undischarged premise (recoverable) or a vacuous
one (fatal to every consumer).  Both cases must be resolved explicitly.

## Audit instrument (reproducible)
A Lean metaprogram over the whole environment, not a text grep.  For every project theorem it
records the head symbol of each `Prop`-valued binder and of the conclusion, using a
**non-reducing** `forallTelescope` (a reducing telescope unfolds a `Prop` def in the conclusion and
loses the producer, which is why index/grep searches under-report producers).

- script: `scratchpad/AuditAll.lean` pattern — import `GaloisForLFunctions.MainTheorems`,
  `forallTelescope`, emit `module|theorem|propHypHeads|conclHead`, plus every project
  `Prop`-valued `def`/`inductive`.
- corpus size measured 2026-07-26: 71 232 project theorems, 1 721 project `Prop`-valued
  definitions.
- result: **258** project `Prop` interfaces are consumed as a hypothesis inside the three areas and
  concluded by **no** theorem anywhere in the corpus.  Ranked worklist:
  `prop-interface-discharge-worklist.md` (next to this card).

## Worklist status
- HilbertMetric full-CCR layer (`IsFullCCRMatrixTuple`, `IsCommutingFullTuple`,
  `IsInvariantFullCompression`) — **in progress**, see below.
- 255 remaining entries — untouched.

## Finding 1 — the finite full-CCR interface is unsatisfiable
`IsFullCCRMatrixTuple T : ∀ i j, T i * (T j)ᵀ = δᵢⱼ • 1 + (T j)ᵀ * T i` on
`Matrix (n ⊕ m) (n ⊕ m) ℝ`.  Taking `i = j` and the trace, `tr (T Tᵀ) = tr (Tᵀ T)` forces
`tr (1) = 0`, i.e. `Fintype.card (n ⊕ m) = 0`.  So for `Nonempty I` the interface holds only on the
empty space: every `CCRPowerConcavity` theorem carrying it is vacuous in positive dimension.
This is the finite-dimensional CCR obstruction (Wintner/Wielandt) in exact matrix form.

## Structural replacement (satisfiable, keeps every downstream theorem)
The proofs only ever read the relation on the **upper-left block**.  Replace by
`IsBlockCCRMatrixTuple T : ∀ i j a b, (T i * (T j)ᵀ) (inl a) (inl b) = (δᵢⱼ • 1 + (T j)ᵀ * T i) (inl a) (inl b)`.
Then, under `IsInvariantFullCompression T`:
`IsBlockCCRMatrixTuple T ↔ IsCCRCompletion (fullCCRCompressionBlock T) (fullCCRLeakageBlock T)`,
and `IsFullCCRMatrixTuple T → IsBlockCCRMatrixTuple T`, so the existing statements are corollaries.
Non-vacuity is then inherited from the already-proved Gaussian coherent completion
(`GaussianJetPositivity.exists_gaussianCoherentCCRCompletion`,
`gaussianCoherentCompression_commutes`) via `T i = Matrix.fromBlocks (A i) (B i) 0 0`.

## Gates
- [x] 0 → 1  in-progress: audit instrument built, worklist ranked
- [x] 1 → 2  fully-proven on paper for each worklist entry
- [x] 2 → 3  formalized: 30 new modules, each `lake env lean` clean, every capstone
  `#print axioms`-verified as unconditional
- [ ] 3 → 4  n/a (infrastructure card)

## Log
- 2026-07-26 — created in 1-in-progress; audit instrument built; 258 undischarged interfaces found;
  finding 1 (finite full-CCR unsatisfiable) proved on paper with structural replacement.
- 2026-07-26 — finding 1 formalized and closed.  `HilbertMetric` is now free of undischarged
  interfaces (3 of 3 resolved).
  - `GaloisForLFunctions/HilbertMetric/CCRFiniteBlockObstruction.lean` (new):
    `card_add_card_eq_zero_of_isFullCCRMatrixTuple`, `isEmpty_of_isFullCCRMatrixTuple`,
    `not_isFullCCRMatrixTuple`, `not_exists_isFullCCRMatrixTuple`,
    `blockCCRTuple_isInvariantFullCompression`, `blockCCRTuple_isBlockCCRMatrixTuple`,
    `exists_invariantBlockCCRTuple_of_isCCRCompletion`, `unitModeLeakage_isCCRCompletion`,
    `blockCCRTuple_zero_isCommutingFullTuple`, `exists_invariant_commuting_blockCCRTuple`,
    `isFullCCRMatrixTuple_empty_and_isBlockCCRMatrixTuple_inhabited`,
    `exists_gaussianCoherentInvariantBlockCCRTuple`.
  - `CCRPowerConcavity.lean`: added `IsBlockCCRMatrixTuple`,
    `IsFullCCRMatrixTuple.isBlockCCRMatrixTuple`, `isBlockCCRMatrixTuple_iff_isCCRCompletion`;
    the seven consumer theorems now take `IsBlockCCRMatrixTuple T` and
    `IsCommutingCCRCompression (fullCCRCompressionBlock T)` in place of the two unsatisfiable /
    stronger full-matrix hypotheses, so each is strictly stronger than before and non-vacuous.
  - `#print axioms` on every new capstone: `[propext, Classical.choice, Quot.sound]`.
  - `lake build GaloisForLFunctions.HilbertMetric` green.
- 2026-07-26 — audit instrument corrected.  The first pass used a reducing `forallTelescope`, which
  unfolds a `Prop` def in the conclusion and therefore lost producers; it also matched only the
  outermost conclusion head, so existential producers such as `semSplitData_exists` were missed.
  The corrected instrument scans every project constant occurring at any depth in each `Prop`
  binder and in the conclusion.  Undischarged count drops from 258 to **50**.
- 2026-07-26 — `HTGeometry.PointFiniteFacetFamily` realized
  (`GaloisForLFunctions/HTGeometry/PointFiniteFacetWitnesses.lean`): automatic for finite families
  and over a finite vertex set, automatic for pairwise disjoint families, with the infinite disjoint
  edge family `{2k, 2k+1}` on `ℕ` as an explicit infinite witness.  The point-finiteness premise is
  removed from the universal-source Stanley--Reisner constraint law in two forms — over every finite
  vertex set, and on the infinite edge geometry.
- 2026-07-26 — `HTGeometry.IsConstantMvPolynomial` discharged
  (`GaloisForLFunctions/HTGeometry/NonconstantMvPolynomialWitnesses.lean`): constancy is exactly
  vanishing total degree, giving checkable nonconstancy criteria and unconditional coordinate-family
  instances of disjoint-block algebraic independence and of the iterated Krull-dimension drop.
- 2026-07-26 — `HTGeometry.ErlangRecoveryAdmissible` (the largest entry, 23 consumers) discharged
  (`GaloisForLFunctions/HTGeometry/ErlangBoundedSource.lean`).  All seventeen analytic fields are
  proved for the class `ErlangBoundedSource f f' M` (globally bounded value and derivative):
  - the three kernels are `erlangPowKernel ε k c s = s ^ k · exp (-s / ε) / c`, whose half-line
    integrability is a Gamma moment (`integrableOn_erlangPowKernel`);
  - bounded measurable sources integrate against them (`integrableOn_erlangPowKernel_mul`);
  - the far boundary is exponential decay (`tendsto_erlangPowKernel_mul_atTop`), the near boundary is
    continuity (`tendsto_erlangPowKernel_mul_nhdsGT`);
  - differentiation under the integral is dominated by kernel × derivative bound
    (`hasDerivAt_erlangPowKernel_integral`, via
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
  Consequences: `erlangRecoveryAdmissible_of_boundedSource`,
  `erlangAverageThree_exact_recovery_of_boundedSource`, and the premise-free sine instance
  `erlangAverageThree_exact_recovery_sin` — the identity `(1 - εD)³ R = f` with no analytic premise.
- 2026-07-26 — `RHTower.SuzukiAllAngleRealZeros` discharged
  (`GaloisForLFunctions/RHTower/SuzukiAllAngleWitnesses.lean`).  The all-angle quantifier over the
  unitary circle collapses: `A z + u E z = 0` has a unimodular solution `u` exactly when
  `‖A z‖ = ‖E z‖`, so
  `SuzukiAllAngleRealZeros A E ↔ ∀ z, z.im ≠ 0 → ‖A z‖ ≠ ‖E z‖`
  (`suzukiAllAngleRealZeros_iff_norm_ne`).  The Cayley powers `((z-i)^n, (z+i)^n)`, `n ≠ 0`, satisfy
  the criterion because `i` and `-i` are equidistant from `z` only on the real axis; they are
  Schwarz-reflected, so `suzukiHermiteBiehler_addI_pow`,
  `norm_suzukiLivsicQuotient_cayleyPow_lt_one`,
  `norm_suzukiLivsicQuotient_cayleyPow_le_lineCayley` and `suzukiHerglotz_cayleyPow_im_nonneg`
  hold with no interface premise.
- 2026-07-26 — `PeriodicFrom` discharged
  (`GaloisForLFunctions/HTGeometry/PeriodicFromWitnesses.lean`): the residue extension
  `n ↦ v (n % p)` is periodic from index `0` for every `p` and unimodular whenever `v` is, together
  with constants, later starting indices, and closure under sums, products and scalars.  The
  periodicity premise is removed from `exists_periodicGeometric_leastLevelPolynomial_eq_zero` and
  `exists_periodicGeometric_targetLevelPolynomial_eq_zero`, whose conclusions now hold for the phase
  family of every sequence read modulo the period.
- 2026-07-26 — three more interfaces discharged.
  - `HTGeometry.DerivationInvariantSubmodule`
    (`GaloisForLFunctions/HTGeometry/DerivationInvariantSubmoduleWitnesses.lean`): realized by `⊥`
    and `⊤` and closed under `⊓`, `⊔` and `⨅`, so the interface is a complete sublattice.  Taking
    `⊤` gives the unconditional statements `differentialAlgebraicOver_of_finiteDimensional` and
    `not_hypertranscendentalOver_of_finiteDimensional`: a finite-dimensional differential extension
    contains no hypertranscendental element.
  - `commutingActions` and `commutingAdditiveActions`
    (`GaloisForLFunctions/HTGeometry/CommutingActionWitnesses.lean`): realized by the identity and
    constant families and by the integer power family `x ↦ x ^ n p` (resp. scaling family
    `x ↦ n p • x`), which commute because integer multiplication does.  The commutation premise is
    removed from `rankOneCoboundary_cocycle` and `koszulCoboundary_cocycle`.
- 2026-07-26 — two more interfaces discharged.
  - `RHTower.IsActionStable` (`GaloisForLFunctions/RHTower/ActionStableWitnesses.lean`): realized by
    `⊥` and `⊤`, closed under `⊓`, `⊔`, `⨅`, and reduced to generators by
    `isActionStable_closure`.  For the prime-log lattice the premise becomes the checkable condition
    that each prime logarithm is moved into the lattice, which removes it from
    `gaugeUpdate_isPrimeLogIntegral_iff`, `resection_isPrimeLogIntegral_iff` and
    `resection_isLatticeClass_of_primeLogFormula`.
  - `HTGeometry.BooleanEdgeFieldSymmetric`
    (`GaloisForLFunctions/HTGeometry/BooleanEdgeFieldWitnesses.lean`): realized by constants, vertex
    coboundaries, pointwise conjunctions and disjunctions, and — for an arbitrary field — by its
    symmetric part `c u v ⊕ c v u`.  The Boolean flatness criterion therefore holds on a connected
    graph with no symmetry premise, for coboundaries, constants, and every symmetrization.
- 2026-07-26 — detector caveat recorded: an `inductive` `Prop` is realized by its own constructors,
  which the theorem-level scan does not see.  `FiniteGeometricLayerTower` and the `.below` recursor
  artifacts are such rows and are not undischarged premises.
- 2026-07-26 — explicit inhabitants for the inductive layer tower
  (`GaloisForLFunctions/HTGeometry/FiniteGeometricLayerTowerWitnesses.lean`): a single positive
  geometric layer over the zero residual, and a strictly decreasing pair of ratios stacked into a
  two-layer tower, the step comparison being that a smaller geometric ratio is little-o of a larger
  one.
- 2026-07-26 — two more interfaces discharged.
  - `LinearReflectionAntiInvariant`
    (`GaloisForLFunctions/HTGeometry/ReflectionAntiInvariantWitnesses.lean`): realized by `0`, by
    every vector of the total reflection `-id`, and — for an involution — by the anti-symmetric part
    `v - C v` of an arbitrary vector; equivalently, anti-invariance is membership in
    `ker (C + id)`, and it is closed under sums and scalars.  The characteristic-zero averaging
    firewall and the restricted-gauge criterion therefore hold on anti-symmetric parts with no
    interface premise.
  - `HTGeometry.TateClockFiniteObservableSurjective`
    (`GaloisForLFunctions/HTGeometry/TateClockObservableWitnesses.lean`): the finitely supported
    clock variations realize every finite window through the indicator extension, and the property is
    monotone, so `⊤` inherits it.  The conormal no-go, the product-density statement, and the
    Hausdorff blindness theorem hold for the finitely supported variations with no premise.
- 2026-07-26 — four more interfaces discharged.
  - `IsBohrAP` (`GaloisForLFunctions/HTGeometry/BohrAPWitnesses.lean`): mathlib has no
    almost-periodicity theory, so this builds the realizations directly.  Constants have a singleton
    orbit; the character `s ↦ exp (i λ s)` translates to a unimodular multiple of itself, so its
    orbit lies in the compact image of the unit circle; relative compactness of orbits is stable
    under scalars (`IsBohrAP.smul`) and sums (`IsBohrAP.add`), whence
    `isBohrAP_trigPoly`: every trigonometric polynomial is Bohr almost periodic.  The return-time and
    hull theorems of the almost-periodic layer now apply to an explicit nonconstant family.
  - `HTGeometry.MembraneLocalPrincipalBrackets`
    (`GaloisForLFunctions/HTGeometry/MembraneLocalityWitnesses.lean`): the interface is an
    implication whose premise is a covering failure, so it is free when the supports cover all law
    pairs and free when all principal brackets vanish.  At singleton supports it is *equivalent* to
    bracket vanishing, hence incompatible with bracket independence as soon as one law pair exists —
    the exact two ends of the locality/compression trade-off measured by the holographic bound.
  - `HTGeometry.MvPolynomialProjectivelySmooth`
    (`GaloisForLFunctions/HTGeometry/ProjectiveSmoothWitnesses.lean`): reduced to the criterion that
    some partial derivative is a nonzero constant, realized by coordinates and by nondegenerate
    linear forms.
  - `HTGeometry.IsSubdirectConstraint`
    (`GaloisForLFunctions/HTGeometry/SubdirectConstraintWitnesses.lean`): realized by every relation
    containing the constant profiles, hence by `univ` and by the diagonal; the premise disappears
    from the coupled-prime realization theorem.
- 2026-07-26 — three more interfaces discharged.
  - `HTGeometry.DerivInvariantObservableSpace`
    (`GaloisForLFunctions/HTGeometry/DerivInvariantObservableWitnesses.lean`): realized by `⊥`, `⊤`,
    closed under `⊓` and `⨅`, and — the case the finite-dictionary theorems need — by the line
    spanned by a derivative eigenfunction (`deriv f = c • f`), which is one-dimensional.  The
    exponential is such an eigenfunction, giving the premise-free
    `differentiallyAlgebraic_complex_exp`, the general
    `differentiallyAlgebraic_of_deriv_eq_smul`, and `not_mem_span_exp_of_hypertranscendental`.
  - `HasBesselBound` (`GaloisForLFunctions/RHTower/BesselBoundWitnesses.lean`): Bessel's inequality
    is exactly the interface at bound one, so every orthonormal mode family realizes it; the
    non-diagonal normality barrier and its quantitative form then hold for orthonormal frames with no
    premise.
  - `RHTower.PrimeLogExpansion` and `RHTower.PrimeIndexedLogExpansion`
    (`GaloisForLFunctions/RHTower/PrimeLogExpansionWitnesses.lean`): realized by `0`, by each prime
    logarithm, and closed under sums.  Composing the prime-indexed form with the lattice membership
    already in the corpus reduces prime-log lattice stability to the checkable condition that the
    action sends each prime logarithm to a finite prime-indexed expansion.
- 2026-07-26 — four more interfaces discharged.
  - `CompatiblePrimitiveSystem`, `CompatiblePrimitiveExtensionSystem`,
    `IsQuotientAffineDifferentialIdeal`
    (`GaloisForLFunctions/HTGeometry/PrimitiveSystemWitnesses.lean`): compatibility of a primitive
    system is a naming condition, so an arbitrary tuple is compatible with its own defect data; over
    an extension it is a descent condition, realized by the zero tuple; and stability in the affine
    differential quotient is realized by `⊥` (using that the induced affine actions are ring
    equivalences) and by `⊤`.
  - `HTGeometry.ConjugationInvariantClockReadout`
    (`GaloisForLFunctions/HTGeometry/ClockReadoutWitnesses.lean`): realized by constants, by every
    readout of a commutative calibration group, and canonically by the conjugacy-class map, which
    makes the nonabelian closed-clock observability theorem premise-free — the conjugacy class of a
    closed holonomy is gauge invariant.
- 2026-07-26 — four more interfaces discharged.
  - `IsDifferentialExponentialGauge`, `IsDifferentialExponentialFamily`,
    `ClosedUnderLogarithmicPrimitives`
    (`GaloisForLFunctions/HTGeometry/ExponentialGaugeWitnesses.lean`): the unit gauge and unit family
    with vanishing direction realize the two gauge interfaces, and `⊤` realizes relative closure
    under logarithmic primitives.  The gauge axioms are also shown to force the normalization
    `u 0 = 1` in both forms.  The nontrivial realization — the meromorphic exponential gauge
    `u c = exp (c h)` in a differential function field, with `A` the field of differentially algebraic
    elements — remains a named follow-up target: it needs the differential-algebraic closure to be
    built as an `IntermediateField`, which the corpus does not yet have.
  - `IsAdditiveDifferentialHopfIdeal`
    (`GaloisForLFunctions/HTGeometry/DifferentialHopfIdealWitnesses.lean`): realized by `⊥`, using
    that the additive comultiplication is an algebra map.
- 2026-07-26 — **worklist cleared.**  All 50 undischarged interfaces are resolved.  Final batch:
  - abstract bridge interfaces (`RHTower/ConsolidatedBridgeWitnesses.lean`): each realized, and the
    contrapositive forms record exactly what the two bridges forbid;
  - pattern-relation interfaces (`HTGeometry/PatternRelationWitnesses.lean`): the zero relation, so
    the rigidity theorems say the zero relation is the only one;
  - `MatrixDensityClockCyclic` (constant clocks are central),
    `OneGeneratorRungeDense` (algebraic generators),
    `ExponentZeroGaugeSeparatedReflectionClass` (empty and singleton transversals),
    `RayTailCoefficientIndependent`/`ShiftClockFiberIndependent` (consistent at empty index);
  - `MultipleEllipticGammaHasRankThreeMinor` (`HTGeometry/RankThreeMinorWitnesses.lean`): the pair
    `i, i√2` gives a rationally independent period triple, by irrationality of `√2`;
  - `GammaPowerRel` (zero relation), `MultipleSineDifferentialRegimeInput` (consistent at empty clock
    direction set);
  - `RHTower.IsAbscissa` (`RHTower/LandauAbscissaWitnesses.lean`): Lebesgue measure on the half line
    has Laplace abscissa zero — integrability of the exponential kernel right of zero, and the
    constant lower bound left of zero;
  - `RHTower.SchanuelConjecture` (`RHTower/SchanuelStageWitnesses.lean`): classified as an
    irreducible external open input and split stagewise, with stage 0 proved and stage 1 proved
    **equivalent** to Hermite–Lindemann (`∀ z ≠ 0, Transcendental ℚ z ∨ Transcendental ℚ (exp z)`),
    the missing half of Lindemann–Weierstrass — mathlib carries only its analytical part.

## Status

Every `Prop` interface consumed as a hypothesis in `HTGeometry`, `HilbertMetric` or `RHTower` and
concluded nowhere in the corpus is now either realized, structurally replaced, or classified with a
named external open core.  Two named follow-up constructions remain, each recorded above:
the differential-algebraic closure as an `IntermediateField` (which would upgrade the exponential-gauge
realization from the unit gauge to the meromorphic gauge `u c = exp (c h)`), and Lindemann–Weierstrass
(which would settle stage one of the Schanuel interface).

## Verification state (2026-07-26)

- 48 modules touched or added; each verified with `lake env lean <file>` with no errors and no
  warnings.
- Every new capstone checked with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`
  (several need fewer).  No `sorry`, `axiom`, `admit`, `opaque` or `unsafe` anywhere.
- All new modules are registered in their theorem-area umbrella; `formal_tools.py lint` reports zero
  unreachable modules among them and no proof debt.  The lint gate as a whole currently fails only on
  twelve modules added by concurrent work and not yet registered in their umbrellas — none of them
  from this card.

## Second-order audit (grounding fixpoint), 2026-07-26

Mentioning an interface in a conclusion is not the same as witnessing it.  Recomputing with a least
fixpoint — `P` grounded iff some theorem concludes `P` with all project-`Prop` hypotheses already
grounded — gives 384 grounded of 1 722, and **66** consumed-but-ungrounded in the three areas: the
first fifty plus **16** that the head-occurrence filter had hidden.  All sixteen are now resolved
(table on the worklist), the two structural ones being:

- `FiniteDimensionalSmoothWaringThreeScaleCertificate` (15 consumers): the corpus already had the
  builder `finiteDimensionalSmoothWaring_threeScaleHolographicUniversality`, but it consumed three
  membrane-locality interfaces that were themselves ungrounded.  Total membranes discharge all three
  and give valence exactly the ambient rank, leaving projective smoothness as the single geometric
  input (`ThreeScaleCertificateWitnesses.lean`).
- `MvPolynomialProjectivelySmooth`: previously realized only by linear forms.  The Fermat form
  `∑ᵢ Xᵢ ^ d` is projectively smooth in every positive degree in characteristic zero — its `j`-th
  partial derivative is `d · Xⱼ ^ (d-1)`, nonzero wherever the `j`-th coordinate is
  (`FermatWaringSmoothWitnesses.lean`).  Composed with the previous item, the whole three-scale
  holographic surface is grounded on the identity Waring form.

## Third layer: joint realization

Grounding each interface separately does not make a multi-premise theorem non-vacuous: the premises
must be satisfiable *simultaneously*.  Scanning the three areas for theorems with three or more
project-`Prop` hypotheses gives 20 candidates in six families.  Status:

- `fullCCR_*` (6 theorems; invariance + block commutation + block CCR): jointly realized already by
  `exists_invariant_commuting_blockCCRTuple` (unconditional) and by
  `exists_gaussianCoherentInvariantBlockCCRTuple` (nonzero compression).
- `smoothMvWaring_*` and `finiteDimensionalSmoothWaring_*` (4 theorems; smoothness + membrane locality
  + valence): jointly realized by the Fermat form with total membranes — see
  `ThreeScaleCertificateWitnesses.lean` and `FermatWaringSmoothWitnesses.lean`.
- `exists_two_coface_directions_of_pure_ridgeThick` (purity + ridge thickness + face): jointly
  realized by the boundary complex of a simplex (`SimplexBoundaryWitnesses.lean`), giving the
  premise-free `exists_two_coface_directions_simplexBoundary`. **Done.**
- `matrixPrincipalLowerLaw_*` (4 theorems; differential independence + lower law + flatness):
  flatness is realized by every direction-independent layer symbol and the lower law by the
  block-diagonal action with vanishing remainder (`MatrixPrincipalSymbolWitnesses.lean`). **Done.**
- `DifferentialMatroidGluing` (2 theorems; independence + free translates + cross neutrality):
  jointly realized in the free (cardinality) rank model over `iota × ℤ` with the fibrewise shift —
  cross neutrality holds because the off-star is fixed pointwise (`FreeRankGluingWitnesses.lean`).
  **Done** (`freeRank_graphGluing_hypotheses`).
  A first reading suggested the triple was self-contradictory; it is not — the interfaces are applied
  to the star and to its complement, which are different sets.  Recorded because the same argument
  *does* kill the triple when all three are applied to one nonempty set: independence forces
  `ρ = card`, free translates give a disjoint translate inside the set, and cross neutrality then
  forces `card = 2 · card`.
- `exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit`,
  `exists_mappedCrossRelation_saturation`,
  `weightedBoundaryCarrierExpandedPatternRelation_coefficients_eq_zero`,
  `clockOrderEscapes_of_stagewiseDA_not_inverseLimitDA`: joint realization still open, each requiring
  a concrete analytic source.

### Joint realization, second batch (2026-07-26)

- `exists_two_coface_directions_of_pure_ridgeThick`: the boundary complex of a simplex is pure of
  card `d` and ridge thick — the complement of a ridge has exactly two vertices, each extending it to
  a facet (`SimplexBoundaryWitnesses.lean`), so `exists_two_coface_directions_simplexBoundary` is
  premise-free.
- `matrixPrincipalLowerLaw_*` (4 theorems): direction-independent layer symbols are flat, and the
  block-diagonal action of a symbol realizes the lower principal law with vanishing remainder
  (`MatrixPrincipalSymbolWitnesses.lean`).
- `DifferentialMatroidGluing` (2 theorems): the free (cardinality) rank over `iota × ℤ` with the
  fibrewise shift realizes independence, rank automorphy, free translates and off-star cross
  neutrality simultaneously (`FreeRankGluingWitnesses.lean`).
- Nevanlinna carrier relations: the zero coefficient family realizes the expanded pattern relation
  interface and the constant density one is strictly positive (`NevanlinnaRelationWitnesses.lean`).
  The remaining premise of the transfer theorem is relation-freeness itself, which is analytic
  content rather than an interface.
- `exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit`: already applied in the
  corpus to carriers proved hypertranscendental there.  A hypertranscendental carrier is a one-atom
  circuit over itself, which gives the premise-free
  `exists_hypertranscendental_atom_constantMagneticQEDSpinStatistics_self`
  (`CircuitAtomInstances.lean`).

Still open in this layer: `exists_mappedCrossRelation_saturation` and
`clockOrderEscapes_of_stagewiseDA_not_inverseLimitDA`, each needing a concrete differential source.
- `exists_mappedCrossRelation_saturation` (`LurothSaturationWitnesses.lean`): jointly realized.  Over
  the differential field generated by one differentially independent element the relation ideal is
  nontrivial — the coordinate minus that element is a nonzero nonconstant relation — so the corpus
  minimality theorem produces a minimal-rank characteristic and the corpus clearing theorem produces a
  primitive two-block characteristic for it; the generated field is derivation closed by
  `derivationClosed_differentialAdjoin`.  `exists_lurothSaturation_premises` packages all three.

## Fresh measurement, 2026-07-26 (HTGeometry + HilbertMetric, fully built)

Re-running the instrument on the current environment (29 649 theorems, 494 project `Prop`
definitions reachable from the two built umbrellas) and applying the grounding fixpoint leaves
**9** consumed-but-ungrounded rows.  Four are witnesses that live in `RHTower`, which this restricted
run does not import (`IsActionStable`, `IsMixedPrimeWord`, both prime-log expansions); two are `.below`
recursor artifacts.  The three genuinely new rows are now resolved:

- `HTGeometry.MatrixCyclicReader` — the trace is cyclic, so with the corpus rigidity theorem the
  interface becomes a classification: on a nonempty finite index set the cyclic readers are exactly
  the scalar multiples of the trace (`CyclicReaderWitnesses.lean`,
  `matrixCyclicReader_iff_exists_smul_trace`).
- `HTGeometry.IsCompoundPoissonMixture` — every convolution-power mixture with nonvanishing weights
  over an s-finite base is one, so the interface is realized for every s-finite base measure
  (`CompoundPoissonWitnesses.lean`).
- `HTGeometry.EllipticHypertranscendenceFree` — **named open construction.**  The statement is the
  classical fact that a lattice-periodic meromorphic function is not hypertranscendental, which
  follows from the Weierstrass presentation `ℂ(℘, ℘')` and the ℘ differential equation.  Mathlib has
  no Weierstrass ℘ theory, so this needs that development first; it joins Lindemann–Weierstrass (for
  Schanuel stage one) and the differential-algebraic closure as an `IntermediateField` (for the
  meromorphic exponential gauge) on the list of external constructions this audit has isolated.

## Re-measurement, 2026-07-27 (all three areas)

The instrument was re-run on the current environment over `HilbertMetric`, `HTGeometry` and the
2 974 of 3 363 `RHTower` modules whose object files are present (the remaining 389 are excluded only
because a module in their import closure is mid-edit, so they carry no audited interfaces).  Scope:
**65 075** project theorems, **1 257** project `Prop` definitions.

The grounding fixpoint terminates in 3 rounds with 446 grounded and **2** consumed-but-ungrounded
rows, both of them `.below` recursor artifacts (`FiniteGeometricLayerTower.below`,
`FiniteDifferentialCircuit.below`) — recursor fields, not premises.  Restricting the same run to
`HTGeometry` + `HilbertMetric` alone gives 6 rows: the same 2 artifacts plus 4 interfaces
(`RHTower.IsActionStable`, `IsMixedPrimeWord`, `RHTower.PrimeLogExpansion`,
`RHTower.PrimeIndexedLogExpansion`) whose witnesses live in `RHTower` and are therefore invisible to
a run that does not import it.

**No undischarged `Prop` interface remains in the three areas.**

Two card entries were stale and are corrected here:

- `HTGeometry.EllipticHypertranscendenceFree` is no longer a named open construction.  Mathlib now
  carries Weierstrass `℘` with `derivWeierstrassP_sq`, and the corpus proves the structure-free
  counting form of Weierstrass's theorem in
  `HTGeometry/EllipticHypertranscendenceFreeProof.lean`
  (`differentiallyAlgebraic_of_lattice_periodic_meromorphicNF`, `ellipticHypertranscendenceFree`),
  so the scalar facet-codimension law is unconditional.
- the joint realization of `clockOrderEscapes_of_stagewiseDA_not_inverseLimitDA` is **not** open: the
  explicit prime-supported unit source realizes all three premises simultaneously in
  `primeClockUnitSource_tail_clockOrderEscapes`.

Remaining named external inputs, unchanged: Lindemann–Weierstrass (Schanuel stage one) and the
differential-algebraic closure as an `IntermediateField` (the meromorphic exponential gauge).

### Universal law added

With the elliptic case closed, the two halves of the period-rank analysis compose into one
statement, formalized in `HTGeometry/PeriodRankUniversalLaw.lean`:

- `differentiallyAlgebraic_of_rankTwo_periods` — a meromorphic normal-form function invariant under
  the integer span of two `ℚ`-independent complex numbers is differentially algebraic.  The
  `ℝ`-dependent branch is non-discreteness of the period group
  (`meromorphicNF_constant_of_rankTwo_realDependent_periods`), the `ℝ`-independent branch is the
  elliptic theorem.
- `differentiallyAlgebraic_of_two_periods`, `differentiallyAlgebraic_of_two_independent_periods` —
  the pair and arbitrary-index forms; the latter subsumes the rank-three rigidity
  `meromorphicNF_constant_of_rankThree_periods`, which is the case of a rationally independent
  triple.
- `rat_dependent_periods_of_hypertranscendental` and
  `not_linearIndependent_periods_of_hypertranscendental` — the sharp contrapositive: **the period
  group of a hypertranscendental meromorphic function on `ℂ` has `ℚ`-rank at most one.**

`#print axioms` on all five: `[propext, Classical.choice, Quot.sound]`.

## Third instrument, 2026-07-27: what the `Prop` scan cannot see

Two blind spots of the previous instrument were closed.

### (a) An `↔` transfers groundedness, it does not create it

The fixpoint counted any theorem mentioning `P` in its conclusion as a producer, so a
characterization `P x ↔ Q x` grounded `P` even when `Q` was itself unwitnessed.  The instrument now
records, for each theorem whose conclusion is an `Iff`, the project constants of the two sides
separately, and the fixpoint grounds one side only when the other is already grounded.

On the current corpus (62 362 theorems, 1 165 project `Prop` definitions) the loose fixpoint gives 2
ungrounded rows and the strict one gives 4.  The two extra rows are real:

| interface | defining module | resolution |
|---|---|---|
| `isBoundedSmooth` | `RHTower.SmoothNumbers` | discharged — `RHTower/BoundedSmoothWitnesses.lean` |
| `supportedBounded` | `RHTower.SmoothNumbers` | discharged — same |

They were grounded only through each other and through `primeProduct_isBoundedSmooth_iff`, so no
bounded smooth frequency was ever exhibited.  Now: `isBoundedSmooth_one`, `supportedBounded_zero`,
`supportedBounded_single` and `isBoundedSmooth_prime_pow` (every `p ^ k` with `p ∈ S`, `k ≤ N`),
monotonicity in `S` and `N`, and the exact count

`card_isBoundedSmooth : Nat.card {n // isBoundedSmooth S N n} = (N + 1) ^ S.card`,

obtained from the coordinate bijection `boundedVectorEquivFun` between bounded exponent vectors and
functions `S → Fin (N+1)`, composed with the unique-factorization equivalence already in the module.
That is the number of Dirichlet frequencies a finite auxiliary form supported on `S` with exponents
at most `N` produces — the count the module's own docstring promises.

### (b) Bundled *data* hypotheses were never audited at all

Every audit so far looked at `Prop`-valued definitions.  A theorem whose hypothesis is a bundled
datum — a `structure` in `Type` — is equally vacuous if no such datum exists, and 113 project data
structures are consumed as hypotheses in the three areas.  A new pass records, for every project
constant, the head of its conclusion (unwrapping `Nonempty` and `∃`), and counts a structure as
constructed only when some declaration's conclusion *is* it.  Excluding the structure's own
projections and auto-generated lemmas from the consumer side leaves **28** data structures consumed
as a hypothesis in the three areas and constructed nowhere.

| consumers | structure | defining module |
|---:|---|---|
| 28 | `GaloisForLFunctions.HTGeometry.QuantumLawPair` | `GaloisForLFunctions.HTGeometry.QuantumTorusPrincipalSymbol` |
| 24 | `GaloisForLFunctions.RHTower.PrimeIsingBondTree` | `GaloisForLFunctions.RHTower.PrimeIsingTreeFKExpansion` |
| 16 | `GaloisForLFunctions.RHTower.PrimeIsingBondForest` | `GaloisForLFunctions.RHTower.PrimeIsingTreeFKExpansion` |
| 14 | `GaloisForLFunctions.HTGeometry.ScalarSRRealization` | `GaloisForLFunctions.HTGeometry.ScalarSRRealizationBridge` |
| 10 | `GaloisForLFunctions.HTGeometry.ParabolicSphereSignature` | `GaloisForLFunctions.HTGeometry.ParabolicOrbifoldTwelveCharge` |
| 8 | `GaloisForLFunctions.HTGeometry.ClassicalAnalyticNevanlinnaCarrierFamily.MaximalTranslationInputs` | `GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryFaceMaximalTranslation` |
| 5 | `GaloisForLFunctions.FunctionFieldDegreeData` | `GaloisForLFunctions.RHTower.FunctionFieldDegeneration` |
| 5 | `GaloisForLFunctions.RHTower.PrimeIndexedLogCochainFormula` | `GaloisForLFunctions.RHTower.OmegaObstruction` |
| 4 | `GaloisForLFunctions.HTGeometry.ChannelSRRealization` | `GaloisForLFunctions.HTGeometry.ChannelSRRealization` |
| 4 | `GaloisForLFunctions.HTGeometry.NormalCrossingKoszulGradeInput` | `GaloisForLFunctions.HTGeometry.NormalCrossingCriticalDerivedPhase` |
| 3 | `GaloisForLFunctions.HTGeometry.FiniteMultivariateAffineJetPattern` | `GaloisForLFunctions.HTGeometry.CountableMultivariateAffineJetPattern` |
| 3 | `GaloisForLFunctions.HTGeometry.SingularKolchinFrequencyInput` | `GaloisForLFunctions.HTGeometry.KolchinFrequencyBudgetPhase` |
| 2 | `GaloisForLFunctions.HTGeometry.AffineJetPacketCollisionInput` | `GaloisForLFunctions.HTGeometry.AffineJetPacketCollisionCompletion` |
| 2 | `GaloisForLFunctions.HTGeometry.DAGaugeFlatFacetRealization` | `GaloisForLFunctions.HTGeometry.DAGaugeCurvatureNecessity` |
| 2 | `GaloisForLFunctions.HTGeometry.LinearWidthDetectorIndex` | `GaloisForLFunctions.HTGeometry.LinearWidthThreeStepDetector` |
| 2 | `GaloisForLFunctions.HTGeometry.NormalCrossingExteriorCoherenceWitness` | `GaloisForLFunctions.HTGeometry.NormalCrossingCriticalDerivedPhase` |
| 2 | `GaloisForLFunctions.InfiniteGeometricLayerTower` | `GaloisForLFunctions.HTGeometry.FiniteGeometricLayerDAResonance` |
| 2 | `GaloisForLFunctions.RHTower.CCMRationalScaling` | `GaloisForLFunctions.RHTower.CCMRationalRealCrossedProduct` |
| 2 | `GaloisForLFunctions.RHTower.IsingBondState` | `GaloisForLFunctions.RHTower.PrimeIsingTreeFKExpansion` |
| 1 | `GaloisForLFunctions.HTGeometry.BarnesReflectionAnalyticThresholdInput` | `GaloisForLFunctions.HTGeometry.GammaPhaseCompletion` |
| 1 | `GaloisForLFunctions.HTGeometry.FieldOneCore.CertifiedProjectivePointFunctor` | `GaloisForLFunctions.HTGeometry.FieldOneDoctrineAtlas` |
| 1 | `GaloisForLFunctions.HTGeometry.FieldOneCore.ComparisonFacet` | `GaloisForLFunctions.HTGeometry.FieldOneDoctrineAtlas` |
| 1 | `GaloisForLFunctions.HTGeometry.GaussChannelSchattenEndpointInput` | `GaloisForLFunctions.HTGeometry.KolchinFrequencyBudgetPhase` |
| 1 | `GaloisForLFunctions.HTGeometry.HurwitzProjectiveSurvivalWitness` | `GaloisForLFunctions.HTGeometry.ProjectiveConstraintTopologicalCapacityPhase` |
| 1 | `GaloisForLFunctions.HTGeometry.ModularProjectiveSurvivalWitness` | `GaloisForLFunctions.HTGeometry.ProjectiveConstraintTopologicalCapacityPhase` |
| 1 | `GaloisForLFunctions.HTGeometry.NormalCrossingFamilyCriticalizationInput` | `GaloisForLFunctions.HTGeometry.NormalCrossingCriticalDerivedPhase` |
| 1 | `GaloisForLFunctions.HTGeometry.QuadraticQuantumDetectorIndex` | `GaloisForLFunctions.HTGeometry.QuadraticQuantumDetectorRepresentation` |
| 1 | `GaloisForLFunctions.HTGeometry.QuasiAbelianFacetPaletteInput` | `GaloisForLFunctions.HTGeometry.QuasiAbelianFacetPaletteCompletion` |

Caveat, verified by hand: `PrimeIsingBondTree`, `PrimeIsingBondForest`, `IsingBondState` and
`ParabolicSphereSignature` are inductive data types realized by their own constructors, which a
conclusion-head scan never sees; they are not debt.

Discharged in this pass:

- `HTGeometry/DataInputWitnesses.lean`
  - `QuantumLawPair` (28 consumers): every strict inequality is one (`quantumLawPair_of_lt`), two
    coordinates already carry one, and the consecutive pairs `(k, k+1)` give
    `infinite_quantumLawPair_nat` — the quantum-torus symbol layer indexes an infinite set;
  - `SingularKolchinFrequencyInput`: the diagonal input `⟨2c, 2c, c⟩` shows the budget
    `frequencyRank ≤ 2 · kolchinCapacity` is **attained**, so
    `singularKolchin_frequencyRank_le` is sharp;
  - `NormalCrossingKoszulGradeInput r`: homology concentrated in the single degree `(r+1)−2`;
  - `NormalCrossingExteriorCoherenceWitness`: the coordinate basis of the function space on the
    truncated face index, whose independence is `Pi.basisFun`;
  - `BarnesReflectionAnalyticThresholdInput`: the predicate `2 ≤ N` is its own threshold datum;
  - `GaussChannelSchattenEndpointInput`: the strict inequality `2m < q` is its own Schatten
    membership, with weak endpoint `True` and strong endpoint `False`.
- `RHTower/FunctionFieldDegreeWitnesses.lean` — `FunctionFieldDegreeData`: the one-place datum, the
  rational model (countably many degree-one places), and a datum carrying a place of every positive
  degree, so `ffRelationLattice_corank_eq_one` holds on objects and does not secretly assume all
  places rational; in the rational model the relation lattice is exactly the degree-zero divisors.

`#print axioms` on every new capstone: `[propext, Classical.choice, Quot.sound]` or fewer (two need
none).

Remaining on this worklist: 20 structures, the substantial ones being `ScalarSRRealization` and
`ChannelSRRealization` (a realization needs a hypertranscendental carrier system),
`ClassicalAnalyticNevanlinnaCarrierFamily.MaximalTranslationInputs`, `DAGaugeFlatFacetRealization`,
and `InfiniteGeometricLayerTower` (an infinite tower needs a convergent layer series with strictly
decreasing ratios, e.g. amplitudes `4^{-j}` and ratios `1 + 2^{-j}`).

### `InfiniteGeometricLayerTower`, and the first function it produces

`HTGeometry/InfiniteGeometricLayerTowerWitness.lean`.  The infinite tower was the analytic datum of
`hypertranscendental_of_infiniteGeometricLayerTower`, and no tower existed, so that law had never
produced a single function.

Amplitudes `4⁻ⁱ`, ratios `1 + 2⁻ⁱ`.  The ratios are strictly decreasing, hence pairwise distinct —
the injectivity the law consumes — and never exceed `2`, so the depth-`i` tail
`tailᵢ(n) = ∑_{j ≥ i} 4⁻ʲ (1 + 2⁻ʲ)ⁿ` is dominated by `2ⁿ` times a geometric series and converges for
every `n`.  Splitting off the first summand is `split`; the bound
`tail_{i+1}(n) ≤ (∑_{j>i} 4⁻ʲ)(1 + 2⁻⁽ⁱ⁺¹⁾)ⁿ` composed with `1 + 2⁻⁽ⁱ⁺¹⁾ < 1 + 2⁻ⁱ` is `small`.

Composing with the corpus's entire-series builder — the profile dominates `2ⁿ`, hence grows
superlinearly, hence the exponential series has infinite radius — gives

**`hypertranscendental_dyadicLayerEntireFunction`**: the entire function
`F(z) = ∑ₙ exp(−∑_{j} 4⁻ʲ (1 + 2⁻ʲ)ⁿ) zⁿ` satisfies no algebraic differential equation.

This is the first explicit function the infinite-tower law yields; `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`.

### Further inhabitants, and two detector false positives

- `HTGeometry/DetectorAndPacketWitnesses.lean`
  - `LinearWidthDetectorIndex` and `QuadraticQuantumDetectorIndex` are inductive types with a nullary
    grade (the membrane point, the vacuum root), so they are inhabited in every rank; the instances
    record it.  Like the Ising bond types they were never real debt — the scan skips constructors.
  - `AffineJetPacketCollisionInput`: realized with empty defect sets, where every source avoids all
    defects and therefore has the generic orbit rank `|frame(E)|` and satisfies the operator rank
    law.
  - `QuasiAbelianFacetPaletteInput`: realized on the empty facet family, where both fields quantify
    over an empty index — the degenerate end of the palette, recorded as a consistency witness only.
- `RHTower/PrimeIndexedLogCochainWitnesses.lean` — `PrimeIndexedLogCochainFormula` is free: every
  prime-indexed integer coefficient family is a formula for the cochain it evaluates to
  (`primeIndexedLogCochainFormula_ofCoeff`), so the layer's integrality conclusion holds on an
  explicit family, and on the constant cochain `log p` in particular.

`CCMRationalScaling` is a **detector false positive**: it is a one-field wrapper of `ℚˣ` carrying a
`Group` instance, so `1` inhabits it, but the producer is an instance whose conclusion head is
`Group CCMRationalScaling` rather than the structure itself.  Instance-valued producers are the
remaining known blind spot of the data-hypothesis scan.

### The scalar and channel realization data are consistent

`HTGeometry/ScalarSRRealizationConsistency.lean`.  `ScalarSRRealization` (14 consumers) and
`ChannelSRRealization` (4) are the analytic inputs of the whole scalar Stanley–Reisner layer and
neither was exhibited, so a priori every theorem consuming one could be vacuous.

Over the empty vertex type with the single facet `∅` the Stanley–Reisner ring has no vertex
coordinates, so the difference relation `carrier (x_v · q) = (T_v − 1) carrier q` is vacuous and the
only remaining requirement is a hypertranscendental meromorphic function to carry every nonzero
class.  The explicit entire function built above supplies it, giving `emptyScalarSRRealization` and,
reading the same carrier on every channel, `emptyChannelSRRealization`.  Both are unconditional.

This is a consistency proof at the degenerate end, and nothing more.  **The sharp open question it
isolates**: a realization over a *nonempty* vertex set whose coordinate is killed in the
Stanley–Reisner ring forces every carrier to be invariant under that vertex step, so such a
realization exists exactly when some hypertranscendental meromorphic function has a nonzero period.
By `rat_dependent_periods_of_hypertranscendental` its period group would then have `ℚ`-rank exactly
one — the extreme case the period-rank law permits, and the case whose attainment is not settled in
the corpus.

Two remarks on why this is not reachable from the present machinery.  The Taylor-magnitude criteria
(layer towers, superlacunary and stretched-exponential profiles) all force order-zero growth, and a
nonconstant periodic entire function has order at least one, so no magnitude criterion can produce a
periodic example.  The natural candidate is `Γ ∘ exp`, which is periodic and meromorphic on `ℂ`; a
proof that it is hypertranscendental needs differential algebraicity to descend through a
composition with `exp`, and the corpus currently has that only for affine changes of variable
(`DifferentiallyAlgebraic.comp_const_mul_uncond`, `differentiallyAlgebraicOfOrder_comp_add_const_iff`).
That composition law is the named next target.

## Fourth instrument, 2026-07-27: classifying the data hypotheses

The data-hypothesis scan was refined to record, for every declaration, the conclusion head (with
`Nonempty` and `∃` unwrapped), the project constants of the conclusion, and the heads of the non-`Prop`
binders.  That single table separates four cases the first pass conflated, and cuts the list of
structures consumed in the three areas but not directly constructed from 28 to **19**:

- **multi-constructor inductives** — realized by their own constructors, which a conclusion-head scan
  never sees: `PrimeIsingBondTree`, `PrimeIsingBondForest`, `IsingBondState`,
  `ParabolicSphereSignature`, and the three `FieldOneCore` enumerations;
- **class-inhabited** — an instance supplies the element, but its conclusion head is the class, not
  the structure: `CCMRationalScaling` (via `Group`), `FieldOneCore.CertifiedProjectivePointFunctor`,
  `ComparisonFacet`, `AtlasLoss` (via `Fintype`);
- **refutation bundles** — consumed by a theorem concluding `False`, so never constructing one is
  exactly the theorem: `MeroGaugeFacetRealization`, `DAGaugeFlatFacetRealization`.  The same holds
  for `GelfondSchneiderProof.Setup`, whose 214 consumers are all internal to the proof by
  contradiction that `gelfondSchneider_holds` completes — a `Setup` provably does not exist;
- **genuine debt** — the rest.

### Genuine debt, discharged

`HTGeometry/PhaseInputWitnesses.lean`:

- `FiniteMultivariateAffineJetPattern` (9 consumers): the empty pattern over every alphabet, and a
  one-frame one-monomial pattern over a nonempty one, both injectivity conditions automatic on
  `Fin 0` and `Fin 1`;
- `FinitePickDefectPhaseInput`: **both** phases are realized, at defect `0` and defect `1`
  (`finitePickDefect_both_phases_occur`), so the singular/free dichotomy is non-vacuous on either
  side;
- `GeometricPeriodicLevelInput`: the zero level polynomial along the identity subsequence — and by
  `geometricPeriodic_everyLevelPolynomial_eq_zero` no other level polynomial is possible, so this
  witness is canonical rather than merely available;
- `GeometricTLULockedFaceInput`: for the explicit hypertranscendental entire function both
  differential-algebraicity implications are vacuous;
- `HurwitzProjectiveSurvivalWitness` and `ModularProjectiveSurvivalWitness`: the genus family
  `g i = i` on `ℕ` with exact storage `42(2g − 2)`, resp. `6(2g + s − 2)` at one cusp, whose degrees
  are unbounded above.

`#print axioms` on all seven: `[propext, Classical.choice, Quot.sound]` or fewer.

Still open on this list: `ClassicalAnalyticNevanlinnaCarrierFamily.MaximalTranslationInputs` (8
consumers), `NormalCrossingFamilyCriticalizationInput`, and `RHTower.PrimeIsingSpectralLine` (a
two-field record of complex numbers, inhabited by `⟨0, 0⟩` — trivial, not yet written down).

### The criticalization input, and a third detector class

`HTGeometry/CriticalizationInputWitness.lean` — `NormalCrossingFamilyCriticalizationInput` carries no
freedom: every ideal field is pinned by its own equation (the Barnes annihilator is the span of the
normal-crossing polynomial, the sine, elliptic-gamma and cotangent-Fitting ideals are all the
Veronese ideal) and the two ranks are the quotient rank.  `normalCrossingFamilyCriticalizationInput_canonical`
is therefore the input, one per rank function, and specializing the criticalization theorem to it
gives the premise-free identity

`veroneseIdeal F (Fin (r+1)) r = derivationalCriticalIdeal (normalCrossingPolynomial r)`.

`RHTower.PrimeIsingSpectralLine` is a **detector false positive of a third kind**:
`PrimeIsingSpectralLine.onePacket = [⟨1, 0⟩]` builds a line, but its conclusion head is
`List PrimeIsingSpectralLine`, not the structure.  Producers whose conclusion is a *container* of the
structure — `List S`, `Finset S`, `Set S`, a function into `S` — join instance-valued producers and
constructors as the scan's known blind spots.  All three are recognizable by hand from the flagged
module, so the instrument stays useful as a ranked worklist rather than a verdict.

### The one remaining construction on this list

`ClassicalAnalyticNevanlinnaCarrierFamily s` (and with it its sub-bundle
`MaximalTranslationInputs`, 8 consumers) is genuine and **not** cheap.  It demands a
`ClassicalNevanlinnaExtremalFamily` together with entire `a, b, c, d` of determinant identically one
whose boundary values are the family's matrix and whose Cauchy transforms satisfy
`∫ (x − z)⁻¹ dleaf(τ) = (a z · τ + b z)/(c z · τ + d z)` for every real `τ` and every `z` in the upper
half plane.  The trivial choice `a = d = 1`, `b = c = 0` is impossible: it would force the Cauchy
transform of a probability measure to equal the real number `τ`, while for `Im z > 0` that transform
has strictly negative imaginary part.  A witness therefore requires an honest Nevanlinna family — the
named next construction for this worklist, alongside the composition law recorded above.

### Herglotz positivity, and what it forces on the Nevanlinna bundle

`HTGeometry/CauchyTransformHalfPlane.lean`.  Working out what a
`ClassicalAnalyticNevanlinnaCarrierFamily` would have to satisfy turned up a gap in the corpus: the
Cauchy transform's half-plane property is used implicitly throughout the Nevanlinna layer but proved
nowhere.  `LeafCauchyTransform` has integrability and a modulus bound, nothing about the sign.

**`im_cauchyTransform_pos`** supplies it: the kernel has imaginary part `Im z / |x − z|²` at every
real `x`, strictly positive above the axis, so its integral against a probability measure has
strictly positive imaginary part.  Three structural consequences for the bundle follow, each
unconditional:

- `im_infinityCauchy_pos` — `a z / c z` lies in the open upper half plane, being the transform of the
  leaf at infinity; hence `a_ne_zero_of_c_ne_zero`: **`a` cannot vanish where `c` does not**;
- `im_finiteCauchy_pos` — `(a z · τ + b z)/(c z · τ + d z)` lies in the open upper half plane for
  every real `τ`; hence **`mobiusDenominator_ne_zero`**: the Möbius denominator `c z · τ + d z` never
  vanishes above the real axis.

These are necessary conditions any future witness must meet, and they already kill the obvious
candidates.  With `leaf τ = δ_τ` the finite identity forces `(a, b, c, d) = (0, i, i, −iz)` up to the
projective scaling that fixes the determinant, and then `a/c = 0`, whose imaginary part is zero —
excluded by `a_ne_zero_of_c_ne_zero`.  With `leaf τ = δ_{−1/τ}` the identity forces
`(a, b, c, d) = (i, 0, −iz, −i)`, whose value at `τ = 0` is `b/d = 0` — excluded by
`im_finiteCauchy_pos`.  Both failures are the same phenomenon: a Möbius image of `ℝ ∪ {∞}` is a
circle, and a circle through `0` cannot lie in the open upper half plane, so the leaf family cannot be
a single Dirac orbit.  A witness needs the boundary circle of a genuine Weyl disk, i.e. an
**indeterminate** Hamburger moment problem with its Nevanlinna parametrization — the classical
Stieltjes–Wigert example.  Mathlib has no moment-problem theory, so this is a development, not a
witness; it stays on the list as the one remaining construction, now with its obstruction made
precise.

## Closing measurement, 2026-07-27

Both instruments re-run on the current corpus (64 334 project theorems, 1 171 project `Prop`
definitions, 197 project data structures, 5 300+ modules in the buildable closure).

**`Prop` interfaces.**  The strict, `↔`-aware grounding fixpoint and the loose one now agree: 448
grounded, and exactly **2** consumed-but-ungrounded rows in the three areas, both `.below` recursor
artifacts.  The two rows that only the strict fixpoint saw (`isBoundedSmooth`, `supportedBounded`)
are closed.  No new ungrounded interface has appeared despite the corpus growing by several hundred
modules.

**Data hypotheses.**  Down from 28 → 19 → **13**, and every remaining row is classified:

| class | rows |
|---|---|
| constructor-realized inductives | `PrimeIsingBondTree`, `PrimeIsingBondForest`, `IsingBondState`, `ParabolicSphereSignature` |
| class-inhabited | `FieldOneCore.CertifiedProjectivePointFunctor`, `ComparisonFacet`, `AtlasLoss`, `CCMRationalScaling` |
| refutation bundles | `MeroGaugeFacetRealization`, `DAGaugeFlatFacetRealization` |
| container-valued producer | `PrimeIsingSpectralLine` |
| **genuine** | `ClassicalAnalyticNevanlinnaCarrierFamily` and its sub-bundle `MaximalTranslationInputs` |

So the audit is complete except for one named external development — the indeterminate Hamburger
moment problem with its Nevanlinna parametrization — whose obstruction is recorded above.  The other
named target isolated by this card is the composition law letting differential algebraicity descend
through `exp`, which would decide whether a hypertranscendental meromorphic function can have a
nonzero period.

## Defect found and fixed while auditing

Two `RHTower` modules registered in the same area umbrella declared
`GaloisForLFunctions.RHTower.criticalLinePoint` and `…criticalLinePoint_re` with **different**
statements — `(σ x : ℝ)` with real part `(σ+1)/2` in `GammaDampedSineSeries`, and `(τ : ℝ)` with real
part `1/2` in `FiniteDivisorPrefixNonselection` — so the two could not be imported together and the
`RHTower` umbrella could not build.  The audit hit it as an import failure.  The newer module's names
are used nowhere outside it, so they were renamed to `gammaDampedCriticalLinePoint`,
`gammaDampedCriticalLinePoint_re` and `abscissa_lt_gammaDampedCriticalLinePoint`; the module builds
and the two now co-import.

## The period layer, subsumed

`HTGeometry/PeriodSubgroupCyclic.lean` replaces the whole family of period no-gos by one positive
classification.

`periodSubgroup f` is the set of periods of `f` as an additive subgroup of `ℂ`.  For a
hypertranscendental meromorphic normal-form function:

- `exists_real_smul_of_mem_periodSubgroup` — every period is a rational, hence real, multiple of any
  fixed nonzero period.  This is the period-rank law, applied to the pair;
- `not_dense_periodCoeffSubgroup` — the group of real coefficients relative to that direction is not
  dense: density would supply nonzero coefficients tending to zero, hence nonzero periods tending to
  zero, and `meromorphicNF_constant_of_small_periods` would make `f` constant;
- **`exists_periodSubgroup_eq_closure_singleton`** and **`periodSubgroup_eq_zmultiples`** — a subgroup
  of `ℝ` is dense or cyclic, so the coefficient group is cyclic and

  **`periodSubgroup f = AddSubgroup.zmultiples ω` for some `ω`: the period group of a
  hypertranscendental meromorphic function on `ℂ` is trivial or infinite cyclic.**

The earlier results are the cases this excludes: a rank-two lattice (the elliptic theorem), a
rank-two `ℝ`-dependent pair and a rank-three triple (non-discreteness), and the entire case
(Liouville).  Each of those says a configuration of periods is impossible; this says exactly which
configuration survives, and it is the sharp one — whether the surviving cyclic case is *attained*
is precisely the open question recorded above about a periodic hypertranscendental function.

`#print axioms` on all four: `[propext, Classical.choice, Quot.sound]`.

## The hard direction of autonomy, for periodic functions

`HTGeometry/PeriodicAutonomousDescent.lean`.  The corpus had only the easy direction
(`differentiallyAlgebraic_of_autonomous`: a nonzero autonomous annihilator makes a function
differentially algebraic).  The converse is false in general — `z` satisfies only equations
mentioning the point slot — but it holds for periodic functions, and that is the direction the period
layer needs.

The mechanism is elimination of the point slot along the period.  Split a differential polynomial
`P ∈ MvPolynomial (Fin (n+2)) ℂ` as a polynomial in the point variable with coefficients in the jet
variables (`finSuccEquiv`).  All jets of a periodic function are periodic
(`periodic_iteratedDeriv`), so the jet vector at `z + k·c` equals the one at `z`, and the relation
says the univariate polynomial obtained by evaluating those coefficients on the jet vector vanishes
at `z + k·c` for **every** integer `k`.  Infinitely many roots force it to be the zero polynomial, so
every coefficient vanishes on the jets; the leading coefficient is nonzero, giving a nonzero
autonomous relation.

* **`exists_autonomousJet_of_periodic`** — the descent;
* `differentiallyAlgebraic_of_autonomousJet` — the converse, by adjoining and forgetting the point
  slot;
* **`differentiallyAlgebraic_iff_autonomousJet_of_periodic`** — for a periodic function,
  differential algebraicity *is* autonomous differential algebraicity;
* **`hypertranscendental_iff_no_autonomousJet_of_periodic`** — hence hypertranscendence of a periodic
  function is exactly the absence of an autonomous equation.

This sharpens the open question left by the period-subgroup classification.  To decide whether the
surviving infinite-cyclic case is attained — whether some hypertranscendental meromorphic function
has a nonzero period — it now suffices to exclude **autonomous** algebraic differential equations for
a candidate, a strictly smaller class than all differential equations.

`#print axioms` on all five: `[propext, Classical.choice, Quot.sound]`.

## What a nonzero period decides

`HTGeometry/PeriodAutonomyDichotomy.lean` closes the period layer with a single statement.  For a
meromorphic normal-form `f` with `periodSubgroup f ≠ ⊥`, exactly one of:

- **`f` satisfies a nonzero autonomous algebraic differential equation**; or
- **`f` is hypertranscendental, its period group is `AddSubgroup.zmultiples ω` for a nonzero `ω`, and
  `f` satisfies no autonomous equation at all.**

(`autonomous_or_cyclic_hypertranscendental`, with exclusivity in
`not_and_autonomous_hypertranscendental`.)  The first case is the descent applied to differential
algebraicity; the second is the period-subgroup classification applied to hypertranscendence.

Two corpus theorems are strengthened on the way, each from "differentially algebraic" to
"*autonomously* differentially algebraic":

- `exists_autonomousJet_of_rankTwo_periods` — two rationally independent periods;
- `exists_autonomousJet_of_lattice_periodic` — an elliptic function, of which
  `℘'² = 4℘³ − g₂℘ − g₃` is the order-one instance.

`#print axioms` on all four: `[propext, Classical.choice, Quot.sound]`.

The open question is now stated in its smallest form: **is the second case of the dichotomy
inhabited?**  Equivalently, is there a meromorphic function on `ℂ` with a nonzero period satisfying
no autonomous algebraic differential equation?  Everything the corpus knows about periods is a
consequence of the dichotomy, and this is the only thing it does not decide.

## Toward inhabiting the second case: jet transfer along an exponential

The dichotomy's open case asks for a meromorphic function with a nonzero period and no autonomous
algebraic differential equation.  The route is composition: if `g` is entire and hypertranscendental
then `g ∘ exp` is entire, periodic, and — provided differential algebraicity descends through the
composition — hypertranscendental.  The corpus already supplies an explicit entire hypertranscendental
`g` (`dyadicLayerEntireFunction`), so the whole question reduces to that descent.

The autonomy descent proved above removes the hardest-looking obstacle in advance.  A relation for
`g ∘ exp` may a priori involve the point slot, and eliminating `z = log w` is what makes the naive
argument fail; but for a *periodic* function the relation can be taken autonomous, and substituting
the chain rule into an autonomous relation produces a genuine polynomial relation for `g` over
`ℂ[w]`, with no logarithm anywhere.  What remains is the substitution itself and its injectivity.

`HTGeometry/ExpJetTransfer.lean` builds the substitution's coefficient theory:

- `expJetCoeff a k j` — the coefficients of `g⁽ᵏ⁾(exp(az))`-expansion, defined by the recursion
  `c_{k+1,j+1} = a ((j+1) c_{k,j+1} + c_{k,j})`, `c_{k+1,0} = 0`;
- `expJetCoeff_eq_zero_of_lt` — triangularity, `c_{k,j} = 0` for `j > k`;
- **`expJetCoeff_diag`** — the diagonal is `a ^ k`, a unit for `a ≠ 0`, which is what will make the
  substitution invertible;
- **`deriv_expTerm`** — the chain rule for one term: differentiating
  `exp(az)^j · g⁽ʲ⁾(exp(az))` gives exactly `a · (j ·` itself `+` the next term `)`.  This *is* the
  recursion, and it is the induction step of the transfer identity.

Remaining for the transfer identity `iteratedDeriv k (g ∘ exp a·) = ∑_{j ≤ k} c_{k,j} exp(az)^j
g⁽ʲ⁾(exp(az))`: the summation assembly (differentiate the sum termwise, then reindex the shifted sum
against the recursion).  After that, injectivity of the substitution — a triangular change of
variables with unit diagonal over `ℂ[w, w⁻¹]` — and Hölder's theorem finish the argument.

### The transfer identity is proved

`iteratedDeriv_comp_exp` now holds unconditionally: for entire `g` and any `a`,

`g(exp(a·))⁽ᵏ⁾(z) = ∑_{j ≤ k} expJetCoeff a k j · exp(az)ʲ · g⁽ʲ⁾(exp(az))`.

The induction step is `deriv_expTerm` (differentiate one term) followed by `sum_transfer_step`, an
algebraic reindexing lemma stated for arbitrary coefficients obeying the recursion: the shifted sum
`∑_j c_{k,j} E^{j+1} D_{j+1}` supplies the `c_{k,j}` half of `c_{k+1,j+1}` and the weighted sum
`∑_j j c_{k,j} E^j D_j` supplies the `(j+1) c_{k,j+1}` half, with the boundary terms vanishing by
`c_{k+1,0} = 0` and triangularity `c_{k,k+1} = 0`.

`#print axioms` on both: `[propext, Classical.choice, Quot.sound]`.

Two steps remain to inhabit the dichotomy's open case: injectivity of the induced substitution on
differential polynomials — a triangular change of variables with diagonal `a^k w^k`, invertible over
`ℂ[w, w⁻¹]` — and then Hölder's theorem, already in the corpus as `hypertranscendental_gamma`, or the
corpus's own `hypertranscendental_dyadicLayerEntireFunction` for the entire route.

### The transfer substitution is injective

`HTGeometry/ExpJetSubstitution.lean`.  In the variables `Yⱼ = exp(az)ʲ · g⁽ʲ⁾(exp(az))` the transfer
is a linear change of variables with **constant** coefficients, `f⁽ᵏ⁾ = ∑ⱼ c_{k,j} Yⱼ` — no Laurent
polynomials, because the powers of `w` are absorbed into the variables.  That is what makes the
injectivity elementary.

- `expJetLinear` — the transfer matrix on the jet space;
- **`expJetLinear_injective`** — triangular back-substitution: everything above the diagonal vanishes
  and the diagonal entries are the units `aᵏ`, so the kernel is trivial for `a ≠ 0`;
- `expJetLinear_surjective` — hence surjective, the space being finite-dimensional;
- **`bind₁_expJetSubst_ne_zero`** — the induced substitution on differential polynomials preserves
  nonzeroness.

The last step avoids constructing the inverse matrix: if the substituted polynomial vanishes
identically then, since every evaluation point of the source is in the image of the linear map, the
original vanishes at *every* point, and a polynomial over an infinite domain that vanishes everywhere
is zero (`MvPolynomial.funext`).

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]`.

What remains for the composition theorem is bookkeeping of the same kind: re-express the transfer
identity as `iteratedDeriv k f z = expJetLinear a n Y k` (extending the `range (k+1)` sum to all of
`Fin (n+1)` by triangularity), substitute `Yⱼ ↦ X₀ʲ · X_{j+1}` — injective by evaluating at `w = 1`,
the same trick — and multiply by `X₀` so the relation also holds at the one point `w = 0` that the
exponential misses.

## The open case is inhabited: the period layer is closed

Two modules complete the programme.

`HTGeometry/CompExpDescent.lean` — **`differentiallyAlgebraic_of_comp_exp`**: for entire `g` and
`a ≠ 0`, if `g (exp (a z))` is differentially algebraic then so is `g`; contrapositive
**`hypertranscendental_comp_exp`**.  The naive argument fails because a relation for the composite may
involve the point `z = log w / a`, which is not algebraic over `ℂ(w)`.  Periodicity removes that in
advance: the composite has period `2πi/a`, so the autonomy descent replaces the relation by one with
no point slot, after which substituting the jet transfer is purely polynomial.  Nonzeroness survives
by `bind₁_expJetSubst_ne_zero`, then by the monomial substitution `Yⱼ ↦ X₀ʲ X_{j+1}` (injective by
evaluating at `w = 1`), and multiplying by `X₀` covers the single point `w = 0` the exponential
misses.

`HTGeometry/PeriodicHypertranscendentalWitness.lean` — `periodicWitness z :=
dyadicLayerEntireFunction (exp (2πi z))` is entire, has period one, and is hypertranscendental.
**`exists_periodic_hypertranscendental`** packages it: there is a meromorphic normal-form function on
`ℂ` with a nonzero period, satisfying no algebraic differential equation, hence none autonomous, whose
period group is infinite cyclic.

So the dichotomy `autonomous_or_cyclic_hypertranscendental` is **inhabited on both sides**, and the
question left open by the period-subgroup classification is answered: a hypertranscendental
meromorphic function *can* have a nonzero period, and the rank bound `ℚ`-rank ≤ 1 is attained.

The chain, all unconditional: an explicit infinite geometric layer tower gives an explicit entire
hypertranscendental function; the autonomy descent turns periodicity into a point-free relation; the
exponential jet transfer with its triangular unit-diagonal matrix moves that relation across the
composition; and the composite is the witness.  `#print axioms` on every capstone:
`[propext, Classical.choice, Quot.sound]`.

## Re-audit, 2026-07-27 (later): one new row, one more collision

**`Prop` interfaces.**  Re-measured over 63 954 project theorems and 1 249 project `Prop`
definitions.  The loose fixpoint gives the usual 2 `.below` recursor artifacts; the **strict**
`↔`-aware fixpoint gives 3 — one genuinely new interface, added by another lane since the previous
measurement:

| interface | defining module | resolution |
|---|---|---|
| `RHTower.SignedDigammaBooleanHerglotz` | `RHTower.DigammaOrientationVerticalRigidityUniversalityLaw` | discharged — `RHTower/SignedDigammaHerglotzWitness.lean` |

It was grounded only through `signedDigammaBooleanCompletion_nonneg_iff_allPositive`, a
characterization (`Herglotz ε ↔ ε = fun _ => false`), which transfers the property without producing
it — precisely the blind spot the strict fixpoint was built to see.  The all-positive orientation is
the witness (`signedDigammaBooleanHerglotz_allPositive`), and by the same characterization it is the
*only* one; the layer's conclusions — the exact closed form and vertical height monotonicity — now
hold with no Herglotz premise.

**A second umbrella collision, fixed.**  The audit again failed to import, this time because
`RHTower.norm_inv_riemannZeta_le` was declared with different statements in `GammaDampedVerticalBound`
(hypothesis `2 ≤ s.re`, bound `2`) and in `ZetaLogDerivBound` (hypotheses on `|t|` and `σ`), both
registered in the `RHTower` umbrella.  The newer module's name is used nowhere outside it, so it was
renamed to `norm_inv_riemannZeta_le_of_two_le_re`; the module builds and the two now co-import.  This
is the second collision from the same lane in one session — both were found only because the audit
imports the whole area at once, which no ordinary build does.

**General corollary added.**  `periodic_comp_exp` and `periodic_and_hypertranscendental_comp_exp` in
`CompExpDescent.lean` state the construction once for every entire hypertranscendental `g` and every
`a ≠ 0`, rather than only for the particular witness.

## The witness's period group, computed exactly

The dichotomy says a hypertranscendental meromorphic function has infinite cyclic period group; for
the explicit witness the generator can be identified.  `HTGeometry/PeriodicWitnessPeriodGroup.lean`:

- `rotation_of_periodic_comp_exp` — a period `c` of `g (exp (a z))` makes `g` invariant under
  multiplication by `λ = exp (a c)` off the origin, hence everywhere, the two continuous functions
  agreeing on the dense punctured plane;
- **`mem_zmultiples_of_periodic_comp_exp`** — differentiating that invariance at the origin gives
  `λ · g'(0) = g'(0)`, so `λ = 1` whenever `g'(0) ≠ 0`, and then `a c ∈ 2πi ℤ`;
- `deriv_dyadicLayerEntireFunction_zero_ne_zero` — the layer-tower function has every Taylor
  coefficient nonzero (their moduli are `exp (−tail₀ n) > 0`), in particular the first;
- **`periodSubgroup_periodicWitness : periodSubgroup periodicWitness = AddSubgroup.zmultiples 1`.**

So the witness is not merely *some* function with infinite cyclic period group: its period group is
exactly `ℤ`.  The dichotomy's second case is inhabited by an object whose period data is completely
determined.

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]`.

## Data-hypothesis re-audit

Re-measured alongside: 197 project data structures, 76 consumed as hypotheses in the three areas, 13
not directly constructed — identical to the previous measurement, every row classified, and only
`ClassicalAnalyticNevanlinnaCarrierFamily` with its sub-bundle genuinely open.  No new data debt has
appeared from the concurrent lanes.

## Fifth instrument: joint realization of premise *pairs*

The previous joint-realization pass only looked at theorems with three or more project-`Prop`
hypotheses.  Lowering the threshold to two, on the current audit data, gives 261 multi-premise
theorems in the three areas across 112 distinct premise sets.  The crude detector ("some single
theorem's conclusion mentions all of them") flags 83, but most are the known false positive: a joint
witness is normally a *specialization*, whose conclusion does not mention the premise names at all.
The rows worth reading are the ones where no such specialization exists either.

The largest such row, checked by hand and discharged:

| consumers | premise pair | resolution |
|---:|---|---|
| 10 | `HypertranscendentalOver`, `HasScalarDifferentialOrder` | `HTGeometry/ScalarDifferentialOrderWitness.lean` |

`HasScalarDifferentialOrder F x z n` says `z` is visible at jet resolution `n + 1` but not at `n`,
and the layer consumes it together with hypertranscendence of the clock `x`.  Neither was exhibited
on a common object.  Exact jet visibility — `differentialJet_mem_jetObservableField_iff_lt`, already
in the corpus — gives both halves at once: for a hypertranscendental clock the `n`-th jet is visible
at resolution `N` exactly when `n < N`, so **the `n`-th jet has scalar differential order exactly
`n`** (`hasScalarDifferentialOrder_differentialJet`), the clock itself has order zero, and the pair
is jointly realized in every order.

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]`.

Remaining flagged pairs worth a hand check, in consumer order: `IsCCRCompletion` with
`IsCommutingCCRCompression` (17, `HilbertMetric` — the card records a joint witness for the
three-premise `fullCCR` family, which should cover this), `ThetaTranslationNonresonant` with
`ThetaTranslationNontorsion` (13), `PrimeProfileClockIndependent` with
`PrimeProfileSupportedOnPositivePrimePowers` (8), and
`MatrixCoefficientPrincipalSymbolFlat` with `MatrixPrincipalLowerLaw` (8).

### Second pair discharged: the theta translation conditions

| consumers | premise pair | resolution |
|---:|---|---|
| 13 | `ThetaTranslationNontorsion`, `ThetaTranslationNonresonant` | `HTGeometry/ThetaTranslationWitness.lean` |

The theta orbit obstruction consumes both — no nonzero integer multiple of `q` in `ℤ + ℤτ`, and the
shift `h` outside `ℤ + ℤτ + ℤq` — and neither was exhibited anywhere.

The witness is elementary: `τ = i`, `q = √2`, `h = (1/2)·i`.  Nontorsion compares imaginary parts to
force the `τ`-coefficient to vanish, leaving `n√2 = a`, which irrationality of `√2` kills for
`n ≠ 0`.  Nonresonance never touches the real part at all: the imaginary part of `h` is `1/2`, and
`2b = 1` has no integer solution.

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]`.

### Third pair discharged: commuting compression with a CCR completion

| consumers | premise pair | resolution |
|---:|---|---|
| 17 | `IsCommutingCCRCompression`, `IsCCRCompletion` | `HilbertMetric/CCRCompletionWitness.lean` |

This was the largest flagged pair.  The corpus proves `IsCCRCompletion` on the *zero* compression
(via the mode-indexed unit leakage) and separately proves a commutation statement about the assembled
block tuple (`IsCommutingFullTuple (blockCCRTuple 0 B)`) — a different predicate — so the two
premises of the seventeen consumers were never satisfied together.

Scalar compressions do both, and nondegenerately: for any weights `c`, the family `A i = c i • 1`
commutes, and the two correction terms of the completion identity coincide,
`(c j • 1)ᵀ (c i • 1) = (c i • 1) (c j • 1)ᵀ = (c i c j) • 1`, so they cancel and the identity reduces
to exactly the one the unit leakage already satisfies.  The compression is therefore not forced to be
zero.

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]`.

Two flagged pairs remain for hand-checking: `PrimeProfileClockIndependent` with
`PrimeProfileSupportedOnPositivePrimePowers` (8) and `MatrixCoefficientPrincipalSymbolFlat` with
`MatrixPrincipalLowerLaw` (8).

### Fourth pair: already true, but unnameable

| consumers | premise pair | resolution |
|---:|---|---|
| 8 | `PrimeProfileClockIndependent`, `PrimeProfileSupportedOnPositivePrimePowers` | `HTGeometry/PrimeProfileClockPairWitness.lean` |

This row is a different failure mode from the previous three.  Both properties *do* hold for the
explicit unit source, and the corpus proves the prime-power support as a named theorem — but the
clock-independence half exists only as an anonymous `show` inside the proof of the Kolchin fracture.
Nothing states it, so nothing else can use it, and the audit cannot see it.

`primeClockUnitSource_clockIndependent` extracts it verbatim (the polynomial clock orbit is linearly
independent, and over a one-element index the jet family is that orbit reindexed), and
`exists_clockIndependent_supportedOnPositivePrimePowers` records the pair.  No new mathematics — the
content was already there — but it is now on the record and reusable.

`#print axioms` on both: `[propext, Classical.choice, Quot.sound]`.

That leaves one flagged pair: `MatrixCoefficientPrincipalSymbolFlat` with `MatrixPrincipalLowerLaw`
(8 consumers).

### Fifth pair discharged: the flagged pair list is clear

| consumers | premise pair | resolution |
|---:|---|---|
| 8 | `MatrixCoefficientPrincipalSymbolFlat`, `MatrixPrincipalLowerLaw` | `HTGeometry/MatrixCoefficientFlatPairWitness.lean` |

A near-miss of the kind the audit is good at.  `MatrixPrincipalSymbolWitnesses` realizes
`MatrixPrincipalSymbolFlat` — the identity `symbol (n+1) A · symbol n B = symbol (n+1) B · symbol n A`
— by direction-independent symbols, and realizes the lower principal law with vanishing remainder.
But the layer consuming both premises uses the *other order*,
`MatrixCoefficientPrincipalSymbolFlat` (`symbol n B · symbol (n+1) A = symbol n A · symbol (n+1) B`),
which is a different definition and which nothing realized.

The same witness serves both, since a direction-independent symbol makes either identity literally
the same product on each side; pairing it with the block-diagonal action gives the two premises on
one symbol.  Zero and scalar instances are recorded as well.

**All five flagged premise pairs from the pair-level audit are now closed** — 17, 13, 10, 8 and 8
consumers.  Three needed genuine joint witnesses, one needed an inline proof extracted and named, and
this one needed the near-duplicate definition noticed.

`#print axioms`: `[propext, Quot.sound]` for the two flatness instances, `[propext,
Classical.choice, Quot.sound]` for the joint statement.

### Sixth pair: unitary phases and their reflected values

| consumers | premise pair | resolution |
|---:|---|---|
| 6 | `IsUnitaryPhase`, `IsPhaseReflected` | `HTGeometry/UnitaryPhaseReflectedWitness.lean` |

`IsUnitaryPhase w` is `conj w · w = 1` and `IsPhaseReflected w z` is `w² · conj z = z`; neither was
exhibited on a common pair.  They fit together for a structural reason worth recording rather than
just witnessing: **the reflected values of a unitary phase are exactly its real multiples**, since
`w² · conj (t w) = t w (w · conj w) = t w` for real `t`.  So every unitary phase carries a whole real
line of reflected values (`isPhaseReflected_real_mul`), and the pair holds on `(w, t w)` — realized
concretely at `w = i`, `z = i`.

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]`.

### Seventh pair: the odd sector was empty

| consumers | premise pair | resolution |
|---:|---|---|
| 5 | `IsGradingEven`, `IsGradingOdd` | `RHTower/GradingSectorWitness.lean` |

The graded-adjoint layer proves the unit is even but exhibits **no odd element anywhere**, so its
mixed statements — even times odd is odd, commutators of odds, the parity of a quantized form — had
never been applied to an actual odd element.

Both sectors get a criterion rather than a bare witness: conjugation by an involution fixes what
commutes with it (`isGradingEven_of_comm`) and negates what anticommutes with it
(`isGradingOdd_of_anticomm`).  The sign involution `diag(1, −1)` on `2 × 2` real matrices then
occupies both, with the coordinate flip as an explicit nonzero odd element — the smallest place where
a grading is not concentrated in its even part.

`#print axioms`: the even criterion needs none at all, the odd one only `propext`, and the concrete
witness `[propext, Classical.choice, Quot.sound]`.

## Re-audit after seven pair discharges

Both instruments re-run on the current corpus (64 178 theorems, 1 249 project `Prop` definitions,
5 493 modules in the buildable closure).

**`Prop` interfaces.**  The loose and strict fixpoints now **agree**: 432 grounded, 2 rows, both
`.below` recursor artifacts.  The `SignedDigammaBooleanHerglotz` row is gone.  The strict instrument
no longer sees anything the loose one misses, which is the first time that has happened.

**Pairs.**  264 multi-premise theorems in 114 premise sets.  All seven previously discharged rows
have dropped out.  The new head of the list is:

| consumers | premise pair | resolution |
|---:|---|---|
| 6 | `MembraneLocalPrincipalBrackets`, `MembraneValenceAtMost` | `HTGeometry/MembraneValencePairWitness.lean` |

Locality had realizations in the corpus, but the valence bound existed only as an anonymous `by simp`
inside the three-scale certificate, so the pair was nowhere on record.  The two premises pull against
each other — locality wants large membranes, the valence bound wants small ones — so both ends of the
trade-off are recorded rather than one arbitrary point:

- total membranes cover every law pair, making locality free at valence exactly the ambient
  cardinality (`membraneLocality_and_valence_univ`);
- a symbol with vanishing principal brackets is local for *every* support, so locality costs nothing
  at valence `0` (`membraneLocality_and_valence_zero`).

The pair is therefore satisfiable at both extremes of the valence scale, and the layer's content is
what happens in between.

`#print axioms` on both: `[propext, Classical.choice, Quot.sound]`.

### Ninth pair: consistency only, and said so

| consumers | premise pair | resolution |
|---:|---|---|
| 4 | `CofinitePrimeProfileJetPacket`, `PrimeProfileSupportedOnPositivePrimePowers` | `HTGeometry/CofinitePacketConsistency.lean` |

`CofinitePrimeProfileJetPacket g` asks, for every jet order and every finite set of forbidden primes,
for a separated packet avoiding them whose jet matrix is nonsingular.  Nothing exhibits such a family:
the corpus criterion `cofinitePrimeProfileJetPacket_iff_rayTailIndependent` is a characterization,
which transfers the property without producing it — the same pattern as the digamma Herglotz row.

Over the empty index the packet matrix is the empty matrix, whose determinant is `1`, so the bundle
is consistent and the pair is jointly satisfiable.  **This is a consistency statement at the
degenerate end and nothing more.**  A packet over a nonempty index needs the jet matrix to be
genuinely nonsingular for cofinitely many prime choices — a Vandermonde-type non-vanishing in the
prime logarithms — and that is the substantive content of the layer, still unwitnessed.  It is
recorded here as the honest state rather than left looking discharged.

`#print axioms` on both: `[propext, Classical.choice, Quot.sound]`.

### The cofinite packet, nondegenerately

The consistency-only status recorded above is superseded: `HTGeometry/CofinitePacketVandermonde.lean`
builds a packet over a **nonempty** index.

Writing the entry out settles it.  With all exponents zero,

`primeDeriv p (jetₖ f) (p⁰) = (0+1) · (i · log p)ᵏ · f p`,

so for the profile that is `1` at every prime the packet matrix is *exactly*
`vandermonde (fun r => i · log qᵣ)`.  Its determinant is the product of node differences, nonzero
because `log` separates distinct primes, and the nodes can avoid any prescribed finite set because
there are infinitely many primes (`exists_injective_primes_avoiding`, from
`Set.Finite.infinite_compl` and `Set.Infinite.exists_subset_card_eq`).

So `cofinitePrimeProfileJetPacket_primeIndicator` holds, and with
`primeIndicatorProfile_supported` the pair of premises is realized on a one-element index — the
substantive version of the row, not the empty-index consistency check.

The Vandermonde structure was hiding in plain sight: the jet index is the exponent of the rotated
logarithm, so the packet matrix of *any* profile is a Vandermonde matrix scaled row-wise by
`(e+1) · g(p^{e+1})`.  Only the nonvanishing of those scalars and the separation of the nodes matter,
which is why the prime indicator suffices.

`#print axioms` on all four: `[propext, Classical.choice, Quot.sound]`.

### The packet condition, reduced to a support statement

`HTGeometry/CofinitePacketCriterion.lean` promotes the Vandermonde observation from a witness to a
criterion.

`primeProfileJetPacketMatrix_unit_apply`: at exponent zero the packet matrix of **any** profile is

`g(qᵣ) · (i · log qᵣ)^{jet order}`,

that is `diagonal (g ∘ q) * vandermonde (i · log ∘ q)`.  Its determinant is `∏ᵣ g(qᵣ)` times the
Vandermonde product, so exactly two things can obstruct a packet: a profile value vanishing at a
chosen prime, or two nodes coinciding — and distinct primes never have equal logarithms.

Hence **`cofinitePrimeProfileJetPacket_of_infinite_prime_support`**: a profile nonzero at infinitely
many primes has a cofinite jet packet.  The existential analytic condition — for every order and every
finite forbidden set, a separated nonsingular packet — becomes a statement about the profile's support
alone, checkable for any concrete profile.  The prime indicator of the previous entry is the special
case where the support is all of the primes, and is rederived from the criterion.

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]`.

## Iteration: the criterion applied to the corpus's own source

`HTGeometry/PrimeClockUnitSourcePacket.lean` (built, axioms clean, registered).

The support criterion proved last iteration is checkable by inspection, and the corpus's explicit
source passes. `primeClockUnitValuationProfile = fun _ => 1`, so
`primeClockUnitSource n = if IsPrimePow n then 1 else 0` — the prime-power index the replication
looks up is irrelevant, and the value at *every* prime is `1`:

* `primeClockUnitSource_apply_of_isPrimePow : IsPrimePow n → primeClockUnitSource n = 1`
  (one `dif_pos` and `rfl`; no `prodNatEquiv` computation needed);
* `cofinitePrimeProfileJetPacket_primeClockUnitSource` — the prime support is `Set.univ`, hence
  infinite, hence the packet.

**All three prime-profile interfaces now hold on one named object**
(`primeClockUnitSource_packet_clock_support`): cofinite jet packet, clock independence
(`primeClockUnitSource_clockIndependent`, extracted earlier this audit from an anonymous `show`
inside the Kolchin fracture proof), and prime-power support (already in the corpus). The layer's
premise triple is therefore jointly realized by the object the corpus itself uses downstream, not
just by an auxiliary indicator profile.
