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

## Iteration: `PeriodsIntegrallyIndependent` — a new ungrounded interface, discharged

Re-running the grounding fixpoint over the current tree surfaced a row that was not there before
(a concurrent lane added the face-lattice layer): `GaloisForLFunctions.PeriodsIntegrallyIndependent`
with **11 consumers** (9 in `FaceShiftLatticeNonresonance`, 2 in `BottomFaceCrossSeparation`),
ungrounded in both the loose and the strict fixpoint. It says `1` together with the periods admits
no integral relation:
`∀ (m : ℤ) (n : ι → ℤ), (m : ℂ) + ∑ i, (n i : ℂ) * τ i = 0 → m = 0 ∧ ∀ i, n i = 0`.

Nine of the eleven consumers additionally require `∀ i, 0 < (τ i).im`, so the useful object is a
*joint* realization in the upper half plane.

**Corpus check first.** `Core.lean` already proves `logPrime_linearIndependent_int` (and its `ℚ`
localization `linearIndependent_log_primes`); `OrbitFreeness` exports the finite-relation form.
Nothing needed to be re-derived — the discharge is one composition away.

`HTGeometry/PeriodIntegralIndependenceWitness.lean` (built, axioms clean, registered):

* `logPrimePeriod q i = i · log (q i)` for a family of primes: real part `0`, imaginary part
  `log (q i) > 0`, so the whole family sits in the upper half plane;
* `periodsIntegrallyIndependent_logPrimePeriod` — the real part of a relation *is* its coefficient
  of `1`, and its imaginary part is an integral relation between logarithms of distinct primes,
  which unique factorization kills. **No transcendence input at all**: the hypothesis reads as if
  it needed one, and it does not, because the periods may be chosen purely imaginary.
* `exists_periods_im_pos_integrallyIndependent (ι) [Fintype ι]` — the realization at *every* finite
  index type, via `Fintype.equivFin` ▸ `Fin.valEmbedding` ▸ `Infinite.natEmbedding Nat.Primes`.

**The second premise, discharged as a connector.** The bottom-atomicity consumer also carries
`LinearIndependent ℚ (ellipticGammaSourcePeriods (τ a) (τ b))`, i.e. of `![1, τ a, τ b]` — a mathlib
`Prop`, so invisible to the interface audit, but a genuine open premise appearing in four files.
It is exactly the two-parameter restriction of the lattice hypothesis:

* `linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent` — clear the `ℚ`
  denominators by proving `LinearIndependent ℤ ![1, τ a, τ b]` (route a `Fintype.linearIndependent_iff`
  relation through `PeriodsIntegrallyIndependent` with `n` the two-point indicator, splitting the sum
  by `Finset.sum_subset` + `Finset.sum_pair`) and then `LinearIndependent.localization ℚ`.

**The payoff — an unconditional theorem.** `HTGeometry/BottomFacePacketUnconditional.lean`
(built, axioms clean, registered): with `ι = Bool`, `τ = (i log p, i log r)` for distinct primes and
the empty face,

  `multipleEllipticGammaFacePacket_diffIndepOn_logPrime : p ≠ r → (∀ g ∈ G, DifferentialAlgebraicOver ℂ g) →`
  `  DiffIndepOn ↥(differentialAdjoin ℂ G) (multipleEllipticGammaFacePacket (twoLogPrimePeriods p r) _ ∅)`

— bottom-layer atomicity of the elliptic gamma hierarchy with **both** arithmetic hypotheses
discharged and nothing left but the choice of two distinct primes.

## New instrument: mathlib-`Prop` premises that no corpus theorem produces

The `PeriodsIntegrallyIndependent` episode showed that the interface audit is blind to premises whose
head is a *mathlib* `Prop` applied to corpus objects (`LinearIndependent ℚ (ellipticGammaSourcePeriods …)`
was open in four files and invisible). New metaprogram `AuditM.lean` + `m4.py`: for every theorem in
the three areas, `forallTelescope` the statement, and key each `Prop` binder by
(head constant, set of `GaloisForLFunctions` constants occurring in it); do the same for conclusions.
A premise key counts as produced when some conclusion has the same head — or is existentially
quantified — over a *superset* of its corpus constants.

Calibration mattered: exact-set matching reported `Matrix.PosDef (circleToeplitzGram …)` as open with
56 uses (the producer is `InfiniteSupportCayleyGram`, stated for `cayleyMomentZ mu`), and ignoring
`∃`-headed conclusions reported `IsIntegral ℤ (R.scaledCoeff c i)` as open with 46 uses (the producer
is `Relation.exists_common_integer_scale`, already used at three call sites). Both are false alarms
of the instrument, not gaps in the corpus — recorded here so the next run does not re-raise them.

**Result: 233 corpus-specific mathlib-`Prop` premise keys, of which 16 are produced nowhere**, none
with more than 3 uses. The premise layer outside the `Prop`-interface audit is therefore essentially
closed as well. The 16 are dominated by deep analytic hypotheses (face-packet displacement
injectivity, stretched-exponential Taylor magnitude, locally uniform convergence of Ising partition
functions).

## Iteration: the paraorthogonal root set is full

`Polynomial.IsRoot (finiteParaorthogonalPolynomial p τ)` was one of the 16 — a *root-existence*
hypothesis, so the two root-location theorems (`‖z‖ = 1`, and reality of the Cayley image) were
compatible with there being no root at all.

`HTGeometry/ParaorthogonalRootCount.lean` (built, axioms clean, registered):

* `natDegree_finiteParaorthogonalPolynomial : p ≠ 0 → (X·p − τ·conj(p)ᵣₑᵥ).natDegree = p.natDegree + 1`
  — reversal cannot raise the degree (`reverse_natDegree_le`), so the subtraction keeps the leading
  term of `X·p`;
* `exists_isRoot_finiteParaorthogonalPolynomial` — hence the degree is positive and `Complex.exists_root`
  applies: **the premise is never vacuous**;
* **`finiteParaorthogonalPolynomial_roots_on_unitCircle`** — `Splits.natDegree_eq_card_roots` upgrades
  this to the exact count: the terminal closure has `deg p + 1` roots with multiplicity and every one
  lies on the unit circle, i.e. it splits into unimodular linear factors;
* **`finiteOPUCParaorthogonalPolynomial_roots_on_unitCircle`** — for the terminal polynomial of a
  positive definite Toeplitz section of level `N` the count is exactly `N + 1`.

This is the classical Jones–Njåstad–Thron picture, and it converts the corpus's per-root statement
into a statement about the whole root set.

## Iteration: the Cayley reality statement is inhabited

`HTGeometry/ParaorthogonalCayleyRealization.lean` (built, axioms clean, registered). The companion
premise to the root hypothesis is `IsRoot (finiteParaorthogonalPolynomial p τ) (lineCayley z)` — a
root *of Cayley form*. Existence of a root does not by itself give one, because `lineCayley` misses
the point `1`.

* `exists_lineCayley_preimage` — `w` unimodular and `≠ 1` is `lineCayley (i(1+w)/(1−w))`, and the
  preimage is real by the corpus's own norm criterion `norm_lineCayley_eq_one_iff_im_eq_zero`, not by
  computing an imaginary part;
* `exists_unimodular_terminal_not_isRoot_one` — `eval 1 (X·p − τ·conj(p)ᵣₑᵥ) = p(1) − τ·c`, and
  `p(1) ≠ 0` because `1` is not in the open disk; if `p(1) = c` take `τ = −1`, otherwise `τ = 1`;
* **`exists_real_lineCayley_paraorthogonal_root`** — for every `p ≠ 0` with roots in the open disk
  there are a unimodular `τ` and a real `z` with `(X·p − τ·conj(p)ᵣₑᵥ)(lineCayley z) = 0`.

Both root premises of the Carathéodory--Fejér layer are therefore realized, and the earlier
`Polynomial.IsRoot` rows of the mathlib-premise scan are closed.

## Iteration: the universal bottom-layer law

Extending the two extractions above:

* `finiteOPUCPolynomial_ne_zero`, `finiteOPUCPolynomial_roots_norm_lt_one` — named (they existed only
  inside one proof), and `exists_real_lineCayley_finiteOPUC_root`: a positive definite Toeplitz
  section has a unimodular terminal parameter and a **real** Cayley point that is a paraorthogonal
  root.
* **`exists_periods_bottom_faces_diffIndepOn (ι) [Fintype ι] [DecidableEq ι]`** — over any finite
  index there is a period family in the upper half plane such that *simultaneously for every face
  `J` with exactly two surviving parameters*, the packet is differentially independent over every
  differentially algebraic extension of the constants. This subsumes the `ι = Bool`, `J = ∅`
  instance: one period family works for all faces at once, because integral independence is a
  property of the whole family and the pair restriction is derived from it, not assumed per pair.

Instrument note: `Set.Infinite {p | primeOrientationPattern ε p = …}` also appeared in the 16, and is
likewise a false alarm — `constraintOrientation_tailIndependent_of_anchoredSkeleton` realizes it in
the same file, but through an `Iff`-headed producer whose constant set does not contain the pattern
constants. The residue of the mathlib-premise scan is now dominated by genuinely analytic items.

## Iteration: face-packet freeness — base case proved, general case characterized

`Function.Injective (facePacketDisplacementSlice τ hτ J hq)` is the largest remaining row of the
mathlib-premise scan (the freeness hypothesis `hinjD` of the telescoping layer).

**Connector shipped.** `HTGeometry/DiffIndepLinearIndependence.lean` (built, axioms clean,
registered): `DifferentialIndependent` unfolds to `AlgebraicIndependent` of the whole jet family, so
restricting along `x ↦ (x, 0)` and rewriting `differentialJet 0 x = x` gives
`linearIndependent_of_differentialIndependent`, `linearIndependent_of_diffIndepOn`, and
`injective_of_differentialIndependent`. Nothing in the corpus had drawn the linear consequence of
differential independence; it is the tool any freeness argument needs.

**Base case shipped.** `HTGeometry/FacePacketBottomFreeness.lean` (built, axioms clean, registered).
`faceShiftLattice τ J` is the span of the parameters the face *retains*, so `faceShiftLattice τ ∅ = {0}`,
`multipleEllipticGammaFacePacket τ hτ ∅` is the single untranslated face log-derivative, and
`facePacketDisplacementSlice_injective_empty` follows from subsingletonness. This is exactly the base
of the face induction the telescoping layer runs.

**Why the general case is not algebraic.** Attempted route: `y_i = T_{g_i}Ψ_J`, and
`T_{τq}y₁ − y₁ = T_{τq}y₂ − y₂` is a ±1 relation among the four translates
`T_{g₁+τq}Ψ_J, T_{g₁}Ψ_J, T_{g₂+τq}Ψ_J, T_{g₂}Ψ_J`, which linear independence of the translate family
would kill (the multiset identity `{g₁+τq, g₂} = {g₁, g₂+τq}` forces `g₁ = g₂` since `τ q ≠ 0`).
Two independent obstacles:

1. The four shifts lie in `faceShiftLattice τ J + ℤ·τ q`, which is **not** the lattice of any face
   carrying the same `Ψ`. A bottom face has `Jᶜ = {a, b}` exactly, so `J` cannot be enlarged while
   keeping the surviving pair — there is no corpus packet containing all four elements.
2. The available independence engine, `ellipticGammaTranslatePacket_diffIndepOn_daExtension`, demands
   `ThetaTranslationNonresonant (τ b) (τ a) (hs j)` for every shift and every difference, and
   `ThetaTranslationNonresonant τ q h := ¬∃ a b n : ℤ, h = a + b·τ + n·q`. The displacement shift is
   `τ q` itself, which is resonant by definition (`n = 1`). **The displacement direction is precisely
   the direction the independence machinery excludes**, so no amount of nonresonance bookkeeping can
   produce it.

Named open core: `w := T_{g₁}Ψ_J − T_{g₂}Ψ_J` invariant under translation by `τ q` forces `g₁ = g₂`.
Iterating invariance gives `T_{g₁+nτq}Ψ_J − T_{g₂+nτq}Ψ_J = w` for all `n : ℤ`, so the route is the
pole orbit rather than differential algebra — the same shape as
`JacobiThetaDifferentialOrbitObstruction`'s finite-pole-orbit argument, which is where a proof should
start.

Instrument note (second false alarm class): `Filter.Eventually` on `taylorPS`/`stretchedExp` is also
already produced — `StretchedExponentialMagnitudeHypertranscendence` builds the explicit entire family
`stretchedExponentialPhaseFunction` with `taylorPS` coefficients of exactly the prescribed magnitude
and concludes `hypertranscendental_stretchedExponentialPhaseFunction`. Of the 16 residual rows, the
ones inspected so far are: 2 genuine (paraorthogonal roots — now discharged; face-packet freeness —
base case discharged, general case characterized), 3 false alarms of the const-set matching. The
scan's role is to *nominate*; each row still needs the producer search by hand.

## Iteration: the parabolic sphere signatures are exactly six (universal law)

The structure scan's largest unexamined row was `ParabolicSphereSignature` (16 consumers, six nullary
constructors, never produced by a theorem). It is not an open premise — it is an *enumeration*, and
the corpus proves things about its six values (`holonomyOrder_dvd_twelve`, tower rigidity) without
ever proving the list complete. That completeness is the law the enumeration was standing in for.

`HTGeometry/ParabolicSignatureClassification.lean` (built, axioms clean, registered):

* `coneDefect k = 1 − 1/k`, `orbifoldDefect m c = ∑ coneDefect + c`, with
  `coneDefect ∈ [1/2, 1)` for `k ≥ 2`;
* **`parabolic_triple_classification`** — for `2 ≤ a ≤ b ≤ c`, `1/a + 1/b + 1/c = 1` holds exactly for
  `(2,3,6)`, `(2,4,4)`, `(3,3,3)`. Ordering gives `a ≤ 3` from `1 ≤ 3/a`, then each branch bounds the
  next entry the same way — the same shape as the corpus's hyperbolic `hurwitz_ordered_eq_237`, which
  had no parabolic companion;
* **`parabolic_signature_classification`** — cone defects in `[1/2, 1)` and unit cusp defects force at
  most four cone points and at most two cusps, and the six cases are exactly
  `([], 2)`, `([2,2], 1)`, `([2,2,2,2], 0)`, `([2,3,6], 0)`, `([2,4,4], 0)`, `([3,3,3], 0)`;
* **`exists_parabolicSphereSignature_iff`** — a cone-order list with a cusp count comes from a
  `ParabolicSphereSignature` **iff** its orders are at least two, weakly increasing, and its total
  angle defect is two.

The enumeration is now a theorem rather than a definition-by-list: every statement quantified over the
six signatures is a statement about all parabolic data.

## Iteration: the trichotomy of triangle signatures

`HTGeometry/TriangleSignatureTrichotomy.lean` (built, axioms clean, registered). With the parabolic
case proved and the hyperbolic case already in the corpus (`hurwitz_triple_sum_le`,
`hurwitz_ordered_eq_237`), the spherical case completes the classification:

* **`spherical_triple_classification`** — `1/a + 1/b + 1/c > 1` for `2 ≤ a ≤ b ≤ c` holds exactly for
  the dihedral family `(2,2,c)` and the Platonic triples `(2,3,3)`, `(2,3,4)`, `(2,3,5)`;
* **`triangle_signature_trichotomy`** — every ordered triple of cone orders is spherical from that
  list, parabolic from `(2,3,6)/(2,4,4)/(3,3,3)`, or hyperbolic with reciprocal sum `≤ 41/42`.

The Hurwitz bound was an isolated inequality in the corpus; it is now the third branch of a
classification, and the parabolic signatures are the boundary case between the two.

## Iteration: the face-packet freeness row, re-scoped

`Function.Injective (facePacketDisplacementSlice τ hτ J hq)` — the largest row of the
mathlib-`Prop` scan — is no longer a single open statement.  New card:
`face-packet-displacement-freeness.md`; new module
`HTGeometry/FacePacketDisplacementFreeness.lean` (built, axioms clean, registered).

* **`facePacketDisplacementSlice_injective_iff_period`** — freeness *is* a comparison of
  translation stabilizers, with no side condition:
  `Injective ↔ ∀ h ∈ faceShiftLattice τ J, T_h Ψ_{J∪{q}} = Ψ_{J∪{q}} → T_h Ψ_J = Ψ_J`.
  The card's earlier "named open core" (a `τ q`-invariant difference of translates must vanish) is
  this statement, and the pole-orbit route it proposed is not needed to *state* it.
* `addTranslationMeroEquiv_intCast_multipleEllipticGammaLogDerivFaceMero` — every integer
  translation fixes every face coordinate, so the comparison only has to reach `ℤ`.
* The `d ≥ 2` case (at least two parameters surviving the deeper face) was closed by a concurrent
  lane in `FaceTranslateInjective`; read through the equivalence it gives the period statement
  `multipleEllipticGammaLogDerivFaceMero_period_comparison`.
* **The premise is unsatisfiable at the terminal face.**  With `insert q J = univ` the deeper
  coordinate is the constant `−2πi`, the labelling is constant on the packet, and
  `Injective ↔ Subsingleton (packet J) ↔ faceShiftLattice τ J ⊆ Per(Ψ_J)`.  So the freeness
  hypothesis there is not freeness but triviality of the external action.

Remaining open core, now isolated to one face: `Per(Ψ_L) = ℤ` for a face with exactly one surviving
parameter.  `ℤ ⊆ Per` is proved; the gap is `Per ⊆ ℤ + ℤσ`, whose single missing analytic input is
that the backward product has a simple zero at the origin.

### The face-packet freeness row is closed

`HTGeometry/FaceOneSurvivingTheta.lean` (built, axioms clean, registered) finishes the row:

* `multipleEllipticGammaLogDerivFaceMero_one_surviving` — a face with exactly one surviving
  parameter is a translated `thetaLogDerivMero` plus a constant.  The rank-one face is a *coface* of
  a rank-two face, and the corpus already crosses the product hierarchy to the series-side theta at
  rank two (`ellipticGammaLogDerivMero_source_face_sigma`), so no product formula for `jacobiTheta₂`
  is needed — the Jacobi triple product, which the earlier note called the missing input, is not.
* `exists_lattice_of_fix_one_surviving` — hence `Per(Ψ_L) ⊆ ℤ + ℤ(τ b)`, from
  `thetaLogDerivDefectMero_ne_zero_of_nonlattice`.
* **`facePacketDisplacementSlice_injective_iff`** — the exact criterion: for an integrally
  independent period family, freeness holds **iff** `insert q J ≠ univ ∨ J = ∅`.  Positive in the
  one-surviving regime, negative at the terminal face with nonempty `J` — an unsatisfiability proof,
  so the consumers there are vacuous and the hypothesis must exclude that face.
* **`facePacket_differentialIndependent_of_periodsIntegrallyIndependent`** — the descending
  face-lifting lemma with both arithmetic premises discharged; only its inductive independence
  premise remains.

### Universal law: the exact independence threshold of the face hierarchy

`HTGeometry/FaceIndependenceDichotomy.lean` (built, axioms clean, registered).  The corpus had the
two halves separately — joint independence of all faces retaining two periods, and differential
algebraicity of every packet below that — but never the equivalence, so "two periods" read as a
convenient sufficient condition rather than the threshold it is.

* **`hypertranscendentalOver_facePacket_iff`** — an external translate of a face coordinate is
  hypertranscendental over the constants **iff** the face retains at least two periods;
* **`diffIndepOn_multipleEllipticGammaFacePacket_iff`** — the same threshold for a whole packet;
* **`diffIndepOn_facePacketUnion_iff`** — and for an arbitrary family: a family of face packets is
  jointly differentially independent over the constants **iff** every face in it retains at least
  two periods.

The negative half is a vacuity check on every downstream statement quantified over faces: below the
threshold no independence statement can hold, so the hypothesis `2 ≤ (Jᶜ).card` in the layer
theorems is exactly the right one and cannot be weakened.

### The theta period group, computed

The freeness argument only needed `Per ⊆ ℤ + ℤτ`; the exact group is now proved as well.
`meromorphicTranslationStabilizer_thetaLogDerivMero : Per(thetaLogDerivMero τ) = zmultiples 1`, from
the corpus quasi-periodicity `T_τ Ψ_θ = Ψ_θ − 2πi` iterated over `ℤ` and the nonvanishing of the
defect off the lattice; and `meromorphicTranslationStabilizer_faceMero_one_surviving` transports it
to every face with exactly one surviving parameter.

## Re-audit, 2026-07-31: the mathlib-premise instrument re-run on `HilbertMetric`

The instrument (`forallTelescope`, key each `Prop` binder by its head constant together with the set
of `GaloisForLFunctions` constants occurring in it; a key counts as produced when some conclusion —
with `∃`/`Nonempty` unwrapped — has the same head over a superset of those constants) was rebuilt
and run over the built `HilbertMetric` environment: 1 265 project constants, 21 premise keys, 686
conclusion keys, **13 unproduced**, none with more than two uses.

The head of that list is the **scale calibration pair** of the CCR scale-sandwich law:
`logarithmicScaleMean F₁ t = ccrMeanEnergy (A t)` and
`logarithmicScaleVariance F₁ F₂ t = ccrNumberVariance (A t) (B t)`, consumed by four theorems and
satisfied by nothing.  `HilbertMetric/CCRScaleCalibration.lean` (built, axioms clean, registered):

* **`ccr_calibration_energy_law`** — the two calibrations are **one differential law of the family**.
  Differentiating `t · F₁ t = ccrMeanEnergy (A t)` on the open half line gives
  `ccrMeanEnergy (A ·)` the derivative `F₁ t + t F₂ t`, and the variance calibration says exactly
  that this is `ccrNumberVariance (A t) (B t) / t`.  So a calibrated family is one whose mean energy
  has logarithmic derivative equal to its number variance, and nothing about the log-volume survives
  beyond that.
* **`ccrNumberVariance_scalar_eq_ccrMeanEnergy`** — for scalar compressions with the mode-indexed
  unit leakage the number variance *equals* the mean energy (both are `|n| · ∑ᵢ cᵢ²`), so the corpus
  bound `variance ≤ |I| · mean` is attained exactly in one mode.  Sharpness of that bound was not
  previously recorded.
* **`exists_calibrated_ccrFamily`**, **`ccr_scaleSandwich_sqrtScalar`** — the `√t`-scaled scalar
  compressions realize the calibration pair with the linear log-volume `F t = |n| · t`, giving the
  first unconditional instance of the scale-sandwich law (both the logarithmic convexity and the
  power-scale concavity), and showing the four consumers are non-vacuous.

Remaining `HilbertMetric` rows, all with one or two uses: two `fullCCR`-block variants of the same
calibration pair (the same realization should transport through `blockCCRTuple`), four
inequality-shaped budget hypotheses (`gradedFockTransverseFanoMargin`, `quasiFreeSpectralBandBudget`,
`quasiFreeSpectralFanoMargin`, `scalarLogCurvatureNumerator`), two non-degeneracy hypotheses
(`GradedMultiIndex`, `matrixSelfCommutator`), one `LinearIndependent (evaluationRow)`, one
`Filter.Eventually (finiteExponentialInnerGram)`, and one degree-five index inequality.

### The instrument, corrected and persisted

Two blind spots of the first version were closed, and the instrument now lives in the tree at
`scripts/lean/audit_mathlib_premises.lean` (run it with the theorem-area umbrella as its import):

- a conclusion contributes atoms through `∧` and through **both sides of an `↔`**, not only through
  `∃`/`Nonempty`.  Without this, `exists_injective_evaluation_basis` (whose conclusion is
  `∃ nodes, Injective nodes ∧ LinearIndependent …`) and the Fano strict-defect classification
  (an `↔`) were invisible, and their premises were reported open;
- atoms are read **under leading binders**, so a producer of the shape `∃ …, ∀ t, 0 < t → P` counts
  for `P`.

Both were false alarms of the first run: `LinearIndependent (evaluationRow …)` and
`LT.lt (gradedFockTransverseFanoMargin …)` are produced.  Recorded so the next run does not
re-raise them.

**Measurement after the calibration discharge** (umbrella rebuilt, 1 281 project constants): 21
premise keys, 719 conclusion atoms, **7 unproduced**, each with a single use — all four calibration
rows are gone, confirmed by the instrument rather than by hand.  What remains in `HilbertMetric`:

| uses | premise |
|---:|---|
| 1 | `Ne (GradedMultiIndex …)` |
| 1 | `Ne (matrixSelfCommutator …)` |
| 1 | `LT.lt (quasiFreeSpectralFanoMargin …)` (a negative Fano margin) |
| 1 | `LT.lt (quasiFreeSpectralBandBudget …)` |
| 1 | `Ne` on the degree-five normalized value matrix |
| 1 | `LT.lt (scalarLogCurvatureNumerator …)`, i.e. `0 < z z₂ − z₁²` |
| 1 | `Filter.Eventually (finiteExponentialInnerGram …)` |

All seven are satisfiability rows — each asks for a witness rather than a theorem — and none is
consumed more than once.

### The full-tuple calibration, also realized

`exists_calibrated_fullCCRTuple` — the invariant block tuple `blockCCRTuple` of the `√t`-scaled
scalar compression with the mode-indexed unit leakage satisfies every premise of the block-interface
scale-sandwich law, including both calibrations, via `blockCCRTuple_compressionBlock` and
`blockCCRTuple_leakageBlock`.  Axioms clean.

### Residual `HilbertMetric` premises: 7 → 4

`HilbertMetric/PremiseWitnesses.lean` (built, axioms clean, registered).  Three of the seven
single-use rows are closed, each measured by re-running the instrument rather than asserted:

* **`eventually_finiteExponentialInnerGram_det_ne_zero`** — the eventual-nonvanishing premise of
  `finiteHalfGaussianDistance_logDet_secondDerivative_eq` existed only as an anonymous `have` inside
  one long argument, at the single bandwidth `1`.  Named and generalized to every point: the
  determinant is differentiable in the bandwidth, so pointwise nonvanishing spreads.
* **`finiteExponentialInnerGram_posDef_of_coordinate_injective`** — and the pointwise premise is
  itself discharged.  `finiteExponentialInnerGram x t` is the coherent Gaussian Gram of the
  coordinates scaled by `√t`, so the corpus's
  `gaussianCoherentGram_posDef_of_coordinate_injective` makes it positive definite at every positive
  bandwidth on a configuration separated by one coordinate; hence
  **`finiteHalfGaussianDistance_logDet_secondDerivative_eq_of_coordinate_injective`**, the gauge
  invariance of second log-determinant curvature with no determinant hypothesis at all.
* **`matrixSelfCommutator_ne_zero_iff_mul_transpose_ne`** with the nilpotent Jordan block — the
  strict Fano defect `squareEnergy < trace (columnEnergy²)` is *attained*, so the strictness theorem
  is not vacuous.
* **`scalarLogCurvatureNumerator_pos_iff`** (`0 < z z₂ − z₁²` is strict log-convexity of the 2-jet)
  and **`eventually_pos_scalarLogCurvatureNumerator_of_tendsto_unit`** — persistence of strict
  log-curvature holds for every 2-jet converging to the unit jet, with no positivity premise.

Remaining, one use each: two quasi-free sign conditions (`quasiFreeSpectralFanoMargin < 0`,
`0 < quasiFreeSpectralBandBudget`), which need a witness carrying an orthonormal frame and its
energy bounds simultaneously; and two instrument false positives now documented in the script header
— `q ≠ r` between two elements of a corpus index type is a parameter constraint, and the
degree-five determinant row is produced by a theorem that specializes the amplitude, which the
constant-superset test cannot see.

### `HilbertMetric` mathlib-premise layer: closed

The two quasi-free sign conditions are the last genuine rows, and one configuration settles both.
On the diagonal two-orbital frame with one half-occupied level at energy `4` and one empty level at
the band floor (`PremiseWitnesses.lean`):

* `quasiFreeSpectralFanoMargin_twoMode = -2` — mean `2`, variance `4`, so the Fano margin is
  negative and `twoMode_filling_failure` is the filling-failure consequence on an actual
  configuration;
* `quasiFreeSpectralBandBudget_twoMode = 4` on the band `[0, 4]` — positive, so
  `twoMode_support_rank_lower_bound` is the tomography-free support-rank certificate on an actual
  configuration.

Both consumers previously carried a sign hypothesis satisfied by nothing.

**Closing measurement** (1 313 project constants, 22 premise keys, 742 conclusion atoms):
**2 unproduced rows**, and both are the documented false-positive classes — `q ≠ r` between two
elements of a corpus index type, and a determinant row produced by a theorem that specializes the
amplitude.  The trajectory over this sweep was **13 → 11 → 7 → 5 → 4 → 2**, every step re-measured.
No genuine unproduced mathlib-`Prop` premise remains in `HilbertMetric`.

Next scope for the instrument: `GaloisForLFunctions.HTGeometry`.

## The instrument moves to `HTGeometry`

### A collision had made the area unbuildable

`lake build GaloisForLFunctions.HTGeometry` failed outright: `GaloisForLFunctions.HTGeometry.shiftEnd`
was declared both in `SRDifferenceCarrier` (translation of functions on `E`, as a `Module.End`) and
in `ShiftStableLatticeStructure` (its restriction to a translation-stable subspace), and both are
registered in the umbrella.  This is the **third** collision of this kind found by an audit that
imports a whole area at once — no ordinary build does.  The newer module's name is used nowhere
outside it, so it was renamed `translationEnd`/`translationEnd_apply`; the area builds again
(11 979 modules).

### First measurement: 49 155 constants, 496 unproduced premise keys

Two refinements were needed before the list was readable:

- **instance-only keys are dropped.**  A premise such as `Set.Infinite S` whose only corpus constant
  is a measurable-space *instance* is a mathlib hypothesis in a corpus-instrumented type, not a
  premise about a corpus object.  Four such rows accounted for 202 uses.

### The largest premise class in the area, discharged

`Function.Injective (onsiteProductEnergy onsite)` — the total energy `x ↦ ∑ v, onsite v (x v)`
separates configurations — is carried by **133 statements** of the local-spectral observer layer
(85 real, 48 complexified) and was exhibited nowhere.
`HTGeometry/OnsiteEnergySeparation.lean` (built, axioms clean, registered):

* **`injective_onsiteProductEnergy_complexOnsite_iff`** — complexification is inert: the complex
  total energy is the cast of the real one, so the 48 complex consumers carry the *same* hypothesis
  as the 85 real ones, not a stronger one;
* `injective_onsite_of_injective_onsiteProductEnergy` — separation is inherited at every site, so it
  is a genuine strengthening of sitewise injectivity;
* **`injective_onsiteProductEnergy_digitOnsite`** — and it is attained: reading a configuration of
  `n` sites with `m` states as a base-`m` numeral gives a real on-site energy whose total energy is
  the numeral, hence separates (`finFunctionFinEquiv`).  With the equivalence above, the complex
  layer inherits the witness.

### Current `HTGeometry` frontier

After the discharge and the instance filter: 1 351 premise keys, **487 unproduced**.  The head of the
list, by use count:

| uses | premise | reading |
|---:|---|---|
| 20 | `MutuallySingular (…, circleLebesgue)` | genuine — the singular-continuous layer |
| 19 | `z ∈ positiveHalfPlane` | parameter constraint, not debt |
| 38 | `Ideal.IsPrime p` on the projective chart rings (three keys) | parameter constraint; the layer is non-vacuous because `⊥` is prime in a domain |
| 16 | `LT.lt (jetMonomialDegree …)` | degree bound, likely a constraint |
| 12 | `IsWeightedHomogeneous (gammaPoleSourceDerivativeWeight …)` | genuine candidate |
| 11 | `Function.Injective (ClassicalAnalyticNevanlinnaCarrierFamily.quotient …)` | part of the known open Nevanlinna bundle |

`HilbertMetric` remains clear (2 documented false positives).

### The circle singularity premise, discharged

`mu ⟂ₘ circleLebesgue` — carried by the F. and M. Riesz layer and the pure-singular carrier
trichotomy (20 statements) — was satisfied by nothing.  `HTGeometry/CircleSingularWitness.lean`
(built, axioms clean, registered):

* **`circleLebesgue_singleton`** — circle Lebesgue measure has no atoms.  It is the transport of the
  additive Haar probability measure along `AddCircle.homeomorphCircle`, and the preimage of a point
  is a point, whose Haar measure is the volume of a closed ball of radius zero;
* the `NullSingletonClass` instance, hence
  **`mutuallySingular_circleLebesgue_of_countable`** — *every* measure carried by a countable set is
  singular to circle Lebesgue measure.  This is the reusable criterion: singularity to Lebesgue is
  free for purely atomic carriers;
* **`mutuallySingular_dirac_circleLebesgue`** and `oneSidedFourierRigid_dirac` — the point masses are
  witnesses, so the F. and M. Riesz conclusion holds on an explicit finite circle measure.

Note on the neighbouring row: the pure-singular *trichotomy* additionally requires
`mu.support.Infinite`, which the instrument does not nominate because it mentions no corpus constant
(only the measurable-space instance).  A joint witness therefore needs a countably-supported measure
on infinitely many points — the criterion above already gives its singularity, so only the finiteness
of the total mass remains.  Recorded as the next step in this lane.

**Concurrent-lane note.**  `lake build GaloisForLFunctions.HTGeometry` currently fails on
`HTGeometry/CompactOperatorBoundedBelow` (unknown constant, unsynthesized instances) — a module
another lane is mid-edit on, registered in the umbrella while broken.  It is unrelated to this work;
the modules here build and were axiom-checked directly.  The area-wide re-measurement is blocked
until that module compiles.

### The pure-singular carrier hypotheses, jointly realized

The trichotomy needs a finite circle measure that is *simultaneously* singular to `circleLebesgue`
and of infinite support; the previous entry gave only the singular half (point masses have finite
support).  `HTGeometry/CircleAtomicCarrier.lean` (module built, axioms clean, registered):

* **`support_infinite_of_injective`** — a measure with infinitely many atoms of positive mass has
  infinite support.  Every neighbourhood of an atom has measure at least that atom's, so the range
  of the atom sequence sits inside the support;
* `circleAtomPoint n = Circle.exp (1/(n+1))` with `circleAtomPoint_injective` — the angles lie in
  the principal branch, where `Circle.arg_exp` inverts the exponential, so distinct indices give
  distinct points;
* `circleAtomicMeasure` — mass `2⁻ⁿ⁻¹` on the `n`-th point; a probability measure by the geometric
  series, singular by the countable-carrier criterion of the previous entry, and with every atom of
  positive mass;
* **`exists_pureSingularCarrier_circle`** — the joint witness: a probability measure on the circle,
  singular to Lebesgue, with infinite support.  The pure-singular carrier trichotomy is therefore
  not vacuous.

The area umbrella still does not build (`HTGeometry/CompactOperatorBoundedBelow`, another lane's
work in progress), so these modules were built and axiom-checked directly rather than through the
umbrella, and the area-wide re-measurement remains deferred.

### `HTGeometry` re-measured, and what the residue actually is

The area umbrella builds again (another lane's `CompactOperatorBoundedBelow` was repaired), so the
scan could be re-run with the three new modules in place: 49 254 constants, 1 355 premise keys,
**488 unproduced**.  The `MutuallySingular … circleLebesgue` row is gone.

The head of the list was then checked by hand, and none of it is debt:

| uses | premise | verdict |
|---:|---|---|
| 19 | `z ∈ positiveHalfPlane` | parameter constraint |
| 16 | `0 < jetMonomialDegree n anchor` | parameter constraint — the anchor monomial must involve a derivative variable |
| 38 | `Ideal.IsPrime p` on the projective chart rings (3 keys) | parameter constraint; `⊥` is prime in a domain |
| 12 | `IsWeightedHomogeneous gammaPoleSourceDerivativeWeight P W` | **produced by mathlib** — `MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous`, used exactly so inside `gammaPoleSymbolicPolynomialJetLaurentEval_maximalWeight_coeff_ne_zero` |
| 11 | `Function.Injective (ClassicalAnalyticNevanlinnaCarrierFamily.quotient …)` | the known open Nevanlinna bundle, already classified on this card |

That last line is a **third false-positive class**, now documented alongside the other two: a premise
whose producer is a *mathlib* theorem applied to a corpus object is invisible to a scan that looks
for corpus producers only.  Reversing the constant-set test to catch it would make every `Eq` premise
match every `Eq` conclusion, so the instrument keeps its current direction.

**Reading of the number.**  `488` is not a debt count.  At this scale the scan's value is that it
surfaces *large* premise classes — the 133-use `onsiteProductEnergy` separation and the 20-use circle
singularity, both genuinely open and both now discharged — not that it enumerates gaps.  Above 11
uses there is no genuine open row left in `HTGeometry`, and the one at 11 is the Nevanlinna bundle
whose obstruction (an indeterminate Hamburger moment problem with its Nevanlinna parametrization) is
recorded above.

Next scope for the instrument: `GaloisForLFunctions.RHTower`.

### The atom-dominant integrability premise, discharged

`Integrable (atomDominant a R) ν` — the dominating-function hypothesis of the atom-limit and
chamber-bound layers (7 statements) — was assumed everywhere and proved nowhere, although the module
defining `atomDominant` already supplied the decomposition its proof needs.
`HTGeometry/AtomDominantIntegrable.lean` (built, axioms clean, registered):

* `measurableSet_atomBall` — the near-node set is open;
* **`integrable_atomDominant`** — the dominant is integrable under exactly the two standing
  conditions of a Herglotz measure: finite mass on the bounded set `{|t − a| < R}`, and an integrable
  Herglotz weight `1/(1+t²)`.  Near the node the dominant is the constant one on a finite-measure
  set; away from it, a constant multiple of the Herglotz weight;
* `integrable_herglotzWeight_of_isFiniteMeasure` and
  **`integrable_atomDominant_of_isFiniteMeasure`** — the Herglotz weight is bounded by one, so on a
  finite measure both conditions are automatic and the premise disappears entirely.

### `RHTower` scan: blocked this round

The area umbrella does not build — `RHTower/MobiusBinaryExcursion` is another lane's work in
progress — and a scan assembled from the built object files failed on a moving target: fourteen
successive rounds of dropping modules reporting `incompatible header` did not converge, because
concurrent builds are rewriting the large `RHTower` object files while the scan reads them.  The
area-wide `RHTower` measurement is therefore deferred rather than reported; nothing about it is
claimed here.

### `RHTower` is unbuildable: a systematic post-bump repair wave

The `RHTower` umbrella fails, and not because of one lane's edit.  Four distinct modules were
repaired this round, each a different mechanical failure class, and the chain continues:

* `MobiusBinaryExcursion`, `HermitianMertensIntegrationLaw` — **name shadowing**.  `Finset.antidiagonal`
  in these files resolves to the Hahn-series `Set.IsPWO` antidiagonal, not the `ℕ` one; the sibling
  `MobiusLaplaceAdditiveTriangle` already writes the qualified
  `Finset.HasAntidiagonal.antidiagonal (A := ℕ)`, which is the fix.  Adding
  `Mathlib.Data.Finset.NatAntidiagonal` does **not** help — the ambiguity, not a missing instance, is
  the cause.
* `EvenIndexHermitianAbelBound` — **instance path**.  `Summable.comp_injective` now lands on
  `addCommGroup.toAddCommMonoid` while the goal carries `instAddCommMonoid`; `simpa only` cannot
  cross that, `exact` can (the two are defeq).  Same shape as the recorded `HasDerivAt` workaround.
* `XiSquaredSeamTailFromSixtyFour` — **numeral normalization**.  The dyadic rung lemmas state
  exponents as `2 ^ k` while the goals carry `16`, `8`, `4`, `2`; `simp only` no longer reduces the
  power, so each use needs a `norm_num` pass on the hypothesis first.

Still failing after those four: `XiCTaylorThetaTailPhaseAdaptedProuhetFiniteEdge`,
`PrimeArchBernsteinExponentialPhase`, `SuzukiCausalEntryThirdJetBoundaryLaw`, and whatever the build
reaches after them.  The failures are all of the same three mechanical kinds, which points at a
toolchain or mathlib bump rather than at in-progress research edits.

**Consequence for this card**: the `RHTower` premise scan cannot run until the area builds, and the
earlier attempt to scan from object files instead failed on a moving target.  The `RHTower`
measurement stays deferred; no figure is claimed.

### Repair wave, round two: six modules green, one left standing

Three more classes fixed, each verified with `lake env lean`:

* `XiCTaylorThetaTailPhaseAdaptedProuhetFiniteEdge` — **coercion spelling**.  `coeff_map` now leaves
  `algebraMap ℝ ℂ (G.coeff x)` where the goal carries `↑(G.coeff i)`; adding
  `Complex.coe_algebraMap` to the `simpa only` set closes it.
* `PrimeArchBernsteinExponentialPhase` — the limit point `1 - 0 + 0 * w` is no longer reduced to `1`
  by `exact`; `simpa using h` is.
* `SuzukiCausalEntryThirdJetBoundaryLaw` — **not fixed**, and deliberately restored to its original
  text.  `convert … using 1` on a `HasDerivAt` now emits an instance goal
  `addCommGroup = instNormedAddCommGroup.toAddCommGroup` *before* the value goal, so the following
  `rw` lands on the wrong goal.  Two of its four sites adjust only the derivative value and are fixed
  by `HasDerivAt.congr_deriv`; the other two adjust the *function* as well, and rewriting those needs
  the intended function identity written out, which is more than a mechanical edit.  Rather than
  leave a half-converted file, every edit was reverted: the module is exactly as it was found.

Running total for the wave: `MobiusBinaryExcursion`, `HermitianMertensIntegrationLaw`,
`EvenIndexHermitianAbelBound`, `XiSquaredSeamTailFromSixtyFour`,
`XiCTaylorThetaTailPhaseAdaptedProuhetFiniteEdge`, `PrimeArchBernsteinExponentialPhase` — six green.
`SuzukiCausalEntryThirdJetBoundaryLaw` is the next module to take, with the diagnosis above; after it
the build will reveal the rest.  The four failure classes now on record — name shadowing, instance
path, numeral normalization, `convert` goal order — cover everything seen so far.

### Repair wave, round three: eleven modules green, two new classes

`SuzukiCausalEntryThirdJetBoundaryLaw` is fixed.  Its four `convert … using 1` sites split in two:
the two that adjust only the derivative value take `HasDerivAt.congr_deriv` (with `symm`, since
`congr_deriv` wants `hValue = goalValue` while `convert` produced the reverse); the one that also
adjusts the *function* needs the function identity written out as a `funext` lemma and rewritten
into the goal first, after which `congr_deriv` applies.  That is the general recipe for this class.

Also fixed this round:

* `PrimeArchBernsteinConfinedPhase` — `simpa only` no longer unfolds
  `xiEndpointNormalizedReciprocalSquare`; adding the definition to the simp set closes it.
* `PrimeArchThetaMorseFisherExponentialEnvelope` — **`ring` cannot see inside `Real.exp`**:
  `exp (-2 * x)` and `exp (-(2 * x))` are distinct atoms, so the old `convert … <;> ring` fails.
  Rewriting the exponent first and finishing with `linarith` is the fix.
* `ScaleCovariantBernsteinPurityJet`, `ScaleCovariantBernsteinDividedPowerStability`,
  `TwistedMertensOrderLowerBound` — the antidiagonal shadowing again, and two follow-on classes it
  exposed: `Finset.mem_antidiagonal` needs the same `HasAntidiagonal` qualification, and
  **`Finset.sum_eq_add_sum_diff_singleton` no longer exists**.  Its modern replacement is
  `Finset.add_sum_erase` together with `Finset.sdiff_singleton_eq_erase`; a three-line private lemma
  restores the old statement so the surrounding proof structure is untouched.

Eleven modules green so far.  Six failure classes are now on record: name shadowing, instance path,
numeral normalization, `convert` goal order, `ring`-through-`exp`, and renamed `Finset` lemmas.

Next failure named by the build: `PrimeArchThetaSingleGibbsGammaCoordinate` (`simp` made no
progress).  The `RHTower` premise measurement remains deferred until the area builds.

### Repair wave, round four: seventeen modules green

`PrimeArchThetaSingleGibbsGammaCoordinate`, `XiShiftedReciprocalHankelTailCriterion`,
`SuzukiCriticalEntryWallQuarterShiftGreenLaw`, `ScaleCovariantBernsteinPurityJacobian`,
`PrimeArchThetaGibbsEquipartition`, `PrimeArchThetaTwoChannelSteinRobertson`.

The `convert` class is now fully characterised.  `convert X using n` on a `HasDerivAt`, `HasSum` or
`Tendsto` goal emits an **instance-equality goal first** — for example
`instAddCommMonoid = instNonUnitalCommRing.…toAddCommMonoid` — which the following tactic script was
never written to see.  Three repairs cover every occurrence:

* value-only sites → `HasDerivAt.congr_deriv` (or `HasDerivWithinAt.congr_deriv`), which never
  produces the spurious goal;
* sites that also adjust the function → keep `convert`, but raise the depth (`using 2`) and discharge
  the instance goal with `exact rfl`; at depth 2 the function goal arrives already beta-reduced, so
  the old `funext` step must be dropped;
* `all_goals ring` scripts → `all_goals first | rfl | ring`.

Two further classes appeared and are recorded:

* `simpa` failing where the residue is only `id x` versus `x` (add `id_eq`), or a partially applied
  definition that `simp only` cannot delta-unfold (use `exact`, which sees through delta and eta);
* a `Tendsto` whose limit *value* is no longer normalized — `𝓝 (f 0 * (a·0 + b·0²) * …)` against
  `𝓝 0` — where the fix is to prove the value is zero and rewrite, not to fight the filter
  (`𝓝[>] 0` and `𝓝 0 ⊓ 𝓟 (Ioi 0)` are already defeq).

Seventeen modules green.  The wave is mechanical from here: every failure so far falls into one of
eight recorded classes.  `RHTower` still does not build, so its premise measurement remains deferred.

### Repair wave, round five: twenty-two modules green

`XiSquaredSeamPowerSixtyFourMassCriterion`, `GammaSewnJuliaRectangularDivisorTransgression`,
`SuzukiCausalDepthFrostmanTransfer`, `PrimeArchThetaThermalSusceptibility`,
`GammaXiResponseGapOneCutSpectrum`.

Refinement of the `convert` recipe, learned here: the number of spurious instance goals is **not
always one**.  `GammaXiResponseGapOneCutSpectrum` emits two — an `AddCommGroup` equality and a
`Module` equality (`Semiring.toModule = RCLike.toInnerProductSpaceReal.toModule`) — so the repair is
to prepend one `· exact rfl` bullet per instance goal and leave the original bullets untouched.
Reading the goal the failing tactic actually saw is the only reliable way to count them.

Three further small classes, all `simpa → exact` in effect:

* `Complex.ofRealCLM.hasDerivAt` and `HasDerivAt.comp` now land on a different
  `AddCommGroup`/`Module` path than the goal; `exact` crosses it, `simpa` does not;
* `Summable.map … reCLM` produces `⇑reCLM ∘ f` where the goal has `fun q => (f q).re` — again `exact`;
* a `Prop`-valued certificate definition (`ThetaCuspFirstRadialQuadraticSteinEnergyCertificate`) must
  be unfolded in the hypothesis before `simpa`, since `simp only` will not delta-unfold it.

Twenty-two modules green.  Every failure in five rounds has fallen into the recorded classes; none
has needed new mathematics.  `RHTower` premise measurement still deferred.

### Repair wave, round six: twenty-six modules green

`XiSquaredSeamPowerSixtyFourJensenKernel`, `XiCTaylorThetaTailPhaseAdaptedProuhetRankTwoCurrent`,
`XiCTaylorThetaTailPhaseAdaptedProuhetHalfLine` (seven separate sites),
plus the earlier ones.

Everything this round was the **`simpa` → `exact` class**, in five new spellings.  The pattern is
always the same: `simp` normalizes the *statement it is given* into a form that no longer matches the
goal syntactically, while the two remain definitionally equal, so `exact` succeeds where `simpa`
fails.  The spellings seen so far:

| hypothesis shape | goal shape |
|---|---|
| `(fun x => x ^ 64)⁻¹` (`Pi.inv`) | `fun x => (x ^ 64)⁻¹` |
| `f / g` (`Pi.div`) | `fun N => f N / g N` |
| `ofReal ∘ f` | `fun a => ↑(f a)` |
| `⇑reCLM ∘ f` | `fun q => (f q).re` |
| `RCLike.im (∫ …)` | `(∫ …).im` |
| `Integrable f (volume.restrict (Ioi 0))` | `IntegrableOn f (Ioi 0) volume` |

The reliable repair is to bind the term with `have`, run whatever `simp only` normalization the
original `simpa` intended *on the hypothesis*, and finish with `exact`.  One extra wrinkle:
`Complex.continuous_ofReal…comp` now produces the limit `𝓝 ↑0` rather than `𝓝 0`, so
`rw [Complex.ofReal_zero]` is needed on the hypothesis before `exact`.

Twenty-six modules green over six rounds, nine failure classes recorded, no new mathematics needed at
any point.  `RHTower` premise measurement still deferred.

### Repair wave, round seven: thirty-three modules green

`PrimeArchThetaAtomLikelihoodRatio`, `GammaJuliaEndpointCorrectionHilbertSchmidtDressing`,
`XiCTaylorThetaTailPhaseAdaptedProuhetTopRow`, `XiSquaredSeamCassiniSource`,
`XiCTaylorThetaTailFiniteArithmeticEndpoint`, `SuzukiCausalDepthRectangularCaratheodoryGrowth`,
`XiSquaredSeamPowerSixtyFourJensenKernel`.

**Important correction to the `simpa` → `exact` recipe.**  `exact` is not always the right tool: on
`Summable.comp_injective` with a composed index map it made the elaborator unfold far enough to hit
a `whnf` heartbeat timeout.  The cheap and reliable repair for a *composition* mismatch is
`simp only [Function.comp_def]`, which turns `f ∘ g` into `fun x => f (g x)` syntactically; reserve
`exact` for small definitional gaps such as `IntegrableOn f s μ` versus `Integrable f (μ.restrict s)`
or `Pi.sub`/`Pi.pow` against an explicit lambda.

Two more value-normalization cases: `(hasDerivAt_const x 1).sub (hasDerivAt_id x)` now reports its
derivative as `0 - 1` rather than `-1` (`simp only [zero_sub]` on the hypothesis), and
`Complex.continuous_ofReal…comp` needs `Function.comp_def` *and* `Complex.ofReal_zero` together.

Thirty-three modules green over seven rounds.  Still no new mathematics anywhere in the wave;
`RHTower` premise measurement remains deferred.

### Repair wave, round eight: thirty-six modules green

`PrimeArchThetaReflectedBudgetTailTransfer`, `PrimeArchThetaGaussianApertureBalance`,
`ThetaCuspLikelihoodSpectralMeasure`.

Nothing new in kind — all three were the `convert` goal-order and `IntegrableOn`/`Integrable`
classes.  Two practical notes worth keeping:

* when a `convert … using 1` has **no** following tactic (the old elaborator closed the value goal
  itself), the repair is `refine (…).congr_deriv ?_` followed by `ring`, not an added bullet;
* the `IntegrableOn` repair sometimes needs the normalization applied to *both* sides
  (`simp only [neg_mul] at hI ⊢`) before `exact`, because the goal carries the un-normalized form.

Thirty-six modules over eight rounds.  The wave is still entirely mechanical.

### Repair wave, round nine: thirty-nine modules green

`XiCTaylorThetaTailProductFiberGlobalCurrent`, `SuzukiCofinalPositiveFinitePartNoGo`,
`XiSquaredSeamCassiniPairQuotient`.

The `whnf` timeout trap struck a second time, so the rule is now firm: **never reach for bare
`exact` when the definitional gap sits under a big `Summable`/`Integrable` statement.**  Three safe
alternatives, in order of preference:

1. `Summable.congr` (or the analogous `.congr`) with a pointwise `rfl` — cheap, because the
   definitional check happens one argument at a time rather than on the whole statement;
2. `simp only [Function.comp_def, Complex.imCLM_apply]` and friends, to make the two sides
   syntactically equal;
3. bare `exact`, only for genuinely small gaps such as `IntegrableOn` versus `Integrable … restrict`
   or a partially applied definition (`¬ Summable suzukiCriticalSharpPrimeMass`), where `simp only`
   cannot delta-unfold and `exact` is cheap.

Note also that `simp only [someDef]` will not unfold a **partially applied** definition — that case
always needs `exact`, which is the exact opposite of the rule above; the discriminator is the size of
the term, not the shape of the mismatch.

Thirty-nine modules over nine rounds.

### Repair wave, round ten: forty-four modules green

`ThetaCuspLikelihoodModularSeam`, `ThetaCuspFiniteShellSeamCancellation`,
`XiCTaylorThetaTailCoreCurrentCapstone`, `XiCTaylorThetaTailProductFiberGlobalReflection`,
`CCMFirstClockLandauNormal` (partial — see below).

One diagnostic lesson worth recording: an error message that names a *lemma application* rather than
a tactic (`Type mismatch: … integrableOn_cos_mul_thetaCuspTailDerivative 0 t`) points at the place
that term is **consumed**, which need not be the line the error cites.  Here the real site was a
`simpa only [mul_comm] using …` several lines down, and editing the cited line changed nothing.
Read the surrounding tactic block, not just the reported line.

Still open in `CCMFirstClockLandauNormal`: three sites at lines 74–85 involving `(id ^ 2)⁻¹`
(`Pi.inv` of `Pi.pow`) against an explicit lambda, plus a `field_simp` that no longer fires.  Same
classes, not yet applied.

Forty-four modules over ten rounds.

### Repair wave, round eleven: `CCMFirstClockLandauNormal`, partly

The two `Complex.hasDerivAt_sin/cos … comp` sites and the two inverse-power sites are fixed.  The
inverse-power repair needed a shape not used before: the goal function had to be rewritten with a
`funext` lemma (`(fun z => 1 / z ^ 2) = fun z => (z ^ 2)⁻¹`) *before* `exact`, because
`(id ^ 2)⁻¹` is `Pi.inv` of `Pi.pow` and no `simp only` set bridges it to `1 * (z ^ 2)⁻¹`; the
derivative value additionally needed `norm_num` to reduce the exponent `2 - 1`.

Still failing in that module: `convert … using 1` blocks whose trailing combinator leaves
"No goals to be solved" — `<;> tac` runs `tac` on goals `convert` has already closed, and replacing
it with `all_goals first | rfl | …` moves the error rather than removing it, so those blocks need
their bullets written out explicitly against the goals actually produced.  One further `hi` site and
one `funext`/instance site remain.

The module is left in a consistent, partially repaired state — better than found (the sin/cos sites
were failing before) but not green, and that is recorded here rather than implied by a count.

## The `RHTower` mathlib-premise measurement, at last

The area umbrella loads again, so the instrument of
`scripts/lean/audit_mathlib_premises.lean` ran on `RHTower` with producers collected from all
three areas: **102 579 project constants scanned, 311 premise keys, 22 983 conclusion atoms,
114 unproduced**.  Wall time under three minutes; no object-file surgery was needed this round.

Head of the list, classified by hand:

| uses | premise | verdict |
|---:|---|---|
| 148 | `2 * h7.m ∣ q ^ 2` (`GelfondSchneiderProof.Setup.m`) | parameter constraint — the capstone `transcendental_cpow_of_isAlgebraic_of_irrational` *chooses* `q := 2·m·(6h·⌈c₁₅⁴⌉)` and discharges it in a `have` |
| 8 | `u ∈ Fin (m * n q)`, `t ∈ Fin (q*q)` | the same choice, same capstone |
| 6 | `canonicalFeatureVolume … ≠ 0` | discharged: `gammaSewnFourRateBoundaryFeature_canonicalFeatureVolume_pos` gives `0 < …`, and all six `_of_volume_ne_zero` theorems already have an unconditional sibling |
| 5 | `ReesOperatorGradeAtMost atTop primeWoldBoundaryVolumeBelow K R` | **genuine — the class was never exhibited**; discharged below |
| 3 | `…ctorIdx`, `HEq …` rows | recursor artifacts, not premises |

**Two more false-positive classes**, on top of the three already recorded:

4. *A premise discharged by a `let`/`have` inside the capstone.*  The producer is not a theorem at
   all, so no conclusion-atom scan can see it.  This is the 148-use row, by far the largest in the
   area, and it is not debt.
5. *A producer whose conclusion has a different head.*  `0 < X` does not match the premise `X ≠ 0`,
   although `.ne'` bridges them in one step.  The whole `canonicalFeatureVolume` row is of this
   kind.

**Namespace hygiene, found while reading the flagged rows.**  Five modules
(`PrimeValuationHellingerReesJetStability`, `CriticalActivationReesSourceLaw`,
`AsymptoticTypeSuperselection`, `PrimeValuationHellingerReesReflectionFracture`,
`XiSourceModularTypeSuperselectionLaw`) declare into the *top-level* namespace `RHTower`, not
`GaloisForLFunctions.RHTower`.  The instrument's `isProj` test therefore reads their `Prop`
definitions as mathlib heads.  Not corrected here — the rename touches five modules and their
dependents while other lanes are editing them — but recorded, since it changes what the scan means
on that layer.

### The Rees operator-grade row, discharged: a filtration with inhabited levels

`ReesOperatorGradeAtMost l a K R` is the hypothesis of every no-sewing theorem in the Rees layer
(`no_finiteReesOperator_sews_flat_to_nonflat`,
`no_finiteReesOperator_sews_reflected_Hellinger_sectors`, and the two Xi-charge specializations).
Nothing in the corpus ever exhibited an operator family satisfying it, so every one of those no-go
statements was formally at risk of being vacuous — and a vacuous no-go asserts nothing.

Two new modules close this, both built and axiom-clean
(`propext, Classical.choice, Quot.sound` only):

`RHTower/ReesGradeFiltrationFlatRadicalLaw.lean` — the abstract law.  Call a scale *contracting*
when `∀ᶠ x in l, 0 < a x ∧ a x ≤ 1`.  Then

* `reesGradeAtMost_zero_iff` — grade zero **is** boundedness along the filter;
* `ReesAllOrdersFlat.reesGradeAtMost_zero` — the flat radical sits inside grade zero, hence inside
  every grade;
* `reesGradeAtMost_mono`, `reesGradeAtMost_add`, `reesGradeAtMost_const_mul`,
  `reesGradeAtMost_mul` — the grades are a filtration of an `ℝ`-algebra, and a product **adds**
  grades;
* `ReesAllOrdersFlat.add`, `ReesAllOrdersFlat.const_mul`, together with the corpus's
  `reesAllOrdersFlat_mul_reesGradeAtMost` — the flat germs are an **ideal** of that algebra;
* `not_reesAllOrdersFlat_one` — on a scale tending to zero along a nontrivial filter the ideal is
  **proper**;
* `not_reesGradeAtMost_inv_pow_succ` — and the filtration is **strictly increasing at every step**,
  so the no-go at grade `K+1` is strictly stronger than at grade `K`;
* `reesGradeAtMost_of_isBigO_one`, `reesOperatorGradeAtMost_of_isBigO_one`,
  `reesOperatorGradeAtMost_const`, `reesOperatorGradeAtMost_zero`,
  `reesOperatorGradeAtMost_smul_const`, `reesOperatorGradeAtMost_inv_pow_smul_const` — every
  bounded family has **every** finite grade, and a scalar family of prescribed inverse-power growth
  realizes a grade exactly.  These are the producers the scan wanted.
* `reesGradeFiltration_law` — the five statements bundled as one law.

`RHTower/ReesGradeFiltrationPrimeWoldWitness.lean` — the same on the arithmetic scale.  The prime
Wold boundary volume is contracting (`primeWoldBoundaryVolumeBelow_eventually_contracting`: positive
at every stage, and eventually below one because it tends to zero), so every grade is inhabited on
it and the filtration is strict there.  The no-go statements then acquire content:

* `no_boundedOperator_sews_primeWold_flat_to_halfNormal` — no **bounded** operator family carries
  the flat reflected irregular Gamma gauge onto the vacuum half-density;
* `no_invPowMultiplier_sews_primeWold_flat_to_halfNormal`,
  `no_invPowOperator_sews_primeWold_flat_to_halfNormal` — nor does any multiplier or operator family
  of prescribed inverse-power growth `(volume)⁻¹ ^ K`, for every `K`;
* `no_boundedOperator_sews_reflected_Hellinger_sectors`,
  `no_invPowMultiplier_sews_reflected_Hellinger_sectors` — the same two witnesses applied to the
  reflection fracture at an arbitrary charge `0 < c < 1/2`, so the fracture no-go is non-vacuous
  without any hypothesis about an actual Xi zero;
* `primeWoldReesFiltration_law` — bundled.

**Reading.**  The scattered no-sewing theorems are one statement: *the all-orders-flat radical is a
proper ideal of the filtered algebra of finite-Rees-grade germs, and the filtration is exhaustive
in the bounded direction and strict in the singular one.*  What the corpus had was the ideal
property alone; what was missing, and is now proved, is that the algebra acting on it is large —
containing every bounded family — and strictly graded, which is what makes "no finite-grade
operator sews" a real obstruction rather than an empty quantification.

### The Ising-tree convergence rows: refuted, except one

The `TendstoLocallyUniformly` rows nominated by the `RHTower` scan are not debt but *category (b)*
— the premise is proved unsatisfiable:

* `balancedPrimeIsingTreePartition → unitCentralXiC` —
  `not_tendstoLocallyUniformly_balancedPrimeIsingTreePartition_unitCentralXiC`;
* `centralNormalizedPrimeIsingTreePartition → XiC` and `→ unitCentralXiC` —
  `not_tendstoLocallyUniformly_centralNormalizedPrimeIsingTreePartition_{XiC,unitCentralXiC}`.

Both go through one universal law,
`HTGeometry.not_tendstoLocallyUniformly_of_hypertranscendental_of_fixedModalJetWidth`: a sequence
of entire functions of *uniformly bounded modal jet width* cannot converge locally uniformly to a
hypertranscendental limit.  The arithmetic input is the second-jet variance bound
`vertexCount_mul_logTwo_sq_div_four_le_neg_re_iteratedDeriv_two_balanced`, which turns convergence
of the second jet into an eventual bound on the vertex count, hence a uniform modal width `2 ^ V`.

**The one row not yet closed** is the *unbalanced* partition:
`riemannHypothesis_of_primeIsingTreePartition_tendstoLocallyUniformly` (and its
`_mul_XiC` variant) assume `primeIsingTreePartition (T n) → XiC` locally uniformly, and no no-go
covers that hypothesis.  The obvious route: `XiC 0 ≠ 0`, so locally uniform convergence makes
`Z_n(0) → XiC 0 ≠ 0`, `Z_n'(0)`, `Z_n''(0)` converge as well, hence the *normalized* second
cumulant `Z_n''(0)/Z_n(0) − (Z_n'(0)/Z_n(0))²` converges; if that cumulant carries the same
`vertexCount · (log 2)² / 4` lower bound as the balanced one, the vertex counts are eventually
bounded and the same modal-width law applies — which would refute the hypothesis and retire the
unbalanced tree route to RH.  Next step in this lane: check whether the variance bound is stated
for the normalized cumulant or only for the balanced normalization.  Card:
`1-in-progress/prime-source-ferromagnetic-ising-lee-yang-limit-rh.md`.

### The unbalanced Ising row, closed: a central mass floor

The remaining `TendstoLocallyUniformly` row — the *unnormalized* partition, hypothesis of
`riemannHypothesis_of_primeIsingTreePartition_tendstoLocallyUniformly` — is now category (b) as
well, and by a shorter route than the variance/modal-width argument sketched above.

`RHTower/PrimeIsingTreeCentralMassFloorLaw.lean` (built, registered, axioms clean):

* `deriv_primeIsingTreePartition_zero` — the unnormalized partition satisfies
  `Z'(0) = Z(0) · (−m(T)·i/2)`, where `m(T) = treePrimeLeeYangMass T`.  This is the scalar
  normalization identity read backwards: the corpus already had
  `deriv_centralNormalizedPrimeIsingTreePartition_zero`, and `Z = Z(0) · N` with `Z(0) ≠ 0`;
* `logTwo_div_two_le_norm_logDeriv_primeIsingTreePartition` — hence `|Z'(0)/Z(0)| = m(T)/2 ≥
  log 2 / 2`, since `log 2 ≤ m(T)` for **every** finite tree;
* **`logTwo_div_two_le_norm_logDeriv_of_tendstoLocallyUniformly_primeIsingTreePartition`** — the
  floor survives the limit: any locally uniform limit `f` with `f 0 ≠ 0` has
  `|f'(0)/f(0)| ≥ log 2 / 2`.  Both jets converge by
  `HTGeometry.iteratedDeriv_tendsto_of_locallyUniform` at orders `0` and `1`, and `f 0 ≠ 0` makes
  the quotient converge;
* `not_tendstoLocallyUniformly_primeIsingTreePartition_XiC`,
  `…_unitCentralXiC` — the completed Xi germ and its unit-pointed version are even, so their
  central derivative vanishes and the floor excludes them.  **The unbalanced tree route to RH is
  therefore refuted**, exactly as the balanced and scalar-normalized ones already were.

The remaining variant, `riemannHypothesis_of_primeIsingTreePartition_tendstoLocallyUniformly_mul_XiC`,
is *not* refuted, and the law says precisely why:

* **`logTwo_div_two_le_norm_logDeriv_normalization_mul_XiC`** — if the limit is `E · XiC` with `E`
  entire and zero free, then `|E'(0)/E(0)| ≥ log 2 / 2`.  The Xi factor contributes nothing to the
  central logarithmic derivative, so the zero-free normalization must carry the *entire* mass
  floor by itself.

**Reading.**  Four scattered no-gos (balanced, central-normalized to `XiC`, central-normalized to
`unitCentralXiC`, unnormalized) are one inequality: the central logarithmic derivative of a finite
prime Ising tree partition is bounded away from zero by `log 2 / 2`, uniformly in the tree, and
that bound is closed under locally uniform limits.  What used to look like four separate parity or
modal-width obstructions is a single mass floor, and the only surviving formulation of the route is
the one that pays for it in the normalization.

### The Suzuki transport-derivative row, discharged by the inverse function theorem

`HasDerivAt (suzukiPhaseTransport φₛ φᵣ) transportSpeed x` is a hypothesis of the conjugacy
Jacobian layer (phase speed, Clark atom mass, Donoghue probability mass).  It is not an
independent assumption at all: the transport **is** `φₛ⁻¹ ∘ φᵣ`.

`RHTower/SuzukiPhaseTransportDerivative.lean` (built, registered, axioms clean):

* **`hasDerivAt_suzukiPhaseTransport`** — if `φᵣ` is differentiable at `x` and `φₛ` has nonzero
  speed at the transported point, the transport is differentiable at `x` with speed
  `phaseSpeedₛ⁻¹ * phaseSpeedᵣ`.  The inverse branch comes from
  `HasDerivAt.of_local_left_inverse` with `φₛ.symm.continuous.continuousAt`, the idiom the corpus
  already uses in `hasDerivAt_suzukiCenteredInversePhase`;
* `suzukiPhaseTransport_phaseSpeed_of_phases`, `suzukiPhaseTransport_atomMass_of_phases` — the two
  Jacobian theorems restated with the transport hypothesis removed and the transport speed given
  explicitly as the ratio;
* `affineOrderIso`, `hasDerivAt_affineOrderIso`, `hasDerivAt_suzukiPhaseTransport_affine` — the
  layer is inhabited, and increasing affine phases realize **every** positive transport speed
  `a₁⁻¹ a₂`, so the Jacobian statements are not about an empty class.

This is the cleanest kind of row on the list: the premise was a theorem, not an input.

### The `K_R` continuity row, discharged by realizing both parities

`Continuous KW.sigma` is the standing hypothesis of the `KRealClosedCokernel` layer, and the
corpus exhibited no `KRealStructure` at all — in either parity.  The whole layer was a
quantification over a class never shown to be nonempty.

`RHTower/KRealStructureRealization.lean` (built, registered, axioms clean):

* `conjSemilinear`, `kRealConjugation`, `continuous_kRealConjugation_sigma` — complex conjugation
  on `ℂ` is an **even** structure, and it is continuous;
* `quaternionicSemilinear`, `kRealQuaternionic`, `continuous_kRealQuaternionic_sigma` — the
  quaternionic map `(x, y) ↦ (−conj y, conj x)` on `ℂ × ℂ` is an **odd** structure, and it is
  continuous;
* `KRealStructure.eq_zero_of_sigma_eq_self` — an odd structure has no nonzero fixed vector;
* `KRealStructure.sigma_sigma` — an even structure map is an involution;
* **`not_nonempty_kRealStructure_true_complex`** — and the odd realization is *minimal*: `ℂ`
  carries no odd structure at all.  Every conjugate-linear endomorphism of `ℂ` is `z ↦ conj z · c`
  with `c = σ 1`, so `σ² = normSq c ≥ 0` and can never be `−1`.  Two complex dimensions are
  necessary.

So the `K_R` layer is inhabited in both parities, the odd parity is genuinely quaternionic, and the
minimal odd model is `ℂ²`.

### The Schatten log-residue row: two analytic inputs collapse to one asymptotic

`HasSchattenLogResidue p T R` — the existence of the honest logarithmic limit of the critical
energy, i.e. Connes measurability — is assumed by every Gauss-paired endpoint capstone, alongside
a separate weak endpoint bound `MemWeakSchattenClass p T`.  Neither was ever produced.

The corpus already contained the analytic engine, in the *other* area:
`HTGeometry/HarmonicResidueTransfer.lean` proves `tendsto_logResidue_of_mul_succ_tendsto` — a
pointwise law `(n + 1) a_n → R` forces the logarithmic mean `(∑_{n<N} a_n)/log N → R` — together
with `tendsto_harmonic_div_log`.  It had never been connected to the Schatten layer.

`RHTower/SchattenCriticalAsymptotic.lean` (built, registered, axioms clean):

* `tendsto_log_div_log_natCast_succ` — the two logarithmic normalizations `log N` and `log (N+1)`
  are asymptotically equal, which is what the Schatten definition needs and the harmonic transfer
  lemma does not supply;
* `memWeakSchattenClass_of_tendsto_mul_succ` — the weak endpoint bound is *free*: a convergent
  sequence is bounded, so `(n+1) a_n^p → R` gives `a_n^p ≤ C/(n+1)` for all `n`;
* `hasSchattenLogResidue_of_tendsto_mul_succ` — and the residue exists and equals `R`;
* **`exact_schattenDepth_of_tendsto_mul_succ`** — hence a *single* pointwise asymptotic
  `(n + 1) · a_n(T)^p → R` with `R > 0` determines the exact critical depth of `T`: no Schatten
  class at or below `p`, every class strictly above.

`RHTower/GaussPairedChannelCriticalAsymptotic.lean` restates all four consumers with the pair of
certificates replaced by the one asymptotic:
`gaussPairedChannel_exact_schattenDepth_of_asymptotic`,
`gaussPairedFinChannel_exact_schattenDepth_of_asymptotic`,
`exists_cutoff_not_memSchattenClass_of_asymptotic`, and the census law
`finitePrimeAperture_cuspDivisorSchattenRankUniversality_of_asymptotic`.

**Reading.**  The layer's remaining debt is no longer "does an honest Dixmier limit exist" — an
existence-of-limit condition nobody can check — but "what is the exact critical constant of the
approximation numbers", a single asymptotic.  Connes measurability was never an independent
hypothesis: on this scale it is implied by the critical asymptotic, and so is the weak endpoint
bound.

### The Suzuki finite-shift row: smallness, and the finite/infinitesimal bridge

`suzukiFiniteShiftSource F J δ (-z) ≠ 0` — nonvanishing of the *shifted* source — is the standing
hypothesis of the exact finite-shift carrier identities.  It is not independent of the rest.

`RHTower/SuzukiFiniteShiftGeneratorLimit.lean` (built, registered, axioms clean):

* **`suzukiFiniteShiftSource_ne_zero`** — a shift strictly smaller in norm than the endpoint value
  cannot cancel it: `‖δ‖ ‖J w‖ < ‖F w‖ → F w + δ J w ≠ 0`.  No hypothesis on `F w` is needed; when
  `F w = 0` the bound is already impossible;
* `eventually_suzukiFiniteShiftSource_ne_zero` — hence the premise holds for **all sufficiently
  small shifts** whenever the unshifted source is nonzero at that point;
* `tendsto_suzukiFiniteShiftSource` — and the shifted source tends to the unshifted one;
* **`tendsto_suzukiFourierLivsic_finiteShift_dividedDifference`** — on the punctured neighbourhood
  where both `δ ≠ 0` and the premise hold, the exact divided difference of the Fourier--Livšic
  carrier converges to `lineCayley z · (reflected tangent numerator) / F(−z)²`;
* **`tendsto_suzukiFourierLivsic_finiteShift_dividedDifference_generator`** — and that limit *is*
  the logarithmic source generator, dressed by the Cayley factor and the reflection ratio:
  `−lineCayley z · (gen · F z / F(−z))`.

The module already had both halves — an exact finite identity and an infinitesimal generator — and
no theorem linking them.  The link is now proved, so the finite identity is the global form of the
infinitesimal one with no remainder at either end, and its hypothesis is a smallness condition
rather than an assumption.

### The prime-log gate rows: the lattice is proper, and the weld witnesses the gate

Two rows of the obstruction layer: `D.defect g h ∉ primeLogLattice` (the fail-fast prime-log
gates) and `∃ b, D.defect = twoCoboundary b` (the global-choice hypothesis).  Neither had a
producer, and — more seriously — the corpus contained **no `SectionDefect` at all** on a concrete
group, so both gates quantified over data never exhibited.

`RHTower/WeldSectionDefectPrimeLogGate.lean` (built, registered, axioms clean):

* **`not_mem_primeLogLattice_of_isAlgebraic`** — no nonzero algebraic real lies in the prime-log
  lattice.  This is the contrapositive of the corpus's own `weld_spectrum_transcendental` (every
  nonzero lattice element is transcendental), which had never been read in this direction;
* `one_not_mem_primeLogLattice`, **`primeLogLattice_ne_top`** — so `1` is an explicit element
  outside, and the lattice is a *proper* subgroup of the line.  With the recorded
  `primeLogLattice_dense` this pins it exactly: dense and proper;
* `weldSectionDefect θ` — the universal weld cocycle packaged as section-defect data, the first
  `SectionDefect` on a concrete group in the corpus;
* `weldSectionDefect_obstruction_ne_zero_iff` — its class is nonzero exactly when the conversion
  constant is;
* **`exists_sectionDefect_obstruction_ne_zero_isEmpty_primeLogGates`** — with conversion constant
  `1` the weld is a genuine, ungaugeable defect (nonzero obstruction class) that nevertheless
  admits **no** finite prime-log formula and **no** prime-indexed log formula.

So the two gates are simultaneously satisfiable and neither is vacuous: nontriviality of the
obstruction class and failure of the prime-log integrality gate are compatible, and the witness is
the universal weld itself.

## The corpus-`Prop` instrument reaches `RHTower`, and the area is almost clean

The mathlib-premise instrument scans premises with a *mathlib* head.  The complementary instrument
— premises whose head is a **project** `Prop` — had never been run on `RHTower`.  It has now been,
with the same non-reducing telescope and the inductive-`Prop` filter:

**83 509 project constants scanned, 66 project-`Prop` premise keys consumed inside `RHTower`,
6 263 produced constants, 3 unproduced.**

(Blind spot of this run, recorded: the `HTGeometry` umbrella olean was missing — another lane was
mid-rebuild — so only the part of `HTGeometry` inside `RHTower`'s transitive cone supplied
producers.  Two of the three rows were checked by hand against the full source tree.)

| uses | interface | verdict |
|---:|---|---|
| 3 | `IsReflectionTateConservative` | genuine; **classified and closed below** |
| 1 | `IsRelativeCharacterCarrier` | genuine; **classified and closed below** |
| 1 | `MatrixDensityClockCyclic` | false positive — `matrixDensityClockCyclic_const` produces it in `HTGeometry/MatrixDensityClockWitnesses`, outside this run's cone |

Combined with the mathlib-premise scan, `RHTower` now has **no undischarged project-`Prop`
interface**.

### `IsRelativeCharacterCarrier`: the carrier *is* character equality

`RHTower/ReflectedCharacterCarrierClassification.lean` (built, registered, axioms clean):

* `isRelativeCharacterCarrier_zero`, `isRelativeCharacterCarrier_of_eq` — the class always contains
  zero, and contains everything once the characters agree;
* **`isRelativeCharacterCarrier_iff_of_ne_zero`** — a *nonzero* vector is a carrier **iff** the two
  characters coincide.  So "a nonzero internal carrier" is not extra structure; it is `α = β`
  restated.  `exists_ne_zero_isRelativeCharacterCarrier_iff` says the same for the existence form;
* **`riemannHypothesis_of_reflectedCharacterNorm_eq`** — the RH consumer needs no module, no
  carrier and no cohomology class: the scalar equation `‖α q‖ = ‖β q‖` at every Xi zero already
  gives RH, and `riemannHypothesis_of_nonzero_reflectedCharacterCarrier_via_norm` recovers the
  original statement as the special case where a nonzero carrier supplies that equation;
* **`reflectedCharacterNorm_eq_iff_criticalLine`** — and under the two calibrations that scalar
  equation is *equivalent* to the critical-line conclusion at every zero.  The reflected-character
  programme therefore **restates** RH at this point; it does not reduce it.

### `IsReflectionTateConservative`: conservativity is fixed-locus support

`RHTower/ReflectionTateConservativeClassification.lean` (built, registered, axioms clean):

* `fixedSupportedCharges` — the charges supported on the reflection fixed locus form a subgroup;
* `reflectionFixedRestriction`, `reflectionFixedExtension_reflectionFixedRestriction` — restricting
  a fixed-supported charge to the fixed locus and extending it back is the identity;
* **`isReflectionTateConservative_iff`** — a charge lattice admits a conservative reflection-Tate
  reporter **iff** every charge in it is supported on the reflection fixed locus.  The recorded
  faithful-localization theorem was one direction; the converse builds the reporter by restriction
  composed with the inverse Tate identification, needing no new input;
* `isReflectionTateConservative_fixedSupportedCharges` — so the maximal such lattice is
  unconditionally conservative, and the interface is inhabited nontrivially;
* **`riemannHypothesis_iff_exists_reflectionTateConservative_landing`** — hence the reduction has an
  exact converse: a conormal landing lattice with a conservative Tate reporter exists **iff** RH
  holds.

**Reading.**  Both surviving `RHTower` interfaces were re-encodings, and both are now proved to be
so rather than suspected.  This is the `rh-criterion-reencoding` pattern in its sharpest form: the
second clause of the Tate reduction ("a conservative reporter exists") is, after classification,
the statement that all Xi point charges sit on the reflection fixed locus — which is RH itself.

## `HilbertMetric` and `HTGeometry` under the corpus-`Prop` instrument

**`HilbertMetric`**: 1 313 project constants, 7 project-`Prop` premise keys, **0 unproduced**.  The
area is clean under both instruments.

**A fourth area-wide name collision, repaired.**  `lake build GaloisForLFunctions.HTGeometry`
failed outright: `GaloisForLFunctions.HTGeometry.freeCoordinate_ne_zero` was declared both in
`ProjectiveHorizonAffineChartField` (a chart-specific specialization, in a module another lane was
editing minutes earlier) and in `ProjectiveHorizonDepthTwoCurrentTransition` (the *general*
statement, untouched since 26 July, with all four of its uses inside its own module).  The stable
module's name was changed to `freeCoordinate_rationalField_ne_zero`, which resolves the collision
without touching the in-flight file; the area builds again.  As with the previous three, no
ordinary build sees these — only an audit that imports a whole area at once.

**`HTGeometry`**: 103 306 project constants, 319 project-`Prop` premise keys, **12 unproduced**.
Worklist, by use count:

| uses | interface | status |
|---:|---|---|
| 12 | `ComponentProjectivelyIndependent` | **discharged below** |
| 10 | `FiniteLocalInteractionFamily.WeightedObserverSteinerLowerBound` | open |
| 5 | `CoordinateLocalOn` | open |
| 4 | `HasComplexBirthProfile` | open |
| 3 | `FiniteLocalInteractionFamily.ObserverSteinerLowerBound` | open |
| 2 | `HasSemigroupObserverActionRegime` | open |
| 2 | `TriangleRelabelInvariantReporter` | open |
| 2 | `BinaryNaturalOperation.Natural` | open |
| 2 | `WaveSpectrum.CofinalWaveSignEscape` | open |
| 1 | `HasObserverActionRegime` | open |
| 1 | `IsRelativeCharacterCarrier` | already closed this session (stale umbrella olean in this run) |
| 1 | `IsVerticalBohrAP` | open |

### `ComponentProjectivelyIndependent`, discharged by prime logarithms

The standing hypothesis of the component-histogram and replica-factorization laws — every balanced
rational relation among all component energies is componentwise trivial — was assumed twelve times
and exhibited nowhere.  `HTGeometry/ComponentProjectiveIndependenceWitness.lean` (built,
registered, axioms clean):

* **`componentProjectivelyIndependent_of_linearIndependent`** — ordinary integer linear
  independence of the *joint* energy family implies it, and the balanced-relation (zero row sum)
  clause is then not even used.  The proof is `Fintype.linearIndependent_iff` after regrouping the
  sigma sum;
* **`componentProjectivelyIndependent_primeLog`** — labelling the joint index set by distinct
  primes and taking logarithms gives such a family, by the corpus's own
  `logPrime_linearIndependent_int`;
* **`exists_componentProjectivelyIndependent`** — hence for *every* finite family of finite
  component label sets a projectively independent energy family exists.

The hypothesis is therefore a genuine transversality condition, satisfiable on every finite label
set, and the arithmetic source the corpus already owns supplies the witness.

### The two observer-Steiner rows, discharged by the sharp constant

`ObserverSteinerLowerBound L sites r` (3 uses) and
`WeightedObserverSteinerLowerBound L sites weight r` (10 uses) are the standing inputs of the
observer-onset laws — `r` bounds from below the cost of every connected packet spanning the
queried sites — and neither was ever produced.  Both are now closed, with the canonical inhabitant
and a complete characterization.  `HTGeometry/ObserverSteinerNumberLaw.lean` (built, registered,
axioms clean):

* `observerSteinerNumber L sites` — the least cardinality of a spanning packet, as `sInf` over the
  set of spanning-packet cardinalities;
* **`observerSteinerLowerBound_observerSteinerNumber`** — it is a lower bound *unconditionally*
  (`Nat.sInf_le` needs no nonemptiness);
* `le_observerSteinerNumber` — and it is the largest one as soon as a spanning packet exists;
* **`observerSteinerLowerBound_iff`** — so with a spanning packet present the interface is exactly
  `r ≤ observerSteinerNumber`.  `observerSteinerLowerBound_of_not_exists` covers the other case:
  with no spanning packet every `r` qualifies and the onset laws hold at every order;
* `observerWeightedSteinerNumber` with the same three statements
  (`weightedObserverSteinerLowerBound_observerWeightedSteinerNumber`,
  `le_observerWeightedSteinerNumber`, **`weightedObserverSteinerLowerBound_iff`**);
* **`weightedObserverSteinerLowerBound_of_observerSteinerLowerBound`** — the weighted interface is
  not independent: for a positive switch-on schedule an unweighted bound is already a weighted one,
  since `packet.card ≤ ∑_{e ∈ packet} weight e`.  Hence
  `observerSteinerNumber_le_observerWeightedSteinerNumber`.

So the ten weighted consumers need no separate analytic input beyond the three unweighted ones, and
both interfaces are pinned to a sharp, computable-in-principle constant rather than an arbitrary
`r`.

### `CoordinateLocalOn`: locality is factorization

The spectral-causality contrast theorems all take "the term depends only on the coordinates in
`S`" as a hypothesis; five sites consume it and nothing produced it.  It is an entirely structural
condition.  `HTGeometry/CoordinateLocalityLaw.lean` (built, registered, axioms clean — two of its
theorems need no `Classical.choice` at all):

* `coordinateLocalOn_univ`, `coordinateLocalOn_const`, `coordinateLocalOn_apply` — the canonical
  inhabitants: every function is local on everything, constants on nothing, and evaluation at `i`
  on `{i}`;
* `CoordinateLocalOn.mono`, `.comp`, `.add`, `.mul`, `.neg`, `.sub`, and
  `coordinateLocalOn_finsetSum` — monotone in the coordinate set, and closed under
  post-composition, the ring operations and finite sums.  The last one matches the shape the
  causality theorems consume (`∀ c ∈ s, CoordinateLocalOn (support c) (term c)`);
* `coordinateLocalOn_of_factor` and **`coordinateLocalOn_iff_exists_factor`** — the sharp
  statement: a configuration function is local on `S` **iff** it factors through the restriction of
  the configuration to `S`.  The forward direction extends a partial configuration by an arbitrary
  default outside `S`; this is what makes the interface constructive, since a producer now only has
  to exhibit the factored function.

### `HasComplexBirthProfile`: attained, and an invariant

The wall-crossing regimes are stated for a mode with an exact birth profile `c g^b` on the
positive-coupling ray; four sites consume it, none produced it.
`HTGeometry/ComplexBirthProfileInvariance.lean` (built, registered, axioms clean):

* **`hasComplexBirthProfile_monomial`** — the monomial `c g^b` has profile `(b, c)` for `c ≠ 0`, so
  the interface is attained at every order;
* `HasComplexBirthProfile.congr'` — eventual equality along the ray preserves it;
* **`HasComplexBirthProfile.leadingCoeff_eq_zero_of_lt`** — a profile at a strictly smaller order
  forces the higher-order leading coefficient to vanish.  The mechanism is one line of filter
  algebra: `(mode / g^{b'}) · g^{b'-b} = mode / g^b` on the ray, and the left side tends to
  `c' · 0 = 0`;
* **`HasComplexBirthProfile.order_unique`** and **`.unique`** — hence the order and the leading
  coefficient are both invariants of the mode.  The nonvanishing clause `c ≠ 0` in the definition
  is exactly what makes the profile well defined, and this proves it.

### The two observer-action regimes: attained, invariant, and one law

`HasObserverActionRegime` (1 use) and `HasSemigroupObserverActionRegime` (2 uses) say that an
action family *realizes* a regime — a finite limit, or a dephasing escape.  Neither was produced.
`HTGeometry/ObserverActionRegimeInvariance.lean` (built, registered, axioms clean):

* `hasObserverActionRegime_const`, `hasObserverActionRegime_id_dephased`,
  `hasSemigroupObserverActionRegime_const` — both regimes are attained, the dephased one by the
  identity action along `atTop`;
* `hasObserverActionRegime_congr` — eventual equality preserves the realized regime;
* **`HasObserverActionRegime.unique`** and **`HasSemigroupObserverActionRegime.unique`** — along a
  nontrivial filter an action realizes *at most one* regime.  A convergent family has convergent
  magnitude, which cannot also tend to `atTop`; so the regime is an invariant of the action, not a
  choice;
* **`hasSemigroupObserverActionRegime_mul_I_finite`** and **`..._mul_I_dephased`** — the two
  interfaces are not independent.  Multiplying a real character action by `i` gives a contractive
  semigroup action: its real part is zero, so it lies in the closed contractive half-plane, and its
  magnitude is unchanged.  The character observer-action law is therefore the purely imaginary case
  of the contractive semigroup law at the level of regimes, and the dephased coefficients agree
  (both are zero).

A recurring Lean pitfall, now hit twice this session: naming a lemma `Foo.congr'` or `Foo.add` when
`Foo` is a `def` unfolding to a mathlib structure makes the proof body's dot-notation resolve to the
lemma being defined, and the declaration fails as a non-terminating recursion.  Use a snake_case
free function name (`hasObserverActionRegime_congr`) when the body needs the underlying
`Filter.Tendsto.congr'`.

### `BinaryNaturalOperation.Natural`: the classification, as an equivalence

The bare-source no-go proves that a binary operation natural under every map of bare types must be
a coordinate projection, and concludes that no such operation is commutative.  The *converse* — that
the projections are natural — was never recorded, so the naturality interface had no producer and
the no-go quantified over a class never shown to be nonempty.

`HTGeometry/BinaryNaturalOperationClassification.lean` (built, registered, axioms clean; two of its
theorems need only `Quot.sound`):

* `binaryFirstProjection_natural`, `binarySecondProjection_natural` — both projections are natural,
  by `rfl`;
* `binaryFirstProjection_ne_binarySecondProjection` — and they are distinct, evaluated on `Bool` at
  `(false, true)`;
* **`binaryNaturalOperation_natural_iff`** — hence the classification is an *equivalence*, not just
  an implication, and `setOf_binaryNaturalOperation_natural` states it as a set equality: the
  natural binary operations are exactly `{π₁, π₂}`;
* **`binaryNaturalOperation_witnesses`** — so the non-commutativity no-go has exactly two witnesses,
  and is not vacuous.

### `TriangleRelabelInvariantReporter`: invariants exist, and the descent applies

The quadratic-witness descent assumes a scalar reporter blind to every relabeling of the unlabeled
triangle; nothing produced one, so the descent had no instance.
`HTGeometry/TriangleRelabelInvariantWitness.lean` (built, registered, axioms clean):

* `triangleRelabelInvariantReporter_const`, `..._trace`, `..._det` — constants, the trace and the
  determinant are invariant.  Relabeling is the symmetric submatrix reindexing
  `c ↦ c.submatrix σ⁻¹ σ⁻¹`, so determinant invariance is exactly
  `Matrix.det_submatrix_equiv_self`;
* **`triangleRelabelInvariantReporter_sumEntries`** — and so is *every* entrywise sum
  `∑_{i,j} φ (c i j)`, for an arbitrary `φ`, since relabeling only permutes the index pairs.  This
  is the general producer;
* `.add`, `.mul`, `.comp` — invariance is closed under sums, products and post-composition;
* `triangleSquareSumReport` with `differentiable_triangleResidualReport_squareSum` and
  **`exists_entire_squareFactor_triangleSquareSumReport`** — the entrywise square sum is an
  invariant reporter whose orientation restriction is entire and non-constant, so the descent
  theorem applies to it and returns an explicit entire square factor.  The descent is therefore not
  vacuous, and not confined to reporters that restrict to constants.

Note on the trace and determinant: both are invariant, but on the orientation residual `a · C` they
restrict to `0` (the cycle is traceless and singular), so neither witnesses a non-constant descent.
The entrywise square sum does, which is why it is the exhibited witness.

### `CofinalWaveSignEscape`: half of it is free, the rest is non-vanishing

The convex-recurrence law assumes cofinal sign escape — every nonzero polynomial weight drives its
wave trace strictly negative after every time.  That is a dynamical hypothesis, and none was
produced.  `HTGeometry/WaveTraceOddPeriodicEscape.lean` (built, registered, axioms clean):

* **`WaveSpectrum.realWaveTrace_neg`** — every wave trace is an *odd* function of time, for every
  spectrum, with no hypothesis at all.  The only time dependence sits inside `Complex.sin`, and the
  polynomial factor depends on the frequency through its square, so each trace term flips sign;
* `exists_neg_of_odd`, `WaveSpectrum.exists_realWaveTrace_neg` — hence a trace that is nonzero
  anywhere is *negative* somewhere.  Sign escape at a single time needs nothing beyond
  non-vanishing;
* `cofinal_neg_of_odd_periodic` — an odd `p`-periodic function that is nonzero somewhere is
  negative after every time (translate the negative value forward by `⌈(T−s)/p⌉` periods);
* **`WaveSpectrum.cofinalWaveSignEscape_iff_of_periodic`** — so for a spectrum whose traces are
  periodic in time, cofinal sign escape is *equivalent* to the static statement that no nonzero
  polynomial weight has an identically vanishing trace.

**Residual content, stated exactly.**  What remains open is not recurrence but Fourier uniqueness:
whether the map `P ↦ (P((γ_g²)⁻¹))_g` is injective enough that no nonzero weight annihilates the
whole trace.  Oddness was free; periodicity holds for integer frequency families; injectivity is
the real input.

### `IsVerticalBohrAP`: attained, and total boundedness

Bochner's criterion — relative compactness of the vertical translation orbit — is the input of the
uniform-return theorem and was never produced.
`HTGeometry/VerticalBohrAPWitness.lean` (built, registered, axioms clean):

* `isVerticalBohrAP_of_translationInvariant` and `isVerticalBohrAP_const` — every vertically
  invariant function, in particular every constant, satisfies the criterion: its orbit is a single
  point;
* **`isVerticalBohrAP_iff_totallyBounded`** — and since bounded continuous functions into `ℂ` form
  a complete metric space, the criterion is exactly total boundedness of the orbit, which is the
  form in which almost periodicity is actually verified.

## `HTGeometry` project-`Prop` worklist: closed

All twelve rows of the 2026-07-31 measurement are now resolved — nine discharged with producers or
characterizations, one was a false positive of that run's import cone, one (`IsRelativeCharacterCarrier`)
had already been closed earlier the same day, and the last (`CofinalWaveSignEscape`) is reduced to a
named static input with its dynamical half proved.  With `RHTower` and `HilbertMetric` already
clear, no project-`Prop` interface in the three owned areas is left unproduced.

## Re-measurement, 2026-07-31 (evening): the discharges verified

Both area umbrellas were rebuilt with the session's new modules (`lake build
GaloisForLFunctions.RHTower`, `… .HTGeometry`, both green), and the mathlib-premise instrument was
re-run on `RHTower`: **103 942 constants, 320 premise keys, 113 unproduced** (was 102 579 / 311 /
114).  The composition, not the count, is the point.

**Verified gone from the nomination list** — each was a genuine row discharged this session:

| was | premise | closed by |
|---:|---|---|
| 5 | `ReesOperatorGradeAtMost … primeWoldBoundaryVolumeBelow` | `ReesGradeFiltration*` |
| 4 | `Continuous KRealStructure.sigma` | `KRealStructureRealization` |
| 4 | `HasDerivAt (suzukiPhaseTransport …)` | `SuzukiPhaseTransportDerivative` |
| 3 | `suzukiFiniteShiftSource … ≠ 0` | `SuzukiFiniteShiftGeneratorLimit` |

The count barely moved because the new modules also *introduce* legitimate premise keys of their
own — three of my own theorems take `TendstoLocallyUniformly (primeIsingTreePartition …) f` as a
hypothesis with a general limit `f`, which is why that row went 2 → 5 even as the `XiC` and
`unitCentralXiC` instances of it were refuted.

**Three rows the re-measurement showed were only half closed**, now finished
(`RHTower/GlobalChoiceAndBondConfigurationWitness.lean`,
`RHTower/GaussPairedSchattenResidueProducer.lean`; built, registered, axioms clean — the
global-choice one needs only `propext`):

* `∃ b, D.defect = twoCoboundary b` — the weld witness exhibited a defect with *nonzero*
  obstruction, which is the opposite of global choice.  The global-choice defect realizes the
  hypothesis by `rfl` (`SectionDefect.globalChoiceDefect_exists_twoCoboundary`);
* `HasSchattenLogResidue … (gaussPairedChannelResidue …)` — the general producer concludes at an
  arbitrary residue value and so never mentions the Gauss constant, which the instrument keys on.
  The two specializations `hasSchattenLogResidue_gaussPairedChannelResidue` and
  `…_gaussPairedCriticalDepth` record it at the value the capstones consume;
* `B ∈ treeBondConfigurations T` — never vacuous: the FK coefficients of a tree's bond
  configurations sum to one, so the list is nonempty (`exists_mem_treeBondConfigurations`).

**Instrument lesson, recorded.**  A general producer whose conclusion does not *mention* the
consumer's corpus constants is invisible to a superset-keyed scan.  This is the mirror image of the
recorded "specialized producer" false positive, and the fix is the same one line: state the
specialization the consumers actually use.

### The Gamma-puncture ball condition is a half-plane

The capacity and tangent laws of the puncture atlas are stated for base points whose Laurent
coordinate lies in the quarter ball, four times, with no producer.  The coordinate *is* `exp z`, so
the condition is not implicit at all.  `HTGeometry/GammaPunctureCoordinateBallRegion.lean` (built,
registered, axioms clean):

* `norm_gammaPunctureCoordinate` — the modulus of the Laurent coordinate is `exp (Re z)`;
* **`gammaPunctureCoordinate_mem_closedBall_iff`** — membership in the closed ball of radius `r > 0`
  is exactly the half-plane `Re z ≤ log r`;
* `gammaPunctureCoordinate_mem_closedBall_quarter` — the producer the atlas laws consume;
* `exists_gammaPunctureCoordinate_mem_closedBall` — the region is nonempty for every positive
  radius, witnessed by `z = log r` with no numerical estimate needed;
* `gammaPunctureCoordinate_mem_closedBall_deck` — and it is invariant under the deck translation
  `z ↦ z + 2πi`, which is the invariance the atlas laws record for the sheets themselves.

### When the Suzuki ground leakage vanishes

The ground-edge universality law is driven by `leakage → 0`, produced nowhere.  The leakage is
`τ · oddBudget / (gap · groundMass)`.  `RHTower/SuzukiGroundLeakageVanishing.lean` (built,
registered, axioms clean):

* `suzukiGroundLeakage_of_oddBudget_eq_zero` and
  `tendsto_suzukiGroundLeakage_zero_of_eventually_oddBudget_eq_zero` — no odd budget, no leakage;
  the hypothesis is realized outright;
* **`tendsto_suzukiGroundLeakage_zero_of_tendsto_oddBudget`** — the usable criterion: a shrinking
  odd budget, a clock bounded in modulus and a gap-mass product bounded away from zero force the
  leakage to zero.  The proof is a squeeze against `(C/c) · |oddBudget|`.

So the ground-edge law applies to every nondegenerate ground pole whose odd budget shrinks, and the
no-go corollary (`…_nonCayley_forces_leakage_not_tendsto_zero`) now has a nonempty class to
contradict.

### The adelic structural premises: Haar, measurability, compactness

Three standing premises of the adelic layer — an additive Haar measure on the finite-stage adeles,
measurability of the test set in the `L²` density theorems, compactness of the set carrying a
common integer denominator — were consumed and produced nowhere.  None is an analytic input.
`RHTower/AdeleHaarMeasurableWitness.lean` (built, registered, axioms clean):

* **`exists_isAddHaarMeasure_fieldOneFiniteStageAdele`** — the finite-stage adeles
  `ℝ × ∏_{v ∈ S} ℚ_v` are a *finite* product of locally compact abelian groups, so the canonical
  `Measure.addHaar` is one, and every instance resolves.  The corpus already supplied the missing
  piece: `fieldOneAdicCompletionLocallyCompactSpace`;
* `measurableSet_of_isOpen_fieldOneFiniteAdele` and
  **`exists_compactOpen_measurableSet_subset`** — the finite adeles have a basis of compact open
  sets (`fieldOneFiniteAdele_compactOpen_basis`, already in the corpus), and open sets are Borel,
  so measurable test sets refine *every* neighbourhood.  The measurability hypothesis is satisfied
  on a basis of the topology, not merely on some set;
* `exists_isCompact_nonempty_ccmRationalFiniteAdele`, `isCompact_of_finite_ccmRationalFiniteAdele` —
  the compactness hypothesis holds on every finite configuration, so the common-denominator
  theorems are not vacuous.  (Recorded honestly: these two are cheap, and the substantive question
  of whether the *integral* adeles are compact is not settled here.)

**Correction to the entry above, same session.**  The gap I flagged — whether the compactness
premise has a witness beyond finite sets — is closed, and the corpus already held the answer.
`FieldOneFiniteAdeleIntegralBruhatTest` proves
`fieldOneFiniteAdeleIntegralAddSubgroup_isCompact`: the integral adeles are compact, by Tychonoff
through `RestrictedProduct.range_structureMap` and the local `ℤ_p` compactness supplied by
`Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv`.

The reason it was not visible from the `CCMRational…` side is a **naming duplication**:
`CCMRationalFiniteAdele` (in `CCMRationalFiniteBruhatReal`) and `FieldOneFiniteAdele` (in
`FieldOneFiniteAdeleWeylCharacter`) are two `abbrev`s for the *same* type,
`IsDedekindDomain.FiniteAdeleRing ℤ ℚ`, developed in two module families that never cite each
other.  So `isCompact_integralAdeles_ccmRationalFiniteAdele` is a one-line transport, and
`exists_commonIntegerDenominator_integralAdeles` applies the common-denominator theorem to an open
compact subgroup rather than to a finite configuration.

Recorded as a lead: the two adele module families should be checked for further duplicated
development — the compact-open basis, local compactness, sigma-compactness and the Haar layer all
exist on the `FieldOne…` side and may be silently re-proved on the `CCMRational…` side.

## A new instrument: duplicate statements across modules

Following the `CCMRationalFiniteAdele` / `FieldOneFiniteAdele` finding, a third instrument was
written: group every project proposition by the *structural form of its type* (de Bruijn indices
make the comparison alpha-invariant), keep the groups spanning more than one module.  Script:
`scratchpad/AuditDuplicateStatements.lean`.

**29 629 project propositions scanned; 46 cross-module duplicate groups.**

The head of the list is not duplicated mathematics but **`local instance` boilerplate**: 38 modules
separately declare `local instance : IsDomain upperEndAnalyticSubring`, 7 declare
`CharZero upperEndMeroField` (which `UpperEndDifferentialInstances` already exports as a `scoped`
instance), 7 declare the same complex/prime scalar tower.  These are re-declarations of a missing —
or unimported — global instance, not repeated proofs.

Below that the groups are genuine duplicate theorems, mostly pairs, e.g.

* `isOpen_upperTail` (`UpperEndDigammaShift`) vs `upperTail_isOpen` (`UpperEndFilter`)
* `upperTail_infinite` vs `infinite_upperTail`
* `finrank_graphCoboundary_range` (`GraphCoboundaryRank`) vs `finrank_range_graphCoboundary`
  (`CoherenceGraphCapacity`)
* `differentiallyAlgebraic_exp` (`Hypertranscendence`) vs `differentiallyAlgebraic_complex_exp`
  (`DerivInvariantObservableWitnesses`)
* `hypertranscendental_gamma` (`GammaHypertranscendental`) vs
  `gamma_pointedSource_member_hypertranscendental` (`GammaPointedSourceNonEffectivity`)
* `taylorPS_polynomial_eval` vs `taylorPS_polynomial_eval_hardy`

**Not acted on here, deliberately.**  Removing a duplicate means editing modules other lanes are
writing, and the instance boilerplate spans 38 files.  The finding is recorded as a lead with the
instrument in place, so the dedup can be done as its own pass when the tree is quiet.  The
direction rule of `dedup-move-direction` applies: check each pair's helpers before deciding which
side survives.

## `HTGeometry` mathlib-premise scan, head enumerated

The earlier `HTGeometry` mathlib-premise run reported "488 unproduced, no genuine open row above 11
uses" but never listed the tier below that.  Re-run with the session's modules in place:
**104 159 constants, 1 364 premise keys, 482 unproduced**.  The head, now enumerated:

| uses | premise | reading |
|---:|---|---|
| 19 | `z ∈ positiveHalfPlane` | parameter constraint |
| 16 | `0 < jetMonomialDegree n anchor` | parameter constraint |
| 15+15+8 | `Ideal.IsPrime` on the projective chart rings | parameter constraint; `⊥` is prime in a domain |
| 12 | `IsWeightedHomogeneous gammaPoleSourceDerivativeWeight` | produced by mathlib |
| 11 | `Function.Injective (…NevanlinnaCarrierFamily.quotient)` | the known open Nevanlinna bundle |
| 8 | `numOrder = denOrder` on a Gamma rational datum | parameter constraint |
| **8** | **`DifferentiableOn ℂ f (openVerticalStrip σ η)`** | **genuine — discharged below** |
| 7 | `x ∈ upperTail` | parameter constraint |
| 5 | `∃ packet, ObserverSpanningPacket L sites packet` | the existence side of the Steiner layer |

### Holomorphy on a vertical strip, produced

`HTGeometry/VerticalStripHolomorphyWitness.lean` (built, registered, axioms clean):

* `differentiableOn_openVerticalStrip_of_differentiable` — every entire function qualifies, which
  is the producer the strip-collapse and valuation-boundary theorems needed;
* **`differentiableOn_openVerticalStrip_iff`** — the strip is open, so the hypothesis is *pointwise*
  differentiability on it, which is how it is checked in practice;
* `…_const`, `…_exp` — concrete instances;
* **`differentiableOn_openVerticalStrip_inv_sub`** and
  `exists_differentiableOn_openVerticalStrip_with_pole` — and the hypothesis is **strictly weaker
  than entirety**: a simple pole at the boundary abscissa `σ + η` sits off the open strip, so
  `z ↦ (z − c)⁻¹` is holomorphic on it.  That is the point of stating the theorems on a strip
  rather than on `ℂ`, and it is now recorded rather than implied.

### The spanning-packet existence premise, produced

The sharp form of the observer Steiner law is conditional on `∃ packet, ObserverSpanningPacket L
sites packet`, and that existence had no producer — including in the module I added earlier this
session, which is why the row appeared at 5 uses in the re-measurement.
`HTGeometry/ObserverSpanningPacketExistence.lean` (built, registered, axioms clean):

* **`not_spatiallyDisconnectedPacket_singleton`** — a one-interaction packet is *never* spatially
  disconnected, because a singleton is not the disjoint union of two nonempty sets.  No hypothesis
  on the family is needed;
* **`observerSpanningPacket_singleton`** — so a single interaction touching every queried site is
  already a spanning packet, and `exists_observerSpanningPacket_of_subset_support` discharges the
  existence hypothesis;
* `observerSteinerNumber_le_one_of_subset_support` — the Steiner number is then at most one, i.e.
  the observer contrast can appear already at first order;
* `exists_subset_support_of_observerSpanningPacket_card_le_one` — and conversely a spanning packet
  of at most one interaction *is* such a singleton, so the bound is sharp: Steiner number `≤ 1`
  exactly when one interaction covers the queried sites.

### The Gamma-rational balance premise is one integer invariant

The valuation-boundary theorems compare two Gamma-rational data through the four-term relation
`n₁ + d₂ = n₂ + d₁`, or its shifted form with an offset — eight consumer sites, no producer.
`HTGeometry/GammaRationalOrderDefect.lean` (built, registered, axioms clean):

* `GammaRationalDatum.orderDefect` — each datum carries a single integer,
  `numOrder − denOrder`, and `orderDefect_one = 0`;
* **`balanced_iff_orderDefect_eq`** — the four-term relation says *exactly* that the two defects
  agree, and **`shifted_iff_orderDefect_sub_eq`** — the shifted form says their difference is the
  offset.  Both are one `omega` call once the invariant is named;
* `ofOrders` and **`exists_orderDefect_eq`** — every integer occurs as a defect, so the premise is a
  genuine one-parameter condition rather than a coincidence;
* `balanced_of_orderDefect_eq`, `balanced_self`, `exists_balanced_pair_orderDefect_eq`,
  `exists_shifted_pair` — the producers: pairs realizing the balance at every defect, and the
  shifted premise at every offset.

The premise was never about four numbers; it is equality of one invariant of each datum, and naming
that invariant discharges it.

### The lower-jet Jacobian nondegeneracy, attained

The terminal-linear orbit law is conditional on `(derivationLowerJetJacobian δ n partials A).det ≠ 0`
and nothing produced it, so the law quantified over a class never shown nonempty.
`HTGeometry/DerivationLowerJetJacobianWitness.lean` (built, registered, axioms clean):

* `natShiftDerivation` — the shift derivation on `MvPolynomial ℕ ℂ`, `X k ↦ X (k+1)`, built with
  `mkDerivation`.  Indexing by `ℕ` rather than `Fin` avoids all wrap-around arithmetic;
* `natShiftDerivation_iterate_X_zero` — its iterates applied to the first coordinate are exactly
  the coordinates, `δ^[k] (X 0) = X k`;
* **`derivationLowerJetJacobian_natShift`** — so with the coordinate partial derivatives the
  lower-jet Jacobian is the **identity matrix**, at every order;
* **`det_derivationLowerJetJacobian_natShift_ne_zero`** and
  `exists_det_derivationLowerJetJacobian_ne_zero` — the nondegeneracy hypothesis is therefore
  attained at every order, by the universal polynomial model.

## Full gate

`lake build GaloisForLFunctions.MainTheorems` — **green**, no errors across all six theorem areas
with this session's modules in place.  The only warnings are two `<;>` style notes in another
lane's `BlaschkeLocalizedClockAsymptotic`.

### Two more region premises, produced

`HTGeometry/PointedSupportDisjointness.lean` (built, registered, axioms clean; one theorem needs
only `propext` and `Quot.sound`):

The superselection theorems compare configurations through disjointness of their pointed supports,
five times.  The corpus discharged it once *inside* a proof with a bare `simp`, hiding the general
fact.

* `mem_pointedSupport` — membership is `x i ≠ 1`;
* **`disjoint_pointedSupport_iff`** — disjointness is pointwise: two configurations have disjoint
  pointed supports exactly when at every site at least one of them is unpointed;
* `pointedSupport_one`, **`disjoint_pointedSupport_one`** — the unit configuration has *empty*
  pointed support, so it is disjoint from everything, which is exactly what the hidden `simp` was
  proving.

`HTGeometry/ReciprocalGammaBlowUpDiskRegion.lean` (built, registered, axioms clean):

* **`mem_reciprocalGammaBlowUpDisk_iff`** — the disk is the open ball of radius `1/4` about `−1`, so
  membership is the explicit bound `‖x + 1‖ < 1/4`;
* `neg_one_mem_reciprocalGammaBlowUpDisk`, `reciprocalGammaBlowUpDisk_nonempty`,
  `reciprocalGammaBlowUpDisk_mem_nhds` — the centre is in it, it is nonempty, and it is a
  neighbourhood of the centre, so the local hypertranscendence hypotheses are not vacuous.

### The two largest `HTGeometry` rows, produced

`z ∈ positiveHalfPlane` (19 uses) and `0 < jetMonomialDegree n m` (16 uses) head the area's
nomination list.  Both were classified as parameter constraints on this card and left there; both
now have named producers.

`HTGeometry/PositiveHalfPlaneRegion.lean` (built, registered, axioms clean):

* `mem_positiveHalfPlane` — membership is `0 < Re s`;
* `isOpen_positiveHalfPlane`, **`convex_positiveHalfPlane`**, `isPreconnected_positiveHalfPlane` —
  the region is open, convex and preconnected, which is exactly what the identity-theorem arguments
  over it need (`identity-theorem-on-convex-halfplane`);
* `ofReal_mem_positiveHalfPlane`, `one_mem_positiveHalfPlane`, `positiveHalfPlane_nonempty`,
  `add_mem_positiveHalfPlane` — every positive real is in it, it is nonempty, and it is stable
  under adding a nonnegative real part.

`HTGeometry/JetMonomialDegreePositive.lean` (built, registered, axioms clean):

* **`jetMonomialDegree_pos_iff`** — positive jet degree says exactly that some *derivative*
  variable occurs in the monomial.  The card had guessed this reading; it is now proved;
* `jetMonomialDegree_single`, `jetMonomialDegree_pos_single`, `exists_jetMonomialDegree_pos` — the
  monomial in a single derivative variable has jet degree one, so the premise is attained at every
  order.

### The projective-chart prime-ideal premise, produced

The chart incidence and base-change theorems carry `[p.IsPrime]` on the chart coefficient ring —
38 uses across three keys, the largest class in the area after the half-plane — recorded on this
card as "parameter constraint; `⊥` is prime in a domain" and left there.  A premise in *instance*
position still needs a lemma to cite at the use site.
`HTGeometry/ProjectiveChartPrimeIdealWitness.lean` (built, registered, axioms clean):

* `bot_isPrime_projectiveChart` — the chart ring is a polynomial ring over a field, hence a domain,
  so the zero ideal is prime: the generic point;
* **`isPrime_ker_eval_projectiveChart`** — and every *point* of the affine chart gives one, as the
  kernel of its evaluation map, the values living in a field.  So the layer runs on point ideals,
  not only on the generic one;
* `exists_isPrime_projectiveChart`, `exists_isPrime_ker_eval_projectiveChart` — the existence forms.

Toolchain note: `Ideal.bot_prime` is deprecated in favour of `Ideal.isPrime_bot`, and `push_neg` in
favour of `push Not`; both emit warnings, which the lint gate treats as failures.

### The last two membership rows, and a sixth false-positive class

`HTGeometry/SelectedLayerWitnessSiteNonempty.lean` (built, registered, axioms clean):

* **`SelectedLayerAnalyticRelationWitness.site_nonempty`** and `…exists_mem_site` — the analytic
  site of a selected-layer witness is nonempty, because the witness structure carries `S.Infinite`
  as a field.  The producer was inside the interface all along and had never been extracted;
* `exists_mem_polynomialPatternMinimalCluster` — the minimal pattern cluster has a member, which is
  the recorded `polynomialPatternMinimalCluster_nonempty` restated existentially.

**Sixth false-positive class, now on record.**  A producer whose conclusion is a *container* of the
existential — `Finset.Nonempty s`, `Set.Nonempty s`, `s.Infinite` — is invisible to the scan, whose
`conclAtoms` unfolds `Exists` but not the containers that mean it.  The two rows above were both of
this kind: the mathematics existed, only the shape the instrument looks for did not.  With the
"different head" class (`0 < X` versus `X ≠ 0`) and the "general producer that never mentions the
consumer's constants" class, the instrument now has three distinct ways of hiding a producer that
is really there — all three fixed the same way, by stating the form the consumer actually needs.
