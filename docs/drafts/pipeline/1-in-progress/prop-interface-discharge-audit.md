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
