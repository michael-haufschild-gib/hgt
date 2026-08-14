# Universal-law-field Lean certification boundary

Project rule: **paper proof does not count as proved until its exact significant theorem is closed in
Lean**.  Files remaining in this Stage-2 folder are therefore research claims awaiting certification,
even when their paper argument is dependency-closed.

Dedicated Lean umbrella:
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Session 2026-08-11 addition (formation-scale receivers)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-FSR-1-CORE | One-norm derivation impossibility; formal-receiver collapse; analytic-collar ghost transport; exact Adams/ghost/evaluation exchange | `HTGeometry.FormationScaleReceiver` |

The source card remains Stage 2 because its full Wiener character-space classification and
infinite exterior/formation inverse have not yet been formalized.  The declarations above are
wired into `HTGeometry.UniversalLawField` and recorded separately in Stage 3.

## Session 2026-08-10 addition (native sequential repair heredity)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ECMPL-TOPO-1 | Actual Arens topology, exact two-generation native sequential repair, hereditary second witness, and stationary ordinary closure | `HTGeometry.ConstitutiveSequentialRepairHeredity` |

Direct elaboration and the foreground `HTGeometry.UniversalLawField` build pass; the latter
completed 11,585 jobs. The capstone axiom print reports only `propext`, `Classical.choice`, and
`Quot.sound`. No forbidden declaration occurs in the module.

## Session 2026-08-10 addition (endogenous completion mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ECMPL-1 | Terminating execution, nonconfluent finite completion, stationary semantic equivalence, strict conservative repair, and inherited next-stage failure | `HTGeometry.ConstitutiveCriticalCompletionMechanics` |

Direct elaboration and the foreground `HTGeometry.UniversalLawField` build pass; the latter completed
11,584 jobs.  Axiom prints for the capstone and its semantic, confluence, and well-foundedness
components report only `propext`, `Classical.choice`, and `Quot.sound`.  No forbidden declaration
occurs in the module.  Repository lint found no target reachability or proof-debt error; its nonzero
exit was caused by four unrelated currently unwired modules in the separate `RHTower` umbrella.

## Session 2026-08-10 addition (Law-History Spectral Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-LHSM-1 | Finite future-tail survival filtration, exact refactorization, and canonical split-cancellation transgression | `HTGeometry.ConstitutiveLawHistorySpectralMechanics` |

Direct foreground elaboration and the leaf build pass; the latter completed 8,700 jobs. The module
is wired into `HTGeometry.UniversalLawField`, whose final foreground build completed 11,581 jobs.
The theorem index contains its declarations. Axiom prints for all four capstones and
`splitTransgressionEquiv` report only `propext`, `Classical.choice`, and `Quot.sound`.

Repository-wide lint passed before concurrent theorem-area changes. A later concurrent audit was
blocked only by unrelated newly owned modules not yet reachable from their own umbrellas; no LHSM
reachability, forbidden-declaration, elaboration, or axiom error was reported.

## Session 2026-08-10 addition (observer-overlap mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-FKT-OD-1 | Nonnegative lax-meet overlap defect, exact serial composition, total-variation loss budget, injectivity classification, and false-overlap witness | `HTGeometry.ConstitutivePositiveOverlapDefect` |

Direct elaboration, formal lint, and axiom audit pass. Significant declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Final foreground
`lake build GaloisForLFunctions.HTGeometry.UniversalLawField` completed 11,482 jobs.

## Certified and promoted to Stage 3

| ID | Theorem | Lean module |
|---|---|---|
| ULF-PIR-1 | Positive doctrine, additive nondescendence, faithful response coframe, recurrence/open lift | `HTGeometry.ConstitutivePositiveResponse` |
| ULF-CFL-1 | Complete passive equivalence versus injective marked intervention | `HTGeometry.ConstitutiveInterventionSeparation` |
| ULF-SLOT-1 | Independent-slot transitivity; invariant phases trivial; invariants constant | `HTGeometry.ConstitutiveIndependentSlotNoGo` |
| ULF-RADIUS-2 | Serial-radius counterexample and hidden-pair/diameter survivor | `HTGeometry.ConstitutiveReconstructionNoGo` |
| ULF-AEEC-1 | Adaptive mimicry, coherent non-effective boundary, finite effectivity-classifier no-go | `HTGeometry.ConstitutiveAdaptiveProcompletion` |
| ULF-AMCC-1 | Minimal adaptive transcript support, universal additive-cost minimizer, exhaustive coercivity | `HTGeometry.ConstitutiveAdaptiveCost` |
| ULF-GCP-1 | Exact response-kernel persistence, Gamma Bockstein death set, critical survival, and lifetime | `HTGeometry.ConstitutiveGammaResponseLifetime` |
| ULF-RBD-PREFIX-1 | Prefix observer stabilization, non-effective horizon, recurrent phase, positive erasure, singleton production, open action | `HTGeometry.ConstitutiveEffectivityHorizon` |
| ULF-RBD-JET-1 | Exact DA/HT finite-jet double realization, mutual density, empty interiors, nonclosed strata, continuous-classifier no-go | `HTGeometry.ConstitutiveFiniteJetBoundary` |
| ULF-REG-KONIG-1 | Locally finite realization tower has a global section; finite-local/global gap requires noncoherence, nonproperness, or extra admission | `HTGeometry.ConstitutiveRealizationKonig` |
| ULF-REG-SEID-1 | Surjective erasure forces infinite dimension; fixed-corona Gamma-Bockstein death has no faithful finite-dimensional linear model | `HTGeometry.ConstitutiveSurjectiveErasure` |
| ULF-HISTORY-1 | Nonnegative additive groupoid costs vanish; complex real-cost part vanishes; directed histories admit nonzero additive cost | `HTGeometry.ConstitutiveHistoryPolarization` |
| ULF-PRD-PUMP-1 | Observer unitization forces recurrence, injective open history, linear action, and cost nondescendence | `HTGeometry.ConstitutiveObserverUnitization` |
| ULF-DEFECT-2 | Same endpoint defects and size admit split/nonsplit events distinguished by carry and lifted-period holonomy | `HTGeometry.ConstitutiveExtensionCarry` |
| ULF-NFD-2 | One periodic producer and quotient force recurrent observation, nonclosed lift, carry, decoder failure, and unbounded prefix history | `HTGeometry.NomogenicFixedPointCalibration` |
| ULF-NPG-PIN-1 | Natural free-monoid interventions are uniform powers; ramification comparisons are inverse-depth; power naturality does not select radial origin | `HTGeometry.ConstitutiveNaturalPowerNormalization` |
| ULF-CTX-1 | Exact parity contextuality criterion, one-dimensional total-charge obstruction, proper-face blindness, and compatible uniform positive state without a global law | `HTGeometry.ConstitutiveParityContextuality` |
| ULF-IRR-1 | Minimal irreducible `N`-ary law with all composites zero, abelian proper colour faces, non-homotopy-abelian total law, interaction order `N`, and non-locally-compact unbounded spectrum | `HTGeometry.ConstitutiveIrreducibleInteraction` |
| ULF-TORS-1 | Acyclic based two-term complexes, determinant history as a complete based invariant, multiplicativity, positive shadow as the exact phase quotient, and closed observation with open logarithmic lift | `HTGeometry.ConstitutiveDeterminantTorsion` |
| ULF-FILL-1 | Van Kampen area of `aⁿbⁿa⁻ⁿb⁻ⁿ` is exactly `n²` with trivial endpoint, length `4n`, and orientation-blind cost | `HTGeometry.ConstitutiveQuadraticFilling` |
| ULF-DOCT-1 | Nondistributive doctrine lattice, exact lcm-periodic finite congruence observers with infinite fibres, cofinal separation, and the phase doctrine as a positive quotient | `HTGeometry.ConstitutiveDoctrineLattice` |
| ULF-ENDP-1 | Derived, endpoint, and unweighted observers are constant while determinant history, van Kampen area, and cellular area are not | `HTGeometry.ConstitutiveEndpointInsufficiency` |
| ULF-BULK-1 | Scalar-indistinguishable `C₃` boundary conditions separated by the bulk character, with exactly three-periodic fusion and open marked lift | `HTGeometry.ConstitutiveBulkBoundaryFusion` |
| ULF-MATCH-1 | Proper-face matching map, realization fibres, four exhaustive and exclusive phases invariant under diagram equivalence, kernel/cokernel chart, native interaction and contextual instances | `HTGeometry.ConstitutivePolyscopicMatching` |
| ULF-DGLU-1 | Determinant-sign gluing is the parity incidence equation: effectivity iff even charge iff trivial anomaly, cycle-memory count `2^(|E|-|V|+1)`, and positive erasure | `HTGeometry.ConstitutiveDeterminantGluing` |
| ULF-FLUX-1 | Abelian determinant-flux exact sequence, realizability iff trivial total charge, realization torsor, proper-face invisibility, positive coefficient quotient (cycle-basis isomorphism not constructed) | `HTGeometry.ConstitutiveAbelianDeterminantFlux` |
| ULF-MOORE-1 | Moore law cell parity dichotomy: odd degree bijective, even degree kernel and cokernel both two-element, positive coefficients repair effectivity and erase memory | `HTGeometry.ConstitutiveMooreLawCell` |
| ULF-INV-1 | Strict inversion/Cartier square has zero defect (`ε ∘ σ = ε`), the conormal class is odd, the positive displacement is the squared generator, and every radial gain is already a positive square | `HTGeometry.ConstitutiveStrictInversionCartier` |
| ULF-MPE-1 | Metric-phase exactness: Gram phase quotient, singular values and filling energy, open determinant winding, and the cofinal Hilbert wall with dense nonclosed proper range | `HTGeometry.ConstitutiveMetricPhaseExactness` |
| ULF-LSW-1 | A₂ stability wall: three subrepresentations, phase-order criterion, strict semistability on the wall, and a modulus packet identical on opposite chambers | `HTGeometry.ConstitutiveStabilityWall` |
| ULF-IPE-1 | Isotropic Gaussian law: rotations invisible passively, seen modulo `π` by a marked intervention port, `π`-recurrent projective history with unbounded lift, and orientation erased by positive data | `HTGeometry.ConstitutiveIsotropicInterventionPort` |
| ULF-OPM-2 | Failed unary exchange generates the least preserved congruence; induced quotient laws commute; every commuting observer factors uniquely through it; no smaller strict repair exists | `HTGeometry.ConstitutiveExchangeStrictification` |
| ULF-OPM-3 | One exchange residual admits strict quotient and nonsplit central promotion; cocycle coherence, exact commutator carry, fixed lift residual, and no-section theorem | `HTGeometry.ConstitutiveExchangeCentralPromotion` |
| ULF-OPM-4 | Reporter descends exactly when constant on generated exchange congruence; critical-pair detection forbids commuting strictification with reporter preservation; Heisenberg history reporter selects central promotion | `HTGeometry.ConstitutiveExchangePromotionSelection` |
| ULF-OPM-5 | Future reporter orbit induces greatest conserved law congruence; strict promotion exists exactly when minimal exchange repair lies inside it; delayed detection defeats present-only selection | `HTGeometry.ConstitutiveFutureReporterPromotion` |
| ULF-OPM-6 | Promotion differential selects associative central closure versus coherent ternary birth; every associator obeys pentagon coherence; unary gauge changes leave it invariant | `HTGeometry.ConstitutivePromotionDifferential` |
| ULF-OPM-7 | Exactness trichotomy relative to admission; constant residual is algebraically exact and finitely repairable at every horizon but has no upper-bounded global primitive | `HTGeometry.ConstitutiveAdmissionRelativePromotion` |
| ULF-OPM-8 | Paired reporters intersect future envelopes; strict-promotion admissibility composes by conjunction; refinement is monotone and one conserved detector vetoes strictification | `HTGeometry.ConstitutiveReporterMeetPromotion` |
| ULF-OPM-9 | Promotion differentiation commutes with additive observation; observed closure iff source associator lies in observer kernel; mod-two observation creates exact false closure | `HTGeometry.ConstitutivePromotionObservationExchange` |

Formalized cards and declaration-level records live in
`docs/drafts/pipeline/3-formalized/universal-law-field/`.

## Partially certified, not promoted

`ULF-MPTB-1` has a certified coordinate-free core in
`HTGeometry.ConstitutiveProcessTomography`: exact annihilator blind sector, reconstruction iff
spanning, nonzero blind-direction existence, affine record equality, and qualitative open-interior
robustness. Product-slot dimension formula and quantitative PSD spectral bound remain uncertified,
so card stays in Stage 2.

`ULF-EQG-1` has a certified local and finite core:

- `HTGeometry.QPochhammer`: q-Pochhammer convergence, shift, nonvanishing; normalized q-Gamma
  translation; positive local weights; mass one; every nonnegative-integral moment;
- `HTGeometry.EulerQGammaFiniteProcess`: finite response/divisor telescopes and genus-one exchange.

Its global prime probability, zeta ladder, meromorphic divisor, hypertranscendence, and recurrence
claims remain uncertified.  The card therefore stays in Stage 2.

## Rejected by formal attack

`ULF-DISTORTION-1` claimed monotonicity of internal-centre reconstruction radius under serial
postprocessing.  A Lean-certified three-point counterexample shows strict decrease from two to one.
The rejected card is in `docs/drafts/pipeline/5-failed/universal-law-field/`; ULF-RADIUS-2 records
the exact survivor.

## Session 2026-08-09 additions (inverse-theory layer)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-INV-N8-J | Source involution `f ↦ conj(f(-x))` is involutive and realizes the sharp operation on `e^{-izx}` transforms, hypothesis-free (junk-value exact); eigen-transform compatibility | `RHTower.XiWeilSourceInvolution` |

Axiom print: `[propext, Classical.choice, Quot.sound]` on all three declarations; module wired
into the `RHTower` umbrella; `lake build +GaloisForLFunctions.RHTower.XiWeilSourceInvolution`
green (8937 jobs). This certifies the involution-existence half of the N8 gate analysis
(ULF-INV-11 §4): the involution is free in Lean too; the open content is the positivity of its
pairing, exactly as re-typed.

| ULF-INV-D4A | Theta-cusp seed evenness; Gaussian half-moments 1/(4π), 3/(8π²) via the cold-moment recursion; **zero half-line mean of the seed** (the D4a cancellation) | `RHTower.ThetaCuspSeedZeroMean` |
| ULF-INV-7-CORE | Two-point pattern cap \|b\| ≤ a (Page's ρ(ℤ/2)=1, tight); circle witness 3+4cosθ+cos2θ ≥ 0 with ratio 4/3 > 1; width-cap inequality (the 1/𝔏 shape forced) | `HTGeometry.FiniteAmplifierPatternCap` |

`ThetaCuspSeedZeroMean`: build green (9051 jobs), axioms `[propext, Classical.choice,
Quot.sound]` on all printed declarations. `FiniteAmplifierPatternCap`: clean elaboration;
umbrella build and axiom print recorded in the session log on completion.

| ULF-INV-1-CORE | The compensation is forced (normalizer convergence derived from product convergence, A ≠ 0); **cross-system blindness in derived form** — same nonzero leading coefficient + one convergent regularization ⟹ identical limits | `HTGeometry.MultiplicativeRegularizationBlind` (extended) |

Build green (8655 jobs); axioms standard. This is the abstract engine of ULF-INV-1
(Beurling cross-system blindness); the arithmetic instantiation (Mertens-normal systems, the
generator-swap comparison pair) remains paper-level in the stage-2 card.

| ULF-INV-10-S1 | Stage 1 of the eigen-pair identification's prime half: real vonMangoldt summability at σ>1; line-kernel continuity and exact modulus n^{−σ}; per-term integrability and exact integral norms; **termwise LSeries line integration against any integrable weight** | `RHTower.VonMangoldtLineSeriesSwap` |

Build green (8826 jobs); axioms standard. Stages 2–5 (boundary vanishing, residue collapse,
double pole, assembly) remain per the staged plan in the promoted card.

| ULF-INV-10-S2A | Stage 2, Lemma A: exponential substrip decay of `deriv XiC` by Cauchy transfer from the XiC strip bound (strip-shrink, slack absorbed into the constant) | `RHTower.XiCDerivStripDecay` |

Build green (8941 jobs); axioms standard. Remaining prime-half stages: 2B (vertical-segment
vanishing for the single-pole integrand), 3 (one-pole residue), 4 (matched/double case),
5 (assembly).

| ULF-INV-10-S2B | Stage 2B: vertical-edge vanishing under exponential horizontal domination, both sides (the widening-rectangle boundary engine) | `HTGeometry.VerticalEdgeVanishing` |

Build green (2580 jobs); axioms standard. With the corpus-owned rectangle Cauchy formula
(stage 3) and today's XiC' bound (2A), the prime-half chain's remaining new work is stage 5
(assembly) plus at most a stage-4 bridge.

| ULF-INV-10-S5A1 | The convention bridge: the Hedenmalm eigen transform equals the mathlib Fourier integral of the imaginary-part-tilted flow at frequency `z.re/(2π)` — the linchpin linking the corpus's `e^{-izx}` normalization to mathlib's convolution/inversion machinery | `RHTower.HedenmalmLineTransformBridge` |

Build green (8937 jobs); axioms standard. Remaining in the chain: 5a-2 (line-product
integrability from the 18a bounds — assembly-level), 5a-3 (inversion application), 5b (final
assembly), stage-4 bridge if the two-pole variant needs adaptation.

| ULF-INV-10-S5A2 | Eigen-pair line integrability: the product of a removable quotient with the conjugate-reflected partner quotient is integrable on every substrip line, dominated by the (18a) bounds at doubled rate | `RHTower.EigenPairLineIntegrable` |

Build green (8946 jobs); axioms standard. Chain: 1, 2A, 2B, 5a-1, 5a-2 certified; 3 owned;
4 likely owned; remaining new work: 5a-3 (inversion application) and 5b (assembly).

| ULF-INV-10-S5A3 | The eigen-pair line product IS one Fourier transform of a convolution: `T_α(t−iY)·conj(T_β(t+iY)) = 𝓕(tilted-α ⋆ conj-reflected-tilted-β)(t/2π)`; with the hypothesis-free conjugation–reflection law for 𝓕 and real-tilt integrability | `RHTower.EigenPairLineConvolution` |

Build green (8959 jobs); axioms standard. The prime-half chain's remaining new work is now
5a-3b (Fourier inversion of the convolution at ±log n) and 5b (rectangle assembly).

| ULF-INV-10-S5A3B | Scaled Fourier inversion: `∫ e^{−itξ₀}·𝓕h(t/2π) dt = 2π·h(−ξ₀)` for continuous h with h, 𝓕h ∈ L¹ — converts every frequency integral of the termwise swap into a time-side sample | `HTGeometry.FourierScaledInversion` |

Build green (2781 jobs); axioms standard. The ELEVEN-module chain (1, 2A, 2B, 5a-1, 5a-2,
5a-3a, 5a-3b certified new + N8-J, D4A, INV-7-CORE, INV-1-CORE) leaves ONE new module: 5b,
the rectangle assembly, every ingredient of which is now a certified or corpus-owned lemma.

| ULF-INV-10-S5B1 | Fixed-aperture rectangle identity for the single-pole eigen integrand: boundary integral of `deriv XiC · sharp F/(z−p)` = `2πi`·(numerator at p) — the antidiagonal Gram datum; plus sharp-of-entire is entire | `RHTower.EigenPairRectangleIdentity` |

Build green (8800 jobs, clean first elaboration); axioms standard. TWELVE session modules.
Remaining: 5b-2, the widening-limit assembly gluing S5B1's fixed-aperture identity to the
horizontal expansions (stage 1 + 5a chain) and the vertical vanishing (2A/2B) — the final module
of the identification's machine-checked closure.

| ULF-INV-10-S5B2-L3 | The concrete vertical-edge vanishing of the single-pole eigen integrand: `deriv XiC · sharp F_β/(z−p)` right-edge integrals tend to 0 (2A bound × 18a bound × inverse-linear factor, eventual-form engine variant included) | `RHTower.EigenPairVerticalBound` |

Build green (8948 jobs); axioms standard. THIRTEEN session modules. The assembly's L3 is done;
remaining: L1 (bottom-edge rewrite), L2 (truncated-to-full-line limits), L4 (evenness folding),
MAIN (the widening-limit gluing) — per the 5b-2 spec memory.

## Session 2026-08-09 additions (Reflexive Law Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-RLM-10 | Contextual decomposition of three-promotion reversal; Jacobi conservation; contextual arity certificate; initial pairwise-flat/triple-nonflat countermodel; no uniform finite exchange horizon | `HTGeometry.ConstitutiveContextualPromotionExchange` |
| ULF-RLM-11 | Compensator admission iff restricted-carrier closure iff quotient residual vanishes; unique restricted promotion; associative-but-nonadmitted parity countermodel | `HTGeometry.ConstitutiveCentralAdmissionExchange` |
| ULF-RLM-12 | Fixed exact rule--test polarity: serial revision is idempotent; synchronous revision satisfies `P^3=P`; open genesis requires endogenous compatibility change | `HTGeometry.ConstitutivePolarityRevision` |

Direct foreground elaboration and the final
`lake build GaloisForLFunctions.HTGeometry.UniversalLawField` pass (11,405 jobs).  Axiom audit on
all significant declarations and the closed capstone reports only `propext`, `Classical.choice`,
and `Quot.sound`.

`ULF-RLM-11` also passes direct foreground elaboration and is wired into the same umbrella.  Final
`lake build GaloisForLFunctions.HTGeometry.UniversalLawField` completed 11,408 jobs.  Its closed
capstone certifies that exact ambient associativity can coexist with nonzero admission obstruction
and nonclosure of the admitted carrier.  Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

`ULF-RLM-12` passes direct foreground elaboration and the same umbrella's 11,410-job build. Its
capstone certifies serial idempotence and synchronous `P^3=P` for every fixed compatibility
relation. The axiom audit reports only `propext` and `Quot.sound`.

## Session 2026-08-09 additions (Defect-Driven Exactification Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-DDE-2A | Mandatory pointwise maximum of two scalar-exact work laws is scalar-integrable iff parent potentials differ by a constant; every disagreement creates a positive two-cycle; pointwise minimum always remains integrable | `HTGeometry.ConstitutiveCompetitiveWorkHistory` |
| ULF-DDE-2B | On every finite path, mandatory/permissive composition is the endpoint work plus/minus relative total variation; on closed paths mandatory work is half-variation; observer descent holds exactly when collapsed two-cycle memory vanishes | `HTGeometry.ConstitutiveCompetitivePathVariation` |

Direct foreground elaboration and final Universal Law Field umbrella build pass. The final build
completed 11,417 jobs. Significant declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`; forbidden-token scan is clean.

`ULF-DDE-2B` passes direct foreground elaboration and is wired into the same umbrella. Its
capstone combines closed-path variation production with the exact attained-range observer-descent
criterion. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; forbidden-token
scan is clean. Final foreground
`lake build GaloisForLFunctions.HTGeometry.UniversalLawField` completed 11,420 jobs.

## Session 2026-08-09 additions (Endogenous Compatibility Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ECM-1 | Every state-indexed transition relation is exactly the universal one-test polar of an endogenous compatibility law; deterministic updates are the singleton case | `HTGeometry.ConstitutiveEndogenousCompatibility` |

Direct foreground elaboration, final Universal Law Field umbrella build, forbidden-token scan, and
axiom audit pass. The final umbrella build completed 11,412 jobs; significant declarations depend
only on `propext` and `Quot.sound`. The theorem is a mechanism-vacuity boundary: state dependence
alone imposes no dynamics.

## Session 2026-08-09 additions (Genesis Termination Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-GTM-1 | No infinite strict compatibility-enrichment history on finite vocabulary; every monotone history has an adjacent stable step | `HTGeometry.ConstitutiveFiniteRevisionTermination` |
| ULF-GTM-2 | Arbitrary joint saturation of monotone extensive finitary formations remains finitary and is the least containing closure; concrete cofinal-birth closure has no finite witness and cannot be such a saturation | `HTGeometry.ConstitutiveFinitaryFormation` |
| ULF-GTM-3 | Finite continuous formation families commute with compact Hausdorff completion at every bounded word depth; completion-born laws force unbounded formation depth, persist under bounded generator changes, and can only be erased by equivariant observers | `HTGeometry.ConstitutiveFormationCompletionExchange` |
| ULF-DDE-1 | Repair splittings form a simply transitive shear torsor; nonzero shears fix no selector; every selector is the unique minimizer of an explicit manufactured squared-norm cost | `HTGeometry.ConstitutiveRepairTorsorSelectorNoGo` |

This certifies the finite-monotone leg of the law-genesis trilemma. Direct elaboration and the final
11,413-job umbrella build pass. Significant declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`; the forbidden-token scan is clean.

`ULF-GTM-2` certifies the cofinal-exit barrier: arbitrarily many noncommuting finitary law-formers
cannot produce an irreducibly cofinal consequence through finite-history saturation. The concrete
closure adjoining `0` only to infinite sets supplies the sharp separated mechanism. Direct
foreground elaboration and forbidden-token lint pass. The final Universal Law Field umbrella build
completed 11,426 jobs. Significant declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

`ULF-GTM-3` certifies the completion-exchange successor.  On compact Hausdorff law spaces, finite
continuous formation families commute with completion at every bounded word depth.  The exact
limit boundary forces deeper-than-`d` effective realizations in every neighbourhood for every
finite `d`.  Mutually bounded generator dictionaries preserve the boundary, while equivariant
observer maps can erase but cannot create it.  An explicit one-point-compactification model proves
finite signature is load-bearing: infinitely many continuous constant generators violate exchange
already at depth one. Direct foreground elaboration and forbidden-token lint pass. Final Universal
Law Field umbrella build completed 11,430 jobs. Significant declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Session 2026-08-09 additions (Marked-Symmetry Experiment Quotient)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-MSQ-1 | Marking an intervention replaces the passive gauge group by its stabilizer; the homogeneous quotient embeds in the law space, one-parameter responses recur in every compact group, and the lifted history closes exactly when the response class is trivial | `HTGeometry.ConstitutiveMarkedSymmetryQuotient` |

Direct foreground elaboration and the final 11,418-job Universal Law Field umbrella build pass with
no warnings; the forbidden-token scan is clean and `#print axioms` on every capstone reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The recurrence clause is proved by a pigeonhole
over sample times against a finite subcover, which is strictly more elementary than the paper's
closure-of-semigroup argument.  The exact instantiation is certified concretely: `K` is proved to be
the stabilizer of a marking, `Circle ⧸ K ≃* Circle`, and the angle lift of the response loop is the
genuine mathlib path lift along `Circle.exp`, with endpoints escaping through distinct deck
translations by `2π`.

## Session 2026-08-09 additions (Equivariant Intervention-Response Blindness)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-EIR-1 | An invariant doctrine map and equivariant interventions have first responses that factor through the orbit space; separation forces one of four structural failures, and non-equivariance alone is provably insufficient | `HTGeometry.ConstitutiveEquivariantResponseBlindness` |

Stated on genuine manifolds with `mfderiv` and the manifold chain rule.  The exact radial-source
instantiation reuses `HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness` verbatim and
adds only the reporter-coframe reading.  Direct foreground elaboration and the final 11,423-job
Universal Law Field umbrella build pass with no warnings; `#print axioms` on every capstone reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-09 additions (Antisymmetric Wall Response)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-A2R-1 | The A₂ passive modulus packet is even in the wall parameter, while one intervention fixed beforehand has antisymmetric response `4 sin θ` whose sign is exactly the stable/semistable/unstable trichotomy | `HTGeometry.ConstitutiveAntisymmetricWallResponse` |

Reuses `ConstitutiveStabilityWall` and `ConstitutivePositiveResponse` verbatim; the new content is
the real-part computation of the charges, the derivative form of the component responses, and the
two missing legs of the stability trichotomy (unstable and strictly semistable).  Direct foreground
elaboration and the final 11,424-job Universal Law Field umbrella build pass with no warnings;
`#print axioms` on every capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Structured Mutational Genesis)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SEGM-1 | One fixed local mutation has a period-two visible rulebook and an unbounded positive semantic lineage; its transported certificate forces exact linearization, reconstructs the nonlinear exchange, and forbids every positive semantic period | `HTGeometry.ConstitutiveMutationalGenesis` |

The formal theorem occupies the strict middle between fixed-polarity collapse and arbitrary
state-indexed compatibility: future values are generated by one source-fixed exchange rather than
stored in a transition oracle. Direct foreground elaboration, formal lint, and the final `11,433`-job
Universal Law Field umbrella build pass. `#print axioms` on every capstone reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Equivariant Arity Genesis)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-EAG-1 | An unoriented failed pair with fixed background admits no equivariant deterministic binary reporter; every equivariant separator has three distinct values, ternary repair is sharp, convex binary repair has unique fixed mixture `1/2`, and orientation resolves the pair by breaking swap symmetry | `HTGeometry.ConstitutiveEquivariantArityGenesis` |

The theorem classifies three exact successor-doctrine repairs from one source orbit type: raise
deterministic arity, add orientation, or convexify into a mixed fixed point. Direct foreground
elaboration, axiom audit, formal lint, and the final `11,435`-job Universal Law Field umbrella build
pass. Reported build linter messages are pre-existing and outside the new module.

## Session 2026-08-09 additions (Metaplectic Action History)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ACTION-1 | The rotating quadratic action has `2π`-periodic critical locus, positive Hessian shadow and unoriented descent line, while its oriented parametrization and Gaussian amplitude `√(2π) e^{-iθ/2}` reverse after one loop and close only after two | `HTGeometry.ConstitutiveMetaplecticActionHistory` |

The amplitude is the genuine pullback line integral — `descentLine_hasDerivAt` certifies the
Jacobian and mathlib's `integral_gaussian` supplies `∫ e^{-y²/2} = √(2π)` — so equation (3) is
computed, not posited.  Direct foreground elaboration and the final 11,425-job Universal Law Field
umbrella build pass with no warnings; `#print axioms` on every capstone reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Session 2026-08-09 additions (Toeplitz Defect and Index)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-TOEPLITZ-1 | The `n`-fold unilateral shift on `ℓ²(ℕ₀)` is an isometry whose defect is the rank-`n` truncation projection obeying an orthogonal cocycle law; every root-of-unity boundary observer is periodic while the defect rank and the index `−n` diverge along its returns, and no invertible compact perturbation of `Sⁿ` exists | `HTGeometry.ConstitutiveToeplitzDefectIndex` |

New infrastructure: `ℓ²`-summability and norm identity for the coordinate reindexings, the adjoint
relation, the defect projection with an explicit `ℂⁿ` coordinate isomorphism, the cokernel
isomorphism `ToeplitzSpace ⧸ range Sⁿ ≅ ℂⁿ`, and a compact-perturbation rigidity argument built on
mathlib's Fredholm alternative.  Clause 7 is certified computationally (mathlib has no C*-algebra
K-theory); clause 8 is certified in the stronger invertible-perturbation form.  Direct foreground
elaboration and the final 11,427-job Universal Law Field umbrella build pass with no warnings;
`#print axioms` on every capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-09 additions (Balanced Defect, Zero Index)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-DEFECT-1 | `Tₙ = Sⁿ ⊕ S*ⁿ` has equal `n`-dimensional kernel and cokernel defects, hence index zero, unit symbol determinant and vanishing signed class, while its unsigned defect energy `2n` diverges along the exact returns of the root-of-unity boundary observer | `HTGeometry.ConstitutiveBalancedDefectZeroIndex` |

Reuses the certified single-shift calibration `ConstitutiveToeplitzDefectIndex` verbatim.  New
infrastructure: the doubled Hardy space `WithLp 2 (H × H)`, the block-diagonal operator `pairOp`
with `adjoint_pairOp`, the two defect-range isomorphisms, and the kernel/cokernel isomorphisms of
the doubled operator.  The §3 abstract cancellation theorem is stated for an arbitrary additive hom
`M →+ G` and needs only `propext`.  Direct foreground elaboration and the final 11,428-job Universal
Law Field umbrella build pass with no warnings; `#print axioms` on every capstone reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Consensus Faces and Collision History)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-FKT-HMCF-1-CORE | Two nested deterministic observers admit one finite nonnegative coupling simultaneously saturating both overlap capacities | `HTGeometry.ConstitutiveHierarchicalMaximalCoupling` |
| ULF-FKT-CCD-1-CORE | A telescoping collision profile has bounded total capacity and vanishing tail while its depth-weighted history diverges | `HTGeometry.ConstitutiveCofinalCollisionHistory` |

Certification is deliberately narrower than the paper cards.  The arbitrary finite-chain induction,
collision-stratum decomposition, incompatible-partition countermodel, and countable coupling
realization remain paper-only and do not count as Lean-certified results.  Both modules elaborate
directly with no warnings; formal lint passes; the final 11,514-job Universal Law Field umbrella
build passes; `#print axioms` on the four capstones reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Session 2026-08-10 addition (TV Conflict Width)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-FKT-TVCC-1 | Preserving a finite declared family of pairwise total variations is equivalent to properly coloring its source sign-conflict relation; width-`q` observer existence is equivalent to `q`-colorability; collapsed conflict edges force strict loss; every finite symmetric irreflexive relation is realized by nonnegative Dirac task pairs | `HTGeometry.ConstitutiveTVConflictColoring` |

The module elaborates directly and is imported by `HTGeometry.UniversalLawField`.  Formal lint
passes.  The final 11,516-job umbrella build passes.  Axiom prints on the fibre formula,
lossless-coloring equivalence, strict-loss theorem, width equivalence, arbitrary-relation
realization, and capstone report only `propext`, `Classical.choice`, and `Quot.sound`.  The
de Bruijn--Erdos infinite compactness corollary remains a cited classical result rather than a new
Lean certification claim.

## Session 2026-08-10 addition (Identification--Conflict Critical Triple)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-LSM-5 | Mandatory identifications saturate by equivalence generation; a respecting lossless observer exists exactly when generated identifications avoid TV conflicts; residual width is quotient-conflict chromatic width; two separately compatible identification doctrines can jointly close a conflict path and force strict TV loss | `HTGeometry.ConstitutiveIdentificationConflictInterference` |
| ULF-LSM-6 | Source operations generate unitization identifications and canonical exchange reporters; joint execution collapses every formation-word endpoint, exactly erases exchange TV from one to zero, and two idempotent retractions on three states give the state-minimal source-generated critical triple | `HTGeometry.ConstitutiveEndogenousUnitizationInterference` |

The three-state critical triple is explicit: `0~1`, `1~2`, and the task `delta_0` versus
`delta_2`.  Each identification separately admits a certified lossless observer, while no finite
observer respecting both can remain lossless.  Direct elaboration and formal lint pass.  The final
11,522-job Universal Law Field umbrella build passes; the new module builds cleanly.  Axiom prints
report no axioms for equivalence saturation and only `propext`, `Classical.choice`, and `Quot.sound`
for quotient, TV, and state-minimality theorems.

## Session 2026-08-09 additions (Experimental Dimension)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-EXPDIM-1 | Passive fibre size bounds total experimental capacity; the minimal number of scalar experiments for exact linear reconstruction is exactly `dim ker q₀`, and no finite number suffices when the hidden space is infinite-dimensional | `HTGeometry.ConstitutiveExperimentalDimension` |

The finite-information half is proved without assuming the state space finite.  Direct foreground
elaboration and the final 11,429-job Universal Law Field umbrella build pass with no warnings;
`#print axioms` on every capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Monoid Bialgebra and Hopf Envelope)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-BIALG-1 | The group-like monoid bialgebra `k[t]` has no antipode, the Laurent algebra is its Hopf envelope with the expected universal property, and the unilateral-shift representation extends to it exactly after a quotient killing the rank-one Toeplitz defect | `HTGeometry.ConstitutiveMonoidBialgebraHopfEnvelope` |

Uses mathlib's `AddMonoidAlgebra` bialgebra and Laurent Hopf instances and reuses the certified
shift layer `ConstitutiveToeplitzDefectIndex`.  Clause 7 is stated for an arbitrary defect-killing
unital algebra map (mathlib has no Calkin algebra), which is stronger than the Calkin case; clause 4
is certified at the algebra-map level together with group-likeness of every basis image.  Direct
foreground elaboration and the final 11,431-job Universal Law Field umbrella build pass with no
warnings; `#print axioms` on every capstone reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Session 2026-08-10 additions (Invariant Positivity and KMS Wall)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-IPKMS-1 | A faithful invariant probability forces a compact monoid to be a group, while the Toeplitz Gibbs state at positive temperature is faithful, kills every off-diagonal monomial, and assigns each history layer the exact mass `(1−q)qⁿ`, so no such state descends to the reversible quotient | `HTGeometry.ConstitutiveInvariantPositivityKMSWall` |

New reusable infrastructure: `continuous_of_isClosed_graph` — mathlib has no closed-graph
continuity criterion; it is proved here by an ultrafilter argument.  §2 is certified from the
defining equations of the KMS setting (mathlib has no C*-dynamical systems or KMS states) and §3
exhibits the Gibbs state explicitly rather than quoting a uniqueness theorem.  Direct foreground
elaboration and the final 11,432-job Universal Law Field umbrella build pass with no warnings;
`#print axioms` on every capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Time-Reversal Likelihood Cocycle)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-TRLC-1 | A path law and a reversal give a signed likelihood cocycle with `E e^{−Σ} = 1` and mean equal to the relative entropy; every observer contracts that mean by exactly the integrated fibrewise divergence; and a finite recurrent observer can hide an escaping path with linearly growing production | `HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle` |

Three lemmas absent from mathlib were built: invariance of `klDiv` under a measurable embedding, the
graph map of an observer as a measurable embedding, and the conditional divergence as an integral of
fibrewise divergences.  Together with mathlib's disintegration and chain rule these yield the
**data-processing inequality for `klDiv`**, also absent from mathlib.  Recurrence in §4 is proved
without any Markov-chain theory.  Direct foreground elaboration and the final 11,435-job Universal
Law Field umbrella build pass with no warnings; `#print axioms` on every capstone reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Polar Amplitude and Fisher–Phase Coupling)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-PAFP-1 | A full-support projective amplitude is exactly probability together with relative phase (an explicit `Equiv`); the Fubini–Study line element is one quarter of the Fisher–Rao metric plus the weighted phase variance; and a pure-phase loop keeps the probability observer constant while having length `2π√Var` and nontrivial Berry holonomy | `HTGeometry.ConstitutivePolarAmplitudeFisherPhase` |

The polar chart is built as a genuine `Equiv` between the projective quotient and
`OpenSimplex × PhaseClass`, and `hasDerivAt_polarAmp` certifies that the tangent used in the
Fubini–Study identity really is the derivative of the polar curve.  Direct foreground elaboration
and the final 11,436-job Universal Law Field umbrella build pass with no warnings; `#print axioms`
on every capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Visible Kernel and Purification Gauge)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-HKPG-1 | Eliminating a hidden factor yields a positive semidefinite unit-trace kernel of Schmidt rank, rank one exactly for separable amplitudes and reproducing every visible expectation; the maximally entangled amplitude leaves a full-rank kernel; the diagonal does not determine the kernel; and minimal Gram factorizations form one gauge orbit | `HTGeometry.ConstitutiveVisibleKernelPurificationGauge` |

Two lemmas absent from mathlib were built: the rank-one characterization of matrices as outer
products, and the length-preserving gauge equivalence between two surjective coefficient maps of
equal length.  Direct foreground elaboration and the final 11,437-job Universal Law Field umbrella
build pass with no warnings; `#print axioms` on every capstone reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Composed-Failure Genesis)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-EAG-2-CORE | Independent inactive/unoriented failures force support separation and at least `2^(n+1)-1` attained deterministic response values; the canonical support/parity reporter is legal, attains the bound exactly, has precisely support/parity fibres, and independent blocks force `(2^|A|-1)(2^|B|-1)` mixed channels | `HTGeometry.ConstitutiveComposedFailureGenesis` |

The formal theorem is route-independent and finite.  It proves interaction-vocabulary genesis, not
cofinal formation birth or semantic transport.  Arbitrary-minimizer equality rigidity and the
general convex `2n`-atom construction remain paper-only and do not count as Lean-certified results.
Direct foreground elaboration passed.  `scripts/formal_tools.py lint --check-generated` passed.
The final 11,476-job Universal Law Field umbrella build passed; replay warnings were confined to
pre-existing modules and the new module built cleanly.  `#print axioms` on every new headline
declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Cyclic Process Four Shadows)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-CUPR-1 | One finite cyclic unitary process yields a rational transfer function, a positive Gram-rank profile `min(N+1,r)`, a recurrent observer orbit and an open phase lift; its first `2r` moments determine the coefficients, spectrum, weights and every later moment, and predict the withheld response | `HTGeometry.ConstitutiveCyclicProcessFourShadow` |

Two lemmas absent from mathlib were built: discrete recurrence of powers in a compact topological
group, and the rank of a rectangular weighted Vandermonde matrix.  The reconstruction clauses are
certified as determinacy statements.  Direct foreground elaboration and the final 11,477-job
Universal Law Field umbrella build pass with no warnings; `#print axioms` on every capstone reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Three-Realization Packet)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ADOR-1 | One finite spectral packet has equivalent atomic-measure, analytic-differential (`p(D)f = 0`), state-space and rational-transfer realizations; one polynomial gives the recurrence, the Hankel and Toeplitz rank laws, the exact Prony reconstruction and the withheld response | `HTGeometry.ConstitutiveThreeRealizationPacket` |

The card's equation (11), `rank H_N = min(N+1, r)`, is **false** for `N + 1 < r`; formalization
refuted it inside the positive unitary chamber (`rank_packetHankel_cube`: three cube roots of unity
with uniform weight give `rank H₁ = 1 < 2`) and certified the true statements instead — the upper
bound `rank H_N ≤ min(N+1, r)`, the saturated identity `rank H_N = r` for `r ≤ N+1`, and the
Toeplitz identity `rank G_N = min(N+1, r)` of §5, which is correct as printed.  §8 of the paper card
records the correction.  Two lemmas absent from mathlib were built: integrability against a Dirac
measure for an unbounded integrand, and the converse rank/determinant law
`det_ne_zero_of_rank_eq_card`.  Direct foreground elaboration and the final 11,478-job Universal Law
Field umbrella build pass with no warnings; `#print axioms` on every capstone reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Session 2026-08-10 additions (Bipolar Analytic Admission)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-LSM-7-CORE | Algebraic equivalence saturation followed by Hausdorff admission is exactly the bipolar relation of continuous real unitizing reporters; two continuous cofinal retractions admit exact finite reporters of margin one but force every global continuous observer to be constant, with exact analytic replacement gap `1/2` | `HTGeometry.ConstitutiveAnalyticAdmissionHull`, `HTGeometry.ConstitutiveOneEndedAdmissionCriticalShell` |

Formalization uses Mathlib's maximal Hausdorff quotient to construct the admission receiver and
Urysohn separation to prove the converse reporter characterization.  The concrete capstone is the
one-point compactified natural ray, not a finite wrapper.  Direct foreground elaboration and formal
lint pass.  Final Universal Law Field umbrella build passes (11,525 jobs); `#print axioms` on every
headline declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.  General
closed-equivalence minimality, Dirac-measure TV, the two-ended paper model, and bounded-alternation
closure remain paper-only and do not count as Lean-certified.

## Session 2026-08-10 additions (Coefficient-Lift Transgression)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-CRT-2 | A coarse binary cocycle's failed coefficient lift produces a kernel-valued pentagon-coherent ternary defect; its class is lift-independent and vanishes exactly when a strict fine cocycle lift exists; split refinements kill the defect; the cross-parity `ZMod 4 -> ZMod 2` cell and a two-term linear cell have nonzero lift obstruction | `HTGeometry.ConstitutiveCoefficientLiftTransgression` |

Direct foreground elaboration, formal lint, axiom audit, and final Universal Law Field umbrella build
pass.  The unconditional capstone contains both nonliftable laboratories.  General degree, tower,
completion, and admission-relative transgression remain paper-programme questions and do not count
as certified.

## Session 2026-08-10 additions (Kernel--Cokernel--Closure Law Birth)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-KCL-1 | Cokernel controls exact higher-carrier birth, kernel controls next coherence, and closure gap separates exact, approximable-mirage, and Hausdorff-separated birth; dense injective/non-surjective and surjective/noninjective cells prove independence | HTGeometry.ConstitutiveCarrierBifurcation |

Direct foreground elaboration and formal lint pass. Source-level axiom audit reports only propext,
Classical.choice, and Quot.sound. Final Universal Law Field umbrella build completed 11,537 jobs.
Certified capstone bundles both unconditional countermodels. Successive-carrier composition,
nonlinear carrier mechanics, and source-genesis remain open and do not count as certified.

## Session 2026-08-10 additions (Doctrine-Relative Memory Spectrum)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-DRMS-1 | Bounded Hankel rank ⟺ constant recurrence ⟺ constant-coefficient ODE ⟺ exponential polynomial; finite base-aware linear memory ⟺ `D`-finiteness; hypertranscendence ⟺ maximal jet growth; `exp(z²)`, `tan`, `Γ(z+1)` separate the three doctrines strictly | `HTGeometry.ConstitutiveDoctrineMemorySpectrum`, `HTGeometry.ConstitutiveDoctrineMemoryWitnesses` |

Three paper arguments were replaced by unconditional ones: the "minimal dependent initial family of
columns" by a nested-compactness argument on the sphere of candidate recurrence vectors; Stirling's
formula for `e^{z²}` by the exact leading coefficient `2^k` of its Hermite-type jet polynomials; and
the singular-set theorem for rational-coefficient linear ODEs by a pole-limit after dividing by
`tan^{n+1}`.  Equation (7) is certified in jet-independence form for entire germs through the corpus
meromorphic jet bridge; for the shifted Gamma germ, which is not entire, the certified form is the
order form.  Direct foreground elaboration and the final 11,510-job Universal Law Field umbrella
build pass with no warnings; `#print axioms` on every capstone reports only `propext`,
`Classical.choice`, and `Quot.sound`.

| ID | Theorem | Lean module |
|---|---|---|
| ULF-QGPRH-1 | Jackson's `Γ_q` is one process with a positive atomic law, a GNS/compact-resolvent operator realization, integer-time recurrence with an open marked lift, an exact entropy tilt, and — **Pastro's q-analogue of Hölder's theorem** — no algebraic differential equation over `ℂ[z]` on `Re z > 0` | `HTGeometry.QBinomialTheorem`, `HTGeometry.ConstitutiveQGammaProcess`, `HTGeometry.QGammaAnalytic`, `HTGeometry.QDigamma`, `HTGeometry.QGammaBellSubstitution`, `HTGeometry.QShiftField`, `HTGeometry.QShiftInverse`, `HTGeometry.QIncrement`, `HTGeometry.QIncrementAnalytic`, `HTGeometry.QTranscendence`, `HTGeometry.ShiftEliminationEngine`, `HTGeometry.ShiftEigenrelationEngine`, `HTGeometry.QDigammaHypertranscendental`, `HTGeometry.QGammaHypertranscendental` |

Card promoted to `3-formalized/universal-law-field/` on 2026-08-10.  The §4 capstone
`qGamma_jet_annihilator_eq_zero` rests on the intermediate theorem
`annihilatesQDigamma_eq_zero` — `qᶻ` together with the jets `ψ_q, ψ_q', ψ_q'', …` is algebraically
independent over `ℂ(z)` — which is the shift elimination run over the two-variable field
`ℂ(z,u)`.  Two engines were built for it: `ShiftEliminationEngine` (the corpus's Hölder elimination
over an arbitrary shifted field) and `ShiftEigenrelationEngine` (the eigenrelation refutation over
an arbitrary shifted field), both of which subsume the classical `ℂ(z)` case.  Two scope clauses
carry into stage 3: the unbounded-operator statement of §2 is certified as the explicit compact
diagonal resolvent inverting `X − i`, and the recurrence (15) of §3 is certified at integer times.
`#print axioms` on every capstone reports only `propext`, `Classical.choice`, `Quot.sound`.

## Session 2026-08-10 addition (Closure-Doctrine Serial Homology)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-CHM-1 | Every closure/enlargement doctrine on a serial carrier produces independent source-preimage and target-attainment homology defects; the separated serial sequence is short exact iff both vanish; finite cells prove independence and a compact injective dense-range Gamma reporter realizes the target defect topologically | `HTGeometry.ConstitutiveClosureDoctrineHomology` |

Direct foreground elaboration passes. Source-level axiom prints on both exactness equivalences, the
independence capstone, and the Gamma topological cell report only `propext`, `Classical.choice`, and
`Quot.sound`. Global lint is presently blocked by unrelated shared-worktree debt in
`EulerQGammaDirichlet.lean` and unrelated unwired modules. Final umbrella build status is recorded
after its single foreground audit: `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`
completed successfully with `11,545` jobs; the new module built cleanly.

## Session 2026-08-10 addition (Downstream-Kernel Obstruction Filtration)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-DKO-1 | A three-stage history carries a canonical nested filtration of total law birth; the first two grades are local failure quotiented by kernels of the remaining future tails, and restriction to the second filtration gives a canonical short exact sequence | `HTGeometry.ConstitutiveObstructionFiltration` |

Direct foreground elaboration passes. Source-level axiom prints on nesting, layer surjectivity,
middle exactness, short-exactness, and the capstone report only `propext`, `Classical.choice`, and
`Quot.sound`. Global lint remains blocked by unrelated shared-worktree debt. Final umbrella build
audit passed with `11,547` jobs; the new module and umbrella built cleanly.

## Session 2026-08-10 addition (Primary--Secondary Serial Birth)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-PSB-1 | For composable carriers, primary obstruction lies in the outer cokernel; after it vanishes, a lift-independent secondary class lives modulo `im S + ker T`; the secondary, composite, and primary sectors form a canonical short exact sequence; outer-kernel cancellation and genuine secondary failure both occur | `HTGeometry.ConstitutiveCarrierComposition` |

The module certifies zero criteria, exclusive three-phase classification, lift independence,
injectivity of the secondary-to-composite map, exactness in the middle, surjectivity of the
composite-to-primary transition, and dual finite laboratories. Direct foreground elaboration and
formal lint pass. Final Universal Law Field umbrella build completes `11,542` jobs. Source-level
axiom prints on the equivalence, lift independence, exactness, trichotomy, and capstone report only
`propext`, `Classical.choice`, and `Quot.sound`.

| ID | Theorem | Lean module |
|---|---|---|
| ULF-QG5R-1 | Parameter, atomic probability law, characteristic process, marked minimal GNS triple, and analytic response germ of Jackson's `Γ_q` determine one another; equal observed responses force a **unique** marked unitary equivalence, and every reconstructed quantity — including the withheld tilt response — is invariant under it | `HTGeometry.QGammaFiveChart`, `HTGeometry.MarkedCyclicRigidity`, `HTGeometry.AbsConvergentPowerSeries`, `HTGeometry.QGammaGNSChart` |

Card promoted to `3-formalized/universal-law-field/` on 2026-08-10.  Three pieces of new
infrastructure were required: diagonal unitaries of `ℓ²`; the GNS uniqueness theorem for marked
cyclic presentations over an arbitrary group, including the extension of an isometry from a dense
subspace of an infinite-dimensional Hilbert space (mathlib's `LinearIsometry.extend` is
finite-dimensional only); and the vanishing of the coefficients of an absolutely convergent power
series that vanishes on the unit circle, which is what makes the GNS source vector cyclic.  Fourier
uniqueness itself is mathlib's `Measure.ext_of_charFun`, instantiated at the atomic law `qLaw`.
`#print axioms` on every capstone reports only `propext`, `Classical.choice`, `Quot.sound`.

## Session 2026-08-10 addition (Adversarial Law Stress)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ALG-2 | Prefix cylinders have static shattering dimension one while a source-consistent adaptive challenge forces arbitrary deterministic mistake depth; fractional prediction retains the legal horizon and has exact finite-horizon value `d / 2` | `HTGeometry.ConstitutiveAdversarialLawStress` |

Direct foreground elaboration and the module build pass with no warnings.  The module is wired into
`HTGeometry.UniversalLawField`; final umbrella build passed with `11,552` jobs.  Source-level axiom
prints on static laminarity, deterministic all-round stress, convex cumulative lower and upper
bounds, and the capstone report only `propext`, `Classical.choice`, and `Quot.sound`.  This certifies
the fixed-doctrine base mechanism only; doctrine-changing challenge transport remains open. Global
formal lint remains blocked by unrelated unreachable modules
`RHTower.Sieve.GhsUniformError` and `HTGeometry.EulerQGammaContinuation`.

## Session 2026-08-10 addition (Challenge-Prolongation Data Processing)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ALG-3 | An intertwining observer maps every finite promoted challenge language onto its observed language, contracts finite rank, and creates an apparent recurrence exactly by killing a source challenge combination; source-independent/observer-dependent packets produce a nonzero hidden residual | `HTGeometry.ConstitutiveChallengeProlongation` |

Direct foreground elaboration and the owned-module build pass without warnings.  Source-level axiom
prints on prolongation transport, exact span image, rank contraction, recurrence/kernel equivalence,
hidden-residual existence, and the capstone report only `propext`, `Classical.choice`, and
`Quot.sound`.  The module is wired into `HTGeometry.UniversalLawField`.  Source-normal promoter
birth and nonlinear doctrine-changing challenge transport remain open and do not count as
certified.

## Session 2026-08-10 addition (Differential Law Genesis)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-DLG-1 | A marked polynomial-law execution canonically produces a restorative one-hole context; a marked composite leaf produces nested inner/outer repair with strict outer locality; failure pairs partition by common outer ancestry, while the smallest ancestry-blind observer identifies same-branch and split-branch interactions | `HTGeometry.ConstitutiveLawDerivativeGenesis` |

Direct foreground elaboration and the `510`-job owned-module build pass without warnings. The
module is wired into `HTGeometry.UniversalLawField`; final umbrella build passed with `11,558`
jobs. Source-level axiom prints on restoration, nested repair, locality, interaction partition,
ancestry erasure, and the capstone report only `propext`, `Classical.choice`, and `Quot.sound`.
Container differentiation and one-hole contexts are classical parents. The certified field delta
is a route-independent failure-to-challenge mechanism and exact ancestry-erasure no-go; repair
selection, semantic effectivity, presentation invariance, and higher failure partitions remain
open.

## Session 2026-08-10 addition (Contextual Challenge Transduction)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-DLG-2 | Partial evaluation of a fixed reporter in a failure-born one-hole context canonically produces a replacement challenge; semantic birth is exactly strict contraction of old invisible interventions; nested challenges satisfy a strict chain law; postobservation can erase but cannot create effectivity; a born challenge need not select a repair | `HTGeometry.ConstitutiveContextualChallengeTransduction` |

Direct foreground elaboration is warning-free.  The owned-module build passes with `8,666` jobs,
and the final `HTGeometry.UniversalLawField` umbrella build passes with `11,561` jobs.
Source-level axiom prints on restoration, effectivity witnesses, invisible-doctrine contraction,
nested chain, postcomposition, no downstream genesis, injective preservation, sharp erasure,
no-selection, and the capstone report only `propext`, `Classical.choice`, and `Quot.sound`.  The
module is wired into `HTGeometry.UniversalLawField`.  Recursive challenge-language revision,
marked-presentation invariance, partial/admission-sensitive syntax, and strategy admission remain
open.

## Session 2026-08-10 addition (Prospective Challenge Geometry)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-PCG-1 | Finite legal contexts induce a nested prospective-agreement filtration; one exact plateau is permanent; postobservation delays or erases separation; every finite all-true history is source-realized but the coherent infinite history is not, while it lies in the product-topology closure of source signatures | `HTGeometry.ConstitutiveProspectiveChallengeGeometry` |
| ULF-PCG-2 | A fresh legal operation changes eventual distinctions exactly when it fails to preserve the old future kernel; nonpreservation is equivalent to strict prospective refinement; every old-word-definable operation is inert; constant postobservation can erase a genuine source grammar birth | `HTGeometry.ConstitutiveDescentBreakingGrammarExtension` |

Direct foreground elaboration is warning-free. Owned-module builds pass with `8,667` and `8,661`
jobs respectively; the final `HTGeometry.UniversalLawField` umbrella build passes with `11,568`
jobs. Source-level axiom prints report either no axioms or only `propext`, `Classical.choice`, and
`Quot.sound`. Both modules are wired into the Universal Law Field umbrella. The formalized
mechanism classifies effectiveness and exposes the old-term no-genesis barrier; construction of a
source-normal minimal descent-breaking update remains open.

## Session 2026-08-10 addition (Relational Law Renormalization)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-RLR-1 | Canonical observer-induced relation; deterministic descent iff kernel preservation; lax execution; exact serial observer pushforward; selector no-go; two-defect observation--execution interchange; pushforward composition exact iff observer injective; independent strict cells | `HTGeometry.ConstitutiveRelationalLawRenormalization` |

Direct foreground elaboration and the 2,998-job leaf build pass. The module is wired into
`HTGeometry.UniversalLawField`; final umbrella build passes with 11,574 jobs. Source-level axiom
prints on descent classification, pushforward exactness, interchange filtration, both independence
cells, and both capstones report **no axioms**. The certification is set-level and route-independent;
topological closure, convex/probabilistic promotion, cofinal histories, and source-normal selection
remain open.

## ULF-EQG-1 — Euler q-Gamma process, random-integer law, zeta-divisor translation

Promoted to stage 3 on 2026-08-10.  Twenty-two modules, from the global product law and the
arithmetic Dirichlet series through the meromorphic cut ladder, the divisor transgression and its
clean landing, the compact-resolvent observer, the hypertranscendence of the response, and the
genus-one renormalisation with its convergence, zero-freeness and holomorphy.

Three reusable layers were built on the way: reciprocal closure of differential algebraicity
(`recipSub`, `recipSub_eq_zero_iff`, `differentiallyAlgebraicOn_inv`), the domain-local ring and
propagation calculus for algebraic differential equations (`differentiallyAlgebraicOn_mul/_div`,
`differentiallyAlgebraicOn_mono_of_isPreconnected`,
`differentiallyAlgebraic_of_on_compl_singleton`), and the genus-one deviation calculus
(`norm_genusOneFactor_sub_one_le`, `norm_inv_sub_one_le`, `norm_mul_sub_one_le`,
`norm_cexp_sub_one_le`).

Umbrella `HTGeometry.UniversalLawField` green at 11 575 jobs; every capstone axiom print is
`propext, Classical.choice, Quot.sound`.  Companion:
`3-formalized/universal-law-field/euler-q-gamma-process-zeta-divisor-translation-law-formalized.md`.

## ULF-MPTB-1 — Multilinear process tomography, blind sector, positive robustness

Promoted to stage 3 on 2026-08-10.  The two paper-level clauses were closed: the product-slot
dimension formula `dim U^⊥ = ∏ dim Eᵢ − ∏ dim Vᵢ`, built by presenting the product instrument space
as the range of the slotwise tensor inclusion and proving that map injective from the splitting of
each slot inclusion; and the quantitative positive-definite perturbation bound, built on a uniform
positivity constant obtained as the minimum of the quadratic form on the unit sphere.

New reusable declarations: `finrank_piTensorProduct`, `piTensorProduct_map_injective`,
`exists_uniform_positive`, `abs_reApplyInnerSelf_le`.  Umbrella green at 11 577 jobs; all axiom
prints are `propext, Classical.choice, Quot.sound`.

## Session 2026-08-10 addition (Bipolar Observer Repair)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-RLR-2 | Greatest invariant refinement and least invariant coarsening are universal opposite determinizations; each absorbs the other in application order; schedules agree iff the observer was already executable; a three-state cell realizes equality versus the universal relation and raw nondeterminism | `HTGeometry.ConstitutiveBipolarObserverRepair` |

Direct foreground elaboration is warning-free and the leaf build passes with 2,999 jobs.  The module
is wired into `HTGeometry.UniversalLawField`; the final umbrella build passes with 11,578 jobs.
Axiom prints on generic extremality, both absorption laws, exchange, both exact cell endpoints,
nondeterminism, and the unconditional capstone report only `propext` and `Quot.sound`.  Full-tree
lint reaches the owned module but is currently red on unrelated concurrently unwired
`RHTower.DeningerPrimeLogHeightForms` and
`HTGeometry.ConstraintRelativity.CongruenceOrderTraceDual`.  No route, analytic hypothesis,
project axiom, or RH statement occurs in the certified module.

## Session 2026-08-10 addition (Diagonal Law Genesis)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-DJG-1 | Boolean anti-diagonal challenge birth; cardinal-minimal conservative successor; relabelling naturality; finite strict-order tower; finite-cylinder/global realization gap; infinite-support successor; filtered-limit nonexchange | `HTGeometry.ConstitutiveDiagonalLawGenesis` |

Direct foreground elaboration is warning-free and the leaf build passes with 2,997 jobs. The
module is wired into `HTGeometry.UniversalLawField`. Axiom prints on diagonal novelty, the
no-isomorphism theorem, and the unconditional capstone report only `propext`, `Classical.choice`,
and `Quot.sound`. No route object, analytic premise, project axiom, or RH statement occurs. The
result closes one source-normal grammar-update calibration; recursive typed challenges,
admission-sensitive formation, and three-organ realization remain open.

## Session 2026-08-10 addition (Endogenous Representability Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ERM-1 | Two-sided conservative unary-law extension transports every finite word; future-retaining repair pulls back exactly; future-forgetting repair pulls back laxly; compatible semantic retraction restores exactness; a three-state cell has strict fresh return and no compatible retraction | `HTGeometry.ConstitutiveCarrierGenesisRepair` |

Direct foreground elaboration is warning-free. The leaf build passes with 3,000 jobs and the final
`HTGeometry.UniversalLawField` umbrella build passes with 11,580 jobs. Formal lint is clean. Axiom
prints on word restriction/lifting, exact interior pullback, lax closure pullback, retraction
exactness, strict fresh return, no-retraction, and the unconditional capstone report only `propext`
and `Quot.sound`. No route object, analytic hypothesis, project axiom, or RH statement occurs.

## Session 2026-08-10 addition (Representation--Execution Exchange)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-REE-1 | Operational novelty iff row-profile fibre splitting iff strict contraction of invisible interventions; anti-diagonal effectiveness classification; four represented/effective chambers; every finite diagonal stage unrepresented but inert | `HTGeometry.ConstitutiveRepresentationExecutionExchange` |

Direct foreground elaboration is warning-free. The leaf build passes with 8,666 jobs and the final
`HTGeometry.UniversalLawField` umbrella build passes with 11,582 jobs. The module is wired into the
umbrella. Axiom prints on both exchange criteria, anti-diagonal classification, the four-chamber
theorem, finite diagonal-stage law, and unconditional capstone report only `propext`,
`Classical.choice`, and `Quot.sound`. No computation certificate, route premise, project axiom, or
RH statement occurs.

## Session 2026-08-10 addition (Controlled Naturality Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-CNM-1 | Orbit-complete equivariant reporter is effective iff symmetry moves an attained response; invariant-output inertness; Curie stabilizer inheritance; fixed-mark equivariance under mark stabilizer; orbit-completeness and marking insufficiency cells | `HTGeometry.ConstitutiveControlledNaturalityMechanics` |

Direct foreground elaboration is warning-free. The leaf build passes with 8,665 jobs and the final
`HTGeometry.UniversalLawField` umbrella build passes with 11,583 jobs. The module is wired into the
umbrella. Axiom prints report at most `propext`, `Classical.choice`, and `Quot.sound`; the exact
attained-fixed equivalence reports no axioms. No computation certificate, route premise, project
axiom, or RH statement occurs.

## Session 2026-08-10 addition (Autopoietic Law Mechanics viability laboratory)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ALM-1 | Conservative repair preserves semantic range while birthing a kernel-history direction; canonical positive chamber has unique normalized full-support carrier, loses every strict progress functional, and supports stationary-endpoint histories with unbounded positive cost | `HTGeometry.ConstitutiveViabilityCoercivityTransmutation` |

Direct foreground elaboration and the leaf build pass; the final
`HTGeometry.UniversalLawField` umbrella build passes with 11,586 jobs. The module is wired into the
umbrella. Axiom prints on the general conservative-repair laws, canonical chamber theorems, and
unconditional capstone report only `propext`, `Classical.choice`, and `Quot.sound`. Full formal lint
reports only the unrelated umbrella-reachability failure
`GaloisForLFunctions.HTGeometry.AffineFunctionSystemEnvelope`. No computation certificate, route
premise, project axiom, or RH statement occurs.

## Session 2026-08-10 addition (collective-repair threshold mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ALM-2 | Individually nonviable conservative repairs cross an exact spectral threshold: subcritical strict progress, critical carrier ray, supercritical full-support circulation, strict-progress loss, singular symmetric amplification, period-two observation, and open zero-boundary history | `HTGeometry.ConstitutiveCollectiveRepairThreshold` |

Direct foreground elaboration and the leaf build pass. The module is wired into
`HTGeometry.UniversalLawField`. Axiom prints on one-repair nonviability, all threshold chambers,
strict-progress transition, symmetric amplification, period-two interaction, unbounded history,
and the unconditional capstone report only `propext`, `Classical.choice`, and `Quot.sound`. No
computation certificate, route premise, project axiom, or RH statement occurs. Final foreground
umbrella build passes with 11,587 jobs. Full formal lint reaches the module and reports no target
error; unrelated unwired `RHTower.Sieve.*` and `HTGeometry.AbelianZetaGas.NaturalBoundary`
modules keep the repository-wide lint exit nonzero.

| ID | Theorem | Lean module |
|---|---|---|
| ULF-GAS-1 | The Euler q-Gamma source is the zeta-Gibbs measure on finite abelian groups, equivalently the unique KMS state of a free prime-power Toeplitz gas; its order and socle order carry two nonisomorphic zeta-divisor calculi (the dilation one having the line `Re u = −σ` as a natural boundary), its walls `σ = 1/g` are exact depth-`g` condensation transitions with the squarefull sector honest above `σ = 1/2`, depth dilation is an exact renormalization action, and the symmetrized information cost of the canonical tilt is `σ·(−ζ′/ζ)(σ)` | `HTGeometry.AbelianZetaGas.*` (26 modules), `HTGeometry.PartitionGeneratingFunction`, `HTGeometry.PartitionQPochhammerBridge` |

Direct foreground elaboration and the leaf builds pass; every module is wired into
`HTGeometry` and hence into `HTGeometry.UniversalLawField`. Axiom prints on all eight theorem
capstones report only `propext`, `Classical.choice`, and `Quot.sound`. No computation certificate,
route premise, project axiom, or RH statement occurs. Final foreground umbrella build passes with
11,590 jobs.

## Session 2026-08-10 addition (Symbolic--Execution Law Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SELM-1 | Finite execution implies symbolic local admission; exact equality in the one-kernel system; triangle symbolic grades `2n` are locally admitted but nonexecutable for every `n>0`; normalized profile/parity observation is constant while exact grade is unbounded | `HTGeometry.ConstitutiveSymbolicExecutionGap` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Axiom prints on the general implication, one-kernel equivalence,
triangle nonexecution, observer constancy, and unconditional capstone report only `propext`,
`Classical.choice`, and `Quot.sound`. No computation certificate, route premise, project axiom, or
RH statement occurs. Final foreground umbrella build passes with 11,599 jobs. Repository lint
reports no target error; its global nonzero exit comes from pre-existing unreachable modules in
unrelated theorem areas.

## Session 2026-08-10 addition (Primitive Symbolic-Law Genesis)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SELM-2 | Every positive local law is generated by source-canonical indecomposable laws; bounded primitive degree is equivalent to bounded-grammar completeness; unbounded primitive degree defeats every bounded grammar; one degree-two triangle primitive generates the full positive central ray | `HTGeometry.ConstitutivePrimitiveExecutionGenesis` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Axiom prints on canonical primitive decomposition, bounded-degree
classification, unbounded-history obstruction, triangle primitivity, central-ray generation, and
the unconditional capstone report only `propext`, `Classical.choice`, and `Quot.sound`. No
computation certificate, route premise, project axiom, or RH statement occurs. Final foreground
umbrella build passes with 11,600 jobs. Repository lint reports no target error; its global nonzero
exit comes from pre-existing unreachable modules in unrelated theorem areas.

## Session 2026-08-10 addition (Primitive Ray Observer Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SELM-3 | Every positive multiple of a primitive law is locally admitted and canonically generated; bounded-degree generation persists along the ray; normalized positive profile and cyclic grade observer are periodic while exact execution grade advances strictly and is unbounded | `HTGeometry.ConstitutivePrimitiveRayObserver` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Axiom prints on local ray scaling, bounded ray generation,
projective-profile cancellation, periodic observer/open lift, and the unconditional capstone report
only `propext`, `Classical.choice`, and `Quot.sound`. No computation certificate, route premise,
project axiom, or RH statement occurs. Final foreground umbrella build passes with 11,601 jobs.
Repository lint reports no target error; its global nonzero exit comes from pre-existing unreachable
modules in unrelated theorem areas.

## Session 2026-08-10 addition (Primitive-Spectrum Relabeling Invariance)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SELM-5 | Transport along any coordinate equivalence preserves local admission, dominated splitting, primitivity, and occurrence of every primitive degree; hence the complete primitive spectrum is independent of coordinate names | `HTGeometry.ConstitutivePrimitiveSpectrumTransport` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Axiom prints on local transport, split transport, primitivity,
primitive-degree occurrence, and the unconditional capstone report only `propext`,
`Classical.choice`, and `Quot.sound`. No computation certificate, route premise, project axiom, or
RH statement occurs. Final foreground umbrella build passes with 11,603 jobs. Repository lint
reports no target error; its global nonzero exit comes from pre-existing unreachable modules in
unrelated theorem areas.

## Session 2026-08-10 addition (Cofinal Primitive-Degree Escape)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SELM-4 | In the `k`-coordinate complete-complement failure system, the all-ones law is primitive at degree `k-1`; therefore aperture `D+2` contains a degree-`D+1` primitive missed by every `D`-bounded grammar, and cofinal primitive degrees escape every bound | `HTGeometry.ConstitutiveCofinalPrimitiveDegreeEscape` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Axiom prints on local admission, the positive-local total-resource
bound, complete-complement primitivity, bounded-grammar failure, unbounded primitive degrees, and
the unconditional capstone report only `propext`, `Classical.choice`, and `Quot.sound`. No
computation certificate, route premise, project axiom, or RH statement occurs. Final foreground
umbrella build passes with 11,602 jobs. Repository lint reports no target error; its global nonzero
exit comes from pre-existing unreachable modules in unrelated theorem areas.

## Session 2026-08-10 addition (Failure-Antichain Semantic Quotient)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SELM-6 | Mutual inclusion-domination of failure families preserves local admission, execution, dominated splitting, primitivity, exact symbolic--execution gaps, and every primitive-degree occurrence; inserting a dominated superset kernel is therefore semantic chart redundancy | `HTGeometry.ConstitutiveFailureAntichainQuotient` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Axiom prints on domination composition, semantic invariance,
primitive-spectrum invariance, dominated-superset insertion, and the unconditional capstone report
only `propext`, `Classical.choice`, and `Quot.sound`. No computation certificate, route premise,
project axiom, or RH statement occurs. Final foreground umbrella build passes with 11,605 jobs.
Repository lint reports no target error; its global nonzero exit comes from unrelated unwired
modules.

## Session 2026-08-10 addition (Observer Lax Effectivity and Gap Erasure)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SELM-7 | Positive fiber pushforward preserves symbolic local admission and executable repair, so coarse observation cannot create an execution gap but can erase one; the explicit triangle collapse erases its source gap while producing one unit of false overlap | `HTGeometry.ConstitutiveObserverExecutionGap` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Axiom prints on the fiber-sum identity, local and executable
pushforward, gap noncreation, triangle gap erasure, exact false overlap, and the unconditional
capstone report only `propext`, `Classical.choice`, and `Quot.sound`. No computation certificate,
route premise, project axiom, or RH statement occurs. Final foreground umbrella build passes with
11,605 jobs. Repository lint reports no target error; its global nonzero exit comes from unrelated
unwired modules.

## Session 2026-08-10 addition (Observer Gap-Death Filtration)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SELM-8 | Kernel, failure-family, and positive fibre-sum observation compose strictly; gaps persist backward, gap death persists forward, successor-hereditary obstruction histories are initial segments, and the triangle collapse has permanent death time one | `HTGeometry.ConstitutiveObserverGapPersistence` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Axiom prints on strict composition, two-step persistence,
no-revival, permanent triangle death, and the unconditional capstone report only `propext`,
`Classical.choice`, and `Quot.sound`; the abstract initial-segment theorem reports no axioms. No
computation certificate, route premise, project axiom, or RH statement occurs. Final foreground
umbrella build passes with 11,606 jobs. Repository lint reaches the module with no target error; its
global nonzero exit comes from unrelated unwired modules.

## Session 2026-08-11 addition (Generative Response Fusion)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-GRM-1 | One centered intervention is reconstructed by finite phase moments, localized by positive Gram-null geometry, generates exactly the newborn feature span, conserves leverage, and predicts Hankel plus simple-null determinant response | `HTGeometry.GenerativeResponseFusion` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Axiom prints for centered conservation, moment reconstruction,
positive null localization, newborn-span rank, leverage conservation, literal Gram and
log-determinant derivatives, Hankel response, determinant response, and the unconditional full
capstone report only `propext`, `Classical.choice`, and `Quot.sound`. No computation certificate,
route premise, project axiom, or RH statement occurs. Final foreground umbrella build passes with
11,608 jobs. The arbitrary positive corank-one spectral reduction is now Lean-closed: rank `d - 1`
isolates the unique zero eigenline, positivity makes every complementary eigenvalue strictly
positive, orthogonal conjugation transports the diagonal adjugate, and any unit kernel generator
gives `adj(G₀) = det₊(G₀) aaᵀ`. The exact coordinate-free determinant derivative and strict
pseudodeterminant positivity are included in `generativeResponse_full_capstone`; the updated
targeted module build completes 8,665 jobs.

The same module now also certifies the exact finite selection law: conservation of the zeroth phase
moment together with inward response on every positive Gram null face is equivalent to membership
in the generative tangent cone. Any negative first response yields an absent source coordinate with
negative tangent coefficient. `generativeSelection_capstone` is unconditional and introduces no RH
premise; the infinite arithmetic transport of this cone is the next open gate.

## Session 2026-08-11 addition (Cofinal Generative Admission)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-GRM-2 | Reciprocal admission/domination feasibility, positive-map data processing, exact finite-aperture/contingent equivalence, and a mass-conserving probability system with strict finite positivity but zero global straight-line radius | `HTGeometry.CofinalGenerativeAdmission` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Axiom prints on reciprocal feasibility, finite observer
classification, positive transport, the abstract cofinal collapse, and the conserved probability
capstone report only `propext`, `Classical.choice`, and `Quot.sound`. Final foreground umbrella
build passes with 11,609 jobs; repository lint passes. The paper's full `ell^1` norm-closure and
Fourier uniqueness clauses remain explicit formal boundaries.

The module also certifies joint-conservative fusion. Positivity-reflecting observer families
reconstruct source admission and domination at every fixed scale; failure produces an observer
witness that may depend on scale. Coordinate evaluations jointly reflect positivity, yet the
conserved probability countermodel is admitted by every fixed coordinate observer and not by the
source. This is the exact migrating-obstruction theorem behind the uniform cofinal gate.

## Session 2026-08-11 addition (Complex-Time Generative Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-GRM-3 | Exponential tilt preserves probability, its derivative is the centered score tangent, and positive Markov observation satisfies exact source Fisher = observed Fisher + conditional score loss | `HTGeometry.ComplexTimeGenerativeMechanics` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. The countable literal Euler-shell complex-time identity remains a
paper-level bridge; Lean certifies the universal finite generation and Fisher conservation laws,
including impossibility of strict receiver amplification under any positive Markov score
realization.

Source-level axiom prints on exponential-tilt differentiation, exact Fisher conservation,
data processing, and the strict-amplification no-go report only `propext`, `Classical.choice`, and
`Quot.sound`. Final foreground `HTGeometry.UniversalLawField` build passes with 11,610 jobs, and
repository formal lint passes. No `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, computation
certificate, route premise, or RH statement occurs in either new module.

## Session 2026-08-11 addition (Coherent History Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-HIST-1 | Total polar reconstruction, exact phase-dispersion conservation, least positive matrix majorant, nonnegative composition-interference defect, exact associativity conservation, and a closed period-two coherent process with exponentially open positive history | `HTGeometry.CoherentHistoryMechanics` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`.  Axiom prints on phase reconstruction, phase dispersion,
least-majorant minimality, interference positivity, associativity conservation, recurrent witness,
exponential history, and the unconditional capstone report only `propext`, `Classical.choice`, and
`Quot.sound`.  No project axiom, route premise, computation certificate, or RH statement occurs.
Final foreground umbrella build passes with 11,611 jobs.

## Session 2026-08-11 addition (Marked Variation Dynamics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-MVD-1 | Positive-kernel modulus and composition, marked-defect fusion, exact generation-observation interchange, serial loss budget and exact-return rigidity, three-sector conservation, and exact nearest genuine-carrier distance | `HTGeometry.MarkedVariationDynamics` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`.  Final foreground umbrella build passes with 11,612 jobs.
Axiom prints on the fusion capstone, interchange law, macroscopic-loss bound, exact-return rigidity,
and carrier-distance theorem report only `propext`, `Classical.choice`, and `Quot.sound`.  The
module contains no `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, computational
certificate, route premise, or RH statement.

Generated indexes were refreshed. Repository-wide lint reaches
`HTGeometry.MarkedVariationDynamics` through its theorem-area and ULF umbrellas; its nonzero exit is
caused only by nineteen unrelated pre-existing/unowned modules currently unwired from the RHTower
or HTGeometry umbrellas.

## Session 2026-08-11 addition (Calibration-Spectrum Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-CSM-1 | Four-calibrator reconstruction, exact positive-observer spectral transport, adaptive-calibration exchange, nonnegative source ancestry, serial ancestry conservation, refinement transport, and response-stiffness conservation | `HTGeometry.CalibrationSpectrumMechanics` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`.  Final foreground umbrella build passes with 11,613 jobs.  Axiom
prints for reconstruction, transport, ground exchange, one-stage ancestry, observer ancestry,
serial ancestry, refinement, both response-derivative theorems, stiffness conservation, and the
unconditional capstone report only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem proves more than the preceding scalar marked-variation law: the four-point response
spectrum reconstructs the positive envelope and coherent complex output, and every unit of scalar
defect is assigned exact source/observer ancestry.  It also predicts and certifies the same defect
as lost infinitesimal response stiffness in a fourth organ.  No computation certificate, route
premise, arithmetic specialization, custom axiom, or RH statement occurs.

## Session 2026-08-11 addition (Norming-Face Fusion Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-NFFM-1 | Exact residual minimization, perfect-fusion/common-calibrator equivalence, norming-face convexity, Helly witness extraction, minimal-defect dimension bound, observer exchange, and refinement conservation | `HTGeometry.NormingFaceFusion` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Final foreground umbrella build passes with 11,614 jobs. Axiom
prints for exact attainment, common calibration, convex norming faces, bounded witness arity,
minimal-defect dimension, observer exchange, and refinement conservation report only `propext`,
`Classical.choice`, and `Quot.sound`.

Lean certifies the coordinate-free finite mechanism and the dimension-escape lower bound. Complex
phase, finite-port incidence, and trace-norm spectral realizations remain paper-level corollaries;
the arithmetic source realization needed for an RH selection theorem remains an explicit open
gate. No `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, computation certificate, route
premise, or RH statement occurs in the module.

## Session 2026-08-11 addition (Compact Calibration Globalization)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-GRM-WCG-1 | Weak-star norming-face closedness/nonemptiness, finite-packet-to-global common normer, exact finite/global equivalence, and finite witness for every failure | `HTGeometry.CompactCalibrationGlobalization` |

Direct foreground elaboration passes and the module is wired into
`HTGeometry.UniversalLawField`. Final foreground umbrella build passes with 11,615 jobs. Axiom
prints for globalization, equivalence, and finite failure witness report only `propext`,
`Classical.choice`, and `Quot.sound`. Universal-law lint passes.

This formally kills fixed compact norming-face geometry as an explanation of a purely cofinal
obstruction invisible on every finite packet. Any surviving mechanism must change doctrine, lose
closedness/compactness, or retain a separate collapsing execution radius. No `sorry`, `admit`,
project `axiom`, `opaque`, `unsafe`, computation certificate, route premise, or RH statement occurs.

## Session 2026-08-11 addition (Complete Test-Closure Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-CTCM-2 | Complete atom/test reconstruction, complete-order reflection under arbitrary packet equivalence, exact negative-witness preservation, compensation-feasible-set conservation, invertible congruence reflection, and real Vandermonde test closure | `HTGeometry.CompleteTestClosureFusion` |

Direct foreground elaboration passes. Final foreground leaf build passes with 8,655 jobs, and the
module is wired into `HTGeometry.UniversalLawField`, whose final foreground build passes with
11,620 jobs. Axiom prints for the capstone, compensation conservation, and Vandermonde PSD
reflection report only `propext`, `Classical.choice`, and `Quot.sound`. Repository formal lint
reaches the target through its theorem-area and universal-law-field umbrellas; its nonzero exit is
caused only by unrelated pre-existing RHTower/HTGeometry modules that remain unwired from their
theorem-area umbrellas. Target forbidden-declaration scan passes, and no Lean or Lake process
remains.

Lean certifies the route-independent finite fusion core: complete invertible test calculi preserve
and reflect atom reconstruction, positivity, strict negative witnesses, and the exact feasible
compensation set. Exact Sylvester inertia multiplicities, complex Fourier realization,
Kronecker-channel lift, infinite-support closure, and arithmetic source realization remain
paper-level or open and do not count as proved. No `sorry`, `admit`, project `axiom`, `opaque`,
`unsafe`, computation certificate, route premise, or RH statement occurs in the module.

## Session 2026-08-11 addition (Witt Formation Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-WFM-2 | Exact exterior/complete formation conservation, Newton ghost generation, first-`r` ghost reconstruction, Adams subsampling, powered-mode bucket aggregation, exact post-Adams Hankel rank, minimal recurrence order, and positive-real memory preservation | `HTGeometry.WittFormationMechanics` |
| ULF-WFM-3 | Joint Hausdorff completion preserves exact formation/exterior inversion; completed formations and all multiplicative receivers are nonzero, pointwise | `HTGeometry.WittConservativeInverseCompletion` |

Direct foreground elaboration and compiled leaf build pass. The module is wired into
`HTGeometry.UniversalLawField`; its final foreground umbrella build passes with 11,626 jobs.
Axiom prints for conservation, reconstruction, recurrence, exact Hankel rank, recurrence
minimality, and positive-real memory report only `propext`, `Classical.choice`, and `Quot.sound`.

The module reuses the corpus's generic finite packet recurrence/Hankel machinery. Its certified
fusion content is exact formation conservation plus Adams collision aggregation: the number of
distinct powered-mode buckets is both saturated Hankel rank and minimal constant-recurrence order.
No infinite completion, arithmetic source realization, custom axiom, computation certificate, or
RH statement occurs.

## Session 2026-08-11 addition (pole-unit formation mechanics, full card)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-PUFM-2 | Analytic distinguished logarithm, exact ghost law, one-ray coefficient inversion, germ rigidity, divisor memory | `HTGeometry.PoleUnitFormationAnalytic` |
| ULF-PUFM-2 | Universal Gamma base limit, ascending-factorial moments, strict Hankel positivity, exact cumulant slope and curvature laws | `HTGeometry.PoleUnitGammaBase` |
| ULF-PUFM-2 | Euler-shell relative response, first constitutive coefficient `γ + H_m'(1)/H_m(1)`, shell clock mean and variance | `HTGeometry.PoleUnitEulerShell` |

Direct elaboration of all three modules passes; the foreground
`lake build GaloisForLFunctions.HTGeometry.UniversalLawField` completed 11,632 jobs.  Axiom prints
for every listed capstone report only `propext`, `Classical.choice`, and `Quot.sound`.  The card
`pole-unit-scale-cocycle-correction-jet-reconstruction-and-divisor-memory-law.md` is promoted to
Stage 3 with its full displayed surface certified.

## Session 2026-08-11 addition (Source-Formation Harmonic Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SFHM-2/3 | Literal Möbius prime-exponent edges, block boundary conservation, marked-history reconstruction, exact refinement-energy split, source-coefficient character execution, character reconstruction, polar criticality, parity recurrent shadow with linearly open positive history, maximal differential rank of the faithful depth-12 source realization, and bilateral reflection-energy unitarity selection | `HTGeometry.SourceFormationHarmonicMechanics` |

Direct foreground elaboration passes. The module is wired into
`HTGeometry.UniversalLawField`; final foreground leaf build passes with 9,026 jobs. The umbrella
build reaches and builds this module, then fails in unrelated concurrent module
`HTGeometry.ConstitutiveAdversarialLawStress` on pre-existing type errors and heartbeat timeouts.
Axiom prints for arithmetic source realization, reconstruction, energy conservation, polar
criticality, source-native differential independence, and the closed five-shadow fusion certificate
as well as the bilateral summability selector report only `propext`, `Classical.choice`, and
`Quot.sound`.

This is the first literal source realization of the coherent-history/refinement fusion mechanism:
one arithmetic formation has incidence, coherent phase execution, positive variation execution,
a phase-quotiented harmonic radial detector, recurrent/open-history behavior, and maximal
countable differential formation rank. It does not prove the Xi deformation is a harmonic source
section and contains no RH premise, computation certificate, `sorry`, `admit`, project `axiom`,
`opaque`, or `unsafe` declaration.

## Session 2026-08-11 sweep (stage-3 promotion of the certified stage-2 backlog)

Sixty-seven universal-law-field cards were audited statement-by-statement against their Lean
modules and promoted to stage 3.  Where the audit exposed a displayed claim without a matching
declaration, the missing statement was proved rather than the claim dropped:

| Card | Added Lean |
|---|---|
| ULF-PUFM-2 pole-unit formation | new `HTGeometry.PoleUnitFormationAnalytic`, `HTGeometry.PoleUnitGammaBase`, `HTGeometry.PoleUnitEulerShell` |
| ULF-CRT-2 coefficient lift | `kernelHigherDefect_unique` |
| ULF-ALM-1 conservative repair | `conservativeRepairKernelEquiv`, `finrank_conservativeRepairBoundary_ker` |
| ULF-OPM-3 exchange residual | `heisExchangeProjection_ker`, `commutator_heis_eq_center`, `heisStrictShadowEquiv` |
| ULF-OPM-2 minimal strictification | `exchangeQuotientLeft_unique`, `exchangeQuotientRight_unique`, `calibration_exchangeCongruence_iff`, `calibration_quotient_two_classes` |
| ULF-ALG-3 challenge prolongation | exact finite false-closure laboratory `lab_false_closure` |
| ULF-ALG-2 adversarial stress | `versionSpace_card`, `shatteredChallengeDepth_le` |
| ULF-LSM-1 law saturation | `finite_reporter_family_stabilizes`, `reporterVector_tendsto` |
| ULF-SEG-1 mutational genesis | `pentagonLineage_exchange`, `pentagon_versus_open_lineage` |
| ULF-NFF-1 norming-face fusion | `no_finiteDimensional_receiver_of_unbounded_minimallyDefective`, `receiver_closedBall_not_isCompact_of_unbounded_minimallyDefective` |
| ULF-CSM-1 calibration spectrum | `weighted_triangle_eq_iff`, `positiveObserverLoss_eq_zero_iff` |
| ULF-PCG-1 prospective geometry | `prospectiveGauge` and its pseudoultrametric laws |
| ULF-FKT-1 failure-kernel transversal | `minimalSuccessfulKernelRevision_iff_core_certificate` |
| ULF-FKT-TVCC-1 conflict coloring | `stagewise_observerWidthAtMost_iff_conflictColorable` |
| ULF-ECM-1 endogenous compatibility | `constitutiveEndogenousCompatibility_conjugate` |
| ULF-EVM-1 proper-observer viability | `noncompactEscape_countermodel`, `nonclosedAdmission_countermodel`, `incoherentHorizon_countermodel` |

`lake build GaloisForLFunctions.HTGeometry.UniversalLawField` completes 11,633 jobs.  Axiom prints
for every added declaration report only `propext`, `Classical.choice`, and `Quot.sound`, several
needing fewer.  The remaining stage-2 cards and their exact missing statements are tracked in
`_STAGE3-SWEEP-LEDGER.md`.

## Session 2026-08-11 addition (Transverse Information Fusion Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-TIF-1 | Prime Boolean Schur capacity, Gibbs-damped Mass energy, finite Hankel determinant, pure-state transverse QFI, exact four-organ conservation, intervention response, finite joint reconstruction, and arbitrarily late prime-clock recurrence | `HTGeometry.PrimeBooleanMassHankelQuantumFusion` |

Direct foreground elaboration passes.  Foreground leaf build completes 8,675 jobs.  The module is
wired into `HTGeometry.UniversalLawField`; foreground umbrella build completes 11,659 jobs.
Repository formal lint and target forbidden-declaration scan pass.  Axiom prints for nine capstones
report only `propext`, `Classical.choice`, and `Quot.sound`.

Lean certifies the exact cross-organ law
`I_perp * ||j_sigma||^2 = 4 * pi^2 * det(H_1)`, its strict positive chamber, the finite-moment
reconstruction theorem, and the predicted recurrence shadow.  It contains no RH premise, Xi
specialization, computation certificate, project axiom, or cofinal-completion claim.

## Session 2026-08-11 addition (Quotient--Fusion Genesis Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-QFGM-1 | Pairwise and centered reconstruction of the shared-gauge genesis numerator, exact binary quotient--fusion conservation, nonnegativity, zero/compatibility classification, and binary partition-QFI conservation | `HTGeometry.SharedGaugeQuotientFusion` |

Direct foreground elaboration and the 8,676-job leaf build pass.  The module is wired into
`HTGeometry.UniversalLawField`, whose source elaboration passes.  Axiom prints for the seven main
theorems and the closed capstone report only `propext`, `Classical.choice`, and `Quot.sound`.

Lean proves the mechanism without denominators or side conditions:

```text
c1*c2*det(fused) - c2*(c1+c2)*det(block1) - c1*(c1+c2)*det(block2)
  = (c2*b1 - c1*b2)^2.
```

Thus quotient-after-fusion differs from fusion-after-local-quotient by one exact compatibility
square.  No computation certificate, project axiom, route endpoint, Xi specialization, RH premise,
or cofinal-completion claim occurs.

## Session 2026-08-11 addition (Source-Coherent Synchronization Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SCSM-1 | Global-intervention invariance, relative-response cocycle, anchor and modulo-diagonal reconstruction, source response-difference formation, synchronization-kernel classification, and exact equalizer selection | `HTGeometry.SourceCoherentInterventionSynchronization` |

Lean certifies that one source intervention acts diagonally across its organ packet; the complete
pairwise response reconstructs every local gauge modulo that global action; and a trivial
intersection of organ response-difference kernels turns global compatibility into zero-source
selection.  The capstone contains no target specialization or RH premise.  Together with
`SharedGaugeQuotientFusion`, it supplies the missing source-coherence premise behind the finite
three-organ fusion and fourth-organ QFI conservation law.

Direct foreground elaboration passes and the foreground leaf build completes 8,677 jobs.  Axiom
prints for eight main declarations report only `propext`, `Classical.choice`, and `Quot.sound`,
with several requiring fewer.

The module is wired into `HTGeometry.UniversalLawField`; the final foreground umbrella build
completes 11,670 jobs.  Repository formal lint and generated-index checks pass.

## Session 2026-08-11 addition (Inverse-Response Ward Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-IRWM-1 | Inverse derivative law, mixed Riccati fusion, exact mixed-acceleration reconstruction, affine product boundary, strict and anomalous Ward conservation, strict-trace grade blindness, and faithful-square selection | `HTGeometry.InverseResponseWardMechanics` |

The mixed identity is

```text
D1 (M * D2 E) + (M * D1 E) * (M * D2 E) = M * D1 (D2 E)
```

under the sole formation law `M * E = 1`.  No commutation of derivations is assumed.  Under mixed
affinity, the fused product is an exact derivative; every additive reporter annihilating that
derivative kills the product.  The anomalous identity identifies the general value as source
acceleration trace minus boundary anomaly.  Lean also proves that a strict linear Ward reporter
vanishes on every nonzero derivation eigengrade.  The module contains no arithmetic realization or
RH premise.

Direct leaf elaboration and the 1,347-job foreground leaf build pass.  Axiom prints for inverse
response, mixed reconstruction, strict/anomalous Ward balance, grade blindness, faithful-square
selection, and the capstone report only `propext`, `Classical.choice`, and `Quot.sound` (most omit
`Classical.choice`).  Generated-index validation and formal lint pass.  The module is wired into
`HTGeometry.UniversalLawField`; the final foreground umbrella build completes 11,672 jobs.

## Session 2026-08-11 addition (Reciprocal-Character Real-Form Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-RCRFM-2A | Split/compact common quadratic jet, Euler--virial conservation, coercivity, radical, and finite-packet conservation | `HTGeometry.ReciprocalCharacterRealFormMechanics` |
| ULF-RCRFM-2B | Squared-clock positive Prony spectrum, all-future-moment reconstruction, and fixed-clock weight reconstruction | `HTGeometry.ReciprocalCharacterRealFormReconstruction` |
| ULF-RCRFM-2C | Literal Gauss virial realization, prime-harmonic admission lower bound, summability classification, and RH selection equivalence | `RHTower.GaussReciprocalCharacterAdmission` |

Direct foreground elaboration passes for all three leaves and umbrella source.  Final foreground
umbrella build completes 11,798 jobs.  Axiom prints for ten capstones report only `propext`,
`Classical.choice`, and `Quot.sound`.  Target scans contain no `sorry`, `admit`, project `axiom`,
`opaque`, or `unsafe` declaration.

Lean proves that one reciprocal character packet has a common split/compact quadratic jet, that
its virial current is exactly Euler differentiation of split energy, and that its finite moment
packet reconstructs squared clocks and weights.  In literal Gauss realization it also proves

```text
Summable (gaussHodgeMassCurrent m q)
  <-> primeDepthBVWoldXiCenteredRate q.1 = 0
```

and universal summability over Xi-zero copies iff `RiemannHypothesis`.  Latter is exact selection
gate, not RH proof: no independent source theorem forcing universal summability is assumed or
proved.

Repository-wide formal lint reached unrelated pre-existing/concurrent umbrella error:
`CriticalSchurIdealInertiaTransport` is not imported by theorem-area umbrella `HTGeometry`.
No file outside this card's scope was changed to mask that failure.

## Session 2026-08-11 addition (Multi-parent Tropical-Projective Work)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-DDEM-TPW-1 | Finite-family maximum-work formation, tropical-projective zero law, common-gauge invariance, finite-history conservation, closed-work positivity, observer-memory reconstruction, affine clock width, centered selection reduction, and recurrent prime observer with linearly open projective work | `HTGeometry.ConstitutiveTropicalProjectiveWork` |

Direct foreground elaboration passes.  The module is wired into
`HTGeometry.UniversalLawField`; final foreground umbrella build completes 11,799 jobs.  Formal lint
passes.  Axiom prints for five capstones report only `propext`, `Classical.choice`, and `Quot.sound`.

Lean closes the multi-parent open core left by the two-action total-variation theorem.  It also
certifies the withheld recurrence prediction: arbitrarily late finite-prime phase returns coexist
with a projective work lower bound equal to elapsed time times the reconstructed prime-clock span.
The centered zero-width equivalence is an exact RH selection reduction, not an RH proof; no source
theorem forcing profile descent at Xi zeros is assumed.

## Session 2026-08-11 addition (Adelic Plücker History Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-APHM-1 | Plücker exchange reconstruction, exact complete-height growth, all-place conservation, bounded-height/periodic-history classification, static Gram observer, and linearly open adelic history | `HTGeometry.AdelicPluckerHistoryMechanics` |

One diagonal number-field intervention evolves every maximal-minor packet, while normalized
adjacent-minor cross-ratios recover its relative characters.  Every recovered character lies in
the kernel of the Deninger place sum.  Complete exchange height grows exactly linearly and is
bounded exactly when the normalized history is periodic.  Under a unitary complex embedding, the
same intervention leaves the full Gram matrix exactly static while a non-torsion exchange response
has strictly positive linear Weil-height growth.

Direct foreground elaboration and the foreground leaf build pass.  The module is wired into
`HTGeometry.UniversalLawField`; final foreground umbrella build completes 11,817 jobs.  Axiom
prints for the capstones report only `propext`, `Classical.choice`, and `Quot.sound`.  Repository
formal lint and generated-index checks pass.  No RH premise or divisor specialization occurs.

## Session 2026-08-11 addition (Global Formation-Properness Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-GFPM-1 | Source-generated formation scaling, canonical reporter coercivity, divergent scale-orbit work, bounded-orbit neutrality, and bounded dominating-work selection | `HTGeometry.ConstitutiveGlobalFormationProperness` |
| ULF-GFPM-2 | Exact convergent class-law reporter pushforward, Bernoulli symmetric-KL identification, two-sided data-processing domination, and full-source bounded-work selection | `HTGeometry.ConstitutiveGlobalFormationInformationProperness` |

Lean certifies a global producer mechanism.  Existing source exchange generates the central
fugacity formation; literal depth dilation amplifies its size; the canonical least-prime,
least-depth reporter has exact log-odds work with a linear coercive lower bound.  Every nonzero
scale orbit therefore has work tending to infinity, and bounded scale-orbit work is equivalent to
neutral formation.  More generally, any uniformly bounded global work dominating the reporter
forces neutrality; exact vanishing is unnecessary.  The second module closes this interface for
the actual convergent source class law: its least-mode occupation marginal is exactly Bernoulli,
symmetric Bernoulli `klDiv` is the reporter work, and two-sided data processing bounds it by full
class-law Jeffreys work.  A finite uniform bound on that full extended-real work along every source
scale is equivalent to neutral formation.

Both modules elaborate in direct foreground runs and are wired into
`HTGeometry.UniversalLawField`.  Full-source work is allowed to be `⊤`; the boundedness hypothesis
requires one finite `ENNReal` upper bound and therefore hides no finiteness assumption.  Final
foreground umbrella build completes 11,825 jobs.  Formal lint passes.  Scratch axiom prints for the
class-law pushforward, exact Bernoulli KL formula, data-processing domination, and full-source
selection theorem report only `propext`, `Classical.choice`, and `Quot.sound`.  No RH premise,
divisor specialization, or target-route receiver occurs.

## Session 2026-08-11 addition (Static-Heterogeneity Observer Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-SHPC-3 | Positive finite rate-mixture posterior curvature, exact response balance, rigidity, and finite-window properness | `HTGeometry.ConstitutiveStaticHeterogeneityObserver` |

Lean certifies the mechanism extracted from arXiv:2604.15084 without importing its specific
first-passage model. Elapsed time tilts a finite static rate packet; posterior mean rate dissipates
exactly by negative posterior variance; the local apparent exponent obeys
`alpha' = mean - t * variance`; and a positive rate floor forces every bounded exponent sublevel
into a bounded clock interval. Zero variance is equivalent to collapse of all active rates.

Direct foreground elaboration and the 8,699-job leaf build pass. The module is wired into
`HTGeometry.UniversalLawField`; final foreground umbrella build completes 11,829 jobs. Formal lint
passes. Scratch axiom prints for eight capstones report only `propext`, `Classical.choice`, and
`Quot.sound`. No RH premise or route-specific zero specialization occurs.

## Session 2026-08-11 addition (Constitutive Passive-Cycle Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-CDM-1 | Exact heterogeneous defect composition, passivity equivalence, passive two- and three-cycle rigidity, strict-neutral selection, and positive-defect impossibility | `HTGeometry.ConstitutivePassiveCycleMechanics` |

Direct foreground elaboration and the 1,666-job leaf build pass.  The module is wired into
`HTGeometry.UniversalLawField`; final foreground umbrella build completes 11,830 jobs.  Scratch
axiom prints for the headline theorems report only `propext`, `Classical.choice`, and `Quot.sound`.
Lean certifies the abstract rigidity mechanism; it does not construct the literal source-generated
passive compression/reconstruction required for RH selection.

## Session 2026-08-11 addition (Constitutive Interaction-Spectrum Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ISDM-1 | Source parity generates a normalized product interaction-work ledger; marginals reconstruct activation; degree truncation is passive; hidden work obeys a Markov bound and equals one quarter of lost coherent QFI; prime formation is summable exactly above exponent one; reciprocal reflection preserves phase exactly at exponent one | `HTGeometry.ConstitutiveInteractionSpectrumMechanics` |

Direct foreground elaboration and the 2,350-job leaf build pass.  The module is wired into
`HTGeometry.UniversalLawField`; final foreground umbrella build passes.  Scratch axiom prints for
the headline theorems report only `propext`, `Classical.choice`, and `Quot.sound`.  The paper's
explicit Chebyshev fixed-degree escape limit remains outside this certified core.

## Session 2026-08-11 addition (Essential Formation Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-EFM-1 | Summable-work equivalence preserves global formation phase; finite corrections are inessential; reciprocal prime formations are essentially equivalent exactly at exponent one; no summable compensator exists off criticality; any three-leg essential source bridge forces exponent one | `HTGeometry.ConstitutiveEssentialFormationMechanics` |

Direct foreground elaboration and the 2,351-job leaf build pass.  The module is wired into
`HTGeometry.UniversalLawField`; final foreground umbrella build completes 11,832 jobs.  Scratch
axiom prints for headline theorems report only `propext`, `Classical.choice`, and `Quot.sound`.
Lean certifies the selection mechanism, not the open global source-duality producer or RH.

## Session 2026-08-12 addition (Formation-Factorization Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-FFM-1 | Exact semantic/lineage common recovery, scaled-idempotent formed carrier, pointwise certificate conjugacy, certificate-independent recovery ghosts, first-order ghost recurrence, and one-mode Witt comparison | `HTGeometry.ConstitutiveSemanticLineageWittFusion` |

Lean certifies that every formed carrier `P_A=Q_AB_A` satisfies `P_A^2=|ι|P_A`, every certificate
family is pointwise conjugate to the identity family, and every recovery ghost is
`|ι|^(n+1)I`.  Thus carrier polynomial/ghost data are exactly certificate-blind; constitutive
information can survive only in the factorization fibre. Direct elaboration and the leaf build
pass. The module is wired into `HTGeometry.UniversalLawField`; final foreground umbrella build
completes 11,838 jobs. Scratch axiom prints report only `propext`, `Classical.choice`, and
`Quot.sound`. No RH premise or route-specific specialization occurs.

## Session 2026-08-12 addition (Self-dual Factorization Geometry)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-FFM-2-CORE | Exact recovery/gauge equivalence, adjoint-reversal fixed locus, reciprocal-Gram conservation, and finite Cartan-packet bounded-work selection | `HTGeometry.ConstitutiveSelfDualFactorizationGeometry` |

The module proves that exact recovery pairs form a gauge torsor rather than a scalar invariant,
adjoint reversal fixes exactly balanced gauges, and the two leg-Gram reporters multiply to the
identity.  Its Cartan work is nonnegative and reversal invariant; a finite packet with uniformly
bounded work along all natural formation depths has zero radial rate. Direct elaboration and the
8,656-job leaf build pass. The module is wired into `HTGeometry.UniversalLawField`. Scratch axiom
prints report only `propext`, `Classical.choice`, and `Quot.sound`. No RH premise or route-specific
specialization occurs. Final foreground `HTGeometry.UniversalLawField` build completes 11,840
jobs.

## Session 2026-08-12 addition (Involutive Formation-Properness Mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-PFM-2 | Functional-equation action lift through split formation, strict action composition on formed laws, involution, common-recovery KL/Jeffreys isometry, and two-sheet swap | `HTGeometry.ConstitutiveFunctionalEquationPacketLift` |
| ULF-RFTM-3B | Positive reciprocal-packet reconstruction and complete bi-axis logarithmic-work properness | `HTGeometry.ConstitutivePositiveFormationProperness` |
| ULF-IFPM-1 | Finite escort reflection response, exact KL/Jeffreys work, complete-amplification properness, and hidden-information escape under bounded observation | `HTGeometry.ConstitutiveFiniteEscortFormationProperness` |

Lean certifies one common mechanism in stochastic, positive-matrix, and finite-information charts.
Common recovery is exactly information-neutral; reflection alone does not select.  Complete
amplification makes reflected work proper, and every bounded observer of a nonconstant reflected
escort family forces an unbounded hidden-loss sequence.  Direct elaboration and all three leaf
builds pass.  Modules are wired into `HTGeometry.UniversalLawField`; final foreground umbrella
build completes 11,848 jobs.  Scratch axiom prints for capstones report only `propext`,
`Classical.choice`, and `Quot.sound`.  Scoped scans contain no forbidden declaration.  No RH premise
or zero specialization occurs; literal source-generated bounded-work conservation remains open.

## Session 2026-08-13 additions (critical-locus Hessian classification, Θ4 cone engine, Law 6, INV3.2)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-FIELD-2 Θ2(i)–(v) | Exact multi-splitting separation; general and real weight with the conjugation bridge; per-zero detector necessity; diagonal Hessian and second-order determination; composite chain law and composite necessity | `RHTower.CriticalLocusHessianClassification` |
| ULF-FIELD-2 Θ3.1 | The explicit-formula line kernel as a Lean integral and the shadow pairing `⟨Δν,h⟩ = ∫ h·4cos(γx)(cosh(tx)−1)`, single/real/multi forms against `shadowDensity` | `RHTower.CriticalLocusHessianClassification` |
| ULF-FIELD-2 Θ4-A | Cone fullness of the configuration moves (insertions/deletion/quadruples) by strip Phragmén–Lindelöf + harmonic minimum principle; σκ collapse of pair and quadruple values | `RHTower.CriticalLocusConeFullness` |
| ULF-MECH-1 Law 6 | Self-closure: outputs factoring through displacement-even configuration families are even; odd factoring functionals vanish; quadruple/multi-splitting instantiations; no-detector corollary | `RHTower.OddCoordinateSelfClosure` |
| ULF-INV-3 (INV3.2) | The 3–4–1 log-derivative identity and its termwise nonnegativity | `RHTower.PolePurchaseLogDerivIdentity` |

All four modules wired into `GaloisForLFunctions.RHTower`; final module builds green (11,558
jobs); forbidden-token scans clean; `#print axioms` on all 25 audited capstones reports exactly
`[propext, Classical.choice, Quot.sound]`.  The `ring`-related notes in the build log are
pre-existing info-level messages in unrelated replayed modules.

Card movements: `pole-purchase-escape-and-collision-gap-law.md` promoted to
`3-formalized/universal-law-field/` (2026-08-13).  ULF-FIELD-2 stays at stage 2 pending Θ4's
exact-hitting research (hostile audit found the recorded Step 1/Step 2 proof gaps; repair route
and residual open point recorded on the card).  New reusable infrastructure: the reality-symmetry
conjugation bridge for `deriv`/`iteratedDeriv 2`/`AnalyticAt`, and the harmonic cone-fullness
pattern over the Bottcher min/max principle layer.

## Session 2026-08-13 addition (finite-amplifier frame)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-INV-7 | The abstract pole-purchase frame: master bound from (P1)–(P3), zero exclusion, the (INV7.1) width cap, the (INV7.3) threshold, the ratio-controlled constant, multi-σ and positive-average stability, and ρ-finiteness (cosine discrete sampling on the circle, dual averaging on every finite abelian group, and the separating-finite-quotient reduction for general supports) | `HTGeometry.FiniteAmplifierFrame` (+ pre-existing `HTGeometry.FiniteAmplifierPatternCap`) |

Formalization corrections recorded on the card: Theorem 2.1.1's "compactness" proof replaced by
the averaging mechanism; frame axiom (P3) sharpened to the two-sided channel bound for signed
patterns.  All capstones axiom-clean; module build green; card promoted to `3-formalized/` with
Fejér's exact extremal value and f.g.-abelian residual finiteness recorded as cited-classical
inputs per the card's own disclaimers.

## Session 2026-08-13 addition (inverse-theory graph witness)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-INV-5 Thm B | The non-Ramanujan independence witness: the prism `C₁₆ × K₂` with certified 3-regularity, exact mean-zero cosine Rayleigh data, the `50 > 49` margin, operator symmetry, the Laplacian square identity with its equality analysis, an adjacency eigenvalue strictly inside `(2√(d−1), d)`, the Perron pair, and the bundled capstone | `RHTower.InverseTheoryGraphWitness` |

Card promoted to `3-formalized/` with Theorems A/C/D recorded as cited-classical /
in-tree-cited / synthesis per the card's own claim boundaries.  Third promotion of
2026-08-13.

## Session 2026-08-13 addition (positive-face compression)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-RFM-PFC | Fixed positive Gram rays are pointwise bounded exactly when the leading composite vanishes; full subleading energy then survives; simultaneous-family and injective-leading boundaries; explicit divergent diagonal fourth-branch witness | `HTGeometry.PositiveFaceCompression` |

This theorem falsifies the frozen regularization trilemma by an unconditional positive fourth
branch: carrier compression to a leading null face. Direct elaboration and the 8,655-job leaf build
pass. The module is wired into `HTGeometry.UniversalLawField`; final foreground umbrella build
completes 11,861 jobs. Project lint passes. Scratch axiom prints report only `propext`,
`Classical.choice`, and `Quot.sound`. No RH premise or route-specific specialization occurs.

## Session 2026-08-13 addition (entropic alternating formation mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-EAFM-1 | Common-conditional marginal repair, exact KL Pythagoras, arbitrary finite-history action conservation, exact and approximate recurrent stationarity, functional repair reflection, and exact positive gauge radical | `HTGeometry.ConstitutiveEntropicAlternatingFormation` |

Lean certifies an exact Sinkhorn/Bregman bridge across allocation, information, reflection, recurrence,
and quotient properness. Failure-driven repairs accumulate an exact nonnegative KL action; a closed
finite history with finite target divergence forces every repair step to be stationary. Positive
bipartite formation has exactly one global potential gauge. More generally, any cofinally
approximately recurrent real formation potential with nonnegative exact step action has zero action
at every step. Formation transposition exchanges its two repair laws while preserving energy.
Whole-corpus hostile audit subsequently demoted the interpretation from first field mechanism to
`[BRIDGE] [NOT FIELD CORE]`: the earlier abelian-relaxation theorem already gives a stronger
source-endogenous legality/repair/completion/history/work mechanism. The Lean result itself is
unchanged.
Direct leaf build completes 3,492 jobs; the wired `HTGeometry.UniversalLawField` umbrella completes
11,862 jobs. No RH
premise, route endpoint, computation certificate, added axiom, or enlarged heartbeat occurs.

## Session 2026-08-14 addition (common-recovery cocycle mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-RCM-1 | Exact recovery packets and KL isometry; finite periodic-data Livsic classification; canonical harmonic ledger and sharp global/cyclewise Hodge work; primitive-period return law and bounded-history rigidity; skew-lift conjugacy; joint reconstruction; sandpile local/cumulative work; involutive two-cycle consequence | `HTGeometry.ConstitutiveRecoveryCocycleHolonomy` |

Formalization exposes literal periodic-orbit statements in addition to the efficient global-order
Reynolds encoding, so primitive cycle holonomy, return work, and Hodge minimum are not weakened.
Direct elaboration and targeted leaf build pass; module is wired into
`HTGeometry.UniversalLawField`.  All audited capstones depend only on `propext`,
`Classical.choice`, and `Quot.sound`.  No computation certificate, forbidden declaration, RH
premise, or route-specific assumption occurs.

## Session 2026-08-14 addition (nonabelian recovery cocycle mechanics)

| ID | Theorem | Lean modules |
|---|---|---|
| ULF-RCM-2 | Primitive-cycle holonomy conjugacy classification; exact conjugacy-word and balanced-square work minima on actual marked cycles; refinement laws; common-recovery KL isometry; schedule commutator genesis; finite recurrence with linearly open marked action; unitary Gram blindness; automorphic reverse-cycle invariance; joint reconstruction signature | `HTGeometry.ConstitutiveNonabelianRecoveryHolonomy`, `HTGeometry.ConstitutiveConjugacyWordWork`, `HTGeometry.ConstitutiveNonabelianRecoveryWork` |

Formalization uses primitive periods `orderOf (T.cycleOf s)`, avoiding the mathematically invalid
replacement by global-permutation-order holonomy powers.  Word length is constructed as the least
length of an actual word over finite symmetric generating data; conjugacy minima and balanced
factorizations are proved and attained rather than assumed.  Direct checks, targeted leaf builds,
and wired `HTGeometry.UniversalLawField` elaboration pass.  Capstones depend only on `propext`,
`Classical.choice`, and `Quot.sound`; scoped forbidden-declaration and computation scans are clean.

## Session 2026-08-14 addition (complex-time Euler-shell generation)

| ID | Theorem | Lean modules |
|---|---|---|
| ULF-GRM-3 / CTG.1–CTG.16 | Finite and summably admitted complex-time generation; exact covariance response; Markov mean/Fisher conservation, data processing, equality classification, and strict-amplification exclusion; literal marked-shell source ratio, Gibbs shift, phase reporter, all-order centered-moment tower, zero straight radius, exact negative lifetime, wall divergence, and four-organ fusion | `HTGeometry.ComplexTimeGenerativeMechanics`, `HTGeometry.ComplexTimeEulerShellGeneration` |

Direct source checks, targeted shell-leaf build, and wired `HTGeometry.UniversalLawField`
elaboration pass.  Capstone axiom prints report only `propext`, `Classical.choice`, and
`Quot.sound`; scoped forbidden-declaration and computation scans are clean.  Existing
`ConstraintMotiveRelativity.MarkedEulerShellWall.normalization_wall` supplies the physical
half-density beyond-chart obstruction.  RH selection remains conditional on the explicitly
unconstructed positive arithmetic Markov realization.  Whole-corpus lint reaches only four
unrelated `RHTower` umbrella-ownership failures.

## Session 2026-08-14 addition (full bipolar admission and infinite alternation)

| ID | Theorem | Lean modules |
|---|---|---|
| ULF-LSM-7 | Least closed-equivalence analytic hull; exact algebraic/analytic conflict and finitely-supported Dirac-TV laws; closed bounded alternation with first-shell depth divergence; exact two-ended source model, global three-class/total-admission split, finite interval class, continuous finite reporters, pointwise/non-equicontinuous limit, sharp half-gap, endpoint TV erasure, and literal minimal `2m` depth for `(-m,m)` | `HTGeometry.ConstitutiveClosedAdmissionHull`, `HTGeometry.ConstitutiveBoundedAlternation`, `HTGeometry.ConstitutiveTwoEndedAdmissionCriticalShell` |

All previously paper-only clauses are closed without added premises. Direct source checks, three
targeted leaf builds, and wired `HTGeometry.UniversalLawField` elaboration pass. Capstone axiom
prints report only `propext`, `Classical.choice`, and `Quot.sound`; scoped forbidden-declaration and
computation scans are clean. Repository lint reaches only unrelated shared `RHTower`
umbrella-ownership failures.

## Session 2026-08-14 addition (formation-depth compact properness)

| ID | Theorem | Lean modules |
|---|---|---|
| ULF-FDPM-2 | Exact source-depth coercivity, joint reconstruction, cofinal-tail control, bounded expanding-orbit selection, complete-resolution graph admission and mixer conservation; closed depth-generator graph; lower-semicontinuous gauge; exact finite-gauge intersection; ambient and graph-domain compact sublevels; natural-level exhaustion | `HTGeometry.ConstitutiveFormationDepthProperness`, `HTGeometry.ConstitutiveFormationDepthCompactness` |

The former paper-only topological clause is now fully Lean-closed. Finite coordinate heads give
uniform `ell^1` approximation from the sharp depth-work tail bound; continuous finite gauges give
closed sublevels, hence compactness. Direct source elaboration, targeted compactness-module build,
and wired `HTGeometry.UniversalLawField` elaboration pass. Capstone axiom prints report only
`propext`, `Classical.choice`, and `Quot.sound`; scoped forbidden-declaration and computation scans
are clean.

## Session 2026-08-14 addition (asymptotic law-core mechanics)

| ID | Theorem | Lean module |
|---|---|---|
| ULF-ALCM-1 | Nonempty compact-convex tail-law formation; exact continuous-affine exchange; common-recovery reconstruction; involutive functional-equation action and information-neutral lift; approximate-kernel and approximate-fixed exactification | `HTGeometry.ConstitutiveAsymptoticLawCore` |

Scratch and tree foreground elaboration pass. The targeted leaf build completes 1,781 required
jobs and produces the missing `.olean`; no area, umbrella, or project build was run. Headline axiom
prints report only `propext`, `Classical.choice`, and `Quot.sound`. Repository lint reports no
module-local defect; its five ownership errors concern unrelated concurrently added modules. The
module is wired into `HTGeometry.UniversalLawField`. This certifies formation/exchange/exactification
kinematics, not the still-open probability normal/corona properness law or an RH selector.
