# Universal-law corpus audit

Status: working internal audit. Not manuscript prose.

## Candidate law: acquisition--completion duality

A singular, unbounded, rigged, or asymptotic completion is not adequately
modelled by a total map.  Its universal datum is a partial quotient

`D subset X --pi--> Q`,

where `D` is the source-admission domain and `pi` is the observation on that
domain.  Exact global recovery of a target `chi : X -> C` has two independent
gates:

1. **admission:** every relevant source point belongs to `D`;
2. **separation:** `K_pi subset K_(chi|D)`.

This is the admission--separation law.  Postprocessing preserves `D` and can
only enlarge `K_pi`; it can solve neither a missing source-domain estimate nor
an erased target distinction.

For an observation `f : X -> Y`, let

`K_f = {(x,y) : f(x)=f(y)}`.

For an arbitrary heterogeneous family of channels `tau_j : X -> T_j`, a
target `chi : X -> C` is exactly recoverable on the attained joint range of
`(pi,(tau_j)_j)` if and only if

`K_pi intersect (intersect_j K_tau_j) subset K_chi`.

On an admitted domain, a target factors through an observation exactly when every
collision of the observation is a collision of the target. Postprocessing can
only enlarge a kernel pair. It can never recreate a distinction already
collapsed by completion.

Reflection supplies the RH-specific orientation form. If `sigma^2 = 1`,
`pi sigma = pi`, and `chi sigma = -chi`, then `chi` cannot factor through
`pi` unless `chi = 0`. Every sufficient transverse source channel must
separate `x` from `sigma x` wherever `chi(x) != 0` and, for a real scalar
channel, must have nonzero reflection-odd part there.

In a commutative ring the separation obstruction has the sharper identity

`(1-epsilon)(1+epsilon)=0`, `epsilon^2=1`.

Thus the anti-invariant sector is killed by the reflection-symmetric channel.
If `2` is regular, nontrivial orientation is equivalent to nonregularity of
that symmetric channel.  This does **not** mean orientation is intrinsically
singular.  Before symmetric completion, an involution on a module with
invertible `2` has the canonical faithful decomposition

`v = (v + C v)/2 + (v - C v)/2`.

The invariant and anti-invariant summands are complementary.  Singularity is
the price of reconstructing the second summand *from the first after it has
been discarded*, not a property of the source orientation coordinate itself.

Reflection therefore gives an exact trilemma at every nonzero odd charge:

1. admit both reflected source points and retain an anti-invariant channel;
2. admit both but identify them, making orientation unrecoverable;
3. use an invariant recovering completion only by excluding at least one
   member of the reflected pair from its regular domain.

Topology and asymptotic filtration enrich, rather than replace, this law:

- dense completion fibres force every separated downstream reporter whose
  pullback is continuous at one point to be constant;
- an exact linear sewing from an all-orders-flat source germ to a nonzero
  finite-grade target has operator norm larger than every finite inverse Rees
  order.

One sentence: **completion has two irreversible gates--source admission and
fibre separation; a target must pass both before postprocessing, or recovery
is impossible, discontinuous, or singular beyond every finite order.**

### Maximal quotient and positive dual

The recurrence corpus exposes a missing positive half of the law.  For a
family of reporters `F = (f_i)_i`, define

`x ~_F y iff forall i, f_i(x)=f_i(y)`.

Then `X / ~_F` is the maximal accessible quotient: every `F`-recoverable
target factors uniquely through it, and every target that varies on one
`~_F`-class is inaccessible.  If the reporters separate the classes of a
declared symmetry quotient, this proves a sharp statement: the completion
loses exactly that symmetry and no further information.  This maximality is
the positive theorem paired with the no-go.

The recurrence realization is exact.  Survival-return experiments factor
through the reflection-even clock law, and balanced two-level probes with all
gaps distinguish exactly those reflection-even quotients.  Thus recurrence
loses time orientation and universally loses no additional clock
information.  Separately, along a countable affine spectral ray, outside one
countable crossing set the protected relation lattice is the intersection of
the bare and interaction relation lattices.  Its compact annihilator is the
completed future hull.  In finite rank, loss of one independent relation is
therefore gain of one independent completed phase direction.

The primal partial quotient classifies exactly what completion admits and can
still report; the dual protected-relation lattice classifies exactly what
remains constrained.  Reflection orientation is the distinguished
anti-invariant source coordinate.  Singular support, divergent energy, or
beyond-all-orders sewing is the defect created when that coordinate is forced
through a completion which does not regularly retain it.

## Exact formal theorem surface

Abstract set/family law:

- `HTGeometry/CompletionKernelPairTransversalityLaw.lean`
  - `factorsThroughRange_iff_kernelRefines`
  - `observationFamilyRecovers_iff_factorsThroughRecordRange`
  - `mapKernelPair_mono_of_factorsThrough`
  - `oddTarget_eq_zero_of_factorsThrough_invariantCompletion`
  - `transverseChannel_separates_reflection_of_oddCharge_ne_zero`
  - `reflectionOddPart_ne_zero_of_jointlyRecovers`
  - `downstreamReporter_constant_of_dense_completionFibers`
- `HTGeometry/PartialCompletionAdmissionSeparationLaw.lean`
  - `partialCompletion_globallyRecovers_iff_admission_and_kernelRefines`
  - `partialCompletion_kernelPair_mono_postprocess`
  - `oddTarget_eq_zero_on_admitted_of_invariantPartialCompletion`
  - `partialCompletion_separates_reflection_of_oddCharge_ne_zero`

Maximal-quotient and protected-relation realization:

- `RHTower/ObserverRecurrenceDistributionLaw.lean`
  - `clockOrientationQuotient_eq_iff_twoLevelMoments`
  - `clockOrientationQuotient_eq_iff_allReturnLaws`
- `RHTower/StationaryRecurrenceQuotientLaw.lean`
  - `clockSampledSpectralReturnProbabilityMeasure_eq_recurrenceQuotient`
- `HTGeometry/AffineCouplingProtectedRelationLaw.lean`
  - `projectiveCharacter_affineRelation_iff_common_of_not_mem`
  - `projectiveRelationSet_affine_eq_common_of_not_mem`
- `HTGeometry/CountableProjectiveFutureUniversalityLaw.lean`
  - `screwHull_anchoredProjectiveGap_eq_univ`
  - `completeSaturatedProjectiveRecurrenceLaw`

Algebraic singular-support law:

- `HTGeometry/ReflectionOrientationSingularSupportLaw.lean`
  - `reflectionOrientation_mul_hyperbolic_eq_zero`
  - `reflectionOrientation_ne_one_iff_hyperbolic_not_regular`
  - `antiInvariant_eq_zero_of_hyperbolic_smul_injective`
- `HTGeometry/PrimeOrientationHadamardSingularSupportLaw.lean`
  - `primeOrientationHadamardTail_positive_iff_hyperbolic_regular`
  - `primeOrientationHadamardTail_nontrivial_has_hyperbolic_annihilator`
- `RHTower/Deninger/DeningerOrientationDescent.lean`
  - `deningerOrientation_isCompl`
  - `deningerOrientation_eq_zero_of_parts`

Topological and filtered consequences:

- `HTGeometry/FiniteGaugeTailCharge.lean`
- `HTGeometry/TailQuotientSeparationLaw.lean`
- `RHTower/AsymptoticTypeSuperselection.lean`
  - `reesEssentialSewingCost_beyondEveryFiniteOrder`
  - `reesExactSewingOperatorNorm_beyondEveryFiniteOrder`
- `RHTower/Hedenmalm/HedenmalmPrimeNormalSubLogSquareClassification.lean`
  - `primeClockVerticalEnergy_le_four_mul_harmonic`
  - `hedenmalmPrimeNormalSubLogSquare_iff_im_eq_zero`

## Riemann realization of the one target charge

Use

`sigma(rho)=1-conj(rho)`, `c(rho)=Re(rho)-1/2`.

Then `c(sigma rho)=-c(rho)`, while every reflection-invariant or squared
completion identifies the pair. The centered divisor character

`M_rho(z)=exp(z(rho-1/2))`

is a canonical transverse source channel because for every real `t != 0`,

`log |M_rho(t)| / t = c(rho)`.

Exact sources:

- `RHTower/RiemannComplexModularCharacterLaw.lean`
  - real-ray norm and exact charge recovery;
  - reciprocal reflection law;
  - principal Hurwitz phase;
  - escaping-quartet separation: fixed modular charge survives while all
    compact holomorphic jets, bounded Ward windows, reciprocal-square energy,
    and the continuum differential matroid lose the same off-line quartet.
- `RHTower/XiSourceModularTypeSuperselectionLaw.lean`
  - the same positive right-divisor charge appears as shell entropy,
    source-normal residue, Hurwitz phase, and every noncensoring compact-BV
    residue phase;
  - reflected prime-valuation sectors cannot be sewn by a finite-Rees
    operator; exact sewing norm dominates every inverse Rees power.
- `RHTower/EulerHedenmalmGammaStokesTransgression.lean`
  - literal first theta atom Mellin-transforms to the archimedean factor;
  - causal minus anti-causal Green modes equal the nonzero Gamma homogeneous
    character;
  - ordinary Euler multiplication annihilates this jump exactly at Xi zeros;
  - the nonvanishing character preserves Xi multiplicity.
- `RHTower/Hedenmalm/HedenmalmOrientationDivisorTransgression.lean`
  - translated logarithmic-current residue is the exact finite difference of
    Xi multiplicities;
  - every positive translation has infinitely many order jumps;
  - canonical Hedenmalm orientation therefore has infinite, multiplicity-exact
    singular support at every positive aperture.

This is the strongest coherent interpretation presently supported: the
missing RH coordinate is not another bounded invariant completion. It is a
reflection-odd, source-pointed character living on an infinite singular
carrier.

## Exact shadows versus realizations versus upstream walls

### Direct kernel-pair shadows

- finite-support and arbitrary erased-support quotient no-gos;
- recurrence-completion and finite-horizon indistinguishability;
- singular-grade and Hadamard-tail reporter collapse;
- deck/parity decider blindness;
- cofinite exact-blind data processing and finite reporter source
  discrimination;
- every squared/even reflection scalarization that identifies `rho` with
  `1-conj(rho)` while attempting to recover `c(rho)`.

Quantum recurrence supplies a sharp maximal-quotient instance, not merely a
further blindness example: the reflection-even clock quotient is sufficient
for every return law, and the family of balanced two-level reporters is
complete for that quotient.  It therefore proves both halves of the law:
orientation is lost, while every orientation-even clock coordinate remains
tomographically accessible.

These are direct instances once the relevant map and target are identified.

### Topological shadows

- finite-modification quotient has dense fibres and indiscrete coinduced
  topology;
- nonzero theta-null Hedenmalm positive forms have dense proper nonclosed
  ordinary-`L2` radical image and are not closable through ordinary `L2`;
- a proper closed invariant radical cannot contain a cyclic source family.

The Hedenmalm results are not literally quotient-fibre corollaries. They are
the linear/radical realization of the same dense-kernel consequence. Paper
must prove the specialization, not call it a corollary by analogy.

### Filtered shadows

- off-line reflected valuation sectors are all-orders-flat on one side and
  finite/half-normal on the other;
- finite-Rees-moderate sewing is impossible;
- exact sewing costs and operator norms exceed every finite inverse order;
- Fisher whitening/Gamma recovery has unavoidable unbounded gauge at the
  all-prime boundary.

These are quantitative enrichments of a target distinction lying outside the
regular completion kernel.

### Positive transverse realizations

- centered complex modular character;
- compact-BV residue phase and Hurwitz principal phase;
- source-normal cone residue and cofinal shell transfer entropy;
- Gamma Stokes jump before Euler annihilation;
- multiplicity-exact Hedenmalm divisor transgression;
- first-horizon zeta--Gamma/reciprocal-frequency pair: joint field recovery,
  Schwarzian intersection, and loss of nonconstant common observables beyond
  the first horizon;
- Wold--Poisson transport, Sonin--Calkin seams, and resolved Ward energies,
  once supplied with a surviving transverse character.

The last three consumer families are not consequences of the abstract law.
They are downstream realizations or tests of the source coordinate. Paper
must not advertise them as automatically proving orientation.

### Genuine upstream acquisition walls

The 18 primitive obstruction families from the full audit do not disappear.
Their disposition is:

| primitive wall | law disposition |
|---|---|
| first-clock eventual lower bound | upstream comparative-order/sign input |
| first-clock asymptotic Bohr | unitarity/limit acquisition; equivalent consumer |
| completed prime--Gamma sign | upstream one-sided orientation |
| prime--arch source positive form | upstream positivity |
| Hedenmalm Weil positive form | divisor criterion; requires sign |
| Hedenmalm mixed Fourier sign | upstream sign |
| continued two-pole passivity | upstream analytic sign |
| reduced tower dominance | comparative-order input |
| compact Thorin representation | upstream measure/sign/compactness input |
| Connes real-zero limit | spectral-reality consumer |
| Moebius critical cancellation | arithmetic cancellation input |
| Moebius half-decay | arithmetic quantitative input |
| Sonin prime--arch value transfer | source-to-consumer coupling input |
| dyadic prime-window subpower | arithmetic quantitative input |
| Suzuki Hermite--Biehler | global one-sided orientation input |
| moving-polynomial even factorization | positive factorization input |
| Xi Taylor core current | oriented current bound |
| Arakelov integral/contractive chamber | arithmetic-geometry input/consumer |

The universal law explains why downstream manipulations cannot manufacture
these missing signs. It does not prove them. This limitation is a required
honesty condition, not a defect to hide.

## Whole-corpus census evidence

Stable zero-omission census before adding the six previously unreachable
umbrella imports:

- 7,223 modules: 3,946 RHTower and 3,277 HTGeometry;
- 79,162 declarations, including 62,800 theorem/lemma declarations;
- 1,919 deterministic families;
- 688 RH obstruction clusters plus header in the generated TSV;
- 18 primitive obstruction families.

Most frequent obstruction mechanisms among the RH clusters:

- literal zero/divisor location: 327;
- positive-form/moment: 267;
- completed prime--archimedean sign: 183;
- finite-window/limit: 171;
- reflection phase: 158;
- analytic continuation: 107;
- spectral realization: 93;
- arithmetic cancellation/growth: 76.

Most frequent required capabilities:

- rigidity/classification: 639;
- comparative order: 508;
- sign/orientation: 393;
- arithmetic source: 334;
- quantitative bound: 208;
- positive kernel/form: 124;
- zero-location exclusion: 121;
- analytic continuation: 102;
- limit compactness: 95;
- reflection phase: 75.

Interpretation: corpus is not mainly missing another equivalence. It is
missing acquisition and regular survival of one-sided orientation. Kernel
transversality explains survival; singular-support and Rees laws classify the
only possible carrier; arithmetic sign/cancellation remains the true upstream
wall.

## Six previously umbrella-unreachable modules

All six were read and are now imported by the area umbrellas:

- `ReflectionOrientationSingularSupportLaw`
- `PrimeOrientationHadamardSingularSupportLaw`
- `ProjectiveHorizonActualSchwarzianDiamond`
- `EulerHedenmalmGammaStokesTransgression`
- `HedenmalmOrientationDivisorTransgression`
- `ZetaGammaProjectiveHorizonSchwarzianDiamond`

They materially strengthened the law. In particular, the first two give the
algebraic singular-support classification, the next pair gives exact
source/divisor transgression, and the Schwarzian pair gives a sharp positive
joint-observation lattice.

## Antagonist decision gate

Reject manuscript if it does any of the following:

1. calls elementary kernel-pair factorization novel;
2. claims Hedenmalm, Wold--Poisson, Sonin--Calkin, or Ward results are formal
   corollaries without an explicit specialization proof;
3. says modular characters are unitary unconditionally;
4. implies singular transversality itself excludes off-line zeros;
5. treats an RH equivalence as zero exclusion;
6. hides the 18 upstream sign/cancellation walls;
7. presents multiple independent “main theorems” instead of one law and its
   Riemann realization.

Publishable core, if retained after literature audit: a universal
orientation-before-completion theorem; its exact singular/topological/filtered
consequences; and the Riemann theorem identifying one centered modular charge
simultaneously in source-normal, shell, Hurwitz, BV, Gamma--Stokes, Hedenmalm
singular-support, and reflected-Rees charts.

## 2026-08-01 zero-omission delta reconciliation

Fresh stable mechanical census contains 7,889 modules, 84,490 declarations,
and 67,384 theorem/lemma declarations.  Previous checked census contained
7,839 modules.  The following disposition covers all 50 new modules; no
sampling was used.

### Direct strengthening of manuscript theorem

- `CommonCharacterFusionConservation`: finite codiagonal identity, kernel
  codimension, reciprocal signature, reflected action.
- `HighExponentShellFusionConservation`: exact common divisor, infinite
  relative differential fibre, finite signature conservation, nonclosable and
  Bessel infinite-fusion boundaries.
- `CCMFirstClockSourceFusionSuperselectionNoGo`: certified Route-J finite
  centered energy is lower order than squared fused bad mass; infinite regular
  Hilbert fusion fails independently.

These are now in Sections 4, 5, and 8.  They sharpen “breadth obstruction”
from an analogy to an exact finite/infinite theorem.

### Positive admission or separation realizations

- `StripHullSeparation`: central-line restriction is injective on the
  holomorphic vertical Bohr carrier.
- `DeningerKahlerRiemannFlowPurity`
- `DeningerKummerStalkTor`
- `DeningerMiddleFiber`
- `DeningerPacketFrobeniusQuotientNontrivial`
- `DeningerPrimeArithmeticCyclotomicComparison`
- `DeningerPrimePacketContinuousRestrictionGreen`
- `DeningerPrimePacketCyclotomicTowerAction`
- `DeningerRealApexEndpoint`
- `DeningerReesJetTower`
- `DeningerSUnitEndpointPage`
- `DeningerStationaryKahlerGerm`
- `SchattenDoubleCommutatorRelocation`
- `XiPrimeMarkedPhysicalEndpointBoundaryGrowth`
- `XiPrimeMarkedPhysicalEndpointBoundaryNuclearObstruction`
- `XiPrimeMarkedPhysicalEndpointCorrectionTraceClass`

These occupy the positive side of the same ledger: injective strip
restriction; derived transgression; exact nontrivial cyclotomic quotient;
faithful tower action; twisted real orientation; flow purity; source-defined
Green form; Rees jet character; trace-class relocation and valuation
correction.  The manuscript now states both survivors and their exact
remaining acquisition gates.

### Regular Gamma/jet carrier boundary

- `DigammaRationalFieldDatum`
- `EventualRelationFinitePhaseLaw`
- `FullJetPolyNonzeroDatum`
- `GammaFieldCoefficientLaw`
- `GammaFieldRatDatum`
- `GammaShapeDominantResidue`
- `RatCoeffClearing`
- `RatCoeffJetPoly`
- `UpperEndGammaElement`

Together they prove, under the stated strip almost-periodic hypotheses, that
nonzero Gamma-field coefficients do not hide an infinite relation: an
eventual relation collapses to a finite constant-coefficient phase law.
This is a conditional specialization of separation, not a blanket Gamma
no-go.  The manuscript uses exactly that scope.

### Terminal consumers and exact loss

- `CCMSharpPrimeWindowSquareEnergyWidthCollision`
- `CCMSharpPrimeWindowSquarePositiveExcessDuality`
- `SuzukiCompactCorePhaseUniversality`
- `SuzukiEdgeDataInterface`
- `SuzukiIntervalEdgeData`

Sharp-window square energy collides exactly with classical Chebyshev width and
remains a terminal RH criterion.  Dense Suzuki compact-core ranges erase all
bounded boundary schedules in the strong Cayley/resolvent limit, while the
edge-data interface is freely inhabitable and therefore does not acquire an
arithmetic source.  Both are direct admission/separation instances.

### Supporting geometry, analysis, and recurrence/complexity laws

- `CompactIntervalL2Pairing`
- `CuspedHorizonHomotopy`
- `DiagonalProjectorClockPackingLaw`
- `FinTwoProjectorClockComplexityLaw`
- `IntervalL2Density`
- `InverseJetNumerator`
- `MetricEntropyRecurrenceAmplificationLaw`
- `NerveHomotopy`
- `NerveProductComparison`
- `NestedExhaustionPhaseUniversality`
- `OneDeepFibreBound`
- `PeriodicMetricEntropySeparationLaw`
- `SpectralSliceComplexityAmplificationLaw`
- `StarProjectionPeriodicComplexityLaw`
- `FiniteAndersonChoiComplexityAlternationLaw`
- `StaticChoiComplexityAlternationLaw`
- `StaticChoiTraceDistanceLaw`

Compact-interval, inverse-jet, nerve, and cusp results are infrastructure for
already-classified source maps.  Recurrence/complexity results are exact
positive examples of the maximal accessible quotient: one-frequency
recurrence does not bound ambient carrier complexity, and finite dictionaries
fail by metric separation.  They strengthen the universal information law
but do not strengthen the Riemann arithmetic consequence, so importing their
technical statements into the manuscript would recreate the rejected
collage.

### Scope conclusion

Every new module is now one of:

1. a direct theorem used in the biaxial Riemann law;
2. a positive admission/separation realization;
3. a terminal consumer or exact completion loss;
4. an infrastructure theorem; or
5. an unrelated recurrence/complexity realization of the same information
   law.

“Subsumes” therefore means exact specialization through a named source map
and target distinction.  It does not mean that elementary set factorization
proves the analytic estimates, nor that unrelated infrastructure is a
corollary.  No new delta theorem exposes a third obstruction beyond admission
and separation, or a third independent Riemann source axis beyond shell
breadth and reflected valuation depth.
