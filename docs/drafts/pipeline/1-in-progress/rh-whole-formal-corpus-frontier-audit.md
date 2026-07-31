# RH whole-formal-corpus frontier audit

- **ID:** `rh-whole-formal-corpus-frontier-audit`
- **Stage:** 1-in-progress
- **Type:** CORPUS AUDIT / WORKING LOG
- **Scope:** every Lean module and top-level declaration in
  `formal/GaloisForLFunctions/HTGeometry` and
  `formal/GaloisForLFunctions/RHTower`, cross-checked against pipeline status.
- **Statement:** No new RH conjecture is admissible until every formal theorem surface is
  classified as unconditional source theorem, reusable infrastructure, RH consumer/equivalence,
  obstruction/no-go, or genuinely open source-producing input.

## Mission

Determine exact residue left by complete HTGeometry/RHTower corpus, then conjecture beyond that
residue without selecting a route by recency, terminology, or apparent formal convenience.

## Snapshot and instrumentation

Snapshot began 2026-07-31. Other agents are concurrently adding modules and regenerating indexes;
all counts below must be refreshed immediately before conjecture freeze.

Initial complete source inventory:

| Area | Lean source modules | Directly parsed top-level declarations |
|---|---:|---:|
| HTGeometry | 3,048 | 34,628 |
| RHTower | 3,786 | 48,470 |

The source count includes theorems, lemmas, definitions, structures, abbreviations, inductives, and
instances after removing comments and strings. Every source file was processed; no sampling.

The generated `formal/LEAN_API.md` initially exposed 31,644 HTGeometry and 44,757 RHTower
declarations. It is not a complete audit instrument: `scripts/formal_tools.py` uses a line-local
declaration regex and misses declarations whose keyword and name occur on separate lines. Direct
source parsing is therefore mandatory alongside generated API.

Umbrella/source facts at snapshot:

- `formal_tools.py status`: zero active proof-debt findings.
- HTGeometry umbrella: 2,851 direct area imports.
- RHTower umbrella: 3,600 direct area imports.
- RHTower files make 774 direct import edges into 501 distinct HTGeometry modules.
- No Lean build is run in this lane while concurrent Lean processes are active.

## Exact RH status

- 552 RHTower modules mention mathlib's `RiemannHypothesis`.
- Hundreds of declarations prove implications or equivalences from named hypotheses.
- No declaration named bare `riemannHypothesis` has type `RiemannHypothesis`.
- No declaration named bare `not_riemannHypothesis` has type `¬RiemannHypothesis`.
- Therefore corpus does not presently prove or disprove RH.

Foundational capstones in `RiemannTower.lean` are exact characterizations:

- `rh_iff_xi_ne_zero_right`;
- `rh_iff_tower`;
- `rh_iff_forall_ladder`;
- `rh_iff_exists_roots_all_two_powers`.

They formalize zero-freeness/branching equivalences and explicitly supply no zero-location input.

## Whole-interface audit cross-check

`prop-interface-discharge-audit.md` uses environment-level Lean metaprograms rather than text grep.
Its successive corrections matter:

1. conclusion occurrence is not a producer;
2. an `Iff` transfers groundedness but does not create it;
3. independently inhabited premises need joint realization;
4. bundled data hypotheses require constructors, not only `Prop` conclusions;
5. container, instance, recursor, and specialized/general conclusion shapes create detector false
   positives.

Current verified consequences:

- no unproduced project-`Prop` interface remains in HTGeometry, HilbertMetric, or audited RHTower;
- this does **not** mean source-specific RH walls are discharged;
- many interfaces are inhabited only at degenerate/unit/empty models;
- several ostensibly geometric RH producers are exact re-encodings.

Sharp re-encoding theorems already in corpus:

- `isRelativeCharacterCarrier_iff_of_ne_zero`: a nonzero relative carrier is exactly character
  equality;
- `reflectedCharacterNorm_eq_iff_criticalLine`: calibrated reflected-character norm equality is
  exactly critical-line location;
- `isReflectionTateConservative_iff`: conservative reflection-Tate reporting is exactly support
  on reflection fixed locus;
- `riemannHypothesis_iff_exists_reflectionTateConservative_landing`: corresponding landing exists
  exactly iff RH.

Any proposed same-fibre dagger, conservative conormal carrier, or fixed-locus reporter must
therefore construct the equality from literal source data before divisor specialization. Naming
the interface is circular.

## Open constructions found by corpus-wide audits

These are genuine mathematical inputs or constructions, but none is yet established as an RH
producer:

- nonempty-vertex scalar/channel Stanley--Reisner realization, equivalent to attaining a
  hypertranscendental meromorphic function with rank-one period group;
- classical analytic Nevanlinna carrier family, requiring an honest indeterminate moment problem
  and its Nevanlinna parametrization rather than a Dirac orbit;
- exact critical approximation-number asymptotic for the concrete Gauss-paired channel;
- differential-algebraic closure as an `IntermediateField`;
- external Lindemann--Weierstrass input used by Schanuel stage one.

The first three require classification against every RH route before investment. General
infrastructure completion alone is not RH progress.

## Active audit obligations

- [x] Process every HTGeometry/RHTower source file and declaration surface mechanically.
- [x] Establish exact absence of an unconditional RH or anti-RH theorem.
- [x] Cross-check project-`Prop` and bundled-data grounding audits and their blind spots.
- [ ] Classify every module into mathematical mechanism families, allowing overlaps.
- [ ] Classify every RH-facing declaration as source producer, consumer/equivalence, no-go, or
  open premise.
- [ ] Cross-check every module against Stage 2, Stage 3, Stage 5, and current Stage 1 cards.
- [ ] Read and normalize the full post-`RiemannHypothesisSOTA2026` corpus, not only its terminal
  modules.
- [ ] Produce exact frontier matrix and identify residue not already equivalent to RH.
- [ ] Only then perform external literature audit and freeze a conjecture.

## Log

- 2026-07-31 — Reset after invalid recency-based route selection. Began exhaustive direct-source
  and generated-index audit. Recorded API undercount, exact corpus scale, RH non-proof status,
  cross-area dependency surface, interface-audit limitations, and two proved RH-reencoding
  classifications.

## Reproducible source-surface census

`scripts/hgt_corpus_audit.py` now parses the direct source rather than treating the generated API
as exhaustive.  It records every source module, multiline top-level declaration, import,
umbrella-reachability result, mechanism-family label, role signal, pipeline reference, and
RH-facing declaration.  The census is deliberately regenerated while other agents are adding
modules; the following is the 2026-07-31 snapshot, not a frozen repository invariant.

| area | modules | parsed top-level declarations | umbrella-unreachable |
|---|---:|---:|---:|
| HTGeometry | 3,056 | 35,141 | 0 |
| RHTower | 3,794 | 48,517 | 0 |
| total | 6,850 | 83,658 | 0 |

The generated API undercounts multiline declarations, so declaration-level arguments must use the
source census or compiler environment, never API line count alone.

Primary-family partition in this snapshot:

- HTGeometry: algebraic/combinatorial/incidence 1,180 modules; analytic boundary/function spaces
  595; cross-cutting foundational 347; moment/operator/spectral 311;
  differential/hypertranscendence 295; gamma/theta/special functions 134; projective-horizon
  geometry 87; prime/Dirichlet source 58; quantum-clock/observer 49.
- RHTower: xi/zeta foundation 1,002; prime/Euler/Mobius arithmetic 641; explicit-formula,
  positivity, and moments 581; growth/approximation/density 486; operator/spectral/CCM/Suzuki 363;
  gamma/theta/archimedean 272; cross-cutting foundational 182; Deninger 93; Sonin 90; dynamics 84.

The partition is a navigation normalization, not a novelty or dependency judgment.  Overlapping
secondary mechanisms remain in the machine manifest.

RHTower contains 1,545 declarations detected as RH-facing by statement-level syntax:

| syntactic role signal | declarations |
|---|---:|
| named RH interface, without literal source term in statement | 1,314 |
| RH equivalence | 686 |
| RH conclusion | 439 |
| RH premise | 290 |
| literal zeta/xi/prime/Mobius source in statement | 231 |
| anti-RH premise | 96 |
| RH embedded below another connective | 27 |
| anti-RH conclusion | 26 |

Signals overlap.  In particular, the 26 anti-RH conclusions are conditional contrapositives from
named defects; none is an unconditional disproof.  No declaration in either area has the bare
conclusion `RiemannHypothesis` or its negation without a premise.

## Post-ledger normalization

`RiemannHypothesisSOTA2026.lean` is a typed endpoint ledger dated 2026-07-21, not a proof and not the
current corpus boundary.  The RHTower umbrella has 1,654 source imports after that ledger:

- 384 xi/zeta, 337 prime/Euler/Mobius, 280 explicit-formula/positivity/moments, 202
  growth/approximation/density, 138 operator/spectral/CCM/Suzuki, 125
  gamma/theta/archimedean, 65 Sonin, 46 Deninger, 43 cross-cutting foundational, and 34 dynamics;
- 189 modules have an RH-facing signal, 134 an RH-equivalence signal, 81 an RH-conclusion signal,
  44 an RH-premise signal, and 93 a no-go signal;
- 432 have no module-name reference detected in a pipeline card and therefore require direct
  theorem-level normalization rather than inferred card status.

Thus the July 21 ledger cannot be used as a complete frontier audit.

## Whole-corpus-certificate quotient

The apparent 18-family synchronization in
`XiWholeCorpusPositivePhaseUniversalityLaw.lean` is a product of already RH-equivalent certificate
families.  Its reverse direction projects the geometric-phase component; that component projects
the Arakelov component; the Arakelov component is already equivalent to RH.  Likewise:

- `XiTerminalAnalyticSourceUniversalityLaw` reverses by projecting rectangular Weil continuation,
  already equivalent to RH;
- `XiTerminalGeometricPhaseUniversalityLaw` reverses by projecting Arakelov preperiodicity,
  already equivalent to RH;
- the single-Sonin and all-strict-ray collapses are transitivity through RH equivalences.

Positive result: these modules exhibit an exact logical strongly-connected component/product law.
Adding equivalent coordinates to a certificate cannot create a new source producer.  Frontier
analysis must quotient the RH-facing graph by equivalence SCCs and retain only primitive incoming
source estimates.  Conjunction width is not independent mathematical evidence.

## Compiler-frontier baseline, pending refresh

The cached compiler graph (`formal/.lake/hgt-research/rh-frontier.json`, dated 2026-07-26) has
1,583 reductions across 513 modules: 955 implications, 587 equivalences, 41 refutations; 1,574 live
and 9 retired.  Its target is not proved.  It reports 19 minimal cuts and 302 equivalent criteria.
Because 1,654 umbrella imports now follow the July 21 ledger and the cache predates current work,
these cuts are candidates to audit, not a route selection:

1. `MobiusMertensAllStrictHalfPowerBound`
2. `MobiusAdditiveStrictOffDiagonalSubpowerUpperBound`
3. `MobiusAdditiveTriangleLinearPolylogUpperBound`
4. `SoninCoupledPrimeArchPerTestNormalizedValueCoupling`
5. `DyadicWeightedPrimeWindowSubpowerUpper`
6. `MobiusAdditiveStrictOffDiagonalLinearPolylogUpperBound`
7. `MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded`
8. `SoninCoupledPrimeArchRealPerTestNormalizedValueCoupling`
9. `SoninPrimeArchPerTestTraceHankelCoupling`
10. `SuzukiHermiteBiehler`
11. `CompletedOddLogDerivPolynomialRightEvenFactorization`
12. `MobiusDiscreteLaplaceHalfPolylogDecay`
13. `SoninCoupledPrimeArchValuationAtMostSixResidualVariationalUpperBound`
14. `SoninCoupledPrimeArchValuationSixResidualVariationalUpperBound`
15. `SoninPrimeArchCofinalBlockApproximation`
16. `SoninPrimeArchFiniteMomentCoupling`
17. `XiCTaylorThetaTailCoreCurrentSublinearUpper`
18. `XiArakelovConjugateRootsContractive` jointly with `XiArakelovCoordinatesIntegral`
19. `XiCTaylorOddThetaTailSuperaccurateSchedule` jointly with
    `XiCTaylorThetaTailCoreCurrentJointSublinearUpper` and
    `XiCTaylorThetaTailCoreCurrentTwoTermBridge`

Each cut must now be classified as literal source estimate, source-free abstraction,
RH-equivalent mirror, or retired/no-go, with current incoming producers and pipeline status.  A
fresh compiler graph is deferred while other agents have foreground Lean processes active; running
another Lean process would violate the single-process audit rule and has already caused an
incompatible-olean failure.

## Relevance correction: HTGeometry is an independent reservoir

Existing `HTGeometry -> RHTower` import/use edges are historical facts, not mathematical relevance
criteria.  The corrected audit order is:

1. parse every HTGeometry declaration independently;
2. preserve its exact header and classify its mathematical mechanism and conclusion shape;
3. normalize RHTower separately to primitive open obstructions;
4. test every compatible HT mechanism against every primitive obstruction;
5. only after a mathematical transfer map is identified, label it already applied or unapplied.

No candidate may be selected because it is new, recently wired, absent from a card, or already near
RHTower in the import graph.

The refreshed independent declaration pass currently contains 35,171 HTGeometry declarations in
3,056 modules, including 26,470 theorems/lemmas.  Overlapping theorem-mechanism counts are:

| mechanism | theorems/lemmas |
|---|---:|
| algebraic/combinatorial | 9,987 |
| differential algebra | 6,240 |
| Gamma/special functions | 3,024 |
| arithmetic/Dirichlet | 2,174 |
| measure/functional analysis | 2,069 |
| projective/geometric | 1,942 |
| moment/positivity | 1,928 |
| asymptotic/order | 1,893 |
| dynamics/quantum | 1,679 |
| topology/compactness | 1,534 |
| complex analysis | 1,487 |
| spectral/operator | 1,277 |
| integral transforms | 425 |

These tags overlap and do not rank importance.  Another 6,323 theorem headers have no mechanism
keyword; they remain in the exact manifest and cannot be discarded.  The audit tool now writes
every declaration, exact statement header, overlapping mechanisms, and logical conclusion shapes
through `--declarations`.  Import edges and pipeline status do not enter that output.

## First exact transfer audit: reflected digamma orientation

`HTGeometry.ReflectedDigammaAnomalyOrientationUniversalityLaw` proves the maximal orientation of

```text
psi(sigma + i t) + psi(1 - sigma - i t):
Im > 0 iff sigma < 1/2, = 0 iff sigma = 1/2, < 0 iff sigma > 1/2.
```

RHTower imports the underlying `ReflectedDigammaAnomaly` facts in at least the Gamma response,
vertical phase, and rectangular archimedean modules, but no RHTower declaration currently invokes
the maximal orientation theorem itself.  This is genuinely unapplied information, but not yet a
valid transfer.  The completed zeta Gamma factor uses

```text
psi(s/2) + psi((1-s)/2),
```

whose reflected coordinates sum to `1/2`, not `1`.  The needed universal statement is therefore an
arbitrary-center reflected-digamma orientation law; its Xi specialization is centered at `1/4`.
The existing theorem cannot be substituted without this coordinate correction.

Positive survivor if the RH bridge fails: for every `c > 0`, `t > 0`, the imaginary part of

```text
psi(a + i t) + psi(c-a-i t)
```

is strictly decreasing for `0 < a < c`, is reflection-odd about `c/2`, and its sign exactly
orients `a` relative to `c/2`.  This follows from the already proved strict horizontal
monotonicity of `Im psi`.  Its Xi archimedean specialization (`c=1/2`, `a=Re(s)/2`) would match the
actual completed-zeta coordinates exactly.  Status: `[CONJECTURE; PAPER PROOF IMMEDIATE FROM
EXISTING LEAN MASTER; RH TRANSFER UNDER HOSTILE AUDIT]`.

## Conclusion-capability normalization

The independent pass now splits each exact Lean header at its top-level result colon.  Binder
hypotheses and conclusions are classified separately, so a theorem which assumes positivity is
not counted as a positivity producer.  Current moving-worktree snapshot:

| area | modules | declarations | theorems/lemmas |
|---|---:|---:|---:|
| HTGeometry | 3,062 | 35,223 | 26,509 |
| RHTower | 3,799 | 48,549 | 38,424 |

HTGeometry conclusions which supply a capability not syntactically present in their binders:

| produced capability | theorems/lemmas |
|---|---:|
| quantitative bound | 1,107 |
| sign/orientation | 883 |
| limit/compactness | 873 |
| differential transcendence | 802 |
| arithmetic source | 801 |
| reflection/phase | 728 |
| rigidity/classification | 597 |
| positive kernel/form | 582 |
| spectral reality | 518 |
| analytic continuation | 440 |
| factorization/decomposition | 417 |
| rank/dimension/support | 364 |
| zero location/exclusion | 340 |
| measure representation | 263 |
| recurrence/almost periodicity | 196 |

The labels overlap and remain syntactic over-approximations.  They are used to exclude impossible
type matches, never as proofs of compatibility.

The first exhaustive cross-match compared every such HT producer against every current exact
RHT theorem whose conclusion is RH-equivalent.  It scored shared conclusion capabilities and
normalized exact-type vocabulary only; imports, recency, and pipeline status were not inputs.
The pass covered 471 exact RHT interfaces and returned 5,652 top matches drawn from 1,626 distinct
HT declarations.  This is a complete search surface at the chosen capability vocabulary, not a
mathematical ranking.  Exact hypotheses, source instantiation, and equivalence-quotient status
remain mandatory manual checks.

## Prime-occupation/Gamma versus Euler-source audit

`PrimeOccupationPolarizedGammaPhaseSurvival` identifies inverse-prime occupations with all positive
integers and hence the genus-one occupation product with reciprocal Gamma.  Combining this with
the exact arithmetic identity

```text
vonMangoldt * zeta = log
```

does not yield a new positive inverse transfer.  The corpus already contains both directions of
the relevant source algebra:

- `ArithmeticFunction.vonMangoldt_mul_zeta`: the all-integer logarithmic stream is the positive
  divisor smoothing of the prime-power von Mangoldt stream;
- `ArithmeticFunction.moebius_mul_log_eq_vonMangoldt` and
  `RHTower.weightedVonMangoldt_eq_mobiusLogDivisorParaproduct`: recovering the von Mangoldt stream
  is Möbius-signed deconvolution.

Therefore positivity or regularity of the Gamma/all-integer occupation carrier cannot be pulled
back to the Euler prime-power source without a new variation, contractivity, or compensation
theorem for the Möbius inverse.  `eta-mobius-reciprocal-gamma-xi-sewing.md` already proves that the
ordinary plethystic repair returns the RH-equivalent Möbius continuation wall.  No new bridge is
present here.

Positive survivor: the Gamma occupation generator is exactly the zeta-convolution smoothing of
the von Mangoldt generator, while Euler recovery is its signed Möbius deconvolution.  This gives a
sharp structural reason Gamma positivity is easier and identifies the only possible new input:
a source-specific signed-inverse estimate.  Status: `[KNOWN IDENTITIES; NEW COMBINATION NOT
PROMOTED; DIRECT BRIDGE CLOSED]`.

## First whole-match hostile audit

High-coverage matches were checked after scoring, irrespective of whether RHTower imports them.

- `PrimeClockAnalyticEulerCompletion` and
  `AnalyticEulerTailExactFaithfulnessUniversalityLaw` faithfully realize the Euler logarithm and
  bounded prime-tail quotient in analytic differential fields.  RHTower already transfers their
  source consequences to the Xi shift defect and Gamma-sewn Julia boundary.  They prove
  faithfulness/hypertranscendence, not the missing sign, domination, or continuation estimate.
- `PrimeLogKMSRealization` and the Gibbs-limit modules construct the positive prime-log Herglotz
  response.  The live RHT gate is equality of a source-defined thermodynamic limit with the
  *combined prime--archimedean* trace.  Prime passivity alone does not supply this value comparison.
- `TailEventualOrder` classifies eventual positivity and two-stage pointing but does not create an
  eventually positive representative.
- `MomentFiberPickSchurPhase` consumes the RH-to-singular-measure identification; its Xi capstone
  assumes the decisive source criterion.
- `RectangularKreinInertia`, `ConfluentDarboux`, and paraorthogonal root laws give exact finite
  inertia/root geometry only after surjectivity, interlacing, or positive-measure inputs.  Those
  inputs are the RHT source walls.
- maximal-isodivisorial, finite-gauge-tail, and residue-rigidity modules are negative
  identifiability/classification results: they restrict possible selectors but do not orient the
  actual Xi source.

## Bohr-edge rigidity survivor

The full HT Bohr corpus contains mean existence, translation invariance, Parseval/Bessel control,
compact hulls, and recurrence.  It can strengthen the finite-rank rigidity theorem in
`ccm-critical-clock-divisor-blindness.md`:

```text
If h(u) = exp(alpha*u) (Q(u) + o(1)),
Q is a real uniformly almost-periodic function,
h(u) >= 0 eventually,
and the alpha-edge spectrum has no zero frequency,
then Q = 0.
```

Reason: translation recurrence transfers eventual nonnegativity to `Q >= 0` everywhere; absence of
zero frequency gives Bohr mean zero; a nonnegative continuous Bohr almost-periodic function with
zero mean must vanish.  Thus a nonzero separated leading edge forces a zero-frequency term, which
in the completed-source application is a real pole.  Entirety forbids that pole.

This extends the prior trigonometric-polynomial/finite-rank argument to uniformly almost-periodic
edge spectra.  It does not yet constrain the actual zeta source, whose dominant real pole is an
allowed zero-frequency top layer.  Its RH-facing consequence is a sharper no-go: an admissible
off-critical correction cannot have an isolated nonzero almost-periodic spectral edge; it must
have edge accumulation or lose uniform almost periodicity/remainder separation.

Status: `[CONJECTURE; PAPER PROOF SKETCH; NOVELTY AND EXACT RHT INSTANTIATION UNAUDITED]`.  Retained
as a positive survivor while the remaining mechanism/wall matrix is audited; not selected as the
main route.

## Whole-declaration transfer census and correction

The first 471-interface count was not the complete RH-equivalence census.  It counted only exact
RH-equivalent interfaces for which the initial capability vocabulary found at least one typed HT
producer.  The complete source parse contains 686 RH-equivalent interfaces in 340 RHTower
modules; 441 of those interfaces required expansion of at least one named `Prop` definition before
their source content became visible.

The compiler-derived 19 minimal cuts were then quotiented by mathematical source content, rather
than declaration names, to ten primitive families:

1. completed prime--Gamma sign;
2. prime--archimedean source positive form;
3. Hedenmalm/Weil positive form;
4. Möbius critical cancellation;
5. Sonin-to-prime--archimedean value transfer;
6. dyadic sharp prime-window subpower;
7. Suzuki/Hermite--Biehler;
8. moving-polynomial even factorization;
9. Xi Taylor raw core current;
10. Arakelov integral/contractive divisor mirror.

This quotient is a current compiled-cache frontier, not a claim that later source-defined walls
such as the concrete Hedenmalm center-mixed current or Connes ground-state construction are
subsumed.  Those source locks must be added explicitly in the next registry revision.

The audit now retains every HTGeometry declaration before asking about RHTower use.  At the
2026-07-31 moving-worktree snapshot it records 35,288 declarations:

| declaration kind | count |
|---|---:|
| theorem | 26,294 |
| lemma | 271 |
| definition | 7,659 |
| abbreviation | 307 |
| instance | 591 |
| structure | 149 |
| inductive | 17 |

Only after normalizing each declaration's binders, conclusion, and direct definition body does the
audit attach compatible primitive walls.  Only after that relevance pass does it annotate direct
RHT evidence:

| direct RHT evidence | declarations |
|---|---:|
| exact identifier mentioned | 2,480 |
| module directly imported but identifier not mentioned | 5,039 |
| no direct use evidence | 27,769 |

There are 4,412 theorem/lemma declarations with a typed primitive-wall capability and no direct
RHT use evidence, spread across all fourteen HT mechanism lanes.  This is a search reservoir, not
4,412 candidate proofs: generic positivity, compactness, or factorization consumers dominate it.
The application audit must discharge exact source instantiation and hypothesis direction theorem
by theorem.  Imports and novelty never decide relevance.

## Xi Taylor divisor-orientation hostile closure

The complete HT unit-circle/divisor mechanism is already instantiated on the actual Xi Taylor
product fibres.  `XiCTaylorThetaTailProductFiberPhaseOrientation` identifies every fixed positive
product fibre with a complete divisor antidiagonal and imports
`MultiplicativeCenteredDivisorOrientation` to prove strict negative upper current for every
nontrivial fibre.

This does not orient the raw Taylor core.  The exact RHT decomposition proceeds further:

```text
J(core)
 = (1/4) * sum_k C_k,

C_k
 = sum_(mn=k) Im(D_m * conjugate(V_n)),
```

with absolute convergence and divisor-reflection collapse to the unsymmetrized product-fibre
coefficient.  Positive-half-line translation then produces nested swept windows.  Abel/Prouhet/
Haar refinements control all diagonal fibre currents and finite translation edges, but the
off-diagonal Hermitian block current survives.  The final conservation theorem proves that every
attempt to make the Haar top row small transfers the same current into the surviving translation
term:

```text
finiteArithmeticRemainderJointSublinearUpper
  <-> XiCTaylorThetaTailCoreCurrentSublinearUpper
  <-> RiemannHypothesis.
```

Therefore no unused consequence of finitePhase fidelity, mixture log-concavity, unit-circle root
orientation, or complete divisor factorization closes this route.  Static phase dispersion does
not sign a derivative cross-current; termwise negative current is not preserved by summation.

Positive survivor: the full continuous theta-density completion is upper-zero-free and has
unconditional current contraction, so the entire arithmetic product-fibre current cancels in
aggregate.  Exact transfer by this zero-free factor localizes the only remaining divisor to the
quotient `XiC/F`; the hostile Wronskian limit proves that quotient retains exactly the Xi divisor.
This is a sharp gauge-localization theorem, not a proof shortcut.  Status:
`[FORMALIZED IN RHTOWER; DIRECT HT DIVISOR BRIDGE EXHAUSTED]`.
