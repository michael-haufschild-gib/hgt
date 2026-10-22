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
- Schanuel stage two and above; stage one is discharged unconditionally by the corpus
  Hermite--Lindemann theorem `exp_algebraic_transcendental`.

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
aggregate. Exact transfer by this zero-free factor localizes the only remaining divisor to the
quotient `XiC/F`; the hostile Wronskian limit proves that quotient retains exactly the Xi divisor.
The stronger terminal law now shows that every source-selected odd superaccurate raw finite theta
core recovers the exact Xi multiplicity `m` in its horizontal anisotropic charge. A fixed
meromorphic gauge of order `ell` changes this charge only to `m-ell`; screening holds exactly when
the gauge imports matching divisor order. This is sharp divisor tomography, not a proof shortcut.
Status: `[FORMALIZED IN RHTOWER; ROUTE H RETIRED; DIRECT HT DIVISOR BRIDGE EXHAUSTED]`.

## Corrected whole-theory criterion and first exact transfer

User correction: HTGeometry is an independent mathematical theory, not a bag of declarations
ranked by whether RHTower already imports them.  Existing application evidence is therefore
historical metadata only.  Selection order is now:

1. normalize the complete HTGeometry theorem supply;
2. normalize exact RHTower source obstructions independently;
3. test mathematical instantiation;
4. only afterward record whether the transfer was already applied.

The first exact underapplied transfer found by this criterion is compact moment determinacy.
`HTGeometry.CarriedConclusion.measure_eq_of_moments_eq_of_one_carried` had not been applied to the
completed-seam compact Thorin producer wall.

Let `mu` and `nu` be two finite positive compactly supported measures whose Thorin logarithmic
exponents both equal the exact normalized completed Cassini source exponent near zero.
Differentiating the source identity gives equality of both Markov transforms with
`completedSeamMomentGerm`.  Taking every derivative at zero forces

```text
integral x^n dmu(x)
  = normalizedPrimeArchMoment(n)
  = integral x^n dnu(x)
```

for every `n`.  Compact carriage of `mu` and HTGeometry moment determinacy then imply `mu=nu`.
This produces a new source-wall rigidity statement:

> The critical-seam compact Thorin carrier, if it exists, is canonical; changing carrier or
> support radius cannot evade the missing positivity theorem.

Formalized card:
`../../../3-formalized/not_new_scientific_knowledge/completed-seam-compact-thorin-carrier-rigidity.md`.
Lean module:
`RHTower/CompletedSeamCompactThorinRigidity.lean`.
Status:
`[PAPER-PROVED] [LEAN-FORMALIZED] [AXIOM-CLEAN] [NOT CLAIMED NOVEL] [NOT RH]`.

The stronger classification uses the already formalized RH consequence and canonical Xi compact
measure.  Any compact Thorin witness implies RH.  Under RH the atomic measure

```text
primeArchXiCompactMomentMeasure
  = sum_j lambda_j delta_(lambda_j)
```

has exactly the normalized prime--archimedean moments.  Applying compact determinacy again proves
that every witness measure equals this canonical Xi-divisor pushforward.  Therefore the compact
Thorin wall has no alternative-carrier freedom: a source-side construction must reconstruct this
exact measure without reading Xi zeros.  This is the positive classification exposed by the
generic measure-existence no-go.

## First-clock tail lower-bound frontier theorem

Whole-corpus normalization exposed a stronger live claim already implicit in the first-clock
Landau family but not proved there.  For

```text
B1(L) = ccmPublishedSourceSineCoefficient(L/2, 2*pi/L),
```

the exact target is

```text
(exists C>=0 and A>=pi/2, forall L>=A, -C <= B1(L)) <-> RH.
```

Paper proof is dependency-closed and Lean-formalized in
`../../../3-formalized/needs-audit/ccm-first-clock-tail-lower-bound-completeness.md`.  Its decisive carrier is

```text
R(L) = Re Q(L) + (C/2)L
       + 1_(pi/2,A](L) max(-(Re Q(L)+(C/2)L),0).
```

Compact summand has entire Laplace transform.  Affine summand uses exact corpus Perron identity
`integral_0^infinity L exp(-sL) dL = s^-2`; after deleting `(0,pi/2]` it is analytic on `Re s>0`.
Hence `R` inherits the same positive-axis disks as literal first-clock continuation.  Continuous
Landau halving reaches every positive abscissa.  Removing both corrections returns all positive
exponential moments of `Q`, and existing Volterra-reflection capstone implies RH.

Lean implementation is in
`RHTower/CCM/CCMFirstClockTailLowerBoundCompleteness.lean`.  Current file contains exact predicate,
source-to-affine divisor law, compact carrier and integrability, analytic continuation, corrected
Landau measure, halving/dyadic descent, correction removal, full Xi-moment reconstruction, RH
equivalence, and false-RH unboundedness capstone. Targeted `lake env lean` and final `lake build`
are green. `#print axioms` on both RH equivalence and every-tail unboundedness capstone reports
exactly `[propext, Classical.choice, Quot.sound]`. Status:
`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`.

Exact remaining open core is source-side and irreducible under this equivalence:

```text
exists C A : R, 0 <= C and pi/2 <= A and
  forall L >= A, -C <= B1(L).
```

Next whole-corpus pass must ask which general HTGeometry structures can force a lower floor for one
real boundary observable without already assuming zero location. Import/use history is irrelevant;
candidate mechanisms must be extracted from complete normalized HT theorem and object reservoir,
then tested against this exact premise.

## Whole-HT transfer: asymptotic Bohr completeness of first clock

Complete semantic audit of HTGeometry—not import-neighbor tracing—identified
`SummableSpectrumScrewRecurrence` as unused Xi-side structure. Its compact relation-hull theorem
applies to arbitrary positive summable weights and arbitrary integral frequency relations. RHTower
had an abstract Suzuki wrapper, but no multiplicity-exact Xi instantiation and no comparison with
literal moving-denominator CCM first clock.

New generic HT theorem:

```text
nonnegative a + Summable a
  -> IsBohrAlmostPeriodic (screwSeries a omega)
```

proved by uniform finite-frequency approximation, with no countability, nonzero-frequency, or
independence premise.

For scaled literal source

```text
F(L)=L*ccmPublishedSourceSineCoefficient(L/2,2*pi/L),
```

new exact formal theorem is

```text
(exists continuous Bohr-almost-periodic P, F-P -> 0 at +infinity) <-> RH.
```

Under RH explicit witness is twice multiplicity-exact Xi screw series. Per zero, for `L>=2*pi`,
moving-denominator error is nonnegative and at most

```text
(2/15)*(2*pi/L)^2/gamma_q^2.
```

Summability gives full `O(L^-2)` error. Conversely boundedness of arbitrary Bohr witness plus
vanishing perturbation gives literal first-clock tail lower floor, so prior completeness theorem
returns RH.

Relation-hull transfer also yields: every value in full asymptotic interval is approximated by
scaled literal source with bounded gaps after one threshold; absolute endpoint occurs exactly when
every finite integral ordinate relation has even total coefficient. No simplicity or rational
independence premise.

Formalized card:
`../../../3-formalized/needs-audit/ccm-first-clock-asymptotic-bohr-completeness.md`.
Lean modules:
`HTGeometry/SummableSpectrumScrewAlmostPeriodic.lean` and
`RHTower/CCM/CCMFirstClockAsymptoticBohrLaw.lean`. Both umbrellas wired. Targeted Lean checks and final
module build green. Five capstone axiom audits report exactly
`[propext, Classical.choice, Quot.sound]`.

Exact new primitive source wall:

```text
CCMFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic.
```

This strictly sharpens the earlier tail-floor wall: asymptotic Bohr behavior supplies tail floor,
but relation-hull theorem additionally exposes complete conditional recurrence and parity geometry.
Novelty remains unverified; result is not RH.

## Frozen conjecture ABT-1: asymptotic Bohr Torelli law

`[FROZEN BEFORE PROOF — 2026-08-01]`

Let

```text
F(L)=L*ccmPublishedSourceSineCoefficient(L/2,2*pi/L).
```

Assume only the source-side statement that there exists a continuous real Bohr almost-periodic
`P` with `F(L)-P(L)->0` as `L->+infinity`. Then:

1. `P` is unique among all such asymptotes;
2. the source assumption forces RH;
3. for every nonzero real `lambda`, the complex Bohr coefficient of `P` is

```text
- sum_{q : |Re xiSpectralPoint(q)|=|lambda|} 1/(Re xiSpectralPoint(q))^2;
```

4. consequently `-lambda^2` times that coefficient is the exact cardinality of the
   multiplicity-copy fibre at absolute ordinate `|lambda|`; and
5. the support and these integral masses reconstruct the full real Xi divisor, hence the
   normalized even canonical product `XiC`.

Ontological reversal: the Xi ordinate multiset is not supplied to the source-side hypothesis. It
is recovered as the quantized negative Bohr spectrum of the unique asymptotic translation germ of
the literal prime--Gamma first clock.

Hostile tests fixed with the conjecture:

- uniqueness of `AP+C_0` is classical and is not the novelty claim;
- the generic coefficient formula is classical harmonic analysis and is supporting infrastructure;
- zero-frequency atoms must be excluded using the proved Xi spectral gap;
- collisions and divisor multiplicity must be retained by fibre sums, with no simplicity or
  rational-independence assumption;
- the theorem is not an RH proof because existence of the asymptote is already RH-equivalent;
- candidate new content is the source-specific multiplicity-exact Torelli/quantization statement;
  external priority remains open.

## ABT-1 resolution: proved and formalized

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`

ABT-1 survives. Exact source-side theorem:

```text
F-P -> 0, P continuous and Bohr AP
  => P is unique
  => RH
  => P = 2 * xiCriticalScrewSeries
  => a_P(lambda) = -N(|lambda|)/lambda^2  for lambda != 0
  => -lambda^2*a_P(lambda) = N(|lambda|).
```

`N(|lambda|)` is cardinality of exact `XiZeroCopy` fibre at absolute real ordinate, hence retains
analytic multiplicity and every frequency collision. Functional-equation reflection makes
absolute divisor sufficient to recover full real centered divisor. No simplicity or rational
independence appears.

New HT generic theorem proves termwise Bohr coefficient extraction for arbitrary nonnegative
summable screw spectrum. Proof uses uniform finite-subset convergence plus 1-Lipschitz continuity
of Bohr coefficient; no frequency separation is assumed. New HT rigidity theorem proves directly
that a Bohr almost-periodic function tending to zero at positive infinity vanishes identically.

Formal modules:

```text
formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewBohrCoefficients.lean
formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockAsymptoticBohrTorelli.lean
```

Formalized card:
`../../../3-formalized/needs-audit/ccm-first-clock-asymptotic-bohr-torelli.md`.

Remaining source-producing frontier is not uniqueness or spectral recovery. It is direct
construction of the asymptotic Bohr model—or direct proof of its quantized coefficient law—from
the prime/Gamma side without importing RH.

Final audit: targeted Lean checks green; module build `9334/9334`; six capstones have axiom set
exactly `[propext, Classical.choice, Quot.sound]`. Formal lint finds no forbidden declaration and
fails only on six unrelated pre-existing HTGeometry umbrella-reachability gaps. No Lean/lake
process remains running.

## Producer restart: whole-HT verdict and frozen FCES-1

Whole-HT mechanism audit against literal first-clock source sign closes generic Herglotz/KMS/Pick,
finite-jet/hypertranscendence, and positivity-preserving regularization as direct producers. Exact
reasons are already formalized in the corpus: critical transport divergence at every finite
cancellation order, sign-changing raw delays, basiswise common-aperture Pick rigidity, cofinally
unbounded critical Pick index, arbitrary finite-jet controllability, and arithmetic blindness of
convergent multiplicative regularization.

Positive survivor is HT crease tomography. Frozen conjecture `FCES-1` in
`ccm-first-clock-prime-entry-slope-tomography.md`: at aperture `L=log k`, literal active atom has
value zero and slope

```text
-2*pi*criticalMellinAtomWeight(k)/log k.
```

For `k=p^e` this is `-2*pi/(e*sqrt(p^e))`; for non-prime-powers it vanishes. Full derivative-jump
current should therefore recover exact von Mangoldt source. This does not prove sign; it forces any
future lower-floor producer to preserve discrete negative slope current and create compensation in
continuous inter-entry drift.

## FCES-1 resolution: finite-packet source tomography

`[PAPER-PROVED] [LEAN-PROVED] [CORPUS-NEW BRIDGE] [NOT RH]`

FCES-1 is formalized in exact finite-packet form. At `L = log k`, active atom vanishes and has slope

```text
-2*pi*criticalMellinAtomWeight(k)/log(k).
```

Hard-entered atom therefore has zero left slope and displayed right slope. The normalized slope
recovers exact atom weight; at `k=p^e` it is `-2*pi*p^(-e/2)/e < 0`; outside prime powers it is zero.
Log injectivity makes every other finite-packet atom smooth at distinguished aperture, yielding an
exact decomposition of whole packet into smooth background plus unique kink atom.

Formal module:
`formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockPrimeEntrySlopeTomography.lean`.
RHTower umbrella wired; direct `lake env lean` check green. Card moved to
`../../../3-formalized/needs-audit/ccm-first-clock-prime-entry-slope-tomography.md`.

Hostile audit found analogous high-clock result `SuzukiPrimeTangentTomography.lean`; novelty claim is
therefore limited to corpus-new moving-first-clock bridge and finite-packet decomposition. Full
published-source derivative current remains unclaimed until Gamma--polar summand is matched and
proved smooth in exactly same normalization.

Producer consequence: negative atomic crease current is arithmetic-complete. Any successful lower-
floor mechanism must preserve it and explain compensation through smooth inter-entry drift; smoothing
or radial collapse discards decisive source data rather than producing sign.

Final FCES-1 audit: direct Lean check and final module build green (`9262/9262`). Four capstone
`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`. Formal lint finds no
forbidden declaration in new module and remains nonzero only on nine unrelated pre-existing
HTGeometry umbrella-reachability gaps. No claim of RH proof: remaining open core is still a direct
unconditional producer for first-clock lower floor/asymptotic Bohr existence.

## Whole-HT producer restart: canonical Julia prime-order attenuation

The first mechanism surviving the scalar/Pick/convolution/tilt no-gos is the existing canonical
Gamma-sewn Julia normal coordinate.  At critical damping its squared hard mass factors as the
literal `Lambda(p^e)/sqrt(p^e)` mass times one universal profile `R(x log p)`, independent of the
power `e`.  Frozen conjecture `JPOA-1` is recorded in
`ccm-julia-prime-order-attenuation-law.md` before proof.

Paper reduction: with `t=tanh(y/2)` and `P=1+6t^2+t^4`, the compression square is `1/sqrt(P)`.
The derivative sign of `R(y)=4(1-1/sqrt(P))/(3y^2)` reduces to the strict elementary inequality

```text
artanh(t) * t(1-t^2)(t^2+3)/P < sqrt(P)-1.
```

It follows from `artanh(t)<t/(1-t^2)`, itself the strict `z<sinh z` inequality at
`z=2 artanh(t)`, and the polynomial residue
`3P-(t^2+3)=17t^2+3t^4>0`.  Thus the candidate profile is strictly decreasing on paper.

Scientific consequence if the dependency audit closes: every power in one prime tower keeps the
same sign, but every larger prime is attenuated more.  Since first-clock multi-mode towers lie at
`log p<=L/2` and irreducible one-mode counter towers lie at `log p>L/2`, this is a canonical
non-diagonal mechanism that improves the exact unresolved outer/aligned odds; exponential tilts in
the corpus provably move them the other way.  The `p=2,3` two-mode exceptions remain explicit.

Hostile no-go: source-faithful schedules have `x(L)L->0`, which collapses the useful order gap.
Fixed positive `x(L)L` preserves a gap but not uniform recovery of the critical source.  Therefore
Julia dilation alone does not prove positivity; its positive survivor is a sharp regularization
boundary-layer invariant and favorable prime-order transport law.

## JPOA-1 resolution: first favorable whole-HT source transport

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY SEARCH NONCOLLISION] [NOT RH]`

The whole-HT audit produced a non-scalar survivor. The canonical Gamma-sewn Julia environment has
exact critical mass ratio

```text
R(y) = 4/(3y^2) * (1 - cosh(y/2)^2/sqrt(cosh(2y))),  y=x log p.
```

`R` is strictly decreasing on `y>0`. Lean now identifies this universal HT profile with the
literal RHTower source multiplier and proves, without numerical computation:

```text
hard_x(u,p^e)^2 = R(x log p) * boundary(u,p^e)^2,
p<q  =>  R(x log q)<R(x log p),
multi-mode p, one-mode q  =>  p<q,
R_q(G-B) < R_p G-R_q B  when G>0.
```

This is first audited corpus mechanism that moves exact reduced first-clock odds in favorable
direction: all one-mode outer primes are suppressed more strongly than every multi-mode tower
prime. Existing exponential tilts move this comparison in opposite direction.

Sharp no-go is equally exact. Same positive scalar multiplies every exponent in one tower, so
tower sign is unchanged; negative outer towers and negative `p=2,3` two-mode towers are not locally
repaired. Coefficientwise `R(x log p)->1` at lossless boundary. Therefore current open core is not
finding another sign-preserving scalar regularizer. It is an aggregate theorem coupling this
strict cross-prime order gain to continuous/Gamma budget strongly enough to dominate complete bad
residual under a boundary-layer schedule.

Formal modules and card:

```text
formal/GaloisForLFunctions/HTGeometry/JuliaDefectAttenuation.lean
formal/GaloisForLFunctions/RHTower/GammaSewnMobiusJuliaPrimeOrderAttenuation.lean
docs/drafts/pipeline/3-formalized/needs-audit/ccm-julia-prime-order-attenuation-law.md
```

Both theorem-area umbrellas are wired. Final module builds pass; capstone axiom sets are exactly
`[propext, Classical.choice, Quot.sound]`. Repository lint reports only five unrelated pre-existing
umbrella-reachability gaps.

## Whole-HT spectral synthesis: Julia equilibrium clock

`[PAPER-PROVED] [LEAN CORE] [NOT RH]`

Independent audit of HTGeometry's transform, probability, and observer mechanisms found a stronger
interpretation of the same Julia profile. `CoshFourierTransform`, `CoshFourierInversion`,
`GammaCyclicSpectralMeasure`, compound-Poisson infrastructure, finite-matrix Bochner positivity,
and universal clock sampling had not been assembled with `JuliaDefectAttenuation`.

For

```text
kappa(y)=cosh(y/2)^2/sqrt(cosh(2y)),
```

the exact logarithmic Lévy density is

```text
rho(t)=1/(2t sinh(pi t/4))-2/(t sinh(pi t)).
```

It is strictly positive because, with `v=pi t/4`,

```text
sinh(4v)=4sinh(v)cosh(v)cosh(2v)>4sinh(v).
```

The singularities cancel, total intensity is `(3/2)log 2`, and `kappa` is the characteristic
function of a symmetric boundary compound-Poisson law with atom `1/(2sqrt(2))` at zero and variance
`3/2`. Square-biasing that law and multiplying by the difference of two centered uniform clocks
shows the continuously extended attenuation is itself a characteristic function:

```text
R(0)=1,
R(y)=4(1-kappa(y))/(3y^2)
    = E exp(i y Xhat(U-V)).
```

Hostile test exposed a load-bearing Lean totalization issue: existing
`juliaDefectAttenuationProfile` equals `0` at zero, so it is not positive definite. An explicit
two-point negative Gram witness is now formalized. Positive survivor is canonical extension
`juliaDefectAttenuationKernel`, together with strict positivity of exact Lévy density. Complete
monotonicity in `y` is also false; characteristic-kernel positivity is correct replacement.

Formal core:
`formal/GaloisForLFunctions/HTGeometry/JuliaDefectSpectralEquilibrium.lean`.
Paper card:
`../2-fully-proven/needs-audit/julia-defect-equilibrium-clock-law.md`.

RH boundary: diagonal values `R(x log p)` are only origin correlations. New information is full
PSD kernel `R(x(log q-log p))` across prime logarithms. Next risky test is whether this off-diagonal
Julia Gram has an exact action on reduced first-clock good-minus-bad functional; diagonal scalar
gating alone remains insufficient.

## Whole-HT scale-four synthesis: Dirichlet–Julia–CCM innovation tower

`[PAPER-PROVED] [LEAN-PROVED] [AXIOM-CLEAN] [NOT RH]`

The whole-reservoir pass found that three independently developed structures are exact coordinates
of one object:

1. critical centered successor/log-Beta density `D(x)=1/(2sinh x)`;
2. Gamma–Julia compression Lévy density `rho`;
3. CCM `1 mod 4` odd block-Fock archimedean density `A`.

Define `J(x)=D(x)-4D(4x)`. Then, unconditionally,

```text
J(pi t/4)=t rho(t)>0,
D(x)=sum_(j<n)4^j J(4^j x)+4^n D(4^n x),
D(x)=(1+exp(-2x))A(2x).
```

Thus Julia equilibrium is canonical positive innovation left by fourfold subdivision of complete
odd critical Gamma ladder. Factor `1+exp(-2x)` adds CCM's missing `3 mod 4` sector to its existing
`1 mod 4` block-Fock sector. Exact first-clock continuous reflection gap is now written as
difference of two normalized `D` values plus explicit polar reflection, so finite Julia telescope
resolves whole continuous budget at arbitrary scale with exact tail.

Hostile test prevents overclaim: positive innovation values do not sign translated differences,
and theorem does not alter von Mangoldt sine phases. It therefore cannot termwise dominate
counter-phased prime mass. Strongest survivor is exact positive multiscale resolution of complete
CCM Gamma budget. New open core is a source-specific cross-term/comparison coupling this resolved
continuous tower to signed prime-power functional.

Formal modules:

```text
formal/GaloisForLFunctions/HTGeometry/JuliaDefectSpectralEquilibrium.lean
formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockJuliaScaleFourTransfer.lean
```

Card:
`../../../3-formalized/needs-audit/ccm-julia-scale-four-innovation-tower.md`.

Final module build is green at `9285/9285`; eight capstones depend only on
`[propext, Classical.choice, Quot.sound]`. Global lint fails on unrelated missing HT umbrella import
`ProjectiveHorizonActualSchwarzianDiamond`, not on either new module.

## Whole-HT source coupling: Julia–KMS prime innovation tower

`[PAPER-PROVED] [LEAN-PROVED] [NOT RH]`

Pure Gamma positivity exhausted at CJS4-1 because it did not touch arithmetic carrier mass. Whole
HT audit then exposed exact missing coupling. For positive finite KMS gap

```text
x=beta(E_a-E_b)/2,
C_ab=2sinh(x)W_ab,
D(x)=1/(2sinh x),
```

so `D(x)C_ab=W_ab`. Combining this inverse fluctuation--dissipation identity with the existing
scale-four telescope gives

```text
W_ab=sum_(j<n)4^j J(4^j x)C_ab+4^nD(4^n x)C_ab.
```

Every generic layer is nonnegative. Existing Hermitian prime-log KMS realization has
`W_p=primeDyadicWeight(u,p)>0` and `C_p=2sinh(beta log(p)/2)W_p>0`; therefore each prime carrier
weight has an exact finite decomposition into strictly positive Julia response layers plus a
strictly positive tail.

Hostile test closes overclaim exactly. HT prime-dyadic weight is not literal von Mangoldt
prime-power critical Mellin weight, and innovation acts diagonally before external first-clock sine
phase. Lean proves every negative phase stays strictly negative on every positive Julia layer.
Thus source coupling is real, but it does not sign RH functional.

Strong survivor: Julia equilibrium is canonical multiscale inverse-FDT resolution of finite KMS
fluctuation mass, instantiated exactly by arithmetic prime-log carriers. New open core is
non-diagonal, phase-sensitive realization of literal prime-power Mellin source or cross-frequency
quadratic inequality before sine evaluation.

Formal module and card:

```text
formal/GaloisForLFunctions/HTGeometry/JuliaKMSScaleFourInnovation.lean
docs/drafts/pipeline/3-formalized/needs-audit/julia-kms-prime-innovation-tower.md
```

Final direct Lean and module build are green (`8768/8768`). Eight capstone axiom reports are exactly
`[propext, Classical.choice, Quot.sound]`. Lint finds no issue in new module; nonzero status comes
only from three unrelated pre-existing umbrella gaps recorded on card.

## Whole-HT literal-source closure: Julia–KMS prime-power resolution

`[PAPER-PROVED] [LEAN-PROVED] [NOT RH]`

JKPIT-1 reached an arithmetic prime-log carrier but not literal RHT critical Mellin prime powers.
Whole-corpus collision audit found existing results that must be consumed: depth-one von Mangoldt–
Gamma anomaly/Julia factorization, common-prime Julia–Bianchi Gram, and block-Fock identity
`criticalMellinAtomWeight=Lambda·degreeOneDefect`.

New exact weld is

```text
D(h/2)(1-exp(-h))=exp(-h/2),
criticalMellinAtomWeight(q)
 =Lambda(q)(1-q^-1)D(log(q)/2).
```

Thus inverse finite-KMS density renormalizes literal depth-one Gamma displacement into critical
half-weight. Applying scale-four telescope gives exact finite positive Julia resolution of every
literal atom and whole first-clock prime sine sum:

```text
w(q)=sum_(j<n)L_j(q)+T_n(q).
```

On prime powers all layers and tails are strict. First captured fraction and residual fraction are

```text
F(x)=1-1/(cosh x cosh 2x),
R(x)=1/(cosh x cosh 2x).
```

`F` strictly increases and `R` strictly decreases with full integer `q`; this separates valuation
exponents inside one prime tower, unlike previous prime-base Julia attenuation.

Hostile test: each layer remains diagonal in `q`; counter-phased sine atoms remain strictly
negative at every scale. Monotone scale filters also cannot isolate two alternating negative
first-clock bands without affecting intervening positive band. Positive survivor is first exact
common scale-four resolution of literal arithmetic and continuous CCM sectors, with canonical
exponent-sensitive tail. Remaining wall is non-diagonal cross-frequency/inter-scale inequality
before sine evaluation.

Formal module and card:

```text
formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockJuliaKMSPrimePowerResolution.lean
docs/drafts/pipeline/3-formalized/needs-audit/ccm-julia-kms-prime-power-resolution.md
```

Final direct Lean and module build are green (`9377/9377`). Eleven capstone axiom reports are
exactly `[propext, Classical.choice, Quot.sound]`. Lint finds no issue in new module; nonzero status
comes only from three unrelated pre-existing umbrella gaps recorded on card.

## Retired non-novel detour: Julia equilibrium coherent capacity

`[FORMAL BOOKKEEPING] [NOT NEW SCIENTIFIC KNOWLEDGE] [RETIRED]`

Hostile collision audit killed two tempting rediscoveries. Scalar thermal susceptibility is
already strictly stronger in `SoninSemilocalWeylGenerator` and
`SoninSemilocalCyclicWeylDescent`. Independent positive Julia prime layers are excluded as an RH
architecture by the corpus's harmonic Gamma-conductor and semilocal one-prime deficit no-gos.

The exact substitution restores Julia structure before scalarization. The corrected equilibrium kernel

```text
R(0)=1,  R(y)=(4/3)(1-kappa(y))/y^2
```

is paper-proved characteristic. Existing arithmetic attenuation is exactly `R(x log p)`. For
literal reduced first-clock cells `T_p=G_p-B_p`, continuous budget `C_L`, and finite admitted prime
packet, the deformed completed source is exactly

```text
A_x=C_L+sum_p R(x log p)(G_p-B_p).
```

The full bad covariance energy is

```text
E_B=sum_(p,q) B_p B_q R(x log q-x log p).
```

Adding the origin to the Gram with optimizing coefficient `-B_x` proves
`B_x^2<=E_B`. Since completed good origin correlation is positive, every negative excursion obeys

```text
A_x^2 <= E_B.
```

This is only the generic anchored Gram inequality/Cauchy--Schwarz in corpus notation.  Exact source
action does not make the mechanism novel.  It does not change the global RH dependency graph and
must not be presented as frontier movement.

Formal modules and card:

```text
formal/GaloisForLFunctions/HTGeometry/JuliaDefectSpectralEquilibrium.lean
formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockJuliaEquilibriumGram.lean
docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm-first-clock-julia-equilibrium-coherent-capacity.md
```

Lean closure is dependency-honest, but scientific novelty is rejected.  No rank-one, RKHS,
operator-placement, or diagonal-damping sequel is authorized from this detour.  Work returns to
global load-bearing open cores only.

## Whole-corpus source coupling: Gamma--Jacobi artanh transport

`[PAPER-PROVED] [LEAN-PROVED] [ADVANCE] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`

Two near-rediscoveries were explicitly killed. Odd Jacobi modes cannot linearly recover even log
powers, and the proposed edge-integral realization already exists as
`VonMangoldtSuccessorDiracKreinEdge.lean`, classified non-new. The surviving result instead uses
the odd ladder to reconstruct one nonlinear coordinate before forming all jet powers.

For actual coefficient

```text
a_k(t)=(-1)^k c_(2k+1) phi(t)tanh(t)^(2k+1)
```

the fixed incidence `B(k)=(-1)^k/((2k+1)c_(2k+1))` gives

```text
T_K(t)=sum_(k<K) B(k)a_k(t)/phi(t)
      =sum_(k<K)tanh(t)^(2k+1)/(2k+1),
T_K'(t)=1-tanh(t)^(2K),
T_K(t)->t.
```

The two-channel derivative/value lift of `T_K^(i+1)` has exact exchange integral equal to the
endpoint difference of `T_K^(i+j+2)`. Summed with actual `Lambda(n)/n` edge weights, arbitrary
source-dependent starting capacities plus common cofinal growth converge to the full fixed-aperture
`SR-40` matrix. At existing `SR-38` prime capacities, the new incidence head and old zero-padded
coherent residual are coordinatewise complementary. This is first proved common absolute-mode
connector between those two formerly ill-typed marginals.

Lean also exposes required singularity rather than assuming boundedness:

```text
phi(log p)^(-2)=(p^2+1)/(2p)>=p/2,
```

so normalization is unbounded on primes. Positive survivor is canonical unbounded connector in the
only class not excluded by resolved-channel and normal-partial-trace no-gos. Remaining open core is
one joint infinite-index Krein packaging and completed Euler cyclic reader carrying exact `SR-43`
jet-opening flux; fibre orientation and RH remain open.

Formal module and card:

```text
formal/GaloisForLFunctions/RHTower/GammaJacobiArtanhTransportCoupling.lean
docs/drafts/pipeline/3-formalized/needs-audit/gamma-jacobi-artanh-transport-coupling.md
```

## Source boundary closure: adaptive tail is connection defect

`[PAPER-PROVED] [LEAN-PROVED] [ADVANCE] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`

Generic Meixner--Pollaczek coherent states, Szegő kernels, and Hardy shifts were collision-killed as
known; corpus already contains separate prime-valuation Hardy colligation. New source theorem is
exact cross-identification. For `t>0`, forced singular readout of actual coefficient satisfies

```text
d_K(t)=(-1)^K a_K(t)/(c_(2K+1) phi(t)tanh(t))
      =tanh(t)^(2K)=1-T_K'(t).
```

At `K=gammaOddJacobiPrimeCapacity(p)`, coefficient is first surviving zero-padded `SR-38`
coordinate. Thus finite-head connection defect is not extra data: it is tail boundary value.
Applying same readout to full tail gives

```text
H_K(t,u)=sum_(j>=0)d_(K+j)(t)d_(K+j)(u)
        =[tanh(t)tanh(u)]^(2K)/(1-[tanh(t)tanh(u)]^2),
H_K-H_(K+1)=d_K(t)d_K(u)=(1-T_K'(t))(1-T_K'(u)).
```

Every adjacent surviving residual pair reads `tanh(t)^2`; for prime sources it is
`((p^2-1)/(p^2+1))^2` and equality is equivalent to equality of primes. Hence arbitrary adaptive
finite head deletion preserves projective source marking. Coordinate-level head/tail boundary
packaging is closed. Remaining source core is representing existing canonical signed Toeplitz
countertrace and completed Euler multiplication on this nested boundary, then extending to
infinite-index Krein jet current.

Formal module and card:

```text
formal/GaloisForLFunctions/RHTower/GammaJacobiTailConnectionTransgression.lean
docs/drafts/pipeline/3-formalized/needs-audit/gamma-jacobi-tail-connection-transgression.md
```

## Toeplitz-clock escape becomes a Gamma boundary divisor

`[PAPER-PROVED] [LEAN-PROVED] [ADVANCE] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`

The prior von Mangoldt Toeplitz counterreader no-go forces zeros
`zeta_p=1/log(p+1)` toward the analytic germ origin. The exact reciprocal-log Gamma coordinate
does not merely move these zeros: it converts the whole source packet to

```text
r_p=tanh(log(p+1))^2,
1-r_p=4(p+1)^2/((p+1)^2+1)^2<=4/p^2.
```

Thus `sum_p(1-r_p)<infinity`, while distinct primes remain distinct and `prod_p r_p` exists and is
nonzero. The obstruction's positive survivor is a nontrivial Blaschke-admissible boundary divisor,
canonically fixed by the von Mangoldt endpoint clocks and the Gamma--Jacobi projective coordinate.
No prime distribution theorem is used. Generic Blaschke theory is known and excluded from the
novelty claim.

Formal module and card:

```text
formal/GaloisForLFunctions/RHTower/GammaJacobiToeplitzClockBlaschkeCompactification.lean
docs/drafts/pipeline/3-formalized/needs-audit/gamma-jacobi-blaschke-compactification-toeplitz-clock-escape.md
```

Open falsifier: after this conjugation, do normalized finite counterreader inner factors converge
to the prime divisor, and is the residual outer factor forced by the `SR-47` rank-one connection
transgression? A negative answer must identify the exact surviving outer gauge.
