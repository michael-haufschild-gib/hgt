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
