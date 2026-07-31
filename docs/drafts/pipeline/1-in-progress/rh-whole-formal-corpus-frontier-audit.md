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
