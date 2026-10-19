# Exact arithmetic anchoring of the remaining sieve translation

- **ID:** biscale-arithmetic-translation-anchoring-2026-10-19
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); accepted native classification package 2
- **Parent:** [100-contribution programme](../1-in-progress/biscale-100-contribution-programme-2026-10-18.md)
- **Source:** [Field checklist, item 3](../../../reports/BiScaleUncertainty/field-todo-1810.md)
- **Statement:** Complete affine and translated observations recover actual cutoff weights exactly when the active spectrum is odd or has an active divisibility edge crossing down from its highest two-adic class.

## Actual objects and exact theorem

At arbitrary cutoff N and arbitrary real divisor weights c, put

`Y_q = selbergMultiplesCoord N c q`,
`S = {q in [1,N] : Y_q != 0}`,
`V = max {q.factorization 2 : q in S}`, with V=0 for empty S.

An **anchor** is an active q with valuation V and an active divisor d of q with smaller valuation. These are actual coordinates of the literal sieve, not a separately assumed profile. Define

`O = N! / 2^((N!).factorization 2)`,
`h = 2^(V-1) * O`,
`R(c) = 2*sieveGcdProjection N h c - c`.

The verified conclusions are:

1. Equality of fifth and sixth translated moments is equivalent to equality of cutoff weights with either c or R(c). Every translated degree is already determined by degrees five and six.
2. R(c) is a literal translation by h, preserves active support and V, and is an involution on cutoff weights. If V=0 it equals c there; if V>0 it differs at an actual cutoff coefficient.
3. Complete labelled affine moments preserve R(c) exactly when no anchor exists.
4. The joint observation fibre is c, together with R(c) only when no anchor exists. This remains the exact fibre even when every translated moment is supplied.
5. Absolute recovery holds iff V=0 or an anchor exists. A distinct actual sieve with all the same affine and translated observations exists iff V>0 and no anchor exists.

All support and zero cases are included. Coefficients outside [1,N] are invisible to these observations, so equality there is neither claimed nor required. A Fourier readout assembled from a full lag array is not counted as one raw measurement.

One active crossing edge fixes the entire highest class, including parts disconnected in the affine divisor graph. The lower classes are oriented by cross-class translated resonances. This is the arithmetic interaction that the criterion captures.

## Dependency-closed paper proof — PROVED HERE

Sixth-order fixed-valuation recovery already gives every coordinate square, hence common support. For odd q, take r=N!/q and frequencies `(r,r,-(r+r),r,-r)`. They sum to zero and each has order q. The existing moment Fourier formula gives `P^5*Y_q^5`, so fifth-power injectivity fixes odd coordinates.

For positive V, choose a nonzero coordinate in the highest class. The existing mixed quintic receiver `P^5*Y_lower^3*Y_upper^2` then fixes every lower coordinate. Its original cutoff specializes to N by setting the surplus to `N-max(lower,upper)`. The existing sixth-order theorem leaves one common sign on the highest class. Zero coordinates remain zero. Thus no affine or second-order premise is needed for this first classification.

The odd part of every q in [1,N] divides O. Mathlib factorization therefore gives `q | 2^k*O` iff `v_2(q) <= k`. Every active q divides 2h, so 2h is a true period. The existing gcd projection has coordinate Y_q for q dividing h and zero otherwise. Consequently R(c) flips exactly the highest positive class. Fourier injectivity identifies it with the literal shift by h. It preserves every translated moment, preserves support/depth, and squares to identity on cutoff coefficients. An attained nonzero highest coordinate proves the companion is distinct when V>0.

Existing affine Fourier recovery identifies all labelled affine data with the products `Y_q*Y_d` for d dividing q. The companion changes precisely the products crossing from a highest-class order to a lower divisor. Such a product is unchanged iff one endpoint vanishes. Therefore all affine data preserve the companion iff there is no active crossing edge. Combining this fact with the global two-representative classification proves the exact fibre, absolute-observability equivalences, and actual indistinguishable witness.

## Prior corpus work reused

- `MixedValuationQuintic`: exact cross-class fifth readout and its zero exception.
- `SixthValuationPhaseRecovery`: common-sign recovery within one valuation class.
- `SieveMomentFourier`, `ValuationTripleResonance`, `SieveTripleFourier`, `CubicSievePhaseRecovery`, `AffineSievePhaseRecovery`: actual data, Fourier identities and affine comparable products.
- BVI `GcdOrbitProjectionAndExactTranslationPeriods`: exact coordinate projection and actual periods.
- BVI `TrueTranslationPredictionAndExactCompression`: cutoff coefficient injectivity.
- BVI `ExactSuccessorMomentRegionAndUniversalInequalities` and `SelbergHilbertCoordinateEquivalence`, with RHTower Ramanujan inversion: existing realization/inversion, found by cross-field search and audited; no replacement inverse was introduced.
- Mathlib factorization, odd complements and finite suprema. Cross-field search also found `QuantumAlg.ShorFactoring.twoAdicOrderValuation_le_of_dvd` and `_lcm`; their bodies wrap Mathlib, which is used directly.

Relevant complete sources were inspected. The retired affine-plus-odd and affine-plus-through-five routes were retained as boundaries. The separate BVI mixed-support noisy-stability audit is concurrent work and is not modified or counted here.

## Native significance and comparison limits

This package closes the exact mixed-support ambiguity problem stated in item 3 of the field checklist. The accepted advance is the arithmetic **absolute-origin criterion**, its complete two-element-or-trivial ambiguity, and the actual all-observation witnesses across arbitrary real sieve supports. Existing fixed-valuation, prime-family and affine sign-component theorems did not supply that global joint classification.

Classical cyclic six-deck reconstruction, Fourier identities, CRT, and the supporting declarations are not separate contributions. [Jaming–Kolountzakis, §3.4](https://nyjm.albany.edu/j/2003/9-12.pdf) records the classical integer cyclic six-deck baseline; [Keleti–Kolountzakis](https://eigen-space.org/mk/ps/three.pdf) supplies the Fourier/translation framework. [Tóth–Haukkanen](https://arxiv.org/abs/1009.5281) treats arithmetic even-function DFT. None of these cited statements is asserted to be new.

[Mandereau et al., §4](https://math-musique.pages.math.unistra.fr/biblioth%C3%A8que/2012%20-%20MANDEREAU%2C%20GHISI%2C%20AMIOT%20-%20Discrete%20Phase%20Retrieval%20in%20Musical%20Structures.pdf) gives the Fourier-character method and rational cyclic reconstruction bounds. Its cyclotomic argument cannot simply be asserted for arbitrary real coefficients; the present proof uses order-constant sieve coordinates and includes zero mean. That extension alone is not the novelty claim. The public abstract and introduction of [Miao et al.](https://www.sciencedirect.com/science/article/pii/S0165168422004467) concern chirp/linear-canonical transforms, a different meaning of affine Fourier analysis; the full paper was not audited.

Within this audited corpus and primary comparison scope, the joint arithmetic anchoring classification qualifies as **one** substantive native package. No universal literature-priority claim follows from bounded searches. Stability, efficient raw measurements, and the least degree for each support remain separate problems.

## Lean certificate

| Leaf | Public result | Named-source log |
| --- | --- | --- |
| [SieveHalfPeriodTranslation](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveHalfPeriodTranslation.lean) | Exact half-period representability, actual reflected weights, all-degree preservation, affine crossing criterion | `/tmp/bsu-100-half-period-leaf.log` |
| [SieveValuationPhaseRecovery](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveValuationPhaseRecovery.lean) | `coordinates_eq_or_highest_flip` from degrees five and six only | `/tmp/bsu-100-global-phase-leaf.log` |
| [SieveCanonicalTranslation](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveCanonicalTranslation.lean) | Actual `companion`, involution, distinctness, and complete two-representative forward theorem | `/tmp/bsu-100-canonical-shift-leaf.log` |
| [SieveAffineTranslationAnchoring](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveAffineTranslationAnchoring.lean) | `same_all_observations_iff`, `absolute_all_observability_iff`, `distinct_indistinguishable_iff` | `/tmp/bsu-100-affine-anchoring-leaf.log` |

All four named original-source/export checks used `lake --old env lean ... <source>` and exited 0. No diagnostic remains in those logs. The first leaf's seven public closures were previously audited. The final imported audit `/tmp/bsu_100_anchoring_final_axioms.lean` prints all 31 public declarations from the three new leaves, including actual definitions and signatures; all closures use only `propext`, `Classical.choice`, and `Quot.sound`. Its log `/tmp/bsu-100-anchoring-final-axioms.log` exits 0.

All four leaves are imported once by the umbrella. Index regeneration passed (`/tmp/bsu-100-anchoring-index.log`). `scripts/formal_tools.py lint --check-generated` passed (`/tmp/bsu-100-anchoring-lint.log`), with pre-existing large-file warnings only. No full or umbrella build, added axiom, numerical experiment, or heartbeat increase was used. Owned extracted scratch and API drafts were removed; audit sources and logs remain.

Protected README SHA256: `95c0fc8e6bc87af3b980d39f00a17f294b2bd16ae248f9361eff557e303ad275` (unchanged).

## Corpus-search evidence

All returned candidate/source and prose/source-passage inventories were inspected for the following `/tmp/bsu-100-*.json` queries: `mixed-valuation-frontier`, `prescribed-order-resonance`, `arithmetic-anchoring-frontier`, `coordinate-realization`, `coordinate-inverse-targeted`, `half-period-prior`, `two-adic-decomposition`, `global-valuation-recovery`, `odd-fifth-readout`, `canonical-half-period-search`, and `sieve-congruence-deep`. Several broad queries were irrelevant; proposed ingredient sets were not treated as proofs. The zero-hit `sieve-congr-search` lexical query was broadened to deep search.

`anchoring-known-exact` returned exactly the three named dependencies; `gcd-half-period-exact` returned 20 hits, all inventoried. The existing parity-stride energy and prefix-discrepancy reflection concern different operations. An unquoted multi-name query expanded to 154897 matches and was discarded; it is not represented as an audit.

Deep stages completed, but semantic completeness was explicitly unmeasured and refresh often reported a running background indexer. Source/caller checks and Lean verification establish applicability of reused ingredients; search misses do not establish absence.

## Gates and next question

- [x] Well-posed actual-object statement; prior corpus and mathematical mechanisms audited.
- [x] Dependency-closed paper proof, including every support and zero case.
- [x] Exact Lean theorem, named sources, all public axiom closures, wiring, index and lint.
- [ ] Standalone publication manuscript and independent literature-priority review.

The subsequent [sharp observation order under coprime overlap](biscale-prime-overlap-observation-order-2026-10-19.md) package computes the least degree on every support stratum of the three-order overlapping family. The present theorem supplies a universal sixth-degree ceiling; it does not compute the least degree for arbitrary arithmetic supports.
