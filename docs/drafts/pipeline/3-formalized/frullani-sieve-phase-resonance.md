# Mean-one sieve envelopes do not preserve Frullani cancellation

- **Stage:** 3-formalized
- **Type:** OBSTRUCTION / RESIDUE CLASSIFICATION
- **Source:** Argon §4.1; `CoalescentSieveAnatomyAndModelCalibration`.
- **Scope:** The inference from an unsigned factor-two envelope to a signed centered estimate. No counterexample to the actual prime-pair estimate is asserted.

## Candidate and paper proof

Put `g(u)=sin(2u)−sin(u)` and `a_t(u)=1+t g(u)/2`, `|t|≤1`.
These smooth periodic densities satisfy `0≤a_t≤2`, mean one on every period,
and uniformly bounded ordinary discrepancy primitive. Nevertheless

`∫_1^R (a_t(u)−1) g(u)/u du = (t/2) log R + O(|t|)`.

Indeed the centered integrand is `t g²/(2u)`, and

`g²=1−cos(4u)/2−cos(2u)/2−cos(u)+cos(3u)`.

Each nonconstant cosine divided by u has a bounded primitive integral on `[1,R]`,
by integration by parts. The exact logarithmic residue ranges over `[-1/2,1/2]`
without changing the factor-two bound or mean-one normalization.
More precisely, the remainder after subtracting `m log R` is bounded for all `R≥1`
if and only if `m=t/2`; the error at this unique residue is at most `3|t|`.

The positive survivor is this residue classification and its phase criterion: the relevant mean is that of
`(a−1)g`, not that of `a−1`. More generally, if `h−m` has a bounded primitive,
then `∫_1^R h(u)/u du=m log R+O(1)`. The residue vanishes precisely when m=0.

## Arithmetic boundary

The literal `stabilizerDiscrepancyOddCoalSum` is defined by subtraction;
`oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy` does not prove
its mean vanishes. Actual prime-phase correlation control remains necessary.
The model obstruction does not retire the centered prime-pair route.

Even reflection `a(u)=a_1(|u|)` retains continuity, the factor-two envelope,
mean-one periods on positive lags, bounded positive-interval discrepancy, and
the unbounded signed integral. Lag-reflection symmetry does not remove the obstruction.

The stronger near-one corollary holds for every ε>0: choose `t=min(ε,1)`.
Then `a_t≥0`, `|a_t−1|≤ε`, and ordinary interval discrepancy is at most `3ε/2`,
while the centered integral is unbounded above. Thus no fixed positive unsigned
tolerance, however small, forces Frullani cancellation.

## Lean

`TransThresholdPairCorrelation/FrullaniPhaseResonance.lean` proves the bounded-primitive
residue estimate, density bounds, exact period mass, bounded ordinary discrepancy,
logarithmic error bound and unique residue, unboundedness, and both counterexamples.
`abs_frullaniResonantDensity_sub_one_le` and `frullani_near_one_counterexample`
give the arbitrarily small perturbation corollary.
The eleven public theorems pass transitive axiom audits with only `propext`,
`Classical.choice`, and `Quot.sound`. The exact production leaf passes
`lake --old env lean` and is imported by its umbrella.

## Gates

- [x] Corpus search of signed Frullani cancellation and periodic resonance.
- [x] Dependency-closed paper argument.
- [x] Lean counterexample, exact logarithmic residue, phase criterion.
- [x] Focused checks, axiom audit, umbrella import.
