# Exact attainable successor covariance cone

- **ID:** bvi-exact-successor-covariance-cone-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** At every sieve level at least six, prescribed moments `(H,S,B)` are realizable exactly when `2H² ≤ S+B` and `2B ≤ S+H²`.

## Mathematical purpose

The unconditional successor bounds constrain the joint same-node and successor forms.
An exact realization theorem would determine whether additional inequalities can hold
without imposing further arithmetic restrictions on the weights. It would also identify
the two exceptional modes generating the full feasible cone.

## Corpus evidence

Local research queries for Selberg coordinates, successor rigidity, parity, and covariance
realization locate the existing simultaneous diagonals and the new rigidity module.
No successor-moment realization theorem was identified. The renewed deep query was partial
at reranking but located the exact finite multiples inverse:
`RHTower.pmRamanujanResidueCoeff_multiples` in `RHTower/PMRamanujanPeriodDiagonal.lean`.
Its weight is `c(d)=d·Σ_{m≤N/d} μ(m)y(dm)` and its full coordinate profile is already proved.
Reuse this theorem; do not reprove or count inversion as new research.

## Paper proof [PROVED HERE]

Choose Selberg coordinates `Y(1)=H`, `Y(2)=a`, `Y(6)=b`, all others zero.
The required coefficients are

`c(1)=H+b-a`, `c(2)=2a-2b`, `c(3)=-3b`, `c(6)=6b`, with all other coefficients zero.

The corpus inverse realizes this profile at every `N≥6`. The simultaneous diagonals
give `S=H²+a²+2b²` and `B=H²-a²+b²`. Therefore the two inequalities are necessary.
Conversely, set `a=√((S+H²-2B)/3)` and `b=√((S+B-2H²)/3)`.
The proposed inequalities make both radicands nonnegative. Substitution yields the
requested triple exactly. The arbitrary-mean extension follows from the same construction;
it introduces no additional mathematical premise.

The dual classification follows from the same cone. Write `V=S-H²`, `C=B-H²`.
Then `αV+βC≥0` for every finite sieve weight iff `α-β≥0` and `2α+β≥0`.
Necessity follows by using the pure divisor-two and divisor-six modes. For sufficiency,
`αV+βC = ((α-β)(V-2C)+(2α+β)(V+C))/3`, and both defects are nonnegative.

Prefer a symbolic finite-coordinate realization theorem, reused here, over finite numerical
enumeration. The arithmetic content is the successor spectrum `μ(e)/φ(e)` and its
exceptional modes at two and six; the auxiliary triangular transform alone is not a new
field contribution.

## Plan

1. Audit existing inverse-transform infrastructure and current field declarations.
2. Prove symbolic coordinate realization, then derive the exact covariance cone.
3. Audit the named Lean module, axioms, wiring, indexes, and formal lint.
4. Record one significant contribution only after its mathematical verification.

`update_plan` is unavailable; this card stores the task plan.

## Gates

- [x] Renew corpus audit for inverse-transform infrastructure.
- [x] Dependency-closed symbolic paper proof, including arbitrary mean and the dual cone.
- [x] Unconditional Lean realization equivalence and endpoint witnesses.
- [x] Named-module verification without warnings; all eight theorem axioms audited.
- [x] Wiring and declaration index checked; formal lint run.
- [ ] Repository-wide lint passes: five unrelated BiScaleUncertainty import omissions remain.

Counted as **contribution 002**, one connected moment-region and dual-classification result.
The eight supporting theorems and the reused inverse are not separate contributions.

## Lean implementation

Module: `GaloisForLFunctions.BezoutValuationIncidence.ExactSuccessorMomentRegionAndUniversalInequalities`.

- `selbergMultiplesCoord_ramanujan_inverse`: total coordinate bridge to the existing inverse.
- `selbergForm_ramanujan_inverse`, `bezoutForm_ramanujan_inverse`: simultaneous realization.
- `successorThreeModeWeight_moments`: symbolic witnesses with independent mean and endpoint modes.
- `exists_sieve_weight_with_moments_iff`: exact attainable joint moment region.
- `universal_successor_quadratic_inequality_iff`: complete dual classification for all sieve levels.

The construction at level `N+6` uses a universally quantified natural parameter; no
unproved arithmetic premise, mean-zero assumption, or numerical experiment enters the proof.
The existing multiples-inversion theorem is reused, not counted as a contribution.

The named-module command `lake --old env lean -j 1 -o <module.olean> <module.lean>`
passed without warnings. All eight field modules are currently wired; all ten new declarations
appear in the regenerated API. A separate `/tmp` audit imported the resulting module and
printed axioms for every new theorem: only `propext`, `Classical.choice`, and `Quot.sound`.
No added axiom or computation-oracle axiom occurs. The compiled artifact is newer than its
source. `git diff --check` passed. No full or umbrella build was run.

The global lint command was run. It reports no proof-debt or owned-module errors, but exits one
for five unrelated BiScaleUncertainty umbrella omissions: `ClampedPrimeLogResummation`,
`CompactAutocorrelationPolarMoment`, `FactorialBiNullPolarSign`, `FactorialMuntzSeed`,
and `FactorialRampDiagonalIdentity`.

## Consequence and research boundary

A stronger unrestricted half-decorrelation constant is impossible: the pure six-mode attains
the endpoint exactly. The parity mode likewise attains the lower endpoint. The positive
survivor is the complete realizability theorem and the exact dual cone, which identify all
universal linear combinations of the two moment forms that can be nonnegative.

This classification concerns the mean and the two quadratic main terms. It does not estimate
signed finite-prefix sawtooth defects or establish square-root cancellation. Any stronger
result must retain additional information, for example an arithmetic constraint on the weights
or exclusion of an extremal coordinate.

Novelty assessment is relative to the inspected local corpus, not a literature-priority claim.
