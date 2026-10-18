# Divisor-six stability and the next successor gap

- **ID:** bvi-six-mode-stability-and-quarter-gap-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean 4)
- **Statement:** Variance away from divisor six is at most twice the defect in half-decorrelation; deleting the six-mode improves the sharp upper covariance ratio to one quarter.

## Motivation

The exact covariance cone shows that unrestricted universal quadratic improvements are
impossible. The next question is which arithmetic restriction genuinely strengthens the
inequality. The field guide singles out divisor six, but its existing inequality theorem
does not establish the complete equality classification or a quantitative stability estimate.

## Corpus evidence

- `SuccessorEnergyRigidityAndParityStability` classifies the negative endpoint and proves
  its stability, but does not classify the positive half-decorrelation endpoint.
- `ExactSuccessorMomentRegionAndUniversalInequalities` provides symbolic coordinate
  realization and proves that unrestricted improvements cannot hold.
- Corpus search locates `GaloisForLFunctions.HTGeometry.totient_le_two_iff` in
  `HTGeometry/CrystallographicRestriction.lean`: positive integers with totient at most two
  are exactly `1,2,3,4,6`.
- Renew the search before implementation; source-only discoveries require Lean verification.

## Paper proof [PROVED HERE]

For `e≥2`, `e≠6`,

`φ(e) ≤ 2(φ(e)-2μ(e))`.

Outside `1,2,3,4,6`, evenness and the crystallographic classification give `φ(e)≥4`;
then `μ(e)≤1` suffices. At `2,3,4`, the Möbius value is nonpositive.
Thus, writing `V=Σ_{e≥2}φ(e)Y(e)²` and `C=Σ_{e≥2}μ(e)Y(e)²`,

`Σ_{e≥2,e≠6}φ(e)Y(e)² ≤ 2(V-2C)`.

Consequences:

1. Half-decorrelation equality iff every nonconstant coordinate except `Y(6)` vanishes.
2. A quantitative distance estimate to the divisor-six extremizer space.
3. If `Y(6)=0`, then `4C≤V`.
4. The quarter bound and stability constant are sharp: the pure divisor-ten mode has
   `φ(10)=4`, `μ(10)=1`, hence `V=4t²`, `C=t²`.

The classification is exhaustive. If `φ(e)≤2`, the corpus classification leaves
`2,3,4` after excluding `1,6`, and their Möbius values are `-1,-1,0`.
Otherwise `φ(e)>2`; positivity and evenness force `φ(e)≥4`, so `4μ(e)≤φ(e)`.
Equivalently, the half-decorrelation coefficient satisfies
`φ(e)≤2(φ(e)-2μ(e))` away from six. At six, that coefficient is zero.

Let `D=V-2C` and `V₆ᶜ=Σ_{2≤e≤N,e≠6}φ(e)Y(e)²`. Summing the pointwise inequality
gives `V₆ᶜ≤2D`. Since each `φ(e)>0` on the index set, `D=0` forces every
nonconstant coordinate except six to vanish. The converse follows from the exact
diagonal for `D`. Empty index sets cover levels zero and one; when `N<6`, the
six-coordinate is already zero by the cutoff.

There is a canonical operation on actual weights. Prescribe the profile
`Y'(e)=0` at `e=6` and `Y'(e)=Y(e)` elsewhere, and apply the existing finite
Ramanujan inverse. The resulting weight has exactly this profile and applying the
operation twice changes nothing. It preserves `H`, subtracts `2Y(6)²` from `S`,
and subtracts `Y(6)²` from `B`. Thus its variance is `V₆ᶜ` and its centered
covariance is `C-Y(6)²`, satisfying the unconditional quarter bound.

For sharpness, prescribe only `Y(10)=t` at any level at least ten. Multiplicativity
at the coprime primes two and five gives `φ(10)=4`, `μ(10)=1`. Hence `H=0`,
`V=4t²`, `C=t²`, `Y(6)=0`, and `D=2t²`. Taking nonzero `t` proves both the
quarter constant and the stability factor two are optimal. No numerical search is used.

Use the existing symbolic finite inverse for witnesses, not numerical enumeration.
Do not count the already advertised uniqueness claim alone as a new contribution;
the target is the stronger stable classification and sharp next gap.

The sharpness statements can be expressed without side conditions on input weights:

- `C(removeSixMode(N,c)) ≤ K V(removeSixMode(N,c))` for every `N,c`
  iff `1/4 ≤ K`.
- `V₆ᶜ(N,c) ≤ K D(N,c)` for every `N,c` iff `2 ≤ K`.

For sufficiency, use the proved bounds and nonnegativity of the variance and defect.
For necessity, the symbolic divisor-ten witness at amplitude one gives respectively
`1 ≤ 4K` and `4 ≤ 2K`. The operation normalizes irrelevant coordinates outside the
truncation level; its idempotence is equality of complete weight functions, while its
coordinate formula controls every coordinate including zero and those above the level.

These are statements about the centered periodic quadratic forms. They do not bound
the signed finite-prefix discrepancy and do not establish square-root cancellation.

## Gates

- [x] Renew prior-research and dependency audit.
- [x] Complete paper proof and endpoint witnesses.
- [x] Unconditional Lean capstones, named-module check, axiom audit.
- [x] Wiring, index refresh, contribution assessment.
- [ ] Repository-wide formal lint: four unrelated import omissions, listed below.

Counted as **one** connected significant contribution: **003 / 250** in the root ledger.
The reused finite inverse, existing totient classification, and supporting lemmas are not
separate contributions.

## Formal verification

Verified module:
`formal/GaloisForLFunctions/BezoutValuationIncidence/SixModeStabilityAndSharpQuarterDecorrelation.lean`.

- Named source passed `lake --old env lean -j 1` without warnings; `.olean` emitted.
- Every referenced mathlib API was checked in scratch files against this toolchain.
- All 19 public theorem axiom audits passed, with exactly `propext`, `Classical.choice`,
  and `Quot.sound`. This covers the two private arithmetic helpers transitively.
  The audit output is `logs/bvi-root-2026-10-18-six-mode-axioms.txt`.
- All nine field modules are imported by the field umbrella.
- `scripts/formal_tools.py index` completed; both pages of the module's 25 declarations
  were retrieved. All 23 public declarations (19 theorems, four definitions) are present.
- No numerical experiments, new axioms, heartbeat overrides, or full/umbrella builds.

Concurrent rebuilds repeatedly removed inherited compiled imports. The successful audit
used a temporary workspace with the same toolchain and package configuration, a cloned
compiled-import cache, and the original source file. The named command used
`--root=/Users/michael/Documents/code/hgt/formal` to preserve its correct module name.
The resulting artifact was installed in the normal build directory. Temporary audit
files and cache are removed after registration; dependency sources were not edited.

`scripts/formal_tools.py lint` exited 1 with no field or proof-debt findings. Its four
errors are modules unreachable from the unrelated `BiScaleUncertainty` umbrella:

- `EndpointCycleDeterminant`
- `SharpCycleGramRealization`
- `SharpGramDetectionOrder`
- `StationaryResolventMarkovPositivityAndNodalDefectProducer`

This is not a repository-wide passing lint gate.

## Contribution assessment

The new content is the stable classification of the positive endpoint, an idempotent
operation on actual sieve weights with exact moment losses, and complete optimal-constant
classifications for the quarter bound and stability inequality. The divisor-ten witnesses
prove both constants sharp. The already advertised uniqueness of six alone is not counted.

Next candidate: `docs/drafts/pipeline/0-backlog/bvi-finite-prefix-discrepancy-dual-energy-2026-10-18.md`.

## Plan

1. Recheck the arithmetic classification and search for existing stability results.
2. Prove a dependency-closed paper argument, including sharp witnesses and boundary levels.
3. Formalize the universal defect inequality and exact endpoint classification.
4. Verify named modules and axioms, preserve all umbrella imports, refresh indexes,
   run formal lint, and register only the connected significant contribution.

`update_plan` is unavailable; this card stores the plan.
