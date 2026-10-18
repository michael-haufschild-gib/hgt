# Radical checkpoint sign rigidity and constant-mode law

- **ID:** thim-radical-checkpoint-sign-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** Sharp classification of checkpoints whose defect is nonpositive for every
  squarefree-supported weight, and exact dependence on the freely adjustable coefficient at one.

## Plan

1. Search corpus for existing constant-mode laws and universal rough-checkpoint converses.
2. Prove the exact affine law and classify constant-shift-stable sign on paper.
3. Derive the radical-state obstruction with structural prime-supported witnesses; formalize.
4. Audit actual source and all axiom closures, wire leaf, index/lint, update ledger, cleanup.

`update_plan` is unavailable. This card tracks work. README remains read-only.

## Exact mechanism

Adding `a` to coefficient `c(1)` shifts every positive sieve response by `a`, hence
leaves additive jumps unchanged. Polarization proves
`D_N(k-1;c+a*delta_1)=D_N(k-1;c)+a*(s_N(c,k)-s_N(c,1))` for positive `k` and horizon.
Thus sign stable under every constant shift is equivalent to equal endpoint
responses. At a nonrough endpoint, a visible prime indicator has nonzero endpoint
response, permitting every real defect value by an explicit constant shift.

## Gates

- [x] Corpus duplication check and precise theorem selection.
- [x] Dependency-closed paper proof and strongest positive survivor.
- [x] Original-source Lean and all-declaration axiom audit.
- [x] Umbrella/index/lint, ledger, artifact audit, cleanup (global lint exceptions below).

## Boundary

This does not claim a counterexample for the specific Möbius or damped weights.
It tests whether squarefree support or coefficient nonnegativity alone can force sign.
All witnesses must be structural families; no numerical experiments or finite examples.

## Corpus evidence

Whole-corpus lexical search for `sieveRenormalizedPrefixDefect constant` returned no
hits. Search with `rough` returned existing sufficient rough-checkpoint theorems and
band results, without a converse. Source checks confirmed the universal prefix
polarization and forward-step identities and the canonical radical-state classification.
No external or global novelty claim is made.

## Paper proof [PROVED HERE]

Write `U_a c(d)=c(d)+a*1_{d=1}`. For `N>=1`, sieve responses shift by `a`; for `N=0`
they all vanish. In either case all additive response differences are unchanged.
The prefix identity `D(M;c)=sum_{j=1}^M s_c(j)*(s_c(j+1)-s_c(j))` telescopes to
`D(M;U_a c)=D(M;c)+a*(s_c(M+1)-s_c(1))`, including empty prefixes.
Squarefree support is preserved because one is squarefree; nonnegativity is preserved
for `a>=0`.

If the endpoint response equals the initial response, polarization gives
`2D=-sum(delta s)^2<=0`, unchanged by every shift. If responses differ, the shift
`a=(t-D)/(s_c(M+1)-s_c(1))` realizes any prescribed real value `t`.
Thus nonpositivity under every constant shift holds exactly on the equal-response
hyperplane; outside it the defect has full real range.

For positive `k`, `R_N(k)=1` iff `k` is `N`-rough. Indeed, a visible prime dividing
`k` divides the radical state; conversely every nonunit small divisor has a prime
divisor, which would give a nonunit radical state. Positivity of `k` excludes the
zero-divisor edge of the definition of roughness.

If `k` is not rough, choose a prime `p<=N` dividing `k` and let `c=delta_p`.
Its initial response is zero and endpoint response is one. Therefore `U_a c`,
supported on `{1,p}`, is squarefree-supported and realizes every real defect value.
For any requested upper bound `B`, choose `a=|B-D(k-1;delta_p)|+1`: coefficients
are all nonnegative and the defect exceeds `B`.

At rough endpoints the existing pure-energy identity gives nonpositivity for ALL
weights (empty prefix handled separately). Combining directions classifies universal
nonpositive checkpoints equally over all weights, squarefree-supported weights,
and nonnegative squarefree-supported weights: precisely `R_N(k)=1`, or roughness.

## Positive survivor

The obstruction yields an exact affine law, an equal-response hyperplane on which
the defect is a negative energy, and a sharp arithmetic classification of every
weight-universal nonpositive checkpoint. It does not refute any fixed Möbius or
damped-weight sign conjecture: those weights fix the constant coefficient.

## Active sawtooth non-identifiability [PROVED HERE]

`centeredDiscreteSawtooth 1 j=0` at every position. Therefore
`activeCenteredSawtoothSum H (U_a c) m j=activeCenteredSawtoothSum H c m j`
for ALL `H,m,j`, without any squarefree restriction. The same prime-supported affine
family thus realizes every real defect at a chosen nonrough checkpoint while fixing
the entire active sawtooth profile across all horizons and positions. This supplies
a precise information-loss obstruction to deriving general defect sign from radical
invariance of the active sawtooth alone. The affine law states the missing unit-mode
dependence exactly.

## Normalized strengthening [PROVED HERE]

The obstruction is not only freedom to change the unit coefficient. At the same
visible prime let `u=delta_p`, `D=D_N(k-1;u)`, and `t=1/(|D|+1)>0`.
The weight `c=delta_1+t*u` is squarefree-supported, has `c(1)=1`, and satisfies
`0<=c(d)<=1` for every `d`, since `0<t<=1`.
Homogeneity and the affine law give
`D_N(k-1;c)=t+t^2*D=t^2*(D+|D|+1)>0`.
Thus even the normalized, coefficientwise unit-bounded nonnegative squarefree class detects exactly rough
checkpoints. This is still not a witness in the specific Möbius or damped family.

Without normalization the full universal upper-bound classification is
`(forall nonnegative squarefree c, D_N(k-1;c)<=B)` iff `rough_N(k) and 0<=B`.
The zero weight proves sharpness at rough checkpoints; the affine prime family
exceeds every real `B` at each nonrough checkpoint.

## Formal verification

- Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/RadicalCheckpointSignRigidityAndGaugeLaw.lean`.
- Twenty-one public theorems, one public definition, one private helper. Actual source
  compiled with `lake --old env lean -o <leaf.olean> <leaf.lean>`: exit 0, no warnings.
- The existing rough-absorption dependency lacked an object file; its individual
  source was compiled successfully without source edits or a full build.
- Separate scratch import and `#print axioms` checked ALL 23 declarations, including
  the private helper: exit 0, no warnings; every closure exactly
  `propext`, `Classical.choice`, `Quot.sound`.
- Source SHA-256: `794f867becd1c93d3158cdd8259efd4c5c9463e73d77e1de316c917224254619`.
- Field umbrella imports this leaf exactly once; `MainTheorems` imports the umbrella.
  All 22 public exports appear in generated API. No umbrella build performed.
- `scripts/formal_tools.py index`: exit 0. `scripts/formal_tools.py lint --check-generated`:
  exit 1, five unrelated BiScaleUncertainty leaves unreachable from their umbrella and
  the existing THIM field-umbrella registration error. No own-leaf finding or stale
  generated file in this run. Global lint is not clean.
- Evidence: `logs/thim-gauge-{lean,axioms,index,lint}.txt`,
  `logs/thim-gauge-rough-dependency-lean.txt`, and `logs/thim-gauge-audit.json`.
  Artifact audit verified exact source hash, fresh object, every axiom entry, public
  API coverage, and import reachability.
- All nine owned scratch files removed after their jobs terminated. README untouched;
  no numerical experiments, proof holes, added axioms, or heartbeat changes.

## Research boundary

The rejected extension is weight-universal nonpositivity away from rough endpoints,
even under unit normalization and coefficientwise bounds. Its positive survivor is
the exact affine defect law and the complete rough-checkpoint sign classification.
The specific Möbius and damped families remain outside this counterfamily; their
additional coefficient relations are the next sign-control question. Research remains active.
