# Strict Möbius margin and uniform damping stability

- **ID:** thim-strict-margin-damping-stability
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Scope:** Strict integer-energy margin and a damping interval uniform across
  every checkpoint in the certified radical fibers.

## Plan

1. [x] Read objective, all 314 README lines, relevant memory and current source; corpus searches.
2. [x] Close paper proof of the strict margin and uniform stability mechanism.
3. [x] Formalize, run actual-source audit and all axiom closures.
4. [x] Wire leaf, index/lint, reconcile ledger/cards/memory, clean owned scratch.

`update_plan` unavailable; this card tracks work. README is read-only.

## Paper proof

For N≥2 choose a prime N<p≤2N by Bertrand. The Möbius path has values
s(1)=1, s(2)=0, s(p)=1, s(2p)=0. Integer squared increments dominate
absolute increments, so if M+1≥4N, splitting at p and 2p yields
`E_N(M)≥3+|s_N(M+1)|`. Polarization then gives
`2D_N(M)≤s_N(M+1)²−|s_N(M+1)|−4`.
Thus |s_N(M+1)|≤2 implies D≤−1. If M+1≤4N, the established unit envelope
and previous strict unit-response theorem give the same conclusion.
Consequently every nonempty prefix with endpoint magnitude at most two has
D≤−1, at every N≥2. This strengthens the prior nonpositive certificate.

For fixed N and each 2≤r<6(N+1), the finite damped defect
ε↦D_N(r−1;c_ε) is continuous at zero and starts at most −1. Finitely many
such r therefore share one δ_N>0 on which all these defects are <−1/2.
Squarefree radical reduction transfers that same interval to every endpoint
whose radical lies in this finite set, regardless of endpoint height or power
exponent. Radical one has exact nonpositive defect for every damping exponent.
N≤1 has identically zero defect. Hence for every N there is δ_N>0 such that
|ε|<δ_N and R_N(M+1)<6(N+1) imply D_N(M;c_ε)≤0, uniformly for all M.
The interval may depend on N; no explicit size or all-ε assertion is claimed.

## Baseline and limits

Classical ingredients: Bertrand's postulate, integer total-variation control,
discrete polarization, continuity of finite sums, and radical invariance.
Equivalent classical statement uses s_N(k)=Σ_{d|k,d≤N}μ(d) and its damped
version. Classification: New formulation with known constituents labeled;
no external priority claim. Observation/shifted-correlation baselines are
TH10 (https://arxiv.org/abs/1009.5281) and CMS16
(https://arxiv.org/abs/1612.03136). The identical truncated divisor sum appears
in Helfgott–Thompson Proposition 3.2 (https://doi.org/10.1007/s40993-022-00408-8).

Current corpus searches returned partial=false, 74119 inventoried files,
zero pending, generations1454592 and1454607; compiler coverage mixed.
All ranked candidate/source-argument statements inspected. No matching strict
amplitude-two or damping-stability theorem found. Full positive-damping
nonpositivity before 6(N+1) remains open; the integer inequality cannot be
applied directly to real-valued damped jumps.

## Stronger survivor exposed during formalization

Continuity yields a bilateral interval |ε|<δ_N, not only positive damping.
The strict margin also extends to rough radical-one endpoints: small endpoints
are in the finite certified set; a large rough endpoint has the same response as
some prime N<p≤2N and lies after it, so equal-response energy monotonicity
bounds its defect by that finite prime checkpoint. Thus for N≥2,M≥1,
all certified radical fibers have D<−1/2 on one common interval.

At N=6p−1,k=30p, response is two at zero damping. Continuity supplies another
interval where response remains greater than one. Intersecting intervals gives
unit-envelope failure together with strict negative defect, for every positive
power, uniformly in exponent. For ε≥0 the existing bound below 5(N+1) means
these remain first unit-envelope failures at the family horizons.

Draft Lean confirms the strict integer-energy argument, uniform stability on
all certified fibers, and counterfamily power separation without warnings.
The strict-positive envelope classifications also compile without warnings.
Actual-source and closure audits passed.

## Strict-positive envelope classification

A universal response bound valid for every ε>0 passes to ε=0 by continuity.
Therefore excluding zero damping does not enlarge the universal ratio or
additive buffer: uniformly over ε>0, the unit envelope on k≤C N holds iff
C≤5, and on k≤5N+b iff b<5. This is a family-uniform statement, not the
optimal cutoff for each fixed positive ε. The response-two prime family has
an actual positive interval of envelope failure with a strict negative defect
survivor, so the obstruction does not rely only on a limiting value.

Focused corpus query `strictly positive damping unit envelope ratio additive
boundary continuity zero` returned partial=false,74123 files,zero pending,
generation1454675. All ranked candidates/source arguments inspected; found
only the existing ε≥0 classifications. Lean proof of this extension passed. Full scratch: 17 public theorems, two
private helpers; actual source packaged as StrictMobiusMarginAndUniformDampingStability.lean.

## Verification

- Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/StrictMobiusMarginAndUniformDampingStability.lean`.
- SHA256: `a70c33678dcc8e460f13888494892ac6a4bf3a0250b977e51e16c4960b9e2c90`.
- Full scratch and actual-source `lake --old env lean` both exited 0 without warnings.
  All 17 public theorems and two private helpers use exactly {propext, Classical.choice, Quot.sound}.
  Additionally audited 4 compiler-generated helpers; every closure is standard-only.
- `logs/thim-stability-audit.json` checks all declared/generated closures, 17
  baseline docstrings/API entries, source/dependency hashes and fresh artifacts,
  unique umbrella import, MainTheorems reachability, whitespace and prohibited declarations.
- Evidence: `logs/thim-stability-{lean,axioms,index,lint}.txt`.
  `lint --check-generated` exits 1 with 7 external findings, recorded exactly in
  the audit JSON. No new-leaf or prohibited-declaration finding.
  Generated checks saw stale shared indexes during concurrent edits; all 17 owned API entries were verified. No globally clean freshness gate is claimed.
- All owned jobs terminal; twelve owned scratch files removed. README not edited.
  No full/umbrella builds, numerical experiments, added axioms, heartbeat changes,
  commits or pushes. Continuing research goal remains active.
