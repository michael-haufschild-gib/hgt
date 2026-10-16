# CHMD infinite exact critical band — 2026-10-16

Persistent unconditional RH goal remains ACTIVE and unbounded. Do not mark complete or blocked. Ultimate objective is premise-free Lean RH via CHMD, not achieved. Read objective attachment on every new turn: /Users/michael/.codex/attachments/2c5020c9-b71c-40b8-ba6c-e8fb1100e229/pasted-text-1.txt.

## Structural contribution completed

Actual small translates of the theta source now belong to the complete full prime--archimedean Doob graph. Pole-annihilated symmetric translates give a countably infinite independent family in its exact signed radical. The entire closed radical has a canonical graph-orthogonal removal preserving every signed mixed pairing, the original primitive moment, and separate source/edge orthogonality. The complementary signed form is nondegenerate; its positivity remains unproved.

This is stronger than the earlier primitive cusp escape result: the new vectors satisfy the weak jump eigenvalue-one identity against EVERY vector of the actual full domain. It is not merely zero diagonal energy, a formal Fourier multiplier, or a residual-free escape sequence.

Prior foundation: `mem:rh/chmd-full-jump-core-density-2026-10-16`, `mem:rh/chmd-primitive-cusp-escape-2026-10-16`, `mem:rh/chmd-complete-doob-source-closure-2026-10-16`.

## Exact mathematics and files

1. CHMDThetaTranslateMass (namespace RHTower.CHMDThetaTranslate):
ratio a x = Phi(x-a)/Phi(x).
memLp_ratio proves membership in L2(Phi(x)cosh(x/2) dx) whenever 1 < 2 exp(-2|a|).
Uses literal full theta upper/lower cusp envelopes, not a finite-atom model.
radius = log(4/3)/2 > 0; |a| <= radius implies admission.
cusp_integrable proves exp(b|x|-c exp(2|x|)) integrable for c>0 by an analytic squared-polynomial domination.
No sharp maximal admission boundary is claimed.

2. CHMDSignedGraphPolarization (namespace RHTower.CHMDDoobGraph):
sourcePair p q = <edge p,edge q> - <source p,source q>, jointly continuous.
testLift f is the actual compact inverse-Doob lift; energy and mixed translation invariance proved.
cauchySeq_of_energy_transfer: source-coordinate Cauchy convergence plus exact equality of signed difference energies with a graph-Cauchy sequence implies graph-Cauchy convergence. Does not use signed positivity.

3. CHMDThetaTranslateGraph (namespace RHTower.CHMDThetaTranslate):
approx a n = testLift of translate by a of Phi*cutoff_n.
Its signed difference energies equal those of unshifted cutoffLift exactly.
Weighted source dominated convergence and energy transfer yield strong graph limit lift a ha.
lift_source_ae is the literal ratio.
pair_lift_test: B(lift a, testLift f) = -coshHalfMoment(translate f (-a)).
Thus compact mixed pairing depends only on the two hyperbolic moments.

4. CHMDThetaCriticalModes:
critical a ha = lift a + lift(-a) - 2 cosh(a/2)*constantLift 1.
critical_source_ae identifies the literal ratio filter.
critical_radical: B(critical a,q)=0 for EVERY q:SourceGraph, using full compact-core density.
critical_primitive, critical_jump_identity, critical_energy.
critical_ne_zero for any nonzero admitted a, by integrating the un-gauged source filter and using integral Phi>0 and cosh(a/2)>1.
exists_exact_primitive_critical has no hypotheses.

5. CHMDInfiniteCriticalModes:
shifts n = radius/(n+1), positive and strictly decreasing.
sequence n = critical(shifts n).
Full-theta cusp separation shows polarSource(a)/Phi(x-a)->1; smaller positive shifts divided by this denominator tend to zero.
Least occupied coefficient of a finite relation is forced to zero.
criticalFunctions_linearIndependent then sequence_linearIndependent (actual graph vectors, via source representatives).
exists_infinite_exact_primitive_critical at line 165: independent sequence in compactCore, primitive in original mass, exact full-domain weak jump identity.

6. CHMDCriticalBandReduction (namespace RHTower.CHMDDoobGraph):
signedRadical = {p | forall q, sourcePair p q=0}, closed and complete.
radical_inner_eq_two_source; radical_norm_sq; radical_primitive.
criticalProjection = signedRadical.starProjection; reducedSource = id-criticalProjection.
projection_source_orthogonal and projection_edge_orthogonal.
sourcePair_reduced preserves every mixed signed pairing; sourceEnergy_reduced.
reduced_nondegenerate at line 94: restricted form on radical orthogonal complement has no radical.
source_mass_decomposition and reducedSource_primitive_pair.
criticalBandSequence_linearIndependent at line 124: independent sequence INSIDE the closed radical.
exact_critical_band_decomposition at line 128 gives full canonical decomposition and all preservation identities.
No selfadjoint unbounded generator, compactness of the reduced source embedding, spectral gap, or primitive positivity is proved.

## Source integrity

- formal/GaloisForLFunctions/RHTower/CHMDThetaTranslateMass.lean: 139 lines, 11 declarations; SHA256 c5ddfeb1e38ebb377b420bb56605e92519b0cd19c36c76d5f37b79793a2a81ff
- formal/GaloisForLFunctions/RHTower/CHMDSignedGraphPolarization.lean: 145 lines, 19 declarations; SHA256 b50901742fcc3699541c5df6a736b634d45449fe9ac4e68db80d8fa01c972026
- formal/GaloisForLFunctions/RHTower/CHMDThetaTranslateGraph.lean: 145 lines, 16 declarations; SHA256 1d95976c972018d4528e9ec773dd8d69535671c21c7ac36c0028817ae63021df
- formal/GaloisForLFunctions/RHTower/CHMDThetaCriticalModes.lean: 127 lines, 11 declarations; SHA256 321070d8ab0c52211c51b2e5dace7a99b88484c64198db0c85ba2b51a79797fa
- formal/GaloisForLFunctions/RHTower/CHMDInfiniteCriticalModes.lean: 174 lines, 15 declarations; SHA256 f1efa252a6299f338e56f11b775f37a6c98ca51f5094966a09ab399f76306c8e
- formal/GaloisForLFunctions/RHTower/CHMDCriticalBandReduction.lean: 139 lines, 20 declarations; SHA256 a9743539556560b417cb7302fef60a02c09a2821a682bd734291dbaab87d9573

All six leaves wired exactly once into formal/GaloisForLFunctions/RHTower.lean. All six remain untracked (normal workspace state); no commits or pushes.

## Validation / lifecycle

- All six --old leaf builds exit 0. No full/umbrella builds or heartbeat increases.
- All six FINAL plain lake env lean <leaf> audits exit 0 with EMPTY logs.
- ALL 92 declarations #print axioms audited via /tmp: only propext, Classical.choice, Quot.sound.
- 76 explicit have := @Name probes with universe zeros pass, empty log.
- Source hashes unchanged after audits; unique imports and whitespace checked.
- scripts/formal_tools.py index exit 0: 14 changed, 0 removed; generated LEAN_API/GAPS/OVERVIEW.
- GLOBAL LINT EXIT 1, solely six OTHER untracked/unwired leaves:
  RHTower/DeningerHasseHilbertShift,
  RHTower/DeningerHasseResolventTriangular,
  RHTower/DeningerMeyerClosedHasseGenerator,
  RHTower/DeningerMeyerFredholmXi,
  RHTower/DeningerMeyerHasseResolvent,
  HTGeometry/GradedTriangularRegularizedDeterminant.
  The 12 other leaves flagged last turn are no longer flagged. Preserve concurrent work.
- Card moved to docs/drafts/pipeline/3-formalized/chmd-exact-theta-critical-modes-2026-10-16.md; old in-progress path absent.
- All 31 owned scratch files removed with explicit rm -- paths; absence verified. All owned processes terminal and none live.
- Goal status re-read as ACTIVE; no update_goal call.

## Remaining frontier / cautions

Primitive sign on the complementary nondegenerate form remains open. Infinite exact critical multiplicity must be handled before any compact spectral argument. It is NOT established that earlier cusp escape is entirely in this band, or that removing the band makes the source embedding compact.

No new failed route was retired this turn: the small-translation admission and infinite exact critical-mode conjectures succeeded. Earlier speculative derivative approach was replaced before implementation by translated-cutoff energy transfer.

At turn start read headers/inventories of concurrently written CHMD massless/light-cone analytic continuation leaves (see prior full-jump memory/session summary); they were then untracked/unwired and were not used as dependencies here. Current lint no longer flags those leaves, but no independent compilation/audit of them was performed by this agent.

## Lean implementation lessons

- For translate-zero/back-translate inside dependent testLift arguments, use explicit function equality plus testLift_congr; simp/rw alone can fail under proof-dependent arguments.
- Specify literal lambda types for integrability hypotheses before integral_sub; Pi.add/function expressions can block rewriting.
- Give an explicit real-zero target function to Continuous.ae_eq_iff_eq when transferring finite function sums; otherwise an inaccessible zero can remain unresolved.
- Set-valued forall and iInter were not definitionally equal for signedRadical closure: prove set equality with ext/simp first.
- API #check output can shorten namespaces and wrap universe lists. Map output headers to original input names in order; generate have probes with all universe levels 0.
- update_plan unavailable; persistent card used. Serena ignores Lean paths, so rg/apply_patch fallback established.
- No web, novelty audit, old research Markdown, numerical experiments, or subagents used.
