# Physical affine action and explicit commutator producers

- **ID:** physical-affine-commutator-producers
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** continuum-coprime-shear; integer-dilation-cell-coisometry
- **Statement:** Actual physical affine action has an exact positive commutator defect, sharp norm and nonattainment, with explicit finite producers of error2|a|/N.

## Exact theorem and significance

On actual V=L²(ℝ), τ_bq(t)=q(t+b) is an invertible linear isometry,
F_(τ_bq)(t)=F_q(t+b)−F_q(b), and τ_bA_a=A_aτ_(ab) for all real
scales and shifts. Anchored states(d,q) translate as(d+F_q(b),τ_bq),
so primitive evaluation, composition and affine covariance are exact.

For actual bounded C_(a,b)=A_aτ_b−τ_bA_a and c=b(a−1),

    ‖C_(a,b)q‖²=|a|‖τ_cq−q‖²,
    4|a|‖q‖²−‖C_(a,b)q‖²=|a|‖τ_cq+q‖².

Actual ℓ² cell analysis, translated first-cell increments and primitive
injectivity prove τ_cq=−q iffq=0 at every real c. Finite alternating
unit cells have energyN and translation-difference energy4N−2. Their
explicitly dilated, normalized packets P_(c,N) are unit for c≠0 and zero
for c=0. At nonzero gap they give exact commutator deficit2|a|/N.
Therefore

    ‖C_(a,b)‖=if b(a−1)=0 then0 else2√|a|,
    C_(a,b)=0 iff a=0 or a=1 or b=0,
    ‖C_(a,b)q‖=‖C_(a,b)‖‖q‖ iff C_(a,b)=0 or q=0.

A small nonzero gap alone cannot give a small operator bound on full
physical L². The positive survivor is the exact antiperiodic defect and
explicit near-attaining family, proved on paper and in Lean. Future
small-gap control must construct or specify a regularized range. Existing
pointwise primitive resistance estimates remain valid.

## Scope and proof gates

- [x] Corpus and primary-source parent audit, with coverage limits below.
- [x] Dependency-closed paper proof before any new leaf:
  docs/reports/BiScaleUncertainty/PhysicalAffineCommutatorProducers.md.
- [x] Six serial direct leaf checks with empty logs/current normal outputs.
- [x] All76 public axiom checks,29 principal signatures,73 API probes.
- [x] Six unique umbrella imports and76 exact catalog locations.
- [x] Scoped whitespace/freshness and unchanged read-only README.
- [x] Global lint run; unrelated failures recorded explicitly below.

No full/umbrella build, heartbeat increase, added axiom, numerical experiment
or unproved analytic admission premise. Standard Lean axioms only:
propext,Classical.choice,Quot.sound. Actual full-space translations do not
imply a unitary group on the positive half-line or completed divisor-domain
invariance. No full SourceGraph identification, unweighted log H1 or RH
claim. Classical affine representations and orthogonal packets are parents;
no external novelty claim. Trap10 is implemented through explicit producers
and unconditional errors; no receiver-only or pre-floor subtraction route.
One connected significant contribution, certified18/100; goal remains active.

## Formal modules and evidence

| Module | Lines | Public declarations |
|---|---:|---:|
| PhysicalTranslation |120|17|
| PhysicalAffineAction |137|23|
| PhysicalAntiperiodicRigidity |117|7|
| AlternatingPhysicalPackets |92|8|
| PhysicalAffineProducers |103|15|
| PhysicalAffineSharpNorm |105|6|

Total674lines;76public=66theorems+9defs+1abbrev. Final scratch audit:
/tmp/physical_affine_axioms.lean. Evidence:
/tmp/physical-affine-{axioms,lint-final,index-post-lint}.log,
/tmp/physical-affine-{audit-names,manifest-report,leaf-checks,lint-errors}.json,
/tmp/physical-affine-api-entries.txt. No standalone failed probe is retained.

Global lint --check-generated exits1 for22 unrelated unreachable modules:
CollarEndpointTailMass, CollarMeshBounds, CollarRadialPenalty, CompactLipschitzLevyEnergy, CompactProfileLipschitz, ConcentratedCollarExtension, ConcentratedCollarPenalty, ConcentratedCollarRetraction, FermiNymanBrickDictionary, LogarithmicArrayRadialComparison, NyquistWideSourceEnergy, RightNodeCollarPartition, SharpCollarAsymptotics, SharpCollarCutoffComparison, SignedPrimePolarCausalJumpBounds, SignedPrimePolarRampRegularity, SignedPrimePolarSourceArchimedeanCertificate, SignedPrimePolarSourceJumpDomain, SignedPrimePolarSourceJumpUpper, SignedPrimePolarTentJumpLower, SignedPrimePolarTentRegularity, VasyuninReciprocityAndExactTailGramProducer.
Also concurrent LEAN_API drift;381 large-file warnings. No own or proof-debt
error. Index refreshed after lint, then all76 own catalog locations rechecked.
Repository-wide green is not claimed; concurrent files are preserved.

## Corpus and source provenance

Query `actual L2 physical translation dilation anchored primitive affine action`,
BiScaleUncertainty filter, --any,60-second budget. All20 candidate statements
and20 source arguments inspected; no proof ideas or ingredient sets.
Existing continuous shear/affine commutator estimates and compact-source
translation membership are parents. Current package17 drafts appeared in
results while unverified; they are not independent certification. No general
physical L² translation/anchored-action package returned; this is not an
absence or novelty proof. partial=true, text/source retrieval interrupted,
generation1446938 pending, refresh incomplete/background_indexer_running.
Evidence: /tmp/integer-dilation-next-search.json. The follow-up below audited the stronger sharp-commutator mechanism.

Follow-up query `sharp translation dilation commutator norm alternating
disjoint packets nonattainment`: all20 candidate and20 source-argument
statements inspected. Existing coprime projection norm attainers,
continuous affine commutator bounds, compact-source packet Gram formulas
and dyadic anchored producers are relevant parents. They do not supply
the proposed full physical translation-commutator package. Own unverified
package17 drafts again appeared. partial=true; both retrieval stages
interrupted; generation1447034 pending, refresh incomplete; returned
declarations marked source_only. No proof ideas/ingredient sets. Evidence:
/tmp/physical-affine-commutator-search.json. No absence/novelty conclusion.

Current package query `physical translation dilation commutator sharp norm
periodic L2 alternating packets`: all20 candidates inspected; no source
arguments, proof ideas or ingredient sets returned. partial=true; text/source
retrieval interrupted, generation1447234 pending, refresh incomplete,
source_only. Evidence /tmp/physical-affine-search.json. Primary mathlib Lp
pullback API and UCLA translation/Haar notes inspected; links in the paper.
No absence or external novelty inference.

## Next unproved candidate

../0-backlog/physical-box-average-affine-regularity.md seeks actual L² box
averages with exact variance loss, constructed derivative and small-gap
commutator control. Its own corpus audit is recorded there. Uncounted;
primary-source and dependency-closed paper proof remain required.
