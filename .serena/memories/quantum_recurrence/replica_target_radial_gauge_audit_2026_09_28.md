# Exact radial gauge audit — 2026-09-28

Goal ACTIVE/UNSOLVED. Turn delivered a verified proof-route correction, NOT novel physics or complete-circuit exclusion. Prior turn was proof-performance progress only. No Nature/publication completion claim.

## Evidence-changing result
Bare occupied-span coarea action is invariant under arbitrary **targetwise nonzero scalar rescaling**, at every replica order. Source measure, recurrence excision, all surviving source sheets and targets are otherwise unchanged. Thus target residual norm suppression CANNOT itself upper-bound this action. A target's direction can change under anchor subtraction, and actual zero residuals can remove directions: these effects are NOT ruled out.

Existing ReturnExcisedResidualCoareaLaw.lean theorems were sound, but docstrings falsely said residual norm suppression remains inside exact pair action and renormalization erases gain there. Corrected both docstrings, no theorem/proof changes. The capture event does retain norms; the bare projection reporter does not.

## New checked/wired leaf
formal/GaloisForLFunctions/HTGeometry/ReplicaTargetRadialGaugeLaw.lean (namespace GaloisForLFunctions.HTGeometry)
Nine public theorems, no additional hypotheses/axioms (nonzero scalars are data C→ℂˣ):
- finitePureTensorPowerEuclidean_smul: tensor lift homogeneous z^r, all z,r.
- replicaTargetSpan_units_smul: same target span under targetwise nonzero scalars, arbitrary C, finite coordinate α; includes r=0, empty families, zero target vectors.
- replicaTargetProjectionMass_units_smul.
- returnExcisedReplicaIncidenceSpan_units_smul.
- returnExcisedReplicaIncidence_radialGauge (line88): incidence number AND return-excised pair action unchanged for all r, arbitrary μ,X,C,returnSet; no finiteness/integrability suppression assumption.
- finitePureStateFidelity_radial_smul: fidelity scales by norm(z)^2, source/target need not normalize.
- completePureStateCapture_radialGauge (120): exact complete-event equality if each target threshold also scaled by norm(a_c)^2. Does NOT claim fixed physical thresholds invariant or uniqueness of threshold transport.
- replicaReturnShellProjectionMass_radialGauge (136): existing shell reporter retains norm(a_b)^(2r) explicitly in shell weights while projection factors unchanged.
- singleton_returnExcisedReplicaIncidence_radialGauge (151): for any r and a:ℂˣ, constant scalar target a, normalized singleton state1, Dirac source, empty return set, N_inc=1 AND A_exc=1. Nondegenerate counterexample to radial suppression of action, including arbitrarily small nonzero a. Not an ordinary-Hamiltonian physical counterexample, not a disproof of complexity growth.
Wired adjacent to existing ReplicaReturnShellCoareaIncidenceLaw in HTGeometry.lean (9988 at integration).

## Positive survivor reused rather than duplicated
Existing HTGeometry/ReplicaReturnShellCoareaIncidenceLaw.lean already proves:
line50 finitePureStateFidelity_pow_le_replicaTargetProjectionMass_mul_norm_sq;
exact norm replica power; pointwise/measure complete-union shell-weighted reporter.
Existing BuresPositiveReporterIncidenceLaw and StaticChoiResidualDesignFirstReturnLaw provide norm-aware positive-reporter/design alternatives. Still consume hbudget/source estimates. New gauge identity confirms where radial gain resides; do not write these existing inequalities again.

## Verification
Scratch /tmp/hgt-radial-gauge.wad63V/Gauge.lean final session7965 exit0 with no errors/warnings. #print axioms of incidence gauge, capture gauge, shell gauge, singleton example all [propext,Classical.choice,Quot.sound], jointly cover all new helper dependencies. Earlier scratch errors were elaboration (beta reduction, dependent projection rewrite, multiplication cancellation name, pointwise smul eta); none integrated. Name probes in scratch, removed from final leaf, audits only scratch.
Integrated source has same proof bodies; added math header, removed anonymous name probes and #print directives. Checked source equality (initial extra final newline was fixed). Only new leaf, two docstrings, one umbrella import changed. No oleans required/built. No full/umbrella builds, no heartbeat/resource raises, no git/subagents/computations/new axioms. All owned Lean/search jobs terminal; lint26398 exit1 for24 unrelated unwired modules plus concurrent sorry in HTGeometry/AbelianZetaGas/SocleWallDickmanLaw.lean:238. No new leaf lint failure. Do NOT claim repository global lint green or modify concurrent work. Cleanup of scratch Gauge.lean/lint.log and directory follows this memory write.

## Research protocol / provenance
Custom hybrid/deep/method searches used on radial scaling, target norm pruning, fidelity/projection; results partial (semantic_coverage_unavailable, older-generation snapshot). Broad OR search plus rg discovered existing exact norm-retaining shell law, preventing duplication. Read actual definitions of target span, projection, minimal surviving source span, pair action and receiver. Requested hgt-fields-medalist SKILL.md remains absent; L7 fallback protocol and explicit conjecture→failure→positive exact law used. Scientific-method and update_plan tools absent.
Linear homogeneity/projection identities are standard mathematics; NO external novelty claim established. This is validity maintenance that removes a false route assumption, not a newly discovered universal physics law.
Broad arXiv queries mostly irrelevant/empty. Rechecked https://arxiv.org/abs/2609.26885 (late-time complexity, not our first-return closure), and https://arxiv.org/html/2609.07310v1 Prop3.2/Remark3.3: Christoffel conjugated NONorthogonal projection has rank-one correction; asymptotic transfer fixed number of steps, requires corrections vanish; not a growing-replica ordinary-ensemble bound. No new transferable producer established.

## Actual next frontier
Still prove N_inc*A_exc < [c (eps_w-eps_n)/(vT) (1-eps_w^2)^r]^2 with complete occupied circuit image, source sheets, growing r, circuit-budget-dependent initial cutoff. Need angular/source-covariance suppression, or a quantitatively controlled norm-weighted alternative; radial target shrinkage alone cannot deliver bare action bound. Do NOT use kurtosis/residual scalar target moment bounds directly as pair-action estimates. Do NOT substitute full uncut purity or minimum spectral gap. System-size-controlled same-draw continuous first exclusion remains open.
Memory low_replica_complete_incidence_2026_08_09 was read as a lead only: its binomial low-influence reporter result is old paper-only memory, NOT reverified Lean; fixed-shell physical-graph mixing still unproved. Do not promote it to a formal theorem based on the memory.
