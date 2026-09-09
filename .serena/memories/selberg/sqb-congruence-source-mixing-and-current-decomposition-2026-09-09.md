# SQB: actual congruence Reynolds averaging and complete current split

Goal remains ACTIVE: RH is not proved or falsified. Frontier map is READ ONLY for this task. No goal completion/block marker. This goal turn achieved source-specific finite mixing and exact differential current identities, not the quarter comparison or Xi occurrence.

## Constraints and coordination
- User requires broad OR Lean corpus searches, actual source inspection, no training-data starting point.
- One foreground Lean/Lake process per agent. Scratch/source use lake env lean FILE; final audit only lake build MODULE. No full or umbrella builds.
- No numerical proof data or new axioms; all #print axioms in /tmp.
- No subagents used. No commits/push. Preserve other agents' work.
- Frontier was never edited by this work. Shared git status showed concurrent changes in it (27 additions/21 deletions at one snapshot); leave them untouched.
- All owned compiler/build/index/lint handles terminal. Final process scan found no lean or lake process.

## Completed modules: 58 public declarations total

1. formal/GaloisForLFunctions/HTGeometry/FiniteRegularReynolds.lean (11)
Namespace GaloisForLFunctions.HTGeometry.
Imports HTGeometry.ConstraintRelativity.ReynoldsEnergy and Mathlib.Analysis.InnerProductSpace.PiL2.
Actual finite-group Euclidean regular unitary Ug v(q)=v(qg); continuous normalized mean P; exact relation to existing Reynolds operator; constant-coordinate formula; idempotent contraction; fixed vectors iff all regular operators fix them; orthogonal norm decomposition; displacement energy = complement norm squared.
Public names:
finiteRegularUnitary, finiteRegularUnitary_apply, finiteRegularUnitary_mul,
finiteRegularAverage, finiteRegularAverage_eq_reynolds, finiteRegularAverage_apply,
finiteRegularAverage_energy, finiteRegularAverage_idempotent,
finiteRegularAverage_fixed_iff, finiteRegularAverage_norm_decomposition,
finiteRegularAverage_norm_le.

2. formal/GaloisForLFunctions/RHTower/SelbergMaassCongruenceAverage.lean (21)
Namespace GaloisForLFunctions.RHTower.SelbergMaassCongruenceAverage (NOT direct RHTower).
Fix actual f : MaassCuspEigenform (realImage (Gamma (N+1))) lam.
Actual sourceVector is complete quotientForm value family in EuclideanSpace C (Deck N).
sourceMean = card^-1 sum actual Fq; centeredComponent = Fq-mean.
Original integral pullback equals regular finite quotient action.
Mean fully modular, complement actual quotient permutation.
Exact full density = card*normSq(mean)+sum normSq(center).
Exact Reynolds loss = complete original centered variance.
Both mean and every remainder are actual C² solutions of same Maass equation with every integral cusp condition; complement original Gamma invariant.
Mean is either identically zero OR an actual nonzero full-modular cusp eigenform of SAME lambda. Nonzero mean never assumed.
Public names:
sourceVector, sourceMean, centeredComponent, sourceVector_pullback,
sourceMean_modular, centeredComponent_pullback, average_sourceVector_apply,
sourceVector_norm_sq, average_sourceVector_norm_sq, complement_sourceVector_norm_sq,
density_mean_variance, source_mixing_energy, sum_centeredComponent,
sourceMean_smooth, sourceMean_eigenfunction, sourceMean_cuspidal, meanInvariant,
sourceMean_zero_or_full_modular_eigenform, centeredComponent_eigenfunction,
centeredComponent_cuspidal, centeredInvariant.

3. formal/GaloisForLFunctions/RHTower/SelbergMaassAverageCurrents.lean (26)
Namespace GaloisForLFunctions.RHTower.SelbergMaassAverageCurrents.
Imports new CongruenceAverage + SelbergMaassCurrentCurvature.
For actual Fq=m+aq, sums aq and d aq both zero:
J(Fq,Fr)=H_r-H_q+K_qr, Hq=m*d aq-dm*aq, Kqr=aq*d ar-ar*d aq.
Each row/column sum K is zero, so full mixed cross sum vanishes.
sum |H_r-H_q|²=2n sum |Hq|².
Exact pairEnergy = half sum |J(aq,ar)|²+n sum |J(m,aq)|².
Hermitian pairing splits exactly; phase = n*meanPhase+centeredPhase BEFORE squaring.
S_v = centered pair energy+n*mixed bracket squares+(n meanPhase+centeredPhase)^2.
Original D*radialResidual=S_v.
Original R_e³*curvatureWeight=S_x+S_y+e²*gradientDensity, entire regulator kept.
Mixed brackets give nonnegative lower part of original pair energy and full regularized curvature numerator.
div J(mean,centerq)=0 from actual common Maass potential, no amplitude division, no assertion about quotient periods.
All original fields vanish iff mean and all centered fields vanish: exact common-node preservation.
If sourceMean is identically zero, centeredField is full original field and all mean/center mixed brackets vanish. Does NOT assert existence/nonexistence of zero-mean Maass forms.
Public names:
finite_mean_pair_decomposition, meanField, centeredField, meanField_smooth,
centeredField_smooth, field_mean_decomposition, meanField_dir, centeredField_dir,
sum_centeredField, sum_centeredField_dir, pairEnergy_mean_decomposition,
finite_mean_hermitian_decomposition, hermitianPairing_mean_decomposition,
meanPhaseCurrent, centeredPhaseCurrent, phaseCurrent_mean_decomposition,
radialResidual_mean_decomposition, mixed_brackets_le_pairEnergy,
mixed_current_conservation, field_zero_iff_mean_centered, meanSplitCurrentEnergy,
meanSplitCurrentEnergy_eq, curvature_mean_decomposition, mixed_brackets_le_curvature,
centeredField_eq_of_mean_zero, mixed_bracket_zero_of_mean_zero.

## Audits COMPLETE, do not rerun absent changes
Scratch /tmp/sqb13_regular.lean, /tmp/sqb13_average.lean, /tmp/sqb13_currents.lean all passed. All three tree source checks passed with no new-module warnings.
Preflight lake --no-build build <specificModule> listed exactly intended target stale in each case.
Final lake build <specificModule> rebuilt exactly one module:
FiniteRegularReynolds 3.7 seconds (8656 cached graph jobs),
SelbergMaassCongruenceAverage 3.5 seconds (8788 graph),
SelbergMaassAverageCurrents 4.1 seconds (8808 graph).
Logs /tmp/sqb13_{regular,average,currents}_{preflight,build}.log.
#print axioms audit /tmp/sqb13_axioms.lean -> /tmp/sqb13_axioms.log: all 58 unique expected names, no extra axioms beyond propext/Classical.choice/Quot.sound.
Expected names /tmp/sqb13_api_names.txt.
scripts/formal_tools.py index passed; all 58 exact module+name rows in LEAN_API.md.
Each new module wired exactly once in its umbrella.
scripts/formal_tools.py lint PASSED (existing large-file warnings), /tmp/sqb13_lint.log.
No forbidden tokens in any new module, scoped git diff --check passed.
No full builds, computational experiments, web claims, or Runpod tasks.

## Documentation
- New dependency-closed proof/audit: docs/drafts/pipeline/3-formalized/sqb-congruence-source-mixing.md.
- Current own card: docs/drafts/pipeline/1-in-progress/sqb-congruence-source-mixing.md (construction complete, comparison open).
- Added one route-independent universal ledger entry near top: must retain what averaging removes; exact variance, complete mean/remainder currents, combined phase, zero-average case, normalization. Link to closed proof.
- Did not edit peer conserved-current card or frontier map.
- Previous native-resolvent card remains valid; no new occurrence theorem.

## Broad corpus discovery (metadata, not all proofs read)
Saved full JSON:
- /tmp/sqb13_mixing_broad.json: congruence mixing entropy Poincare Hecke --any; 4282 declarations/825 modules.
- /tmp/sqb13_projection_broad.json: Reynolds averaging barycenter variance projection --any; 6241/1641.
- /tmp/sqb13_geometric_broad.json: isoperimetric Cheeger holonomy nodal winding uncertainty --any; 2954/509.
- /tmp/sqb13_expansion_broad.json: expander Kazhdan mixing Poincare congruence --any; 3188/594.
All no per-module cap, no exploration extras, high limit.
Actual source inspection: existing literal congruence trace, Maass definitions, cusp translation,
SourceCurrents, PairPhaseEnergy, TraceEnergy, TraceRadial, CurrentCurvature; existing ReynoldsEnergy entire proof; PiLp/PiL2 API.
Further bounded source inspection:
HTGeometry.ConstraintRelativity.CoframePortUncertainty first190: continuous augmentation/completion dichotomy, not a modular lower bound.
RHTower.L2FourierUncertainty full: bounded-support Fourier unique continuation requires actual bounded support, absent for this source.
HTGeometry.TorusTrigPoincare actual variance theorem (150-215): torus integer-frequency gap; no modular transfer constructed.
CapacityReplicaUncertainty/EulerSupportEnergyUncertainty declaration inventories inspected; not claimed used or fully read.

## Exact remaining gap / next work
Full chain: original modular source -> independent quantitative source comparison or transformed occurrence -> critical-line classifier -> RH.
Maass face: need totalOrbitCurvature >= amplitudeMass/8, keeping complete actual current and nodal measures, full amplitude normalization, all core/cusp costs. This yields Selberg quarter via existing total mass identity. Finite Reynolds averaging gives an exact variance, not a comparison between finite group displacement and actual derivative/current energy. Mixed lower bound can vanish when full source is retained by centered channel. Mean nonvanishing or complementary control MUST be proved if used.
Transformed face separately needs source-derived occurrence at full Xi parameter or another Xi-to-Maass handoff. Unique real preimage/classifier is still a receiver.
Do not relabel these identities as RH or Selberg proof. No route retired; this is a positive exact decomposition, not an all-route no-go.

## Useful Lean lessons
PiL2 vector sum: WithLp.ofLp_sum + Finset.sum_apply (no PiLp.sum_apply).
ContinuousLinearMap use unprefixed smul_apply/sum_apply aliases.
Explicit (S := EuclideanSpace C G) in Reynolds theorem and local hU avoids expensive type inference; no heartbeat increase.
Mean C² equation requires actual first-derivative germ equality before second derivatives; private helpers in average module.
Cusp limits simpa [IsZeroAtImInfty,ZeroAtFilter,sourceMean/centeredComponent] with mul_zero/sub_zero.
Finite cross sums use simp only to avoid over-rewriting; phase extraction needs zero_add and add_zero.
Function zero equality: funext w; simp [meanField,hm].
Use namespace GaloisForLFunctions.RHTower for Maass modules. Previous scattering modules often namespace direct RHTower.

Prior state continues in mem:selberg/sqb-approximate-concentration-and-forcing-normalization-2026-09-09.
Do not repeat fixed-source/cutoff occurrence attempts: their full normalized residual is already proved positive.
