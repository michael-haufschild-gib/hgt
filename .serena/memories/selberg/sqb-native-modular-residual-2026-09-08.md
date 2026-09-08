# SQB exact native modular residual: audited positive survivor

User goal remains ACTIVE and UNPROVED: unconditional Lean proof/falsification of RH via SQB. Frontier map is READ ONLY for this task. Full chain: original Maass source -> modular curvature/exact total mass -> source-specific quarter domination -> Selberg gap -> independent Xi occurrence -> RH. Quarter and occurrence are still open. This turn was concrete progress, not blocked or no progress.

## New closed theorem

formal/GaloisForLFunctions/RHTower/SelbergScatteringNativeResidual.lean, 190 lines, 23 public declarations, namespace RHTower.SelbergScatteringNativeResidual. Imports actual ThetaCuspHawkingBMCuspPacketApproximation, the existing generic Pythagorean identity from ThetaCuspHawkingTeukolskyTiltedAngularLeakage, and source-pure XiEndpointSourceHeightGap.

The actual modular Friedrichs operator is RHTower.D4BMModularCore.energyOperator, A=1-Delta_H (remember shift by ONE; cusp ray starts at 5/4, not 1/4). Existing cuspUnitPacket(tau,L) is an original-domain unit vector. New cuspParameter(tau,eta)=5/4+tau^2+i eta. native_residual_sq supplies Pythagorean split using actual energyOperator_selfAdjoint. cuspUnitPacket_complex_residual_sq proves exact finite-cutoff residual square eta^2+C1(tau)L^-2+C2 L^-4, with original cuspWindowMoment constants. native_unit_residual_lower bounds every domain unit residual by |eta|; cuspApproximateVector_complex_residual_tendsto proves those explicit packets approach that floor.

scatteringEnergy(rho)=1+(rho/2)(1-rho/2). For rho=beta+i gamma, re=5/4+(gamma^2-(1-beta)^2)/4, im=gamma(1-beta)/2. For EVERY actual XiZeroCopy, xiZeroCopy_one_lt_im_sq gives gamma^2>1; actual open strip 0<beta<1 and xi_divisor_support_im_ne_zero imply:
- xiResidualFloor(q)=|gamma|(1-beta)/2 >0.
- xi_scatteringEnergy_re_gt_cusp: real part >5/4.
- xiPacketFrequency(q)=sqrt(re energy-5/4), with exact cuspParameter reconstruction.
- xiNativePacket(q,n)=cuspApproximateVector frequency n; exact unit norm and residual limit equal xiResidualFloor.
- xi_unit_residual_lower covers EVERY original-domain unit vector.
- xi_residual_isGLB: exact greatest lower bound of ALL original-domain unit residuals is xiResidualFloor. Optimality follows from the constructed sequence, not a spectrum premise.
- xi_scattering_no_approximate_eigenvectors excludes ANY unit sequence with residual ->0 at the literal native scattering energy.
- xiResidualFloor_critical: at beta=1/2 the floor is |gamma|/4.

This is not RH falsification: literal native energies fail Hilbert approximate occurrence EVEN AT critical zeros. Only that source/parameter/domain identification is retired. Full SQB and different reconstruction/entire-transform occurrence remain open. Do not claim spectral occurrence from the scalar entire preimage theorem or from these packets; no F(A) operator/domain has yet been built.

## Artifacts

Paper + full proof/audit: docs/drafts/pipeline/3-formalized/sqb-native-domain-residual.md (moved from in-progress).
Narrow failed subclass + strongest positive survivor: docs/drafts/pipeline/5-failed/sqb-native-scattering-approximate-occurrence.md.
Universal STATUS has a new standalone Must distinguish resonance incidence from Hilbert-space occurrence entry with full formula and proof links. Frontier map never edited by this task (peers modified it concurrently). No commits/pushes.

## Verification / process discipline

/tmp/sqb_native_full.lean scratch and direct source lake env lean passed without warnings. All 23 exports audited via /tmp/sqb_native_axioms.lean and .log, ONLY propext, Classical.choice, Quot.sound. Exact full signatures of xi_residual_isGLB and xi_scattering_no_approximate_eigenvectors checked. /tmp/sqb_native_exports.json and /tmp/sqb_native_index_audit.json match all 23 names. Module wired exactly once into RHTower, whitespace and forbidden/numerical proof token scan clean.

Final target lake build GaloisForLFunctions.RHTower.SelbergScatteringNativeResidual PASSED. Its actual cusp source dependencies had stale traces. We honored one foreground Lean process: preflight --no-build, rebuild only one named stale leaf, repeat. 47 necessary dependency modules + final target =48 individual successful audits, EACH built exactly its one named module. Source deps VectorStreamEinstein 167s and QuadraticMixedSource 347s were slow but verified live and completed. No full/umbrella build, no background shell builds, no leftover own Lean processes. All exec/wait handles terminal. Temporary serial audit driver /tmp/sqb_native_serial_audit.py and state .json (status COMPLETE) safely preflighted each leaf before building. /tmp/sqb_native_build_audit.json lists all48; logs /tmp/sqb_native_dep_1.log through _48.log; last log is final target. Native final target took 7.3sec command overhead. Generated research index refreshed.

Final full lint /tmp/sqb_native_final_lint.log FAILED ONLY on 9 concurrent unrelated unwired modules: RHTower.SelbergMaassCurrentFunctional, SelbergMaassCurrentTests; HTGeometry.FokasLenellsRawBounds, RawDivided, RawEndpoints, RawEvolution, RawInteraction, RawScattering, RawZero. Existing large-file warnings. Do not claim repo-wide lint passed, and don't wire other tasks' unfinished modules. New module no lint errors. Source code unchanged after final build.

## Broad searches and possible next constructive source work

Queries full OR/module-unrestricted, returned metadata (NOT every proof read): source products351decl/205mods; occurrence317/144; differential lifts754/159; broad scattering/resonance/spectrum6234/1347; broad Eisenstein/modular/eigenfunction9320/672; residual mechanisms5831/1865. JSONs /tmp/sqb3_source_products.json, sqb3_occurrence.json, sqb3_differential_lifts.json, sqb3_broad_spectral.json, sqb3_broad_automorphic.json, sqb3_residual_bounds.json. No numerical experiment, no runpod computation, no numerical proof input.

While dependencies built, an additional broad OR search for functional calculus / closed inverse / spectral mapping / analytic vector / operator exponential / heat semigroup found107decl/50mods, /tmp/sqb4_operator_calculus.json. Only metadata plus declaration names inspected; NO new operator proof/card yet. Potential next CONSTRUCTIVE mechanism: previous entire casimirTransform F has F(real lam)>=-1, grows rapidly above quarter. Actual A is closed inverse of bounded positive covariance B=J J*. Define on positive x, g(x)=1/(F(1/x-1)+2), extend g(0)=0; prove continuity on spectrum of B, 0<=g<=1 and zero only at0. Let C=cfc g B. To obtain actual transformed operator, prove C injective/dense range from B injective, then closedDenseInverse(C)-2I gives F(A-1) with lower bound -1. This could construct the missing operator/domain for the entire scalar transform; it STILL would not supply Xi occurrence. A kernel transfer may be proved by uniform approximation x*g(x)/(g(x)+epsilon) ->x on compact spectrum, avoiding an assumed spectral measure. This is an unimplemented candidate, not an established theorem; inspect current APIs and write paper card before code. Compact smooth cusp packets must NOT automatically be assumed in the unbounded entire-functional-calculus domain.

Relevant inspected names in HTGeometry.FriedrichsFormOperator: formEmbeddingCovariance, friedrichsFormOperator, formEmbeddingCovariance_isSelfAdjoint/injective/dense_range, friedrichsFormOperator_isSelfAdjoint/apply_covariance/re_inner_nonneg. Body not reread this turn except prior context. Mathlib CFC directories exist and source names include cfc, cfcHom_comp, Commute.cfc_real, tendsto_cfc_fun; all signatures still need scratch checking before use.
