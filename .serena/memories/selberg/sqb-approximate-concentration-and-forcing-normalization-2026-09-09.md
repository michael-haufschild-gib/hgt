# SQB bounded approximate concentration and forcing normalization — 2026-09-09

## Goal and constraints
Active unbudgeted goal: unconditional closed Lean proof/falsification RH via SQB. RH UNPROVED. Do not mark goal complete or blocked; this turn made verified progress. Frontier map is READ ONLY and has no git diff. User explicitly requests broad corpus research-tool searches, not narrow AND-only queries. One foreground compiler per agent, `lake env lean FILE`; final audit `lake build MODULE` only, no full/umbrella builds; inspect every preflight Building and final Built record. No numerical proof input, no added axioms, no subagents, no commits. Preserve peer edits, especially Fokas/Gomes/HB/Maass work. Other agents may have live compilers; do not kill theirs. All this turn's sessions were collected. No owned compiler remains.

Current chain: original modular source -> actual entire-transform operator -> independent normalized occurrence at every full Xi parameter -> critical classifier -> RH. Missing occurrence remains. Previous fixed corrected source and its convergent original cutoffs already excluded; do not retry them. Exact original native graph `(A-e)V=H`, resolvent R_e H=V and exact forcing kernel are closed in prior memories.

## New 34 public declarations, all audited
Three new modules, single imports in corresponding umbrellas. New source/scratch proofs emit no warnings, no proof debt. All34 axioms records contain only propext, Classical.choice, Quot.sound. Every declaration appears in generated API index. No numeric experiments or computed proof input.

### 1. HTGeometry/CfcApproximateKernel.lean (4 public)
Namespace GaloisForLFunctions.HTGeometry; imports CfcKernelPreservation (does not modify old CfcZeroSetKernel).
- cfc_exists_approximate_factor_of_zero_set_subset
- cfc_apply_tendsto_zero_of_zero_set_subset
- cfc_apply_tendsto_zero_iff_of_zero_set_eq
- cfc_residual_tendsto_zero_iff_of_singleton_fibre

General complex Hilbert H, bounded SA B, real f,g continuous on compact real spectrum. Inclusion of zero sets -> arbitrarily small operator-norm error g(B)-k(B)f(B) for continuous k. For bounded vector family ||v_i||<=M, M>=0, f(B)v_i->0 in norm implies g(B)v_i->0. Equal zero sets gives iff. Singleton fibre f(x)=c iff x=b gives two-way bounded approximate eigen-equation, without spectral gap, differentiability, bounded quotient, or b in spectrum.

Proof: signed remainder r_n=g/(1+n f²); abs r_n is continuous, decreasing and tends pointwise to0, including f=0 by zero-set inclusion. Dini yields uniform->0, then CFC operator norm->0. Exact continuous factor k_n=n*g*f/(1+n f²), g-k_n f=r_n. Fixed small operator error and uniform vector bound transfer limits. General filters allowed; final singleton invocation must explicitly pass (l:=l) because Lean otherwise cannot infer it in intermediate have.

### 2. RHTower/SelbergScatteringSpectralConcentration.lean (14 public)
Namespace RHTower.SelbergScatteringSpectralConcentration, imports EntireEigenvectors and new generic module.
Original Space, A=1-Delta_H, B=A^-1, C=g(B), T=C^-1-2. q actual Xi, a=xiNativeEigenvalue q=5/4+(Im rho)^2/4, b=a^-1, c=g(b), mu=xiEntireTarget q.
- entireCovariance_residual_tendsto_iff: ANY uniformly bounded family has ||Cv-cv||->0 iff ||Bv-bv||->0. Uses actual singleton g fibre on nonnegative spectrum including0.
- entire_unit_real_residual_lower: for unit actual T-domain v and any mu, -1-Re mu <= ||(T-mu)v||. Derived from real form bound and Cauchy-Schwarz.
- critical_of_entire_approximate: ANY unit actual T-domain sequence with full-Xi residual->0 forces Re rho=1/2. Imaginary SA floor forces Im mu0; real residual floor forces Re mu>=-1; original full-strip classifier forces critical. This is a receiver implication, not independent occurrence.
- nativeCovariance_residual_of_entire_approximate: same inputs give ||Bu-bu||->0. Actual inverse C(T+2)u=u and c(2+mu)=1 imply Cu-cu=-c C((T-mu)u), then approximate singleton fibre.
- nativeRecoveredDomain v : A.domain = Bv, all v.
- nativeRecoveredDomain_apply: A Bv=v.
- nativeRecoveredDomain_residual: (A-a)Bv=-a(Bv-bv).
- nativeCovariance_norm_pos: v!=0 -> ||Bv||>0 by injectivity.
- nativeRecoveredUnit v : A.domain = Bv/||Bv||.
- nativeRecoveredUnit_norm: v!=0 -> exact norm1.
- nativeRecoveredUnit_residual_norm: exact scalar factor ||Bv||^-1*a times ||Bv-bv||.
- nativeCovariance_norm_tendsto_of_residual: unit v with B concentration has ||Bv||->b>0.
- nativeRecoveredUnit_residual_of_entire_approximate: generated actual native-domain unit sequence has (A-a) residual->0 for ANY full-Xi entire unit approximate family.
- nativeRecoveredUnit_sub_tendsto_of_residual: for ANY unit covariance-concentrating sequence, ||nativeRecoveredUnit(v_n)-v_n||->0. Expand as scaled covariance residual plus scalar normalization error.

Thus genuine entire approximate occurrence preserves native concentration and admits norm-close actual native graph recovery. It does NOT produce the input occurrence family.

### 3. RHTower/SelbergScatteringForcingEscape.lean (16 public)
Namespace RHTower.SelbergScatteringForcingEscape; imports new concentration module.
- highEnergyForcing n : original A.domain. Explicit original pre-divisor cusp packet at frequency n; its cutoff index is chosen from already-proved covariance residual convergence, NOT numeric search. For each n choose m with ||B p(n,m)-b_n p(n,m)||<1/(n+1), b_n=(5/4+n²)^-1. Same family before any Xi selection.
- highEnergyForcing_norm: exact unit.
- highEnergyForcing_covariance_norm_le: ||B f_n||<=2/(n+1), using 5/4+n²>=n+1.
- highEnergyForcing_covariance_tendsto: ||B f_n||->0.
- sourceResolvent_covariance_factor: exact R_e f=Bf+e R_e Bf, from actual inverse equation and R_e/B commutation.
- sourceResolvent_tendsto_of_covariance: for any vector family/filter, Bf->0 in norm implies R_e f->0, no boundedness required. Factor (I+eR_e)B is bounded.
- highEnergyForcing_resolvent_tendsto: ||R_e f_n||->0 for each actual q.
- highEnergyForcing_response_tendsto: ||C R_e f_n||->0.
- highEnergyForcing_numerator_tendsto: ||R_e f_n-(2+mu)C R_e f_n||->0 for EVERY complex target mu, including i.
- highEnergyForcing_transport_tendsto: therefore ||K_q f_n||->0 for every actual Xi copy. This is unconditional but DOES NOT locate zeros.
- highEnergyForcing_response_pos: every denominator ||C R_e f_n|| is positive, by both injectivities and ||f_n||1.
- highEnergyEntireDomain q n : actual T.domain = C R_e f_n.
- highEnergyEntireUnit q n : normalized actual response.
- highEnergyEntireUnit_norm: exact unit.
- highEnergyEntireUnit_residual_norm: exact normalized quotient ||C R_e f_n||^-1 * ||R_e f_n-(2+mu) C R_e f_n||.
- highEnergyEntireUnit_nonreal_residual_lower: at explicit mu=i, normalized residual >=1 for every q,n, although unnormalized numerator->0.

All q limits are pointwise, not uniform over Xi copies. General actual-Xi normalized residual limit of this high-frequency forcing family is NOT CLASSIFIED. Do not claim it gives full-Xi approximate occurrence or excludes all normalized source families. Negative result only rejects unscaled numerator as sufficient criterion. Positive survivor: real original unit family, quantitative covariance bound, exact resolvent factorization, full response limits, every denominator positive, exact normalized quotient. No need to assume any off-critical Xi zero exists for counterexample at i.

## Audits and files
/tmp/sqb12_approx_kernel.lean, /tmp/sqb12_concentration.lean, /tmp/sqb12_escape.lean all terminal successful. Tree source checks successful.
Preflight logs /tmp/sqb12_{kernel,concentration,escape}_preflight.log each exactly ONE Building line for requested target. Final /tmp/sqb12_{kernel,concentration,escape}_build.log each exactly one Built record. Build times3.3s,8.5s,7.7s. Counts2967,12763,12764 include cached dependencies, NOT full builds. RHTower builds each replay83 existing dependency warnings; zero warnings from our3 modules. Kernel log0warnings.
/tmp/sqb12_exports.json exact34 public full names/path/module. /tmp/sqb12_axioms.lean + .log all34 standard axioms; only print axioms in tmp. /tmp/sqb12_audit.json parsed allexports/indexrows/singleumbrellaimports/allbuildrecords/ownwarningproofdebt checks.
`python3 scripts/formal_tools.py index` refreshed generated three indexes andsearchdb; /tmp/sqb12_index.log. Full `scripts/formal_tools.py lint` /tmp/sqb12_lint.log EXIT1 exactly5 unrelated unreachable RHTower modules: FokasLenellsCauchyModulation, FokasLenellsOperatorNormCauchy, FokasLenellsOperatorNormInverse, FokasLenellsOperatorNormObstruction, FokasLenellsOperatorNormRegularity. No own lint errors. These peer modules LEFT UNTOUCHED. Do not repeat lint simply to chase concurrent peers; run once after new work.
Docs links/whitespace verified. Frontier gitdiffempty. Last ps showed another agent building GomesFockExponentialFrame; left it alone. No owned process remains.

Docs:
- docs/drafts/pipeline/3-formalized/sqb-native-spectral-concentration.md dependency-closed proof all34 and audit, missing occurrence explicit.
- docs/drafts/pipeline/5-failed/sqb-unnormalized-forcing-occurrence.md excludes ONLY unscaled inference, strongest positive survivor and Lean audit recorded.
- docs/drafts/pipeline/1-in-progress/sqb-native-source-resolvent-transport.md updated current chain/concentration/normalization/worklist/34audit, broad occurrence open.
- universal-law-field/STATUS.md first spectral-fibre entry broadened to bounded approximate kernels; new route-independent Must-control-residual-relative-to-response-norm entry, exact denominator issue + source witness citation. No route-specific assumption masquerades as general constraint.

## Broad research this turn, avoid repeating blindly
Research tool OR batches with full metadata saved (no claim all proof bodies read):
/tmp/sqb12_source_broad.json phrase batch9declarations9modules.
/tmp/sqb12_automorphic_broad.json OR Selberg Maass Eisenstein curvature resonance:11706/1482.
/tmp/sqb12_transmutation_broad.json OR transmutation Darboux squared-source spectral-measure Maass-Selberg:888/155.
/tmp/sqb12_concentration_broad.json OR concentration localization approximate Weyl compactness:4362/1088.
/tmp/sqb12_escape_broad.json OR high-energy high-frequency escape covariance:4517/1003.
Actual sources inspected:
- BVCoPoissonHellingerBetaResonanceTransmutation header+inventory+initialproof: known NO-GO, Beta scalar moves Gamma resonances to half-integer poles; no nonzero polynomial cancels all. Not a source producer.
- XiWardCubicBoundaryResolventTransmuter1-120: exact signed complex rate transfer ((p+z)/(p+w))²; forward real-rate decrease causes normgain>1. Needs extra paying channel; no SQB source identification.
- ThetaCuspHawkingBMNativePeriodPhysicalValue full: physical period analytic; Xi kills forward principal correction ONLY. Reflected Lambda(rho-1)*nativePrincipalMomentContinuation q(-rho/2) remains. diagonal-only iff remaining moment0, not proved.
- ThetaCuspHawkingBMNativePhysicalSourceValue full: retained native diagonal+reflected moment+all3cutoffchannels.
- ThetaCuspHawkingBMNativeFourierCompletedValue full: exact half4Lambda diagonal on absolute chamber; does not remove reflected term.
- ThetaCuspLikelihoodSpectralMeasure first95: positive spectral measure for full normalized theta tail in nonlinear B coordinate; NOT full Xi occurrence.
- SuzukiDonoghueSpectralMeasure first100: explicitly missing actual unbounded source operator/spectral projections, analytic interface only, NOT ready occurrence.
- all generic Cfc files, actual entire inverse/preimage/eigen/cusp/source graph identities used in newproofs were read.

Latest peer Maass memory read this turn: selberg/source-density-and-invariant-carriers-2026-09-09. It closes actual source current density (at nodes zero), withDensity measure, node carrier restrictions and separate modular invariance of current/residual. Original finite congruence source quarter comparison STILL MISSING. Absolute continuity of current + mutual singularity with residual does NOT establish residual singularity relative to ambient volume; nodal volumezero remainsmissing. Do not redo these peer modules. Peer card selberg-original-source-conserved-currents.md suggests actual congruence mixing operator with uniform source-specific dissipation, not simply relabeling Fisher energy.

## Next useful work
Independent normalized full-Xi occurrence remains the real gap. Do not reattempt fixed corrected source, its convergent cutoff family, or just making ||K f_n|| small. Do not count another reformulation of receiver as solving occurrence. Source-specific Maass congruence mixing/quarter comparison or another fully retained arithmetic source construction remains unexplored here. Full native quadratic source moments retain reflected corrections. If inspecting newer peer work, reread current relevant source/memory; corpus changing fast.

Prior exact kernel/29 memory: mem:selberg/sqb-entire-forcing-kernel-and-source-family-obstruction-2026-09-09. Prior58nativegraph: mem:selberg/sqb-original-source-native-graph-2026-09-09. Goal stays active.