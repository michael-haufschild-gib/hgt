# SQB exact forcing kernel and original source-family obstruction

## Goal/state
Active unbudgeted goal remains unconditional closed Lean proof/falsification of RH via SQB. RH UNPROVED. Previous goal turn (58 declarations) and this turn (29 declarations) both substantive verified progress; no blocker streak. Do not mark goal complete/blocked. Frontier map READ ONLY despite old stored objective. User requires broad OR corpus research, not only ultra-specific AND searches. No computations/numerical experiments or proof inputs. One foreground Lean/Lake compiler per agent; source/scratch lake env lean FILE; final lake build MODULE only, no full/umbrella builds. All handles collected and owned compilers cleaned. No subagents or commits. Preserve peer changes.

Current card: docs/drafts/pipeline/1-in-progress/sqb-native-source-resolvent-transport.md.
Full new paper/audit: docs/drafts/pipeline/3-formalized/sqb-entire-forcing-kernel.md.
Specific failed construction: docs/drafts/pipeline/5-failed/sqb-fixed-corrected-source-exact-occurrence.md (title now fixed corrected source and convergent cutoffs). Negative theorem AND strongest positive survivors closed in Lean before recording no-go. Do NOT retire all SQB or all approximate families from this result.
Universal ledger adds spectral-fibre/eigenspace preservation rule and clarifies distinction between graph approximation of a source and spectral approximation. Frontier map has no diff.

## New decisive result
Let A=1-Delta_H actual native operator, B=A^-1, C=g(B), T=C^-1-2 actual entire operator. For q an actual Xi copy rho, e=1+(rho/2)(1-rho/2), mu=xiEntireTarget q=F((rho/2)(1-rho/2)), a=5/4+(Im rho)^2/4, b=a^-1. R_e=sourceResolvent q=(A-e)^-1, K_q=entireForcingTransport q=(I-(2+mu)C)R_e.

For EVERY native vector f:
K_q f=0 IFF f=0 OR (Re rho=1/2 AND Bf=b f).
For EVERY native v:
v-(2+mu)Cv=0 IFF v=0 OR (Re rho=1/2 AND Bv=b v).
On actual A.domain, Bv=bv IFF Av=a v. No nonzero eigenspace occurrence is asserted. This is exact positive kernel classification, stronger than a source-specific negation.

Original full corrected V=sourceVector q, H=original forcingVector q satisfy (A-e)V=H and R_e H=V (previous goal turn). New theorem: H is NOT cV for ANY complex c. Hence original V is not a native eigenvector at ANY complex parameter. Singleton-fibre classification then gives original G=sourceResidual q !=0, K_q H!=0, and ||(T-mu)U||>0 for original U=CV/||CV|| at EVERY actual Xi copy, including critical copies.

Additional actual-family theorem: original complete compact modular approximants V_n=sourceApproxDomain q n are nonzero for every n. Construct actual normalized entire-domain U_n=C V_n/||C V_n||, prove ||U_n||=1, U_n->U and T U_n->T U in native Hilbert norm. Therefore ||(T-mu)U_n|| tends EXACTLY to ||(T-mu)U||>0. This particular original cutoff family cannot supply approximate occurrence at ANY actual Xi copy. Do not keep trying to prove its residual tends to zero. Other sources/different approximate families remain open. No uniform lower bound across arbitrary families or all q is asserted.

## Four modules / 29 public declarations, all fully audited
1. formal/GaloisForLFunctions/HTGeometry/CfcZeroSetKernel.lean (3 public, final sole-target build 3.3s).
Namespace GaloisForLFunctions.HTGeometry:
- cfc_apply_eq_zero_of_zero_set_subset
- cfc_apply_eq_zero_iff_of_zero_set_eq
- cfc_eigenvector_iff_of_singleton_fibre

2. formal/GaloisForLFunctions/RHTower/SelbergScatteringEntireEigenvectors.lean (9 public, final sole-target build 6.1s).
Namespace RHTower.SelbergScatteringEntireEigenvectors:
- xiNativeEigenvalue q := 1+nativePartner (q.1:complex).im
- xiNativeEigenvalue_pos
- entireCovarianceSymbol_fibre (t nonzero real, x>=0): g(x)=g((1+nativePartner t)^-1) iff x=(1+nativePartner t)^-1
- entireCovariance_eigenvector_iff q v: C v=g(b) v iff B v=b v
- critical_of_entire_eigenvector q v hn he (actual T-domain v): nonzero full-Xi eigenvector forces Re rho=1/2
- covariance_residual_zero_iff q v: full v-(2+mu)Cv zero classification above
- covariance_native_eigenvector_iff q v (v:A.domain): Bv=bv iff Av=a v
- sourceResolvent_nativeCovariance_commute q f: R_e(Bf)=B(R_e f)
- entireForcingTransport_zero_iff q f: full K kernel classification above

3. formal/GaloisForLFunctions/RHTower/SelbergScatteringSourceNonvanishing.lean (6 public, final sole-target build 6.7s).
Namespace RHTower.SelbergScatteringSourceNonvanishing:
- globalResidual_nonzero_below_transition q: exists z in closed fd, z.im<2, original globalResidual q z!=0
- forcingVector_ne_smul_source q c: H != cV in actual native Space
- sourceNativeDomain_not_eigen q lam: A(original native-domain V) != lam V for EVERY complex lam
- sourceResidual_ne_zero q
- entireForcingTransport_original_ne_zero q
- sourceUnitVector_residual_pos q: strictly positive actual normalized full-Xi entire residual

4. formal/GaloisForLFunctions/RHTower/SelbergScatteringApproximateSourceResidual.lean (11 public, final sole-target build 8.8s).
Namespace RHTower.SelbergScatteringApproximateSourceResidual:
- sourceApproxDomain_ne_zero q n
- sourceApproxCovariance_norm_pos q n
- sourceApproxEntireDomain q n: actual T-domain vector C V_n
- sourceApproxEntireUnit q n: actual normalized T-domain vector U_n
- sourceApproxEntireUnit_norm q n: norm exactly1
- sourceApproxEntireDomain_equation q n: (T-mu)C V_n=V_n-(2+mu)C V_n
- sourceApproxEntireUnit_residual_norm q n: exact norm quotient with original full target
- sourceApproxEntireUnit_tendsto q: actual U_n values -> U in Space
- sourceApproxEntireUnit_operator_tendsto q: actual T U_n -> T U in Space
- sourceApproxEntireUnit_residual_tendsto q: exact positive-limit residual theorem
- sourceApproxEntireUnit_not_approximate q: NOT Tendsto actual unit residuals to0

## Proof mechanisms
General CFC: for continuous f,g on compact real spectrum, zeros(f) subset zeros(g). r_n=g^2/(1+n f^2) continuous, nonnegative, antitone, tends0 pointwise (at f=0 also g=0). Dini gives uniform0, CFC norm bound gives ||r_n(B)||->0. Exact factor g^2-r_n=(n*g^2*f/(1+n*f^2))*f implies g(B)^2 v=r_n(B)v if f(B)v=0. Limit gives g(B)^2v0; symmetry yields ||g(B)v||²=0. Equal zeros give equal kernels. Apply to f-c and id-b for singleton spectral fibre. No gap or quotient bound assumed.
Actual g-fibre: target b>0 and g(b)>0, so x>=0 with equal g forces x>0. Reciprocal equality yields F(x^-1-1)=F(nativePartner t), since both values real. Existing real_native_preimage_iff at real t!=0 forces x^-1-1=nativePartner t, hence x=b. Actual B spectrum nonnegative. Every actual Xi copy has nonzero ordinate.
Full-Xi kernel: nonzero v with v-(2+mu)Cv0 produces genuine T-domain eigenvector Cv. Self-adjointness gives Im mu0, actual lower form bound gives Re mu>=-1. BOTH feed critical_strip_range_iff, yielding critical placement (reality alone insufficient). Critical line gives 2+mu=g(b)^-1, so residual0 iff Cv=g(b)v iff Bv=bv. Zero vectors handled separately.
Resolvent commutation: v=R_e f satisfies (A-e)v=f. Applying B gives v-eBv=Bf. Native Bv domain admitted, ABv=v; hence Bv and R_e(Bf) solve same actual shifted equation. Nonreal-shift injectivity identifies them. R_e is injective, so commuting through B also transports exact eigen-equations and zero vectors; yields K kernel for ALL f.
Original source: original scalar horizontal mean nonzero every positive height. Pick nonzero value at3/2, move into fd. modular_orbit_height_le gives new height<=max(3/2,1/(3/2))=3/2<2. The original residual equals full scalar there and invariance preserves nonzero value. Original H vanishes below2. If H=cV in Hilbert space, actual AE representatives + continuity + fd=closure(interior fd) give same equality on entire closed fd. At retained point c=0; then H0 contradicts already proved H!=0. This prohibits every native eigenvector equation for V. Exact CFC kernel then excludes G0. Original normalized residual is positive via nonzero G and positive ||CV||.
Actual cutoff family: all cutoffs height a=n+3 equal1 below2, so same original low point proves V_n!=0 using actual core toLp representative and continuity. Injective C gives positive normalization. SourceApproximation already proves V_n->V. Bounded C implies CV_n->CV, with ||CV||>0, so reciprocal norms converge. Exact T(CV_n)=V_n-2CV_n gives both normalized value and actual operator-image limits. Subtraction/norm preserves limit; sourceUnitVector_residual_pos gives positive limit and uniqueness excludes0.

## Audits/processes
All complete /tmp scratch files passed lake env lean without diagnostics: /tmp/sqb11_{kernel,eigen,source,approx}.lean with corresponding .log. New mathlib names checked /tmp/sqb11_names.lean. Each module final lake build MODULE compiled only its named module; all --no-build preflights and every Built line parsed. No full/umbrella build. Modules wired once into HTGeometry/RHTower umbrellas.
All29 public #print axioms reports in /tmp/sqb11_axioms.log (first18), /tmp/sqb11_approx_axioms.log (11) contain only propext/Classical.choice/Quot.sound. #print only in /tmp scratch. /tmp/sqb11_index_audit.json records full verified29 names, module/import coverage, no forbidden code or trailing whitespace. Public exports /tmp/sqb11_{kernel,eigen,source,approx}_exports.json. Generated corpus indexes refreshed. All command handles collected; do not restart completed compilers.
Final full lint /tmp/sqb11_final_lint.log FAILED ONLY for six unrelated untracked RHTower modules missing umbrella imports: FokasLenellsSecondTimeBounds, FokasLenellsSecondTimeDifferentiability, FokasLenellsSecondTimeForcing, FokasLenellsSecondTimeInverse, FokasLenellsSecondTimeMultiplier, FokasLenellsSecondTimeSymbols. Those other-task files left untouched. This records actual invocation, not assumed future state.

## Corpus searches/read discipline
OR eigenvector/spectral-fibre/kernel-preservation/source-cancellation:807 declarations,373 modules (/tmp/sqb11_kernel_broad.json).
OR kernel-inclusion/kernel-comparison/zero-set/functional-calculus:569 declarations,336 modules (/tmp/sqb11_zeros_broad.json).
OR normalization/residual-limit/normalized-convergence:3141 declarations,1403 modules (/tmp/sqb11_normalization_broad.json).
Counts are metadata coverage, NOT claim to read every proof. Actual read CfcKernelPreservation full Dini proof, EntireSymbol, EntirePreimage, EntireTransform range classifier, actual SourceVector/source nonvanishing proof, CutoffForcing actual representatives and continuity, SourceGraph and SourceApproximation definitions/domain values, actual resolvent/inverse APIs. Use rg directory searches (not huge shell globs). Serena Lean symbol indexing unavailable; use rg/read for Lean. No external mathematical claims or training-data assumptions used.
Lean pitfalls: rw with v=... rewrites v inside Cv on both sides; use controlled conv or linear_combination (norm := module). Explicit type for symmetry inner-product equality avoids CFC coercion mismatch. Rewriting A=B^-1 may require an explicitly typed B(Ax)=x lemma before rw. Normalized operator Tendsto simplification needs Function.comp_apply in simp list. Complex-cast derivative/reciprocal expressions should retain explicit inner real annotation.

## Remaining objective / next action
Original native graph and exact forcing transport remain VALID (previous58 declarations). The fixed corrected source and its specific graph-convergent original cutoff family are now CLOSED NEGATIVELY as occurrence producers. Do not attempt G0 or residual->0 for them again. Preserve exact positive kernel classifier and positive normalized graph limit, not just the negations.
SQB still needs an independent producer of occurrence at every full Xi parameter, via another original-source construction, a different controlled approximate family, or the other Maass-specific occurrence/order face recorded in read-only frontier map. Do not postulate native eigenvectors, scalar real preimages, or critical membership. The scalar rational CFC representation of K is optional infrastructure; by itself it cannot remove this proved obstruction. Broad corpus searches must guide the next genuinely different source mechanism. No claim of RH proof/falsification.

Prior context: `mem:selberg/sqb-original-source-native-graph-2026-09-09` (58 declarations and exact original graph/transport); `mem:selberg/sqb-native-forcing-full-core-2026-09-09` (19 original H/full-core declarations); `mem:selberg/sqb-original-modular-cusp-subtraction-2026-09-09` (original V,CV,G); `mem:selberg/sqb-full-source-cusp-norm-2026-09-09` (complete cusp threshold).
