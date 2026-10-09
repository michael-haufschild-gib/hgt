# PURE EXPONENTIAL CRITICAL ENDPOINT IS NOW CLOSED

OUR LEAN CORPUS ONLY. No web or external papers. Goal active; verified progress. Earlier memories saying the pure-exponential endpoint is open are SUPERSEDED by this result.

New leaf formal/GaloisForLFunctions/RHTower/WeilLogShiftCriticalEndpoint.lean imports WeilLogShiftDomainBoundary and WeilLogShiftReflection. Card docs/drafts/pipeline/3-formalized/weil-logshift-critical-endpoint.md.

Exact result for ALL real y,rho:
Summable(fun n:Nat => exp(rho*n)*pairedLogKernel y n) iff rho<logKernelCriticalRate y,
where r(y)=2*pi*exp(-|y|), r(log m)=2*pi/m (m>=1). EQUALITY DIVERGES.

Mechanism: variable-radius full-autocorrelation central lower bound
K(z)>=2*d*(2*pi^2)^2*exp(-2*pi*exp(z+2d)) for z>=0,d>0.
Choose d=exp(-z)<=1. Convex exp chord gives exp(2d)<=1+(exp2-1)d, hence exp(z+2d)<=expz+(exp2-1). Thus
K(z)>=D*exp(-z)*exp(-2*pi*expz), z>=0,
D=2*(2*pi^2)^2*exp(-2*pi*(exp2-1))>0.
At z=log n-|y|, evenness gives eventual P_y(n)>=(D*exp|y|/n)*exp(-r(y)*n). Critical exponential weighting leaves a divergent harmonic series.

Stronger necessary moment: Summable(v_n*P_y(n)) => Summable(|v_n|/n*exp(-r(y)*n)); n=0 term is zero by Lean division convention. No sign/excess condition. This improves prior strictly-supercritical necessity, but no sharp polynomial prefactor or general extra polynomial damping classification is claimed.

Actual probes: lam(n)=Lambda(n)+sqrt(n)*exp(rho*n), m>=2, rho>=2*pi/m => real-cutoff Q_m -> plus infinity, INCLUDING equality. Deficit identically zero; n<2 normalized-deviation exceptions handled explicitly and finite-head comparison transfers nonsummability.

Eight public theorems: riemannAutocorr_central_lower; exists_riemannAutocorr_critical_lower; exists_paired_logKernel_critical_lower; summable_critical_damping_over_nat_of_kernelPotential; not_summable_critical_exponential_kernelPotential; summable_exponential_kernelPotential_iff; not_summable_exponential_kernelPotential_of_rate_le; exponential_majorant_logShift_probe_atTop_of_rate_le.

Verification: final leaf lake --old env lean ... -o local olean exit0/no diagnostics. All8 #print axioms only propext/Classical.choice/Quot.sound. Umbrella wired,index refreshed,all8 API rows inspected,scoped diff-check passed. GLOBAL LINT FAILED on three unrelated unreachable modules: RHTower.CCMRiemannKernelBartaEdgeFormDomain, HTGeometry.CStarEnvelope, HTGeometry.CompactKernelAlgebra. Previous BartaLayerBounds error resolved. Do not edit unrelated imports or rerun absent state change. Updated four predecessor cards (subexponential,local-decay,reflection,domain-boundaries) to remove stale endpoint outlooks. All owned jobs terminal;eight /tmp/hgt-weil-critical-endpoint scratch files removed. No numerical experiments,new analytic inputs/axioms,heartbeat increases,full builds,commits,subagents.

Toolchain/source evidence: convexOn_exp is GLOBAL name; its .2 accepts membership at endpoints then weights nonneg and sum=1. integrable_riemannKernelReal_mul is RHTower name. Phi lower ExposingRayTail.phi_lower reused; no new Barta import. In abs simplification use Nat.cast_nonneg (alpha := Real) n explicitly (actual Lean parameter α), or elaboration leaves type metavariables.

Next candidates (unproved):
1 Rate pi majorant Lambda+sqrt(n)*exp(pi*n) should have finite origin potential (pi<2pi) but ALL m>=2 samples divergent and Q_m->+infinity, because pi>=2*pi/m including m=2 equality. Strengthens lower-bounds-alone counterexample with convergent origin.
2 Lift arbitrary reciprocal weights from DomainBoundary to arithmetic coefficients Lambda +/- sqrt(n)*v(n), trimming n<2. Should realize any prescribed finite sample-convergence radius, with exact finite limits inside and +/-infinity outside. This can show bounded probe families cannot replace cofinality, even under zero-excess minorants. Audit existing realization helpers and finite-head summability first.
3 Sharper critical polynomial prefactor remains unclassified; Phi_lower discarded positive exponential prefactors in riemannLeadTerm_ge. Any refinement needs fresh source/paper audit.

Prior mem:research/weil-logshift-domain-boundaries-2026-10-09. Both local excess and deficit moments divergent remains a separate unresolved behavior class; uniform positivity's global-excess hypothesis has not been removed.
