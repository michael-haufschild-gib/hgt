# Exact open and closed convergence domains

OUR LEAN CORPUS ONLY. No web or external papers. Goal active; verified progress.

New leaf formal/GaloisForLFunctions/RHTower/WeilLogShiftDomainBoundary.lean imports WeilLogShiftSingleProbeDomain (not the larger reflection chain). Card docs/drafts/pipeline/3-formalized/weil-logshift-domain-boundaries.md.

Definitions: pairedLogKernel y n=K(y+log n)+K(y-log n)>0. polynomialReciprocalLogKernelWeight p c n=(1/((n:Real)+1)^p)*(pairedLogKernel c n)^(-1), p:Nat.
Exact theorem for ALL p,c,y:
Summable(weight p c n * pairedLogKernel y n) iff |y|<|c| OR (|y|=|c| AND 1<p).

Proof: kernel evenness gives identical pairs at equal absolute shifts; strict inward transfer extends to <=, yielding symmetry and interval closure for arbitrary signed weights. In the interior, local critical rates leave room r(c)<b<a<r(y), so P_y/P_c has geometric upper envelope; polynomial damping <=1 preserves summability. At boundary the terms are exactly 1/(n+1)^p, classified by p-series. Outside, necessary growth at rate b below r(c), combined with an upper P_c envelope at a>b, forces 1<=M*C*(n+1)^p*exp(-(a-b)n), contradicting its zero limit. Polynomial-exponential limit proved by rescaling the existing Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero.

Corollaries: for each R>=0 there is a nonnegative sequence with convergence domain exactly (-R,R), and another exactly [-R,R]. p=0 realizes open; p=2 closed. R=0 gives empty domain and singleton origin respectively. This does NOT settle the pure exponential critical-rate endpoint.

11 public declarations (2defs+9theorems): pairedLogKernel; pairedLogKernel_pos; pairedLogKernel_neg; pairedLogKernel_eq_of_abs_eq; summable_kernelPotential_of_abs_le; summable_kernelPotential_between; polynomialReciprocalLogKernelWeight; polynomialReciprocalLogKernelWeight_nonneg; summable_polynomialReciprocalLogKernelWeight_iff; exists_nonneg_weight_with_open_potential_domain; exists_nonneg_weight_with_closed_potential_domain.

Verification: final direct leaf lake --old env lean ... -o local olean exit0/no diagnostics. All11 scratch #print axioms only propext/Classical.choice/Quot.sound. Umbrella wired,index refresh succeeded,all11 API rows inspected,scoped diff-check passed. GLOBAL LINT FAILED on ONE unrelated unreachable module RHTower.CCMRiemannKernelBartaLayerBounds; three previous omissions resolved. Do not touch unrelated imports or rerun without state change. All owned jobs terminal; eight /tmp/hgt-weil-potential-domain scratch files removed. No new analytic inputs/axioms,numerical experiments,heartbeat increases,full builds,commits,subagents.

Lean details learned: open WeilExcess needed for riemannAutocorr_pos/neg. Nat.cast_nonneg type parameter is alpha (α), not R. A newline immediately after method-dot is invalid; bind intermediate Tendsto. Unfold polynomialReciprocalLogKernelWeight explicitly in simpa for inequality. APIs scratch checked: abs_eq_abs, Real.summable_one_div_nat_pow (p:Nat, iff 1<p), summable_nat_add_iff, one_le_pow₀, div_le_one, pow_ne_zero, inv_mul_cancel₀, existing polynomial-exponential limit.

PROMISING NEXT CANDIDATE (unproved): close pure exponential critical endpoint using a SHRINKING full-kernel central interval radius d=exp(-z), avoiding cutoff-transition factors. Existing Phi lower bound and |t|,|t-z|<=z/2+d would give K(z)>=2*d*(2*pi^2)^2*exp(-2*pi*exp(z+2d)). For z>=0, d<=1 and convex-exp chord exp(2d)<=1+(exp2-1)*d imply exp(z+2d)<=expz+(exp2-1). Thus K(z)>=D*exp(-z)*exp(-2*pi*expz) is plausible on z>=0. At z=logn-|y|, critical weighting exp(r(y)n) leaves D*exp|y|/n, a divergent harmonic lower bound. Need fresh corpus search and exact paper audit of integral/chord estimates. Could yield exact pure-exponential classification Summable(exp(rho*n)*P_y) iff rho<r(y), finally deciding equality. No assertion yet.

Alternative application: lift reciprocal weights to coefficients Lambda +/- sqrt(n)*v(n), discarding n<2, to realize exact probe convergence cutoffs with finite limits inside and +/-infinity outside. Not formalized here. Prior memory mem:research/weil-logshift-reflection-duality-2026-10-09.
