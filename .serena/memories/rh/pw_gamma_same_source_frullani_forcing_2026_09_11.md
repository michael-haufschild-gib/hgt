# PW-B iteration 20 — complete same-source nonlocal forcing
RH NOT proved. Goal ACTIVE, no budget. Root /Users/michael/Documents/code/hgt; Lean cwd formal. Prior memory: mem:rh/pw_gamma_reflected_frullani_global_domain_2026_09_11.
Mission audited mathematical/Lean research. No subagents, no commits/pushes, no numerical experiments. Shared worktree; preserve others.

## Chain and hard gap
Literal PW response -> FE partner imbalance -> positive Deninger Ward transmutation -> independently source-forced fixed-grade balance -> RH. Grade imbalance is 4(2k+1)(Re s-1/2)/(k+1)^2. Missing actual source-forced balance before Xi specialization, physical pairing/domain and coefficient/spectral identification.
Iteration19 admitted R M_z and conjugated Frullani current R E_z at every z, with exact R T_h R reciprocal motion. This did not compare original and reflected operators on the same input. Iteration20 now closes that comparison and proves a nonzero leading coefficient of its complete signed forcing. Does NOT determine D_0 or the unweighted global mass or balance at Xi occurrences. PW-B active.

## Verified files and audits
New leaves formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusSameSourceKernel.lean (312 lines, 21 public theorems, 4 defs)
and ...GammaMobiusSameSourceCurrent.lean (319 lines, 23 public theorems, 4 defs).
Namespace RHTower, noncomputable, respectTransparency false.
Both wired exactly once into RHTower.lean near15243.
Card docs/drafts/pipeline/3-formalized/pw-b-gamma-same-source-current.md.
Updated frontier PW-B paragraph and universal STATUS existing first-nonzero-asymptotic constraint; no route-specific worklog in STATUS.
Persistent attack card docs/drafts/pipeline/1-in-progress/pw-b-source-orientation-attack.md iteration20 ends with full math/audit/next candidate.
Four complete deep JSON results saved docs/drafts/pipeline/1-in-progress/pw-b-gamma-same-source-searches.json.
Scratch and targeted final builds passed. No redundant direct repo lake env lean runs: full scratch proof then targeted leaf final audits. Build logs prove only each new leaf rebuilt; all upstream jobs replayed.
All52 public #print axioms via /tmp/pwb-gamma-same-source-axioms.lean passed standard propext, Classical.choice, Quot.sound only.
Current leaf line200 emits informational ring suggestion; exit0 and no open proof goals. Existing upstream warnings replayed.
All52 names unique and indexed in LEAN_API; index regeneration wrote LEAN_API/GAPS/OVERVIEW. Scoped whitespace/conflict/link checks passed.
IMPORTANT authoritative repo lint DID NOT PASS: five unrelated missing umbrella imports:
GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareBlockSwapped
...Sieve.MenonHarmonicRamareLadderSwapped
...Sieve.MenonHarmonicRamareLadderSwappedVolume
GaloisForLFunctions.HTGeometry.WeightedMinimax.Basic
...WeightedMinimax.SignRealization.
Confirmed absent, preserved separate active work. Neither PW-B leaf flagged. Do not claim whole gate passed. This is audit limitation, not external mathematical blockage.
All owned Lean/research/lint/index processes terminal; final scan no owned Lean. ALL iteration20 Lean runs serialized in foreground. Do not kill others' processes.
Logs /tmp/pwb-gamma-same-source-{kernel-build,current-build,current-scratch,axioms,lint,index}.txt.
Final target build sessions26798,21785 terminal0; ax30580 terminal0; lint90872 terminal1; index63918 terminal0. No live sessions now.

## Kernel leaf
Q=pwGammaRaySource, x>0 sqrt(x)exp(-x), Q0=exp(-1) NONZERO.
R f(x)=Qx/Qinvx*f(invx); T_h original sqrt ratio translation.
Actual reflected arithmetic atom A^R_z(n,x)=mu(n)exp(-z log n)*sqrt(n)*Qx*exp(-(n-1)/x) n>0.
Knew = pwGammaReciprocalTranslationKernel a x h =
exp(-h)*(exp(-a/(x+h))-exp(-a/x))/h.
Public _zero (a0), _nonneg ha>=0 hx hh, _pos ha>0 hx hh.
_le: K <= a/(x*(x+h))*exp(-h)*exp(-a/(x+h)).
Proof v=a*h/[x(x+h)], 1-exp(-v)<=v; retains BOTH denominators.
_polynomial_le k ha>0 hx hh: K <= (k+1)!/a^k*exp(-h)*(x+h)^k/x.
J_k = pwGammaSameSourceMajorant k (h,x) =
exp(-h)*(norm Qx/x)*(x^k+h^k).
_split into exp(-h)*(x^k normQx/x)+(h^k exp(-h))*(normQx/x).
_integrable product restricted positive rays, _integrable_section k x ALLrealx, _nonneg k hh hx.
pwGammaRaySource_inverse_polynomial_moment_integrable k and _integral k:
int x^k*(norm Qx/x) dx = Gamma(k+1/2).
Private h moments integrable h^k exp(-h), integralGamma(k+1).
K _source_le k: normQx*K <= [(k+1)!/a^k*2^(k-1)]*J_k.
Uses add_pow_le hx.le hh.le k (allNat k incl0).
K _integrable ha>=0 hx, _integral_pos ha>0 hx.

W_n = pwGammaSameSourceDefectWeight n x:
if n0 then0 else sqrt n*(int_h K(n-1,x,h)+log n*exp(-(n-1)/x)).
_zero x, _one x; _pos hn:1<n hx:0<x.
Anew = pwGammaMobiusSameSourceAtom z n (h,x):
[T_h(A^R_z n)(x)-exp(-h)A^R_z(n,x)]/h (literal actual atom).
_eq z hn>0 hh>=0 hx>0 = mu(n)exp(-zlogn)*(sqrt n*Qx*K(n-1,x,h)).
_zero z globally; _one z hh>=0 hx positive.
_norm_le hN n hh>0 hx:
norm Anew(z,n+2,h,x) <= [2^(N+1)*(N+4)!*2^(N+2)]/(n+1)^2 *J_(N+3),
for normz<=N. Bounds normmu<=1, expcoef<=n^N, sqrtn<=n, n+2<=2(n+1).
Private exp-neg factorial and coefficient bounds not accessible outside leaf.

## Current leaf
Imports Kernel and Mathlib.NumberTheory.LSeries.Injectivity.
Atom _integrable z n product hfirst,xsecond.
_integrable_section z n hx.
_norm_integrals_summable z product norms alln.
_section_norm_integrals_summable z hx in h.
All z complex. Index0/1 handled exactly, n+2 via J commonbound.
Atom _summable z hh>=0 hx via actual reflected atoms at x+h and x.

G = pwGammaMobiusSameSourceResponse z x h =
[T_h(R M_z)(x)-exp(-h)R M_z(x)]/h.
_eq_tsum z hh hx literal full source = sum Anew.
_integrable z hx hsection; _joint_integrable z product.
_integral_interchange z Fubini.

pwGammaMobiusSameSourceCurrent z x := int_h G.
_integrable z globally dx (joint.integral_prod_right);
_eq_tsum z hx = sum_n int_h Anew.
D = pwGammaMobiusSameSourceDefect z x :=
Current_z(x)-R(E_z)(x).
_integrable z globally dx.
_response_joint_integrable z: G minus prior reflected response jointL1.
_response_integral z hx: int_h(G-F^R)=D.

pwGammaMobiusSameSourceAtom_defect_eq z n hx:
(int_h Anew_z n)-pwGammaMobiusReflectedCurrentAtom z n x =
mu(n)exp(-zlogn)*Qx*(W_nx:complex).
Defect _weighted_summable z hx: exact coefficients above summable.
Defect _eq_tsum z hx exact actual D series.
pwGammaMobiusSameSourceCurrent_closed capstone allparameter domains,
full series formula and strict Wn>0.

c_n(x) = pwGammaSameSourceDefectCoefficient x n :=
((mu n:complex)*Qx)*(W_nx:complex).
Private _zero,_one,_term convert LSeries.term c z n to actual exp coefficient.
Defect _eq_LSeries z hx: D_z=LSeries c z.
pwGammaSameSourceDefectCoefficient_LSeriesSummable z hx allz.
Defect _leading_limit hx:
Tendsto (fun r:Real => (2:Complex)^(r:Complex)*D_r(x))
 atTop (nhds(-Qx*(W_2x:Complex))).
Defect _eventually_ne_zero hx: eventually realr->infinity,D_r(x)!=0.
Defect _not_identically_zero hx: not forall z:Complex,D_z(x)=0.
This is complete-source eventual nonvanishing, NOT positivity inference from signed coefficients.
The exact leading coefficient is strongest positive survivor of failed family-wide balance.

## Verified implementation APIs / traps
pwGammaSameSourceDefectCoefficient_LSeriesSummable proof must:
change Summable(fun n=>LSeries.term c z n)
simp_rw [private term lemma]
exact weighted_summable...
Simp cannot rewrite eta-expanded LSeries.term automatically with respectTransparency false.
LSeries.tendsto_cpow_mul_atTop (h:forall m<=n,c_m=0) (ha:abscissaOfAbsConv c<top).
Use n=1, ha from (LSeriesSummable c 0).abscissaOfAbsConv_le.trans_lt (by simp).
Simplifying target (NatCast1+1) needs Nat.cast_one + one_add_one_eq_two.
Term conversion: LSeries.term_def0 (source name term_def₀) c0; Complex.cpow_def_of_ne_zero natcastpositive; <-Complex.ofReal_natCast, <-Complex.ofReal_log (Nat.cast_nonneg _), rw[mul_comm (logn:Complex) (-z)]; dsimp;ring.
Filter.Tendsto.eventually_ne ht hlimit_ne_zero then productnonzero forcesDnonzero.
hasSum_integral_of_summable_integral_norm integrables normsum -> .summable.
No root tsum_sub: use h1.tsum_sub h0.
Integrable.integral_prod_right integrates FIRST product variable and returns secondvariableintegrable.
Real.pow_div_factorial_le_exp explicit y FIRST, then positivityproof,k.
Real.exp(-a/r) parsing (-a)/r vs exp(-(a/r)): simp only[neg_div].
field_simp / rw / congr sometimes closegoal, removefollowingring ifNoGoals.
Use explicit mul_le_mul_of_nonneg_left for kernel source bound: gcongr can peel unequal compound factors and destroy intended subgoal.
Nat.cast_nonneg named type argument is alpha (α), NOT R.
At integrable a0, prove functioneq kernel0x=0 via funext and _zero then rw; simp does not eta-expand it.
Measurable atom by unfolding literal T/R/A/Q; fun_prop.
Factorial/constant normbounds checked in full scratch; no numerical tactics/experiments.

## Research
Four deep method queries kernel/domain/balance/uniqueness allpartial. Three count723442/723502/723510; domain coverage pending no count. Generated positivity ingredient sets not verified as arithmetic premises. Direct rg found correct LSeries leadinglimit theorem.
Broad arXiv dateordered bistability search:
https://arxiv.org/search/?query=bistability&searchtype=all&abstracts=show&order=-announced_date_first&size=50
Primary https://arxiv.org/html/2609.10580v1 (Sep5) model2 andpropositions2.1-2.4 theorem3.2 read: nonnegative rowstochastic W, beta*supf<1 contraction, no such signed arithmetic premise established.
https://arxiv.org/abs/2609.11574 (Sep10) abstract only, passive localizedcubic approximation, no verifiedtransfer.
No external assumption enters Lean.

## Next concrete hard-obstacle attack
Actual spatial pairing of D, not yet proved:
c_n(x)=mu(n)*Qx*W_nx = int_h Anew_z0 n - RCurrentAtom_z0 n.
Each c_n globallyL1; sum_n int norm c_n <= sum_n intprod norm Anew_0 n + sum_n int norm RCurrentAtom_0 n.
All those RHS admitted from new/previous leaves.
Define d_n=int_x c_n(x). Prove literal mass int_x D_z(x)=LSeries d z with full term norm admissions; retain constants n^-z.
d0=d1=0; d2=-int Qx W2x should be strictly negative, with integrability from admitted atom difference and positivity from Qx>0,W2x>0.
Then same corpus leadinglimit gives 2^r int D_r -> d2 !=0, testing INTEGRATED family-wide balance rather than only pointwise.
Must not infer total mass nonzero from pointwise Dnonzero. Do not assert massD0, physical measure choice, Xi identification or source-forced spectral balance without proof.
Prior conditional mass/pointwise toys do not close RH. Preserve goal active.
