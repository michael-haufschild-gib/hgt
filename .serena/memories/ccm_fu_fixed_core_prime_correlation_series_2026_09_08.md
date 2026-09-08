# CCM-FU: complete signed prime-correlation series (2026-09-08)

## Goal/state
RH via CCM-FU remains ACTIVE, UNSOLVED. Previous goal turn was genuine progress: 18 new source theorems closed density, weighted moments, all block limits and full energy limit. This turn is genuine progress: seven new theorems close exact signed prime-release correlation and its complete explicit absolutely convergent coefficient series, with rigorous finite-prefix error. Neither turn supplies signed reserve renewal across changing cores. Full chain remains literal divisor source -> signed prime selection with renewable reserve -> uniform signed Abel bound -> RH. Frontier map READ ONLY by explicit latest user override. Never edit/revert it despite objective replay. STATUS unchanged: no new route-independent fact. No subagents, numerical experiments, commits, pushes, broad/umbrella builds.

Read `mem:ccm_fu_fixed_core_energy_limit_2026_09_08` for the previous 18 checked theorems. Do NOT repeat their checks or audits. Fixed-core reserve experiment from preceding turn complete; do NOT repeat/enlarge it. Only RunPod for any future designed experiment; numerical inputs forbidden in proofs.

## Exact new mathematical result
Let Q_P be complete retained divisor energy, I_P(M,r) the literal clipped processed-head sample, p prime outside P. On every positive squarefree r avoiding P+p:
I_(P+p)(M,r)=I_P(M,r)-sqrt(p)*I_P(M,p*r).
At every cutoff M (including M<=p and M=0):
Q_P(M)-Q_(P+p)(M)=sum_(r in fixedCoreSquarefreeIndices (P+p) M) R_(P,p,M)(r),
R_(P,p,M)(r)=2*sqrt(p)*r*I_P(M,r)*I_P(M,p*r).
The source is inclusive 1<=r<=M, squarefree, primeFactors disjoint P+p. Terminal/beyond-birth samples vanish. No source index omitted; signs retained.

Let a_n=mobiusDivisorHeadBlockSlope P n, b_n=mobiusDivisorHeadBlockIntercept P n, q=floor(n/p). On quotient M/r=n, R=2*M*(a_n+b_n*sqrt(r/M))*(a_q+sqrt(p)*b_q*sqrt(r/M)). Define
Xi_(P,p,n)(t)=2*[a_n*a_q*t+(2/3)*(sqrt(p)*a_n*b_q+b_n*a_q)*t*sqrt(t)+sqrt(p)*b_n*b_q*t^2/2].
c_(P,p,0)=0; n>0 c_(P,p,n)=rho_(P+p)*[Xi_n(1/n)-Xi_n(1/(n+1))].
Each actual correlation block divided by M^2 tends to c_(P,p,n). The series of |c| is summable; HasSum c (kappa_P-kappa_(P+p)), with kappa from prior complete-energy block mass series.

C_P=(3/5)*2^(P.card-1), natural truncated subtraction. Absolute ENTIRE source tail M/r>=T is <=(2*C_P^2/T)*M^2 for every M, T>0. Hence |kappa_P-kappa_(P+p)-sum_(n<T)c_n|<=2*C_P^2/T. This is a rigorous finite-head approximation error, not a sign theorem. C_P depends on growing core cardinality.

## New leaves (7 PUBLIC theorems)
1. formal/GaloisForLFunctions/RHTower/MobiusDivisorFixedCorePrimeCorrelation.lean (~269 lines), imports prior MobiusDivisorFixedCoreEnergyLimit. Three public:
- mobiusDivisorInterpolatedHead_insert_prime (~114): exact two-scale sample update (requires only hpPrime, hpNotP, r positive/squarefree/disjoint).
- mobiusDivisorSelectionEnergy_prime_release_eq_correlation (~151): exact all-cutoff signed release identity (hpPrime/hpNotP; no P primality needed for algebra).
- mobiusDivisorPrimeCorrelation_absolute_tail_le (~231): absolute source tail, P prime core and p outside it.
Definition mobiusDivisorPrimeCorrelationTerm.
Private weighted squarefree source split is a p-multiplication bijection (generic f:Nat->Real) extending previous count recurrence. Private fibre_sample, sample_vanish and correlation_as_fibres retain all endpoints. R term=-2 F_P(primeFactors(r))*F_P(insert p primeFactors(r)); existing source amplitude ceiling and count floor(M/T) give absolute tail.
Final scratch41916 exit0; exact leaf emit92897 exit0.

2. formal/GaloisForLFunctions/RHTower/MobiusDivisorFixedCorePrimeCorrelationLimit.lean (~350 lines), imports new first leaf. Four public:
- tendsto_mobiusDivisorPrimeCorrelationBlock_div_sq (~151): exact signed mixed-block limit.
- summable_abs_mobiusDivisorPrimeCorrelationMass (~294): summable absolute masses.
- abs_mobiusDivisorPrimeReleaseCoefficient_sub_prefix_le (~307): rigorous 2C_P^2/T signed remainder bound.
- hasSum_mobiusDivisorPrimeCorrelationMass (~325): complete signed source series equals kappa_P-kappa_(P+p).
Definitions mobiusDivisorPrimeCorrelationPrimitive, mobiusDivisorPrimeCorrelationBlock, mobiusDivisorPrimeCorrelationMass.
Private mixed_prefix_limit expands product and reuses existing count, sqrt and linear moment limits. quotient_indices retains integer endpoints. term_polynomial uses two affine source identities and Nat.div_div_eq_div_mul. Absolute finite block sums <= complete absolute source bound, pass to limits for summability. Full energy limit + exact source remainder gives coefficient error; T->infty identifies series.
Final scratch10959 exit0; exact leaf97716 exit0. Lean emitted a harmless informational ring-normalization suggestion while exiting0; do NOT rerun merely to remove that message.

## Validation/current global lint issue
Both leaves wired into formal/GaloisForLFunctions/RHTower.lean immediately after MobiusDivisorFixedCoreEnergyLimit. Only needed two leaf oleans emitted, no full/umbrella build. Seven new public theorems audited ONCE in external scratch85968 exit0, all only propext/Classical.choice/Quot.sound. No new axioms/numerical premises/sorry. Do NOT re-audit prior modules.
Declaration index21297 exit0 refreshed (0 changed: another refresh evidently already indexed current files; source names verified present).
Global lint95125 exit1: EXACTLY NINE unrelated unreachable modules, no new CCM-FU errors:
ThetaCuspHawkingBMCuspHeightOperator
ThetaCuspHawkingBMCuspHeightTest
ThetaCuspHawkingBMCuspLogCoordinate
ThetaCuspHawkingBMCuspLogTest
ThetaCuspHawkingBMCuspNativeIntegral
ThetaCuspHawkingBMCuspOperatorIntertwining
ThetaCuspHawkingBMCuspPeriodization
ThetaCuspHawkingBMCuspWindowDifferential
ThetaCuspHawkingBMOperatorCore
Do not claim global lint passes, do not edit others' unrelated work. Re-run only once authoritative state shows relevant umbrella reachability changed. Known Lake packaging audit remains pending to avoid previously established broad stale prerequisite rebuild; do NOT repeat expensive stale preflight/build. No successful lake build claimed.

## Docs
New stage3 exact proof/validation: docs/drafts/pipeline/3-formalized/ccm-fu-fixed-core-prime-correlation.md.
New stage1 current target: docs/drafts/pipeline/1-in-progress/ccm-fu-fixed-core-prime-correlation.md (closed source chain, remaining sign/size; linked stage3).
Updated fixed-core-energy-limit and fixed-core-reserve-sign stage1 cards: direct signed correlation series closed, continuous integral representation optional, reserve-producing sign remains open. Frontier READ ONLY and STATUS unchanged.
Cleanup COMPLETE: four owned /tmp files (ccm_fu_prime_correlation.lean, ccm_fu_correlation_blocks.lean, ccm_fu_prime_correlation_axioms.lean, ccm_fu_prime_correlation_lint.log) removed via Python Path.unlink after all handles exited. Process inspection confirmed no owned lean/lake process remained. Needed leaf oleans preserved. Final key theorem lines in current second leaf: absolute coefficient error at304; hasSum complete signed correlation at322.

## Next hard arithmetic direction, NOT PROVED
A sharper fixed-head remainder is a concrete next target. Prior result H_P(M)/sqrt(M)->0 for nonempty P does not prove H_P tends a constant or give the sign of its distant-prime correlation. Corpus evidence:
- primeFreeDivisorIncrement n=log n-tau(n)+2gamma (CCMFUSuzukiMobiusDivisorDilationChannels ~872), its prefix is primeFreeDivisorDefect.
- SquareRootSummatoryMellin.hasMellin_squareRootSummatoryPrimitive gives L(b,s-1/2)/(2*s*(s-1/2)) on safe half-plane.
- RetainedPrimeSourceInterpolation.squareRootSummatoryPrimitive_nat/between gives literal Abel samples and sqrt-clock interpolation.
- DivisorSourceDirichlet builds source continuation on Re>1/2; RetainedPrimeDivisorConvolution.divisorSourceDirichlet_div_zeta_eq_completed_source identifies completed expression for Re>3/2.
The formal Mellin expression suggested by source coefficients is B(w)=-zeta'(w)-zeta(w)^2+2gamma*zeta(w), so G_empty's Mellin germ should be B(s-1/2)/(2s(s-1/2)). The s=1/2 residue is B(0)=known c=log(2pi)/2-gamma-1/4, matching the already PROVED leading mean. The candidate constant term from s=0 would be A0=-B(-1/2)=zeta'(-1/2)+zeta(-1/2)^2-2gamma*zeta(-1/2). This residue calculation DOES NOT prove the pointwise two-term expansion G_empty(x)=c sqrt(x)+A0+o(1). An actual inverse-Mellin/oscillatory remainder argument is missing; no constant limit or A0 sign has been formalised.
If that expansion were proved, finite processed Euler dilation would suggest H_P(x)->A0*prod_(q in P)(1-sqrt q) for nonempty P. A signed Mellin moment J_P=integral G_P(x)x^-3 dx would factor as J_empty*prod(1-q^-3/2), with J_empty>0 from unsigned source positivity. Then distant-prime release would have p^(-3/2) leading coefficient 2rho_P*A_P*J_P. This is a candidate route to an actual arithmetic sign law and paired reserve supply, not an established theorem. Do not assume the expansion, sign, or growing-core uniformity. Do not run a computation merely to confirm this proposed predictable residue behavior.
Prior research search 'divisor Abel constant' found no residual theorem beyond known block/hyperbola identities; Voronoi search returned only generic HTGeometry reduction/exponent models, not an instantiated exact divisor transform. Build missing source analysis if chosen. Be cautious: discrete integer sampling shifts divisor-defect mean; do not substitute recalled continuous divisor asymptotics for the literal source.

## Lean/API lessons
- Nat.div_self requires positive Nat, not !=0.
- abs_of_nonneg (sq_nonneg _) in a rewrite may target numerator absolute value incorrectly; explicitly use sq_nonneg (M:Real) for denominator.
- abs_ofNat does not exist here; use abs_neg and abs_of_nonneg (by norm_num : (0:Real)<=2).
- Nat.div_div_eq_div_mul verified.
- ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime verified.
- summable_abs_iff verified; le_of_tendsto_of_tendsto takes Eventually, primed version forall.
- Finset.sum_filter_not_add_sum_filter and sum_fiberwise_eq_sum_filter verified.
- Root cwd for formal/... searches, formal cwd for lake. Avoid guessed filenames/globs: several harmless no-match reads were wasteful. Use rg --files first. Limit huge frontier/STATUS lines with --max-columns; frontier remains read only.
