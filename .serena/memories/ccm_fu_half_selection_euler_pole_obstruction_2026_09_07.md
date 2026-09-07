# CCM-FU half-selection Euler product and actual pole obstruction — 2026-09-07

Goal ACTIVE; RH/SD1/PE4 and full PE5 averaged-energy refutation OPEN. Last turn made concrete verified progress. No blockers. No active Lean processes or sessions after cleanup. Never mark goal complete for these partial results.

New-turn opening full chain:
completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → coherent prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH.
Next significant step: formalize the fully discrete two-Abel transfer from H(M)=O(M) to a holomorphic continuation, then apply the new CLOSED actual-source no-continuation theorem to finish PE5's no-linear-growth and fixed-budget obstruction. Do not redo Euler/source proofs.

## New completed modules (root RHTower namespace)
1. formal/GaloisForLFunctions/RHTower/MobiusHalfSelectionEulerProduct.lean —11 public theorems.
- halfSelectionMoebiusAF : ArithmeticFunction Complex has EXACT coefficients (halfSelectionMoebiusWeight n : Complex), namely mu(n)/2^primeFactors.card.
- halfSelectionMoebiusAF_apply (not simp), halfSelectionMoebiusAF_one (simp).
- halfSelectionMoebiusAF_isMultiplicative; norm_halfSelectionMoebiusAF_le_one.
- halfSelectionMoebiusAF_prime=-1/2; halfSelectionMoebiusAF_prime_pow=0 for exponent>=2.
- LSeriesSummable_halfSelectionMoebiusAF for Re>1.
- hasProd_halfSelectionMoebiusAF: local factors1-p^(-s)/2, limit LSeries a.
- norm_halfSelection_prime_cpow_neg_lt_one p for Re>0.
- halfSelectionEulerCorrectionLocal p s :=1+(p^(-s))^2/(4*(1-p^(-s))).
- halfSelectionEulerCorrection s :=tprod correctionLocal.
- hasProd_halfSelectionEulerCorrection for Re>1: product limit LSeries a^2*zeta.
- halfSelectionEulerCorrection_eq_LSeries_sq_mul_zeta for Re>1.
No separate coefficient-function R or fractional binomial system substituted.

2. formal/GaloisForLFunctions/RHTower/MobiusHalfSelectionEulerCorrection.lean —9 public theorems.
- norm_halfSelectionEulerCorrectionLocal_sub_one_le p (hσ:0<σ)(hs:σ<=s.re):
  norm(local-1)<= (1/[4(1-2^(-σ))])*p^(-2σ).
- differentiableOn_halfSelectionEulerCorrectionLocal onRe>0.
- hasProdLocallyUniformlyOn_halfSelectionEulerCorrection for every σ>.5, onRe>σ.
- differentiableOn_halfSelectionEulerCorrection and analyticOnNhd_halfSelectionEulerCorrection onALL Re>.5.
- halfSelectionEulerCorrectionLocal_one:
  local p1 = castReal(1+1/(4*p*(p-1))).
- one_le_halfSelectionEulerCorrection_one_re.
- halfSelectionEulerCorrection_one_im=0.
- halfSelectionEulerCorrection_one_ne_zero.
Uniform prime-square majorant + locally uniform product. Lowerbound1 from all finite products>=1, no numerical premise.

3. formal/GaloisForLFunctions/RHTower/MobiusHalfSelectionPoleObstruction.lean —6 public theorems.
- halfSelectionDivisorSourceAF is cast of existing primeFreeDivisorIncrementAF.
- halfSelectionDivisorSourceAF_apply n≠0 gives cast actual b(n)=log n-tau n+2γ.
- halfSelectionDivisorConvolution :=halfSelectionMoebiusAF*halfSelectionDivisorSourceAF (arithmetic Dirichlet convolution).
- LSeriesSummable_halfSelectionDivisorConvolution forRe>3/2.
- LSeries_halfSelectionDivisorConvolution onRe>3/2:
  LSeries g =LSeries a *divisorSourceDirichlet (existing B).
- sum_halfSelectionDivisorConvolution N:
  sumIcc1N g(n)=castReal(sumIcc1N a(d)*D(N/d)).
- mobiusDivisorHalfSelectionHead_eq_convolution_abel M:
  castH(M)=sum kIcc1(M-1) cast(√(k+1)-√k)*sum nIcc1k g(n).
- not_exists_analytic_halfSelectionDivisor_extension:
  NOT exists F:Complex→Complex,
    AnalyticOnNhd Complex F {s|.5<s.re}
    AND forall s,2<s.re -> F s=LSeries halfSelectionDivisorConvolution s.
This is UNCONDITIONAL and exact actual source.
Proof: entire zetaPoleUnit Z withZ1=1; identity continuation of
F²Z-(s-1)B²R from Re>2 toRe>.5. At1 F1=0. Derivative lhs0, rhsB1²R1 nonzero, contradiction.
This is NOT yet H notO(M): missing transfer from bound to continuation.

## Verification complete — DO NOT REPEAT
All3 scratch checked; exact corresponding oleans emitted with lake env lean file -o exactolean.
26 public theorems axiom-audited ONCE: only propext, Classical.choice, Quot.sound.
No added axioms/sorry/numerical experiment inputs.
All3 wired ONCE into formal/GaloisForLFunctions/RHTower.lean near MobiusDivisorBernoulliPrimeEnergy.
No umbrella/dependency/lake builds.
Global lint once: sole error concurrent unwired HTGeometry.PolynomialODEOddCompactProductC. No new CCM-FU errors. Preserve foreign work.
Index refreshed5changed0removed. Scoped git diff --check passed. Certificate/PE5 links resolve.
All Lean sessions terminal; last index session57618 terminal. Cleanup removes13 owned scratch/log files. No old theorem audits repeated.

## Docs current state
- New docs/drafts/pipeline/3-formalized/ccm-fu-half-selection-euler-pole-obstruction.md has exact sources, theorem, 26 audit.
- PE5 docs/drafts/pipeline/1-in-progress/ccm-fu-bernoulli-prime-energy.md updated:
  Euler correction and no-continuation theorem CLOSED; remaining2steps below; NEW full discrete transfer paper proof.
- rh-current-frontier-map.md CCM-FU paragraph updated current state only.
- mobius-divisor-source-diagonal-dominance.md updated.
- Previous 3-formalized/ccm-fu-divisor-source-harmonic-boundary.md remaining-work sentence links new certificate (old20 theorem audit untouched).
- universal-law-field/STATUS.md MUST-258: must preserve zero multiplicity under analytic factorization; a holomorphic square times a nonvanishing factor cannot acquire a simple zero; actual examplewitha,b,noRHconclusion.
PE5 stays in progress until actual H growth theorem/fixed-budget refutation formal. PE4/SD1 unaffected.

## NEXT: discrete transfer paper proof (no improper Mellin infrastructure needed)
All below written on PE5 card with statuses. Use THIS current chain.
g=halfSelectionDivisorConvolution, G_N=sum n<=N g(n).
h_n=(√(n+1)-√n)G_n.
A_N=sum n<=N h_n=castH(N+1) by new exact finite landing.
Hypothetical |H(M)|<=C M gives |A_N|<=C(N+1), take C>=0 via absolute/enlarging.
For n>=1 define u_n=√n+√(n+1), f_s(n)=castu_n*(n^(-s)-(n+1)^(-s)).
Exact u_n*(√(n+1)-√n)=1.
Two finite Abel summations:
sum n<=N g(n)n^(-s)
 =G_N*(N+1)^(-s)+A_N*f_s(N+1)
  +sum n<=N A_n*(f_s(n)-f_s(n+1)).
Construct F(s)=tsum n>=1 A_n*(f_s(n)-f_s(n+1)).
For σ=Re s>0:
|f_s(n)|<=3|s| n^(-σ-.5).
|f_s(n)-f_s(n+1)|<= (3|s||s+1|+|s|) n^(-σ-1.5).
Reason:
u_n<=3√n;
u_(n+1)-u_n=√(n+2)-√n=2/(√(n+2)+√n)<=1/√n.
Difference f_n-f_n1 =
 u_n*(n^-s-2(n+1)^-s+(n+2)^-s)
 -(u_n1-u_n)*((n+1)^-s-(n+2)^-s).
Use EXISTING first/second difference bounds below.
Then A_n<=C(n+1)<=2Cn => summable majorant const*n^(-σ-.5) forσ>.5.
Each summand entire in s; compact uniform estimates bound|s| and choose lower real part>.5; locally uniform sums yield analytic F onRe>.5.
A_N*f_s(N+1)=O((N+1)^(.5-σ))->0 forσ>.5.
h_N=A_N-A_(N-1)=O(N), G_N=u_N*h_N=O(N^1.5), so G_N*(N+1)^-s->0 forσ>1.5.
OnRe>2, actual LSeries g absolutely converges (already new theorem), and finite Abel identity gives F=LSeriesg.
Apply CLOSED not_exists_analytic_halfSelectionDivisor_extension ->no linear H bound.
Then finite-prefix absorption ->no bounded tail. H²<=E_half and Q<=722M² give no fixed E_half<=KQ, even after any finite prefix.
For arbitrary real K replace with|K| sinceQ>=0, and chooseC=√(722|K|); squared inequality =>|H|<=CM. No pointwise numerical certificate needed.
This proves magnitude unbounded / M, not a sign/asymptotic; do NOT claim H/M tends to negative infinity.
This is the strongest actual survivor needed to retirePE5; do not stop at genericR/no-continuation alone.

## Existing APIs inspected / reusable
- formal/GaloisForLFunctions/RHTower/DirichletSecondDifference.lean, namespace GaloisForLFunctions.RHTower:
  norm_second_difference_cpow_le {s}(hs:0<s.re){x:Real}(hx:0<x):
  norm(x^-s -2(x+1)^-s+(x+2)^-s)<=norms*norm(s+1)*x^(-s.re-2).
  cpow_neg_sub_eq_integral also exists, notneeded for newweighted transfer.
- DirichletPolyBoundedAbel.lean SAME prefixed namespace:
  norm_cpow_unit_diff_le hs hx:
  norm(x^-s-(x+1)^-s)<=norms*x^(-s.re-1).
  Its needed olean already exists.
- RootRHTower.sum_Icc_mul_apply f g N in DirichletSummatorySwap gives generic arithmetic convolution hyperbola. Already imported by new3rdmodule, oleanexists.
- HTGeometry.sum_mul_eq_partial_mul_diff_ring usedpreviousharmonicmodule gives exact twofinite Abel identities overIcc1N.
- Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn:
  Summable.hasProdLocallyUniformlyOn_one_add hopen hu heventualmajor hcontinuous
  gives localuniformproduct on an open domain using one uniform summablemajorant.
  Its additive HasSum analogue likelyuseful for weightedF; inspectactualsource.
- HasProdLocallyUniformlyOn.hasProd membership; hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn; limit.differentiableOn finiteanalytic eventually isOpen.
- AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero, Complex.convex_halfSpace_re_gt. No-continuation proofs nowlocal reference.
- ZetaPoleSplit: entire zetaPoleUnit, of_ne = (s-1)ζ, at1=1.
- LSeries_congr takes coefficient equality THEN explicit s; do not omit s.
- ArithmeticFunction.LSeries_mul' and LSeriesSummable_mul; LSeriesSummable_congr.
- Complex.norm_natCast_cpow_of_pos handles explicit Nat primecasts.
- Complex.mul_cpow_ofReal_nonneg gives multiplicativity of naturalbasecpow after simpa Nat.cast_mul,Complex.ofReal_natCast.
- summable_riemannZetaSummand hs has norm of riemannZetaSummandHom (def n^-s), not syntacticallynormn^-s; change target before rewrites.
- Real.rpow_le_rpow_of_nonpos hxpositive hxy hznonpositive for inversebasecomparison.
- Complex.norm_ofNat (not rootnorm_ofNat).
- Finset.one_le_prod (notone_le_prod₀), Complex.ofReal_prod, ge_of_tendsto.

## Lean efficiency pitfalls from this turn
- Put spaces around <= before variable s! Unicode 'σ≤s.re' parsed graph notation ≤s; use 'σ ≤ s.re'.
- Avoid tagging halfSelectionMoebiusAF_apply simp: it unfoldssourcebeforeprime/one lemmas. Currenttagonlyone.
- Explicit ((p:Nat):Complex) avoids confusing Nat.Primes/subtype coe instances. NormnatCastlemma betterthanrealcastnorm.
- For complex p-1 ne0: sub_ne_zero.mpr followed by exact_mod_cast p.2.ne_one. Direct exact_mod_cast on subtraction inferred Int.subNatNat and failed after long elaboration.
- Some positivecorrection checks took1–2minutes; confirmedsamehandlelive, waited, neverrestartedduetopolltimeout.
- For derivative core, EXPLICIT typed HasDerivAt intermediate goals triggered mismatched Complex additive/module instances. SOLUTION: infer hleft andhright from .pow/.mul, then .unique(.congr_of_eventuallyEq heq.symm). Only simplify resulting equality with [Pi.pow_apply,Pi.mul_apply,hf1]; do not restate the derivative evidence at explicit differentinstances.
- sq_eq_zero_iff exists; rootpow_eq_zero doesnot (eq_zero_of_pow_eq_zero alternative).
- #print axioms can wrap lists acrosslines. Pythonauditparser mustregexblock[...], notcountlines; noLeanrerunneeded.
- Do NOT trust shell glob *.lean in RHTower (argumentlisttoolong). use rg --glob '*.lean' directory.
