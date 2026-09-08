# CCM-FU: physical paired mean now closed; RH remains open

User explicitly forbids editing frontier map: docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md is READ ONLY, including across goal continuations. No STATUS edit: no new route-independent fact. Active unbudgeted goal is RH proof/falsification, NOT complete or blocked. Full chain: actual divisor source -> renewable signed reserve -> exhaustive selection -> uniform signed Abel bound -> RH. This turn made verified progress by identifying the actual W_P with the prior proved contour and inheriting its limit. No subagents, numerical experiments, broad builds, umbrella builds, commits or pushes.

## Three new completed Lean leaves
1. formal/GaloisForLFunctions/RHTower/DivisorContinuousHeadRegularity.lean
   10 public theorems: divisorContinuousUnitHead_le_sqrt; measurable_divisorContinuousUnitHead; squareRootSummatoryPrimitive_divisor_eq_real; measurable_mobiusDivisorContinuousHead; exists_bound_mobiusDivisorContinuousHead; locallyIntegrable_mobiusDivisorContinuousHead; mellinConvergent_mobiusDivisorContinuousHead; differentiableAt_mellin_mobiusDivisorContinuousHead; integrable_log_mobiusDivisorContinuousHead; memLp_log_mobiusDivisorContinuousHead.
   Literal real-ray G0 <=3sqrt(x)/5 via square-root interpolation. Full complex primitive equals real cast G0, all real x. For every finite Nat core P, |G_P(x)|<=C_P sqrt(x), measurable, locally integrable, Mellin convergent/holomorphic at -s when Re(s)>1/2. Log source at sigma=-1 for G_P(Y*x), every Y>0, is L1 and L2 (zero above logY, <=C sqrtY exp(u/2) below). Scratch19327 and exact emission53917 exit0.
2. DivisorContinuousHeadMellin.lean
   3 public theorems: mellin_divisorContinuousUnitHead; mellin_mobiusDivisorContinuousHead_euler; mellin_mobiusDivisorContinuousHead_eq_core.
   Physical Mellin(G0)(-s)=B(s-1/2)/(2s(s-1/2)), Re(s)>1/2. Start Re(s)>3/2 from literal summatory formula, continue holomorphically. Finite Mobius dilation gives exact Euler multiplier E_P(s) for finite prime core. Nonempty core's physical Mellin equals prior filled F_P. Scratch33279/exact5277 exit0.
3. MobiusDivisorDilationMean.lean
   Public def mobiusDivisorDilationMean P Y = integral x>1 G_P(Y*x)G_P(x)/x^3.
   3 public theorems: integrable_mobiusDivisorDilationMean_kernel (any finite P, Y>0); mobiusDivisorDilationMean_eq_contour (nonempty finite prime P, real a); tendsto_mobiusDivisorDilationMean (W_P(Y)->Re(divisorCoreMellinPairResidue P) atTop).
   Direct kernel domination by C_P² sqrtY/x² proves integrability. Polarized Mellin-Plancherel at sigma=-1 uses f=G_P(exp(a)*x) in conjugated slot, g=G_P(x). Conjugation gives f's trace at -1-it, scaling gives exp(a(1+it))F_P(1+it), g gives F_P(1-it). Thus DIRECT exact K(1+it) contour integrand; NO frequency reversal needed. Paired physical integral at -2 equals W, because source zero below1. Compose prior contour limit with logY and real part.
   Scratch93776/exact67325 exit0.

All three wired into RHTower.lean following DivisorCoreMellinMean. All 17 public declarations audited ONCE externally: propext, Classical.choice, Quot.sound only. Audit73652 exit0. Global formal lint36032 passed; existing unrelated large-file warnings. Index24859 passed/refreshed. Scoped git diff --check passed. Packaging lake build audit remains pending due known broad stale prerequisite rebuild; do NOT restart broad rebuild/preflight just to satisfy packaging. All exact checks were lake env lean, one owned foreground process at a time. No old theorem re-audited.

All six owned tmp files removed:
 /tmp/ccm_head_regularity.lean
 /tmp/ccm_head_mellin.lean
 /tmp/ccm_physical_dilation_mean.lean
 /tmp/ccm_physical_dilation_audit.lean
 /tmp/ccm_physical_dilation_lint.log
 /tmp/ccm_physical_dilation_index.log
No owned Lean process remains. Final process scan found unrelated task /tmp/hb-independent-radial.lWxTDo; leave it alone. Shared cache has outside tasks.

## Documentation completed
- New stage3 ccm-fu-fixed-core-physical-dilation-mean.md with exact full paper proof and validation.
- Updated stage1 ccm-fu-fixed-core-correlation-contour.md and ccm-fu-fixed-core-signed-head-moment.md to physical bridge CLOSED, remaining scalar formalization/discrete integral/uniform changing-core control explicit.
- Updated stage3 ccm-fu-fixed-core-correlation-contour.md companion link, no longer stale physical-bridge gap.
- New stage2 ccm-fu-divisor-source-residue-sign.md: concrete dependency-closed PAPER proof B(-1/2)>1/(272pi)>0, Lean PENDING. This is next formalization; don't claim Lean sign already proved.
- Frontier untouched; STATUS untouched. New files untracked, intentional; no commits requested.

## Next direct source attack: formalize PAPER sign proof, then discrete correlation integral
Paper proof:
 Z=ζ(3/2)>0, D=-ζ'(3/2)=sum log n n^-3/2, c=log(8π)-γ-2-π/2.
 χ(-1/2)=-1/(4π) via Gamma_R_add_two at -.5, denominator nonzero.
 logDeriv χ(-.5)=logπ-[ψ(-.25)+ψ(.75)]/2
 =log(8π)+γ-2-π/2,
 because ψ(.75)=-γ-3log2+π/2, ψ(-.25)=ψ(.75)+4.
 Differentiate ζ(s)=χ(s)ζ(1-s) near -.5:
 B(-.5)=(D+cZ-Z²/(4π))/(4π). This proves reality too.
 f(x)=logx*x^-1.5 is positive decreasing on [2,∞); derivative x^-2.5*(1-1.5logx)<0, log2>2/3.
 D>=integral2∞ f=(2log2+4)/sqrt2>64/17 using sqrt2<17/12.
 0<Z<=3 from absolute zeta bound; π>3, π<63/20 (Real.pi_lt_d2), γ<29/50.
 log2>69/100, log3>109/100 ->log8π>log24=3log2+log3>79/25.
 c>79/25-29/50-2-63/40=-199/200>-1.
 Bracket >64/17-3-3/4=1/68. Therefore B(-.5)>1/(272π)>0.
 No numerical computation/truncation. Specific antiderivative -(2logx+4)/sqrtx, its zero tail, monotone integral comparison, exact reflected B identity are Lean tasks, not completed.
 Consequence if formally closed: fixed-core residue and eventually W_P sign is (-1)^(cardP+1). This is not uniform renewal; constants depend P.
 Actual discrete correlation equation κP-κ(P+p)=2ρ(P+p)p^-1.5 W_P(p) STILL NOT PROVED. Needs discrete block-integral identification.

Inspected local corpus APIs:
- ZetaCarrier.lean: zetaChi=Gammaℝ(1-s)/Gammaℝs; zeta_eq_zetaChi_mul {s} h0 h1 hG, zetaChi_analyticAt.
- Mathlib Analysis/SpecialFunctions/Gamma/Deligne.lean: Complex.Gammaℝ_add_two {s} (hs:s≠0): ΓR(s+2)=ΓR(s)*s/2/π. Gammaℝ_eq_zero_iff: zero iff s=-(2*n). These make χ(-.5) direct, no trig eval needed.
- SmoothAFEZetaChiShiftDerivative.lean:52 theorem logDeriv_zetaChi_off_poles {z} (hz:∀m,z/2≠-m) (h1z:∀m,(1-z)/2≠-m): logDerivχz=-ψ(z/2)/2-ψ((1-z)/2)/2+logπ. Namespace needs inspect top when use. It also has div_two_ne_neg_nat_of_re_eq_neg_half.
- SeamDivisionSourceSplit.lean namespace GaloisForLFunctions.SeamSplit: digamma_half; digamma_three_quarters_sub_quarter (difference π); digamma_one_quarter=-γ-3log2-π/2. Combine for ψ(.75). GammaLogDeriv has digamma recurrence; inspect exact name.
- ZetaFisherVariance.lean namespace RHTower: summable_log_natCast_pow_mul_rpow_neg (k) hσ; tsum_log_natCast_pow_eq_eulerLogPowMass hk hσ; deriv_riemannZeta_ofReal hσ = -(eulerLogMass σ:ℂ); riemannZeta_ofReal_eq_eulerMass.
- Mathlib Analysis/SumIntegralComparisons.lean:289 AntitoneOn.integral_le_tsum_comp_add (N:ℕ) (anti:AntitoneOn f (Ici(N:ℝ))) (summable:Summable(fun n:ℕ=>f n)) (nonneg:∀t∈Ioi(N:ℝ),0≤f t): integral x>N f x <=sum' n f(n+N). Need remove n=0,1 zeros.
- RiemannGaussian/RiemannXiSuzukiPointwiseFirstTailBarrier.lean:86 RiemannGaussian.eulerMascheroniConstant_lt_29_over_50. Existing kernel proof, no numerical experiment; norm_num rational finite harmonic with existing log bounds.
- Mathlib Analysis/Real/Pi/Bounds.lean:151 Real.pi_gt_three;163 Real.pi_lt_d2 (<3.15=63/20). No need pi<22/7.
- Mathlib Analysis/Complex/ExponentialBounds.lean:83 Real.log_two_gt_d9 (>0.6931471803),101 Real.log_three_gt_d9 (>1.0986122885).
Search prior research before new Lean (source/sign research done this turn). Verify used APIs in scratch, not from memory.

## Lean implementation lessons
- Avoid token <- in inequalities, |* after abs: spaces mandatory.
- mellin_comp_mul_left needs explicit cast function (fun x:ℝ=>(G_P x:ℂ)), cannot infer from nestedcast.
- Final limit compositions need simp only[Function.comp_apply] before rewriting contour.
- measurable_of_countable needs explicit Nat function, otherwise delta unfolding may infer Multiset ℝ.
- .div_const (d:ℝ), explicit cast to avoid Nat-valued measurable id.
- LocallyIntegrableOn requires explicit set, e.g. .locallyIntegrableOn (Ioi0).
- Set.indicator_of_mem explicit membership of Iic(logY).
- Explicit differentiableAt numerator/denominator types before .div avoid slow wrong unification.
- Complex.natCast_log orientation (Real.log n:ℂ)=Complex.log(n:ℂ); use ← for complexlognat.
- Complex.natCast_mul_natCast_cpow clean multiplicativity.
- No file globs RHTower/*.lean, directory too big; rg directory -g '*.lean'.

Prior completed chains in mem:ccm_fu_literal_mellin_contour_limit_2026_09_08 and mem:ccm_fu_uniform_positive_signed_head_moment_2026_09_08. Do not re-audit/build old finished leaves.
