# FZZ-P subtracted original source analyticity closure, 2026-09-11

Goal ACTIVE; RH UNPROVED. Main chain: complete fixed theta/FZZ source -> integrated mixed replica-momentum Ward law in independently fixed phase frame -> balanced external-Gamma vacuum delay -> passivity -> RH. Full Ward producer/frame still missing. No subagents, one owned foreground Lean at a time; no numerical computations, no full builds, no commits.

## Audited source module
`formal/GaloisForLFunctions/RHTower/FZZCigarSubtractedScreeningAnalytic.lean`, 438 lines, 7 public data-only theorems. Imports audited PlaneScreeningCutoff and Mathlib.Probability.Moments.MGFAnalytic. Wired RHTower umbrella (line can shift with concurrent writers).

For R=1/2, K(alpha,beta)=normz^alpha norm(z-1)^beta, A0=integralB0 normz^alpha(norm(z-1)^beta-1), A1=integralB1 norm(z-1)^beta(normz^alpha-1), E=original exterior integral, define EXPLICITLY
H=(alpha+2)(beta+2)(A0+A1+E)+2pi(beta+2)R^(alpha+2)+2pi(alpha+2)R^(beta+2).

Public theorems:
1 fzzScreeningZeroSubtracted_singular_mark_analytic(u,beta): A0(-3+expu+delta,beta) analytic atdelta0.
2 fzzScreeningOneSubtracted_regular_mark_analytic(v,a): A1(s,-3+expv) analytic at every reala.
3 fzzScreeningPlaneClearedSource_symm(alpha,beta).
4 fzzScreeningPlaneClearedSource_analytic_left(v): beta=-3+expv, AnalyticOnNhd in alpha on Ioo(-3)(-2-beta).
5 fzzScreeningPlaneClearedSource_analytic_right(u), reflected analogous slice.
6 fzzScreeningPlaneClearedSource_pole_values(beta): H(-2,beta)=H(beta,-2)=2pi(beta+2).
7 fzzScreeningPlaneClearedSource_eq_finitePart(u,v): for alpha,beta existing first-continuation-power charts in(-3,-2), H=(alpha+2)(beta+2)*fzzScreeningPlaneFinitePart.

Proof: generic PRIVATE signed_exp_analyticAt splits actual signed weight f into maxf0 and max(-f)0, withDensity MGF. Open original integrability interval admits both weighted MGFs. G0 uses exp(delta lognormz) exact shift and known original subtraction bound alpha>-3. G1 regular exponent uses C1 compact Lipschitz lognormz on disk1 (awayzero), |lognormz|<=C norm(z-1), so oneLogWeight beta =norm(z-1)^beta lognormz is integrable beta>-3. Exact FTC exp(aX)-1=a integral_(Ioc0,1) X exp(a*t*X)dt. Product disk1×interval measure with bounded variable tlognormz: joint integrability before Fubini identifies originalA1. Exterior uses actual tail conditionalpha+beta<-2 and same exponential shift. All original terms combined with powers, then reflection gives other slice. No Gamma equality assumed. Separate REAL analyticity only, not joint/physical replica-p identification.

Scratch `/tmp/fzzp_subtracted_analytic.lean` CLEAN PASS. Leaf finalbuild PASS8838jobs, leaf124s. All7axiomclosures coreonly propext/Classical.choice/Quot.sound. Formal lint PASS. Logs `/tmp/fzzp-subtracted-analytic-{scratch,build,axioms,lint}.log`. Build60977, axes91613, lint77243 all TERMINAL. Noownedanalytic-moduleprocess remains.

Card `docs/drafts/pipeline/1-in-progress/fzz-p-subtracted-screening-analytic.md` complete proof and audits. Main matching card updated [x] separate source analyticity and cutoff assembly. Frontier/STATUS updated accurately; STATUS explicitly says separately analytic and retention of finite pole values. Fixed-puncture simultaneous cutoffs do NOT prove moving/coalescing-puncture limits. Concurrent writer had used ambiguous simultaneous-collision wording; our frontier now says two fixed punctures. Original Gamma identity, full marked physical response, higher depths, frame and Ward producer still open.

## Active next scratch and ownership
`/tmp/fzzp_plane_gamma_match.lean` (about90lines) currently LIVE under session85340, command lake env lean ... from formal, log `/tmp/fzzp-plane-gamma-match-scratch.log`. Previous run72711 TERMINAL1; mathematical power-ball and local-zero-finitepart proofs checked, only Gamma analytic elaboration errors. Do not start other Lean until85340 terminal. Imports new audited analytic source+Beta+Complex.Analytic+Analytic.Uniqueness.

Prefix targets: reciprocal_gamma_analytic(all real) copied from prior checked Complex reciprocalGamma restriction. positive_gamma_analytic r hr by invert reciprocalGamma withGamma_pos nonzero. clearedGamma(alpha,beta)=4pi Gamma(-alpha/2-beta/2-1)Gamma(2+alpha/2)Gamma(2+beta/2)*invGamma(-alpha/2)*invGamma(-beta/2)*invGamma(2+alpha/2+beta/2). Prove analytic inalpha wheneveralpha>-3,alpha+beta<-2. original_power_ball alpha ha: original ball integral normz^alpha =2piR^(alpha+2)/(alpha+2) foralpha>-2. original_zero_finitePart alpha beta ha: FP0 equals unsubtractedK integral onB0 in ordinary chamber. Those latter two passed previous scratch independently of Gamma errors.

Last fixes now checking: positiveGamma.inv returns inverse FUNCTION, not expanded pointwise. Use convert! h using1; ext s; simp. AnalyticAt.comp greedily inferred affine function as final arithmetic binary operator; use .comp_of_eq h1 rfl etc with analytic affine input ratherthan .comp. Removed unused mem_ball_zero_iff simp.

## Exact remaining Gamma match plan
Newmodule H is4times a,b-card normalization, with a=-alpha/2,b=-beta/2. Need source equality on original chamber, then identity theorem, then divide clearingfactor on physicalfirststrip. Do NOT use pole values alone as uniqueness data; analytic remainder would be undetermined.

1 Original powerball and FP0eqoriginal are now in scratch. Reflection supplies FP1eqoriginal beta>-2. Original fullK integrable via provedBeta_chart_iff at a=-alpha/2,b=-beta/2 when alpha,beta>-2 andalpha+beta<-2; these implyalpha,beta<0. Exact B0,B1,E domain union univ with disjoint balls yields integralFPsum=originalwholeintegral. Private clearing identity H=(alpha+2)(beta+2)*FP valid anynonpole viaunfold+field_simp; existing public version coversphysicalonly, so ordinarycase eitherdirectalgebra or privategeneral proof. Then Gamma_add_one at1-a,1-b clears numerator poles and turns the provedordinaryBeta ratio into clearedGamma.
2 First fixbeta∈(-2,0); sourceleft andGamma analytic on Ioo(-3)(-2-beta). Choose alpha0=-2-beta/2, strictlyinsideordinarychamber. Eventual equality nearalpha0 fromordinarychamber. Use AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq, isPreconnected_Ioo. Thisextendsalpha down to-3.
3 For physicalalpha∈(-3,-2), source andGamma rightanalytic on Ioo(-3)(-2-alpha); choosebeta0=-1. Firstextension gives equality onallbeta∈(-2,0) near-1. Identitytheorem yieldsphysicalbeta∈(-3,-2). No needfirst prove larger positive-alpha domain.
4 Divideclearingfactor viaauditedH_eq_finitePart. Gamma recurrence convertsGamma(2+alpha/2) to(1+alpha/2)Gamma(1+alpha/2), similarlybeta. Formula predicted FP=pi Gamma(-alpha/2-beta/2-1)Gamma(1+alpha/2)Gamma(1+beta/2)/(Gamma(-alpha/2)Gamma(-beta/2)Gamma(2+alpha/2+beta/2)). For bothfirststrip, latterGammaargument∈(-1,0), numeratornegativefactorpairpositive, denominatornegative -> predictedstrictnegativeFP. NeedproveGamma sign/nonzero usingGamma_add_one andpositiveGamma, not assume. Gamma matching/value/sign NOT YET proved.
5 Later evaluate original continued marked derivatives with retained counterterms and identify physicaldeficit/p, notjust independent position exponents.

Useful actual APIs verified: AnalyticAt.comp_sub alpha convertsdelta0shift toactualalpha; simplifyzero_add and∀s alpha+(s-alpha)=s. AnalyticAt has .mul but NO .const_mul: use analyticAt_const.mul h. Mathlib.AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq in Analytic/Uniqueness223 takeshf,hg,preconnected,basepointmembership,eventualeq. ReciprocalGamma entire theorem MathlibGammaBeta + Complex.Analytic realrestriction. Primitive publicGammaReal analyticname absent; invert entire reciprocal onpositiveargs.

See mem:rh/fzz_plane_screening_cutoff_2026_09_11 for4public originalindependentcutofftheorems/audits andbroadrecentarxiv/deep/methodsearch. Sourcecard records allmethodproofs; no newly installedplugin needed. Repo has concurrentchanges/commits, preserveothers.
