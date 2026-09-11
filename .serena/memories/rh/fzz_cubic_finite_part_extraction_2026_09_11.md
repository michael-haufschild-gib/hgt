# FZZ-P original cubic finite-part extraction — 2026-09-11

Goal ACTIVE: unconditional closed Lean RH via FZZ-P. RH UNPROVED. Previous goal turn was progress: eight GammaUnit/rational/actual-source jet statements closed and built. No subagents.
Latest user ban: STOP #print axioms. No further such audits. One owned foreground Lean only; scratch lake env lean /tmp/file.lean, cwd formal/. Final lake build exact leaf only, never umbrella/full. No numerical computations or new axioms/sorry/admit. No commits. Preserve concurrent files.

## Current live state
ONLY owned Lean session34749 RUNNING:
lake env lean /tmp/fzzp_cubic_finite_part_value.lean > /tmp/fzzp-cubic-finite-part-value-scratch.log 2>&1
cwd /Users/michael/Documents/code/hgt/formal.
Poll same handle. No second Lean.
This ~460line scratch has FIVE public targets: complete cubic polynomial; original local FP comparison; original plane FP comparison; exact cleared-source mixed-jet extraction; actual FP value -84pi.
First THREE already passed earlier mathematical scratch24294 exit0 (/tmp/fzzp_cubic_finite_part_extraction.lean, log -extraction-scratch.log). No new repo module yet.
First combined5 attempt3319 exit1: id_eq simplification missing, invalid Nat.cast_nonneg argument R, unnecessary ring, implicit pointwise-function instances in radial derivative, outer derivative translation matching. Corrected in current34749. Final formula also had newline-dot chain latent error, fixed before rerun.
No mathematical contradiction found.
All searches terminal, all candidate/method lists + ingredient sets inspected.
After5 passes, add sixth public original independently removed cutoff value theorem, scratch-check then promote e.g. FZZCigarCubicFinitePartExtraction.lean (verify absent), wire after GammaUnit, final leaf build + global lint. No axioms check.

## Chain and hard gaps
Source -> integrated mixed replica-momentum Ward identity in independent phase frame -> balanced external-Gamma vacuum-delay saturation -> passivity -> Re rho=1/2 -> RH.
Previous8 module formal/GaloisForLFunctions/RHTower/FZZCigarHigherScreeningGammaUnit.lean has exact original H_ab=-12288pi and H_aab=16176pi at(-6,-6), through source-germ Q*U with unit flat through2. All8 scratch/build/lint passed, no process live. Full source10 continuation and earlier8 Taylor/7 restoration closed; see mem:rh/fzz_higher_cleared_source_2026_09_11.
Now attacking ORIGINAL unmarked cutoff extraction. Marked cutoff value -141pi/8 and ratio47/224 remain conjectures, as do screening-count continuation, physical normalization/couplings/nonzero modes, independent phase frame and full Ward producer.

## Three proved-in-scratch original comparison statements
Public fzzScreeningFifthAngularPolynomial_cubic r:
full quintic angular polynomial at -6 =1+9r²+36r⁴-460r⁶-405r⁸-21r¹⁰.
Uses exact existing binomial_succ recurrence and all6 restored coefficients, no numerical experiment.
Public fzzScreeningCubicLocalFinitePart_eq_fifthRemainder:
LocalFP=I5(-6,-6)-10993pi/64+72pi log(1/2).
Public fzzScreeningCubicPlaneFinitePart_eq_fifthRemainders:
PlaneFP=2I5+actualExterior-10993pi/32+144pi log(1/2).
Original definitions/independent cutoff theorem imported from FZZCigarCubicScreeningCutoff (public localFP27, independent plane limit289).

Proof mechanism:
remainderPolar(r,theta)=r*originalFifthSubtracted(-6,-6)(circleMap0 r theta).
Public uniform sixth Taylor remainder gives |R5(circle)|<=C on0<r<1/2; hence |polar|<=C*r. Product L1 proved before Fubini, retaining actual source.
Indicator polar change on original half disk via Complex.integral_comp_polarCoord_symm.
Actual sixth-power kernel circle average minus full Taylor circle average. Radius chart inverted u=log((1-r)/r) to specialize original HigherAngular_three_remainder.
Angular polar integrand =2pi[r*CubicAngularRemainder+460r+405r³+21r⁵].
Finite tail integral8177/128 from explicit primitive230r²+405r⁴/4+7r⁶/2. Original local primitive atR is -22+36logR.
Then exact local/plane FP comparison.
Original scratch7093 errors fixed: integral_comp_add_right needs explicit lambda, not underscore; rpow rewriting under theta binder needs explicit pointwise he; denominator nonzero requires interval bounds through mul_nonneg(1/2-r)(1/2+r). Scratch24294 then exit0. Do not redo standalone3.

## Current five-target combined scratch
/tmp/fzzp_cubic_finite_part_value.lean AUTHORITATIVE fixed.
UNFIXED draft /tmp/fzzp_cubic_extraction_derivative_part.lean (do not reconstruct from it).
Imports GammaUnit and CubicScreeningCutoff, no changes to existing dependency modules.
Private exteriorWeight(alpha,beta)=restrict original exterior .withDensity(ofReal originalPlaneKernel).
Actual kernel nonnegative. Original exterior admission from source theorem and exp-log chart.
ProbabilityTheory.mgf(log norm) of that weight equals original exterior integral at alpha+delta.
Local integrableExpSet interior0 from neighboring admitted powers proves parameter analyticity using analyticAt_mgf, then .comp_sub alpha. This replaces generic signed-lift duplication with actual positive exterior source.
Actual exterior reflection retained.
Local fifth singular/regular analytic theorems transported from existing exp charts.
originalRegularPart=I5(alpha,beta)+I5(beta,alpha)+actualExterior; separately analytic in D, exact symmetric.

A(alpha)=(alpha+2)(alpha+4)(alpha+6), A(-6)=0, A'(-6)=8.
Private half_power_deriv(alpha,c) uses HasDerivAt.const_rpow for R^(alpha+c).
radialSlope:
k0=-32,k1=-16,k2=-6+8logR,
k=n+3:8 R^(2k-4)/(2k-4).
Private radial_deriv proves exact HasDerivAt cleared radial alpha k at alpha=-6, all k.
countertermSlope(beta)=2pi sum0..5 c_k(beta)*radialSlope(k).
HasDerivAt.fun_sum proves actual clearedCounterterm first derivative; analytic in beta via actual coefficient analytic theorem.
Specialization countertermSlope(-6)=-14449pi/8+576pi logR.

source_right_deriv alpha for alpha in(-7,-5):
H_beta(alpha,-6)=8*Aalpha*originalRegularPart(alpha,-6)
 +8*CTclear(alpha,-6)+Aalpha*countertermSlope(alpha).
Derivative of full source, no singular unregularized integral differentiated.
At alpha=-6 product rule gives H_ab=64*Rsum+16*countertermSlope(-6).
Original plane FP comparison yields PUBLIC:
fzzScreeningHigherClearedSource_cubic_second_extraction:
deriv_a at0 deriv_b at0 H(-6+a,-6+b)=64*PlaneFP-6912pi.
PUBLIC fzzScreeningCubicPlaneFinitePart_value:
PlaneFP=-84pi, by combining extraction with already checked H_ab=-12288pi.

Last3319 errors/current fixes:
half_power_deriv simpa only [mul_one,id_eq].
radial case2 removed redundant ring after norm_num.
Nat.cast_nonneg uses explicit show (0:ℝ)<=n from Nat.cast_nonneg n (no argument R).
radial generic tail uses fun_mul/fun_div, simp only [he,id_eq,factor_zero,zero_mul,sub_zero,mul_one], explicit change of HasDerivAt lambda and slope before h.congr_deriv. Denominator nonzero from Nat.cast_nonneg and linarith.
Outer shift: after simp_rw [deriv_comp_const_add,add_zero], explicitly rw [deriv_comp_const_add (fun alpha=>deriv(H alpha)(-6)) (-6) 0,add_zero], then change raw mixed-derivative lambda before he.deriv_eq.
Fixed same-line regularPart_analytic(...).differentiableAt.hasDerivAt.
These fixes currently running34749.

## Sixth desired theorem after5 closes
fzzScreeningCubicPlane_independent_cutoff_value:
Tendsto (fun P:ℝ×ℝ=>fzzScreeningPlaneCutoff(-6)(-6)P.1P.2
 +2pi*CubicCollisionPrimitive(exp(-P.1))
 +2pi*CubicCollisionPrimitive(exp(-P.2)))
 (atTop ×ˢ atTop) (nhds(-84pi)).
Proof simpa only [fzzScreeningCubicPlaneFinitePart_value] using existing
fzzScreeningCubicPlane_independent_cutoff_limit.
This ties value to original independently removed cutoffs; no diagonal-only claim.
Do not add trivial extra sign/nonzero wrappers; exact value handles normalization later.

## Current authoritative docs inspected
Card docs/drafts/pipeline/1-in-progress/fzz-p-higher-screening-collisions.md ends with proposed local/extraction formulas; NOT yet updated to this turn’s3 scratch successes.
Frontier source8 paragraph~1686 completed; a stale global summary~44 still calls source10 “source-inspected working-tree” although already built. Update only FZZ phrase when finalizing new work.
STATUS existing line21 already has route-independent “Cannot transfer positivity of an original integrand through finite-part continuation” and sign rationale. Do not add duplicate rule; after6 audit, append concise cubic actual-cutoff citation without route-specific formulas.
STATUS line27 Must retain finite boundary values/parameter subtraction derivatives already cites source10. Can add source extraction evidence after full audit if useful.
Need update card full pending conjecture wording: unmarked value becomes closed ONLY after new proof passes; marked value/ratio remain conjectures. Do not rewrite marked open as solved.
No new research card needed; current higher screening card covers ongoing hard target.

## Search and recent papers this turn
A /tmp/fzzp-cubic-original-polar-methods.json, deep180, session75774 exit0.
partial generation874090; semanticindex and source refresh incomplete; no errors. All20 candidate+20 method names + generated proofidea/ingredient inspected.
Read actual HTGeometry/LebesguePolarIntegral1-108 integral_polar_mul: requires pointwise radial-angular factorization; original R5 is not such a factorization before angular integration. Actual indicator polar mechanism selected, not this premise.
Read HTGeometry/CauchyPompeiu248-280: original annulus indicator transport.
Read RHTower/DeningerRadialKahlerTrace44-70: radial trace, not original nonradial source. No imported false radiality.
B /tmp/fzzp-cubic-cleared-coefficient-methods.json, deep180, session44387 exit0.
partial874107; semanticindex/rerank/source refresh incomplete; local runtime rerank deadline. All20+20 and ingredientset inspected.
Read HadamardFinitePart118-164 exact divided-difference split retains endpoint logarithm; SuzukiRestrictedWeilForm216-253 wraps same theorem and log coefficient. They are Cauchy kernels, no direct cubic source identity.
Read Mathlib Deriv/Mul444-463 explicit finite product derivatives and actual Deriv/Add210-225 HasDerivAt.fun_sum.
Read Mathlib Deriv/Shift25-66 explicit deriv_comp_const_add and Deriv/Pow731 HasDerivAt.const_rpow.

Broad recent arXiv searches “defect” and “resolvent” with Sept/Aug2026 refinements. Opened primary https://arxiv.org/abs/2609.01670, submittedSept1: Countable IET Models and Defect Sets for Interval Translation Maps. Abstract retains branch defect measure and gives finite/countable models under invariant nonatomic probability and finite/null defect-support hypotheses. These premises are not identified for FZZ; no cutoff/Ward theorem imported. Other defect hits experimental solid-state/biology, no mathematical tool extracted. Need document compact intake on card after proof finishes. No absence claim from partial search.
