# HB normalizable temporal horizon current — 2026-09-12, 0912e

RH goal remains ACTIVE and UNPROVED. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

User: optimize Lean; NO raising heartbeats/resource limits, NO axiom checks, NO computations, NO Git/launch.sh, NO full/umbrella builds. One owned foreground Lean/Lake at a time. Frontier READ ONLY. Use documented corpus research directly, broad + deep/method queries, inspect coverage/source arguments. No proactive subagents. Prior authoritative restoration: `mem:hawking_bm_full_horizon_current_restoration_2026_09_12_0912d`.

## Installed, scratch checked, exact-leaf audited, wired (do NOT re-audit unchanged)
All under formal/GaloisForLFunctions/RHTower/, namespace RHTower.D4BMJointSource. No resource-limit changes. Four source files plus five artifacts each installed; RHTower.lean imports added. Exact cache-only audits built target only, two Lake jobs each, no dependency sources/builds.

1. ThetaCuspHawkingBMTemporalOppositeCurrentProfile.lean, audit88s.
- oppositeCurrentRatio q branch u = -1/(2*u*(u-2*physicalRate q branch)).
- oppositeTemporalProfile retains angularSquare * [-2u*spin*selfPart -u*contactPart] * Gauss(-u,z) / (2sqrt(1-z)), times ratio. Complete self/principal/lift/contact source retained.
- ratio analytic away0/sourcepole; ratio*D=C/(2u), no C≠0 hypothesis.
- negativeGaussProfile_germ, oppositeTemporalProfile_germ actual physical q/branch/side/a/angularpoint. Gauss at -u via negated parameter ball. Source germ via explicit compositions/closure.
- profile_eq_ratio relates to incoming cleared profile*Gminus/Gplus whereGplus≠0.
- profile spatial continuity and frequency analyticity through selfQNM; principal/source poles excluded, self connection may be zero.
Optimization: function .congr handles eta/Fin3 expression, no broad expansion/resource hack.

2. ThetaCuspHawkingBMTemporalNormalizableCurrentDensity.lean, audit133s.
- normalizableTemporalRadialDensity13 = original continuedPhysicalTimeAction outer=true at tortoiseOf z, multiplied radius²−1, divided2zsqrt(1-z).
- oppositeTemporalRadialDensity20 = actual normalizable density − actual Aplus*incoming density. Not an arbitrary substitute.
- temporalCurrentSourceFactor27 = [-2w spin*actualSelfResponse −w*actualSourceProjection]*angularSquare.
- oppositeTemporalRadialDensity_eq_mode59 uses original homogeneous connection representation and Aminus=C/(2w).
- oppositeTemporalRadialDensity_eq_profile76 proves actual omitted density=Fopp/z for nonreal, sourcepole separated, C≠0, interiorz. No Gplus nonzero requirement in identity.
- spatial continuities118/136; original finite integral decomposition150 proves IntervalIntegrable of incoming and opposite terms before integral_add. Uses Gplus nonzero throughout finitecutoff; physical Gauss lower bound dischargesnearhorizon.
Optimization: failed rfl due reassociation fixed with `simp only [gaussProfile,mul_assoc]`; all other declarations firstscratchpassed.

3. ThetaCuspHawkingBMTemporalOppositeCurrentRestoration.lean, audit57s.
Main13 physicalOppositeTemporalCurrent_horizon_restoration actualqbranchsideazang:
∃R B d,R>0,B>0,B≤half,∀0<b≤B:
L_b=LogarithmicEndpoint.finitePart Fopp d b analytic at w0;
(w-w0)L_b(w)→0 punctured;
∀w∈ballw0R,C(w)≠0, ∫e..b originaljopp + d(w)log e →L_b(w) as e→0+.
Uses actual quadratic germ .exists_bounded and bound C z²+M z≤(C+M)z, then LogarithmicEndpoint analyticity/cutoff theorem. Gauss bound and actual jopp identity transfer to original finite integral. No supplied analytic/counterterm/residue premises.

4. ThetaCuspHawkingBMTemporalNormalizableCurrentRestoration.lean, audit9.8s.
Definitions normalizableTemporalHorizonFinitePart11 M_b=Aplus*N_b/D+L_b; normalizableTemporalHorizonCutoff20 = SINGLE integral original normalizable temporal density + Aplus*(c0 e^w/w+c1 e^(w+1)/(w+1))/D +d loge.
Main31 physicalNormalizableTemporalCurrent_horizon_restoration_and_residue actualqbranchsideazang:
∃R B c0c1d,R>0,B>0,B≤half,∀0<b≤B,
(w-w0)M_b(w)→ N_b(w0)/physicalFundamentalDenominatorSlope;
∀w∈ballR,C≠0, original SINGLE cutoff expression→M_b(w).
Combines 0912d incoming restoration, opposite restoration, actual finite integral split. Aplus analytic; Aplus(w0)=1 from fundamental_horizonRegularCoefficient. All cutoff terms/source channels/contact remain.

## Exact remaining mathematical work
Normalizable temporal HORIZON current is now restored before residue extraction. Full normalizable OUTER current and evaluation/nonvanishing of joined action still open. Full angular reconstruction, independent SS/VV, retarded/advanced Peierls and fixed Hawking-clock extinction not closed. RH not proved.
Next positive conjecture: at w0, F(w0,z)=K*incomingPairingFactor(w0,chi,z), K=angularSquare*(-2w0*(physicalAngularParameter²−1/4−2))*physicalSelfSourceCoefficient(q)*fundamentalSourceMoment(w0,s,a)*clearedOnset(s,w0).
Paper derivation: D(w0)=0 kills cleared principal/contact terms; clearedReducedGreen_fundamental_factor gives mode times fixedmoment*clearedOnset; selfClearedProfile=Gplus*fixedmoment*clearedOnset; hence F=K Gplus²/(2sqrt). No factorization/evaluation theorem added yet. Need identify actual c0(w0),c1(w0) from uniformjet then N_b(w0)=K*incomingNormFinitePart. Existing `physicalFundamentalNorm_join` gives incomingnorm+outer originalnormalizable²=normFinitePart. Need actual full-current outer integral and physical K survival, not merely bare-response pairing.
Warning about proof interfaces: 0912d incoming restoration and new normalizable theorem only expose c0/c1 existentially, not their jet witnesses. Do not assume witnesses follow from result. New concurrent radial_cutoff_package below exposes jets and cutoff at w0, likely better basis for residue evaluation/global join. Avoid duplicating large proofs just to recover hidden witness.

## Newly available concurrent sources, read only, not verified by our leaves
Existing: ThetaCuspHawkingBMHorizonModeOuterUniformBound (tortoiseMode_outer_uniform_bound96 for modefalse centered arbitrary nonrealfrequency), TemporalCurrentClearedDensity (full source expression; spatial/analytic through selfpole), HTGeometry.JetCoefficientUniqueness (two jet coeffs uniquely determined by O(z²) bound).
New during0912e:
- ThetaCuspHawkingBMTemporalCurrentClearedDensityBound: principal_outer_uniform_bound23, contactFactor_outer_uniform_bound100, selfExpression_norm_le148, contactExpression_norm_le171, clearedTemporalExpression_norm_le195, clearedTemporalDensity_outer_uniform_bound223.
- ThetaCuspHawkingBMTemporalCurrentRadialCutoff: compactPart131, compactPart_analyticAt135, cutoff_integral_split199.
- ThetaCuspHawkingBMTemporalCurrentRadialPackage: radial_cutoff_package23 (FULL SOURCE READ): ∃b c0c1Mel positiveb≤half; c0c1Mel and compactPart analytic; actual uniformjet witness in neighborhood; eventualpunctured original incoming temporal ∫L..0 with twoCT tends atBot to (Mel+compactPart)/D; Mellinvalue atw0 is positiveepsilon limit of actual cleared profile with sameCT. Source only, not imported/audited by us, remains unwired at lint.
IMPORTANT confirmed namespace collision before integrating: TemporalCurrentHorizonRegularity24 (0912d installed) and TemporalCurrentRadialCutoff38 both declare RHTower.D4BMJointSource.tortoiseOf_continuousAt with same signature. Resolve with source owner/afterstable before importing together; don't alter ongoing work indiscriminately.
Potential global opposite proof: use ratio*fullclearedSourceFactor*tortoiseMode false (-w) on outer t interval. Existing horizon-mode outer bound can be centered -w0; source factor uniform bounds from new Bound leaf. This yields analytic original opposite OUTER integral with no Gplus divisions, joins current logarithmic horizonrestoration. Residue opposite entireintegral zero; incoming fullradialpackage supplies jetwitness to evaluate residue K*normFinitePart. Not implemented.

## Search/docs/validation
Three corpus searches: broad `opposite` filteredThetaCuspHawkingBM; deep pole-cancellation/logarithmic restoration; deep finitepart/jetidentification. Candidate lemmas and source_arguments read. Third partialFalse coverage snapshot 57048 files, mostly compilerpending, semantics unmeasured; proposed GammaPole ingredientset inapplicable to thiscurrent. Do not treat coverageasproof. Broad recent arXiv confluence/impedance search opened2608.17844 (18Aug2026 activeimpedancefinitearray); no theoremused, no computation.
Updated docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md topstatus and latest fullnormalizable section with exactformulas, passedchecks and nextconjecture. Frontier and universalSTATUS untouched.
Final `scripts/formal_tools.py lint` ran ONCE after4wires; exit1 seven unreachable concurrent modules (HorizonModeOuterUniformBound, TemporalCurrentClearedDensity, TemporalCurrentClearedDensityBound, TemporalCurrentRadialCutoff, TemporalCurrentRadialPackage, HTGeometry.JetCoefficientUniqueness, HTGeometry.SecondEndpointMellinLaurentInterchange). No lint error names our four newleaves. Large-filewarnings existing. Global lint NOT passed. Do not wire/rebuild otheragentsunfinishedmodules blindly.

All0912e owned sessions completed. Four scratch files/searchJSONs/cache-onlyauditpackage/helper scheduled for explicitcleanup before final; do not depend on tmp paths. No subagents spawned. No goalcompletion/blockupdate.
