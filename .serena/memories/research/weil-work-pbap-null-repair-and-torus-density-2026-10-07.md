# WP01 active goal and verified continuation — 2026-10-07

Goal ACTIVE: solve unconditional full RHTower.WeilOneSided.PrimeBlindPositive in docs/reports/weil-work/01-pbap-existence.md and compile its application to exists_weilPositiveFull_iff_primeBlindPositive. No producer, general sign theorem, or RH proof obtained. Do not mark complete for bridges.

User requires hgtl7 EVERY turn; skill read this turn. No numerical computations, full/umbrella builds, heartbeat hacks, new axioms/placeholders, commit/push. One foreground Lean/build per agent; targeted lake build --old +Module, final lake env lean source. Wire leaves. Check corpus directly using documented research command before new topic/code; inspect candidate_lemmas AND source_arguments and coverage. Keep own card. No agents spawned. Other agents edit shared tree; preserve their changes. Serena ignores Lean files; symbol tools unavailable for this scope, use source-checked rg/bounded reads. architecture/testing docs absent. update_plan/multi_tool_use unavailable, use card plan and Promise.allSettled reads.

## Four finished owned leaves (all RHTower.WeilWorkPBAP)
1. WeilWorkPBAPNullRepair.lean, blob 00d96a1f5d99637bd6731d1c3b18ef249255a3b9: finite defect repair with nonnegative smooth corrections; exact all-integer nulls; full energy-change bound. Target build/direct/eight axioms pass.
2. WeilWorkPBAPGramPackets.lean, blob 0647ce6d3dfb8abb197616fe3f575c5999128ca5: finite PSD matrix -> actual smooth compact tests, rational-log samples select a*k=b*m, finite divisibility traces imply all integer nulls; actual nonnegative Finsupp mixture and exact mass. Target build/direct/ten axioms pass.
3. WeilWorkPBAPMomentPackets.lean, blob 7f77ab2fbe9632cca6aae99daf0eec2ee4699172: actual representing probability μ -> integral monomial Gram PSD, divisible entries vanish, trace, normalized actual null mixture with sample phaseMoment μ a b * packetCoeffCorrelation d a b. Target build/direct/ten axioms pass.
4. WeilWorkPBAPSpectralMeasure.lean, blob 64190369ffaf22352f991b3dccb17fa381a2d176: actual Fourier-square probability for normalized nonnegative mixtures, pushforward to prime torus, exact rational character/sample identity. Target build/direct/nine axioms pass THIS TURN. All printed axioms only propext, Classical.choice, Quot.sound. Umbrella imports lines6919-6922. No umbrella build.

New leaf APIs:
testSpectralDensity f ξ = norm(paperFT f (-(2*pi*ξ)))^2; nonnegative, continuous, integrable. Actual Fourier inversion.
mixtureSpectralDensity c, mixtureSample_eq_integral_density, mixtureSample_zero_eq_integral_density.
abbrev NormalizedMixture := {c : WeilTestFn→₀ℝ // nonnegative coefficients AND mixtureSample c 0=1}.
spectralProbability c : ProbabilityMeasure ℝ from volume.withDensity(ofReal density).
primeSpectralPoint ξ := clockPhasePoint (log p) (2*pi*ξ).
spectralTorusProbability c, phaseMoment_spectralTorusProbability c ha hb: rational moment exactly mixtureSample c (log a-log b).
abbrev ComplexNullMixture := {c:NormalizedMixture //∀n≥2, mixtureSample c.1(logn)=0}.
spectralRepresentingMeasure c : RepresentingPhaseMeasure. This complex-null subclass is STRONGER than WP01 real nulls; broader equivalence needs symmetrization, unformalized.
exists_spectral_representing_mixture N L μ d: actual smooth normalized complex-null mixture from packet family, spectral representing measure moments equal target moment*coefficient correlation for positive a,b with b≤L+1.
No full Weil positivity input anywhere.

Latest finished validation:
- /tmp/wp01-spectral-names.lean exit0.
- targeted build log /tmp/wp01-spectral-build.log exit0.
- /tmp/wp01-spectral-audit.lean and log exit0,9standardaxioms.
- final lake env lean GaloisForLFunctions/RHTower/WeilWorkPBAPSpectralMeasure.lean exit0, empty /tmp/wp01-spectral-final.log.
- index exit0,0Markdownchanges; generated files no tracked diff.
- owned diff check exit0.
- /tmp/wp01-spectral-lint.log exit1: nine unrelated reachability failures: WeilWorkDeficitSquareWindow, WeilWorkQuantizationRadialContour, WeilWorkQuantizationRadialGrowth, WeilWorkSettledPhaseMellinTrace, ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No owned PBAP leaf flagged. Do not fix unrelated concurrent files.

## Changed next formal objective: actual narrow-packet full-energy lower bound
Own paper docs/reports/weil-work/results/01-pbap/PACKET-ENERGY.md contains complete proof, NOT formalized.
For N>=1,L>=105, beta=narrowBumpC(N*L), m=packetMass N L, f=gramPacket N L c, S=sum_{n=1}^N norm(c n)^2, prove
weilArchRe(f*tilde f) >= m*S*((1/2)*log(1+N*L/4)-10-(2/L)*sqrt(1+log N)).
Arbitrary complex c; NO null assumption, both poles kept. Finite nonnegative mixtures inherit it. Normalized energy diverges as N→∞ uniformly L>=105; also as L→∞ with N fixed.
Verdict BRIDGE to classical MVT; scientific novelty unestablished. More informative than another measure interface: exact torus realization pays divergent frequency energy. Does NOT solve general PBAP or establish energy-faithful density.

Paper mechanism:
r=1/[4(NL+1)], w=2r. A=∫|beta|; A²≤w*m by CS. Translated bumps disjoint => mass=m*S. fhat=betahat*DirichletPolynomial up to unimodular centering, |betahat|≤A.
Native dirichlet_meanValue_sharp constant104 at ±T => ∫_{-T}^T|P|²≤(2T+208N)S. T=NL gives2N(L+104)S.
Normalized low mass≤m*S*N(L+104)/[2π(NL+1)]≤m*S/2, because π>=2,L>=105.
gammaBracket>=log(1+|t|/4)-10 => gamma energy≥m*S*(.5log(1+NL/4)-10).
Pole exact2*a_plus*a_minus*Re[(Σc_n√n)conj(Σc_n/√n)], centering cancels. a_plus*a_minus≤exp(r)w*m. CS; Σn≤N²,Σ1/n≤1+logN,2wN≤1/L,exp(r)<2 => pole>=-(2/L)m*S√(1+logN).
No assumptions of missing energy estimates in new Lean statements.

Currently /tmp/wp01-energy-names.lean is the scratch:
- imports GramPackets, Sieve.DirichletMeanValueSharp, ZetaSymbolArchimedeanHorizon.
- noncomputable section.
- verifies principal names and proves gammaBracket lower bound simply unfold EF.gammaBracket; linarith (its definition exactly matches digamma lemma).
- two-sided MVT example all real T: int_-T^T ||dirPoly||² <=(2*T+208*N)*sum||c||².
- previous scratch failed only missing Herglotz import and noncomputable section; fixed by unfolding EF.gammaBracket directly, avoiding extra import.
- next failure at intervalIntegral.integral_add_adjacent_intervals needed explicit (μ:=volume); fixed.
- final scratch run session22911 EXIT0, empty /tmp/wp01-energy-names.log. A final linarith failure was fixed by simp only [Pi.pow_apply] at the adjacent-integral identity; this normalizes the same integrand, not a mathematical change. Both gamma lower and two-sided MVT sublemmas now pass.
- No new energy leaf yet. All owned Lean/build/search/index/lint commands EXITED. No stale owned process. Do not repeat spectral audits without source changes. Continue actual packet Fourier factorization, low spectral mass, and full signed pole bound before claiming the energy theorem formalized.

Source-checked next APIs (verify each needed name in /tmp first):
RHTower.Sieve.dirichlet_meanValue_sharp in Sieve/DirichletMeanValueSharp.lean88; error104Σ(j+1)||c||², all real T. continuous_dirPoly in Sieve/DirichletPoly.lean50.
RHTower.log_sub_seven_le_re_digamma_quarter in ZetaSymbolArchimedeanHorizon.lean132. Same module integral_norm_sq_paperFT_eq261 requires ContDiff2 and tsupport subsetIcc.
EF.gammaBracket in .lake/packages/Zeta23/Zeta23/ExplicitFormula.lean67 =Re digamma(1/4+I*r/2)-logπ.
RHTower.paperFT_translate' in WeilPositivityMultiplicativeToeplitzBound.lean447.
RHTower.paperFT_finset_sum in ZetaWeilFiniteLevelInertia.lean484, continuous compact summands.
gramPacket_rational_sample GramPackets82 at a=b=1 gives exact mass without new disjoint-support argument.
Sieve/HarmonicLogBound.lean41 sum_Icc_one_div_le_one_add_log.
LebesgueAtomWeilPositivity.lean390 integrable_paperFT_weilTest_mul_gammaBracket; 458 compact-support Plancherel alternate (namespace check needed).
Mathlib Bochner/Basic1191 integral_mul_le_Lp_mul_Lq_of_nonneg for CS; no special L2 theorem found yet.
Fresh mean-square proof in scratch derives weighted sum≤N*S, uses adjacent intervals with volume, then linarith.

## Still open density/Jensen survivor, DO NOT retire
TORUS-DENSITY.md complete paper construction:
representing μ on prime torus, finite exponent-box normalized coefficients d. Correlation=product_p max(0,1-|v_p(a)-v_p(b)|/(K+1)). Error≤sum abs exponents/(K+1). Exhaust finite primes,K,L. Every integer character positive/negative prime products; span character dense gives weak convergence.
Actual spectral measure step now done. Box multiplier,counting,weak convergence, even symmetrization, explicit non-Jensen transfer NOT formalized.
Candidate box APIs source checked earlier: BoundedSmoothWitnesses.boundedVectorEquivFun S K and card_isBoundedSmooth=(K+1)^cardS; primeProduct_pos/injective/factorization; BohrMultiFejerMultiplier.card_fejerFibre, fejerMultiplier; InfiniteTorusCharacter.span_torusCharacter_closure_eq_top.
No box scratch/leaf written.
Explicit bidisc μ=diagonal Haar+epsilon(graph B Poisson_a−diagonal Poisson_a), b=2a/(1+a²),B(z)=(b-z)/(1-bz),P(z,w)=(1-bz)w−(b-z). Positive representing measure with graph mass, P0=-b≠0; integral log(|P|+eta)→−∞. Weak density would transfer strict Jensen failure to actual null finite mixture. No full energy sign follows: compact torus forgets frequency height.
Do not claim scalarization Lean complete. Do not import spectral-producer theorem requiring WeilPositiveFull.

## Search and research audit
Current completed search logs:
- /tmp/wp01-spectral-measure-deep.json partial=false,68352files.
- /tmp/wp01-divisor-overlap-search.json partial=false,68364files; no usable boxcount (unrelated multiplicative/divisor hits).
- /tmp/wp01-full-sign-core.json partial=true,68366files; no full closure.
- /tmp/wp01-packet-gap-core.json and /tmp/wp01-packet-mvt.json partial=true,68367files. Inspected candidates AND source_arguments. MVT parent found, source checked.
All searches exited. Mostlypending compiler metadata, noabsenceclaim.
External primary Montgomery survey https://www.nato-us.org/analysis2000/papers/montgomery.pdf sections5-6 verifies parent Hilbert/MVT; exactcodeusesweaker104. ColeGamelin abstractavailable DOI403; noimportednewtheorem.
Prior killed novelty candidates: scalarization L248+classicalBoasKacKrein; smalltwo-window positivity coveredZhu2608.24827v2 fullsupportlength1.6.
L259/L260 signedranktwo and shiftedpoles alreadyopen. L353 primitive-support MVT positivity known; frequency split loses√R robustness vslogRgain, needsphase coherence. Read these exact sections this turn. No pointwiseabsolute-bound shortcut.
hgtl7 anti-theatre/anti-laziness answered in chat: no significant novelty orPBAPsignadvance; excessive interface work; noeffort-basedskipping; corpussearched; next actualfullenergy inequality.

Files: card docs/drafts/pipeline/1-in-progress/weil-work-01-pbap.md, own results RESULT.md,PROOF.md,EVIDENCE.md,TORUS-DENSITY.md,PACKET-ENERGY.md. RESULT/EVIDENCE/TORUS updated for fourthleaf; card records newpaperenergy successor. Mostownedfilesuntracked. No commits.
