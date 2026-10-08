# WP02 cycle33: arithmetic producer complete, critical kernel pending
Goal ACTIVE/unlimited. User requires hgtl7 EVERY TURN, corpus-first conjecture/paper/Lean loop, no numerical experiments, no heartbeat raising, one own foreground Lean process, final lake --old env lean leaf audits, no full/umbrella builds, no commit/push. No subagents. Ownership own WeilWorkExposingRay*.lean and WP02 resultdir/card; other existing Lean read-only. Umbrella wiring authorized.

Mission: advance unconditional WP02 universal exposing-ray inequality and compiled RH receiver. Original target docs/reports/weil-work/02-exposing-ray.md remains OPEN. No goal completion.

## New verified result
For every actual critical logarithmic polar separator (weight1+log(2+|t|)), actual signed Dirichlet series B(z)=sum_{n>=2}b_n n^(-1/2-z) converges absolutely on Re z>0. There exists one M>=0 so sigma*Re B(sigma+i*t)<=M for ALL real t on ONE positive radial neighborhood. Thus for each epsilon>0, sigma^2*Re B(sigma+i*t)<=epsilon eventually uniformly in t.
Derived from actual finite complex Toeplitz budget, positive-integer harmonic characters, actual sqrt(N)log(N) absolute mass, signed pair Fubini/Abel, and mathlib zeta residue. No signs, Laurent expansion, residue, full-positive completion or RH assumed. Separator positivity is intermediate domain, not a final WP02 premise.

Four new saved/wired leaves in formal/GaloisForLFunctions/RHTower:
36 WeilWorkExposingRayCriticalTwists.lean (~165 lines), imports own LogLocalMass.
- signedHarmonicDensity, criticalLogTwist definitions.
- criticalLogTwist_mul, norm_criticalLogTwist, re_criticalLogTwist.
- log_twisted_harmonic_bound for0<=beta<=1, positive integer character proof.
- critical_harmonic_cosine_ceiling atbeta1, uniform allreal t, C(1+logN)^2.
37 WeilWorkExposingRayCriticalSeries.lean (~134 lines), imports own LogLocalMass.
- summable_critical_separator_coefficients for every exponent>1/2.
- private dyadic proof from actual local absolute mass.
38 WeilWorkExposingRayCriticalAbel.lean (~210 lines), imports36/37 and SMALL generic WeilWorkPBAPCriticalAbel.
- criticalCosineCoeff b t n=bn sqrt(n) cos(tlogn).
- criticalCosineSeries b s t=sum if2<=n coeff*n^(-1-s).
- criticalHarmonicFactor s=sum_nat m^(-1-s).
- summable_critical_cosine_terms.
- critical_cosine_dirichlet_product_ceiling: exists K>=0, all s>0,t, s²*(series*harmonicfactor)<=K*(2+s²).
- pair transform and cumulative identity private; absolute summability paid from37.
39 WeilWorkExposingRayCriticalBoundary.lean (~78 lines), imports38+Mathlib.NumberTheory.LSeries.RiemannZeta.
- private criticalHarmonicFactor_residue via tendsto_sub_mul_tsum_nat_rpow.
- critical_uniform_dirichlet_ceiling.
- critical_uniform_quadratic_upper.
Promoted previously private log_toeplitz_of_polar_bound in owned30 LogLocalMass, proof unchanged, audited.

All four final saved-leaf foreground lake --old env lean -o <own-cache> <leaf> checks exit0/no diagnostics. Combined audit of all11 public theorems (5+1+2+2 plus promoted30) exit0; every axiom list exactly propext,Classical.choice,Quot.sound. All39 owned leaves imported exactly once. Scoped git diff --check clean. Latest global lint exit1 on7 unrelated unreachable modules:
RHTower.WeilPaperCovarianceEnergyCertificates
RHTower.WeilWorkQuantizationGaussianFiniteEstimates
HTGeometry.ApertureConeCalculus
HTGeometry.ApertureConeWinding
HTGeometry.ApertureLogTranslation
HTGeometry.ApertureOpenHistoryIdeal
HTGeometry.BoundaryCoronaCStarAlgebra.
No owned WP02 finding. All Lean/search/lint sessions terminal. EXACT13 scratch/search/audit/lint temp files cleaned. No unfinished Lean leaf.

## Important existing-parent applicability trap
WeilWorkPBAPCriticalCoefficients.critical_twisted_density_bound requires multiplicativity for all naturals INCLUDING0 and unit norm at0. chi0=chi0*chin forces chin=1. Not a false theorem, but cannot instantiate nontrivial n^(-it). Parent untouched; owned36 uses multiplicativity only on positive integers. Do not say parent fixed.

## Current conjecture/paper
Saved complete dependency-closed paper argument:
docs/reports/weil-work/results/02-exposing-ray/CRITICAL-ONE-POLE-PROOF.md (~410 lines).
Status SURVIVES PRELIMINARY ATTACK; critical endpoint NOT Lean-verified, novelty unestablished.
Exact conjecture: atbeta1 every finite positive mixture of compactcomplexC2 one-pole sources has arbitrary weightedL1 recovery by both-pole mixtures with EXACT rawtrace everyinteger>=2 inclzero tail. Rows may choose poles separately. Does not cover full sources/Fejer; does not give WP02energyfloor.

Paper:
P=D²-1/4. Actual evenreal kernel k_g=ell(w|FTg|²cosxt) minus shifted arithmetic correlations.
k_Pg is continuous PD from polar finite packets.
OrdinaryBochner gives positive finite nu for k_Pg. h_g=integral cos(tx)/(t²+1/4)²dnu boundedPD,C4.
P_x² k_g=k_Pg, so k_g=h_g+c_g cosh(x/2)+d_g x sinh(x/2).
Actual B(z) above; sourceLaplace Lk_g=LS_g-J_g(.5+z)B(z)+E_g(z), E entire finitehead, J entire compactcorrelation.
ODE decomposition yields double/simple poles. A fixed positive bump has J(.5)>0, deriving B=D/z²+F/z+analytic, Dreal.
New uniform arithmetic theorem at t=0 givesD<=0, at t=2sigma gives-3D/25<=0; henceD=0. Everyg sameLaplace identity givesd_g0 evenifJg(.5)=0.
PDh implies k_g(x)<=k_g0 cosh(x/2).
Common-support smoothing transfers to allC2. Existing cycle32 one-pole primitive/difference quotients already beta<=1, only finalcoshmajcall strictbeta. Replace it, finish exactwholeintegerfibreHBargument.

The original finite damped Gibbs proof in paper also valid, but preferred formal route uses paid genericAbel (now36–39). Do not duplicate weighted truncation theory.

## Next formal work
DO NOT redo arithmetic. Need actual kernel producer:
1. finite real-packet identity of logSeparatorKernel, stability of polar zeros under translates/real sums, real symmetric form to complexPD, weighted continuity.
2. C4 profile sufficient: PgC2, exact multiplier rhoPg=(t²+.25)²rho_g controls weightedmomentsj<=4. Prove P_x²k_g=k_Pg. No need arbitrary smooth Fourierdecay.
3. ordinary Bochner + order4 jet uniqueness for decomposition.
4. actual sourceLaplace identity, nonzero fixedprofile, realLaurent coefficients, then apply arithmeticuniformbound to removeD.
5. C2 smoothing, upgrade own34/35 endpoints (their limitmajorantsalreadybeta<=1); unconditional endpoint capstone audit.

Verified source locations:
- own WeilWorkExposingRayLogKernel.lean: atomicForm_packet PRIVATE at69; logCosDensityL1 at157, logSeparatorKernel at208, zero/neg identities public. May promote owned atomicForm_packet for reuse with final audit. No such promotion yet.
- RHTower.paperFT_finset_sum in ZetaWeilFiniteLevelInertia.lean484 (namespace RHTower).
- actual filename WeilFullConeBochnerMeasure.lean (NO Work), namespace RHTower.WeilSpectral. Defines transl,paperFT_transl,finitepacketcorrelation. Its positiveDefinite_spectralKernel requires WeilPositiveFull; NEVER use as freeproducer.
- HTGeometry/PrimeDirichletPositiveDefinite.lean13 defines PositiveDefiniteOnReal via allfinite complexforms.
- HTGeometry/BochnerPositiveDefiniteReal.lean881 exists_charFun_eq_of_positiveDefinite; onlyPD+continuity, returns finitepositive measure. norm_le etc.
- HTGeometry/ODEJetSeparation.lean88 GaloisForLFunctions.eq_of_jetVec_eq_at ordern companion LipschitzODE +initialjet ->eq, use explicit4.
- own34 OnePoleTransfer integrability+primitivequotientlimits beta<=1; finaltheorems strictbeta.

New stronger conjecture separately audited preliminary: every actualcriticalpolar separator admits UNIQUE scalar F so Q+F*testPole nonnegative on ALL fullC2 sources; F=actualsimpleDirichletresidue. Paperformulas c_g=-2F J_g(.5), testPole=2J; uniqueness from boundedfullPDkernel vsnonzero cosh onpositivebump. NOT Leanverified/notnoveltyestablished. Does not forceF0/fullsourcecriticaldensity.

## Search and source audit
6 direct corpussearches thiscycle: deep120s1complete,2/3/4partial retrieval/reranking deadlines;5lexical all20 hits;6deep120partial semanticdeadline.6 indexed68891, backgroundrefreshincomplete, compilermostlypending/stale. Inspected all20candidate+20source+ingredients perdeepsearch. Noabsenceclaim. Ownindexedresultsnotindependentnovelty.
Externalprimary: Thorn2018 arXiv1801.09478 thm2.2positivecoeffandremark2.3signed; NikolskiPushnitski2020 arXiv2001.01474 boundedrealsymbol/Folner; GuoLiZhou2023 arXiv2305.07860 boundedLinf/positiveL1; ChungKim2005 EMS40904 homogeneousP notourP; JablonskiJungStochel arXiv2008.09494 semigroupHankel notdifferencekernel; Suzuki2023 JLMS12785 primitiveatrealfrequency0 foractualWeil; Zhu2026 arXiv2608.24827v2 fixed-windowcertificate notallapertureexactfibres. No imported unpaid endpoint.

Docs RESULT/PROOF/EVIDENCE/card updated with precise verified arithmetic and pendingkernel. Currentcard docs/drafts/pipeline/1-in-progress/weil-work-02-exposing-ray.md.
Prior verified frontier: cycle32 one-pole beta<1 exactfibre recovery; cycle31 fullsource beta<.5. Fejer hasneitherpole, remainsbeta<.5.

Tooling traps: use formal cwd. Never #print theoremproof (huge); #printaxiomsonly/tmp. Polymorphic have:=@Name needs explicituniverse-types (e.g @tendsto_nhdsWithin_iff ℝ ℝ) or failsunuseduniverse. |x|* or |x|/ tokenrequires spaces. sqrt natcast multiplication needs rw Nat.cast_mul,Nat.cast_ofNat, notchange. One accidental earlyoverlapwrongcwdnamescheck documented inEVIDENCE; allsubsequent strictlysequential. New processnone. No update_plan tool available, cardplantracks. SerenaLean symbolindexunsupported, fallback documented. 
