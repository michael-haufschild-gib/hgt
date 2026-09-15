DI turn (started September 14, ended September 15 2026): full temporal/metric/QNM matching and impossibility remain OPEN. RH goal ACTIVE, not complete or blocked. Do not reread experiments/results.md. Frontier read-only. No computations/Git/launch.sh/axiom printing/heartbeat or transparency hacks. Every new turn state full chain and hard gap: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Current mathematical target only full matching or impossibility. No subagents authorized.

FIVE NEW LEAVES COMPLETED, canonical sources/artifacts installed in formal and wired into formal/GaloisForLFunctions/RHTower.lean. Each passed scratch and isolated exact leaf audit; formal_tools.py lint PASSED globally (large-file warnings only). Do not recheck/rebuild these without new changes. All owned Lean/search/lint handles terminal. Temporary /tmp/hb-di-* (31 paths) scheduled for immediate cleanup after this memory; audit namespace cache symlinks point root cache so shutil.rmtree must not follow them. No required missing olean repairs this turn.

1. ThetaCuspHawkingBMOriginalSourceRadialAdmission.lean (audit 62s), namespace RHTower.D4BMOriginalSourceRadialAdmission:
period_time_integrable actual E compact time; horizon_period_bound any N actual EH ≤ C exp(-Nk-p); horizon_period_time_integrable actual EH compact time by actual E limit; endpoint_radial_error_integrable every p>0 (no exceptional p set), using continuous actual tail density + finite modular measure + exp(-L-p) product domination; endpoint_radial_integrable separately E on compact deep collars; moment_radial_integrable actual int E via F264 product admission and separately admitted EH.
2. ThetaCuspHawkingBMOriginalSourceRadialRestoration.lean (audit 70s), namespace D4BMOriginalSourceRadialRestoration:
sourceFunctional S = mu(mu-2)(E_b-E_a+2w int_a^b E).
horizonSourceFunctional HS same functional applied to EH.
sourceError same functional applied to E-EH.
source_radial_integrable, source_difference, source_error_bound N (C exp(-L-Nk), all0<a<=b), source_error_collar_bound N (all sufficiently deep lower interfaces A<=B), source_radial_joint_limit (actual int S - length HS divided by 2, arbitrary external positive temporal interval nets and upper radial cutoff nets).
Public exponential_interval_bound: if norm f(p)<=C exp(-p) on Icc a b, integral norm<=C exp(-a).
3. ThetaCuspHawkingBMOriginalFullMetricCollar.lean (audit39s), namespace D4BMOriginalFullMetricCollar:
metricDifference D = f*(actual metricTimeCut - restoredMetricTime), f=R_L^2-1; metricTrace H=HS+horizonBoundary; forcingMoment F=mu*w int_a^b forcingPeriodError; metricError = D-F-H.
metric_error_decomposition: actual metricError=sourceError+boundaryError, derived chamber.
metric_error_bound N: uniform all positive time intervals, C exp(-L-Nk).
metric_source_boundary_integrable actual D-F separately radially admitted.
metric_source_boundary_joint_limit line116: one L0, EVERY A>=L0, ANY filter l and K→atTop, arbitrary positive T_i=(a_i,b_i), arbitrary M_i>=A, [(int_A^M (D-F))-(M-A)H]/2→0. This stronger filter version helps composing the actual horizon coordinate.
4. ThetaCuspHawkingBMOriginalFullCollarRestoration.lean (audit123s), namespace D4BMOriginalFullCollarRestoration:
forcing_moment_radial_integrable, full_metric_radial_integrable actual F,D separately, forcing_moment_collar exact original /2 Jacobian sends int_A^L F to mu*w*I(a,b)*int_{-L/2}^{-A/2}(kernelCut-C kernel).
forcingCountertermDifference retains original finite-height weights firstWeight-C and secondWeight times SAME canonical coefficient families at horizonCoordinate(-L/2), multiplied by actual onset integral and mu*w.
fullCollarDifference = [int_A^L D-(L-A)H]/2 - forcingCountertermDifference.
full_metric_collar_joint_restoration line162: derived half-plane, one common A>0, fullCollarDifference→0 as L,k→infinity independently, uniformly over arbitrary external positive temporal interval nets.
This is complete RECTANGULAR INGOING-TIME COLLAR comparison, not static triangle, not log-source/boundary contact identification, not outer assembly, not full matching.
5. ThetaCuspHawkingBMOriginalSourceJointContinuity.lean (audit107s), namespace D4BMOriginalSourceJointContinuity:
period_joint_continuous line23: actual E(p,L,k) jointly continuous on Ici L0 × Ioi0. Derived from actual angular admission, joint tail density continuity, and uniform C+B bound combining actual horizon density/error N0.
moving_endpoint_integrable: every continuous positive temporal endpoint p(L) on compact deep collar is admitted.
static_source_radial_integrable line98: actual complete sourceFunctional at a>0, b(L)=max a (T-L/2) is radially integrable on any compact deep collar. Clamping gives empty interval beyond physical static-time triangle. Uses current mathlib intervalIntegral.continuous_parametric_intervalIntegral_of_continuous, clamping only parameter extension for proof; original integrand retained in result. Static SOURCE admission is now CLOSED; don't keep treating fixed slices as adequate for this graph, or re-prove this.

OWN DOCS:
docs/drafts/pipeline/1-in-progress/hb-own-research-facts.md updated F273–F277.
F273 source admission/restoration; F274 full source+boundary; F275 full rectangular metric+forcing; F276 static source admission. All audited/wired.
F277 is ANALYTICAL consequence with COMBINED LEAN THEOREM PENDING, see next attack below. Do not falsely label F277 Lean-proved.
Own card docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md has new CURRENT complete-collar section near top with exact remaining matching gap and F277 derivation. Do not edit frontier or STATUS (no new route-independent fact).

NEXT HARD ATTACK: close actual logarithmic/source-boundary horizon contact, not arbitrary length subtraction.
Paper proof of F277:
For H=HS+horizonBoundary, derive for each N a common chamber with norm H(a,b,k)<=C_N exp(-Nk) uniformly all0<a<=b.
Source HS: already public horizon_period_bound in new SourceRadialAdmission, then same endpoint/moment inequality as SourceRadialRestoration.source_error_bound.
Boundary:
- OriginalReaderCuspBounds.horizonJet = baseOperator j(actionRemainder(center q)(physicalRate q br)amp p 0).
- Existing original_action_base_jet_horizon_estimate at height parameter 0 gives norm horizonJet <= C exp(Gp-(N+3)k).
- OriginalAngularProductBounds.angularJet_bound gives reader <= A exp k. Gain3 absorbs reader growth + Laplacian exp2k.
- OriginalPrincipalReaderBounds.original_principal_coefficient_horizon_estimate: existsB>=0, eventuallyL, allp>0, norm horizonCoefficient_i(p)<=B exp2p AND approximation bound. Pick one L from eventually to extract first bound (i=Fin3).
- OriginalPrincipalReaderBounds.principal_tail_bound (namespace OriginalAngularReaderBounds): for EVERY complex exponent a, everyN, norm(exp(a*k)*tailJet q d [x,expk])<=C exp(-Nk). Use a=principalExponent_i and fixed jetMultiplier.
- Actual horizonAngularProduct (namespace OriginalAngularProducts, defined in OriginalAngularProductBounds lines213): beta*((horizonJet+horizonPrincipalJet)*angularJet - horizonPrincipalJet*angularPrincipal). Decompose into horizonJet*angularJet plus finite sum of horizonCoefficient_i*jetMultiplier_i*exp(K_i k)*readerTail. Rew>=max(G,2)+1 leaves exp(-p).
- horizonProduct forcing (OriginalForcingProductBounds) exactly beta*timeOnset(2s,p)*(radialCoefficient false 1*fixedProduct false d + radialCoefficient true 1*fixedProduct true d). The algebraic decomposition is currently PRIVATE in that module line173; don't rely on private names. Can derive from displayed definitions or expose a suitable unchanged producer with a focused audit. Its proof uses private profile_product_decomposition line151, forcing_profile_linear line127 and principal_profile_linear line132. All algebra, no new estimate.
- Fixed products have arbitrary cusp decay, and damped onset bound is derived for Rew>=1 from timeOnset_pair_bound and currentRate_re_lt. damped_onset_bound currently private in OriginalForcingProductBounds line99, proof only ~25lines.
- horizonTransfer Fin4 (OriginalBoundaryCollarBounds lines12) = exp(-wp)*[hprod0,true; exp(-k)hprod1,false; exp(2k)hprod2,true+hprod3,true-hprod1,true; horizonProduct,true].
- This gives every horizonTransfer norm<=C exp(-Nk-p); horizontal period length1 preserves bound. Apply actual full horizonBoundary endpoint/moment functional (OriginalBoundaryRestoration line71), using public exponential_interval_bound from new SourceRadialRestoration. Norm constant is 2||lambda||C+||w||(||mu||+2+2||lambda||)C. All leading traces already have separate compact admission F262; source trace admission new modules.
Exact coordinate identity from horizonCoordinate_factor and log rules:
(L-A)/2+log(horizonCoordinate(-L/2))/2 = log(1+radialUnit(-L/2))-A/2.
For L>0, 0<u_L<1, RHS uniformly bounded (A/2+log2 if A>0). Thus changing new fullCollarDifference to [int D]/2+(H/2)*log(e_L)-forcingCountertermDifference adds only bounded scalar*H, jointly→0 by cusp decay. No need H=0, no free finite constant, log2 retained. This should give actual rectangular logarithmic metric matching in Lean. The existing OriginalAngularProductWeightedLimits only bounds SUBTRACTED errors, not absolute H; don't mistake it for the needed H bound.
Afterward static boundary/forcing graphs and corner transition, outer independent cusp/time restoration, and attachment to canonical QNM action still required. Canonical action itself already meromorphic with removable QNM (DG F268–269); finite value not proved0. Do not redo that.

SEARCH THIS TURN:
Deep query slice admission (partialfalse, coverage~58052 index1failed, manycompilerpending) and broad OR slicing/disintegration found actual boundary joint continuity + slice admission; disintegration generic a.e. recovery does not provide every physical endpoint, hence actual density domination proof.
Deep leading horizon metric/source/boundary trace cancellation Green identity: partialTRUE, reranking deadline and BrokenPipe; inspected all candidates/source_arguments/methods. No direct actual H cancellation theorem; source-specific existing horizon traces/temporal corner relevant, generic Euler/Deninger abstract trace=0 not applicability.
Broad OR parametric primitive: partialfalse, ~58064files1failed, sourcecompilerpending; read candidate_lemmas and source_arguments/methods. Found exact mathlib continuous_parametric_intervalIntegral_of_continuous (DominatedConvergence.lean598), continuous_parametric_primitive_of_continuous493. Applied in new static_source proof. Current continuousOn_of_dominated Bochner/Basic.lean435 used for actual source joint continuity. No search implementation/help read.
Broad own arxiv searches disintegration/corners requesting2026 returned older papers; sorted arxiv URL cachemiss. Read primary arxiv2202.04511 (2022, revised2024, published2025). Not a2026 result, no mathematical dependency. No experiments reviewed or run.

LEAN LESSONS (avoid repeated mistakes):
No heartbeat increases. Large implicit ContinuousOn.comp on unfolded physical period timed out; fixed by small generic private continuous_clamped with f a free variable and explicit MapsTo target, then instantiate source. In MapsTo goal use change to expose pair membership and real inequalities; otherwise inferred projections caused stuck elaboration.
Write spaces in 'A ≤ max ...': 'A≤max' tokenizes as Matroid ≤m plus ax.
ContinuousOn.congr expects new=old; IntervalIntegrable.congr expects old=new.
IntervalIntegrable.congr membership is uIoc, integral_congr is uIcc.
Use explicit typed IntervalIntegrable(... )volume to avoid stuck IsLocallyFiniteMeasure metavariables.
Use tendsto_snd.eventually or hK.eventually; no .comp_tendsto on Eventually.
Avoid unqualified rw[intervalIntegral.integral_symm], which can flip unrelated time integral; instantiate a named radial equality.
No need mathlib axiom checks.

Isolated audit setup for future: minimal /tmp task audit lakefile with one lean_lib roots=[exactmodule], copied lean-toolchain. Cache top entries symlink root .lake/build/lib/lean + installed package cache top entries. Stage ONLY target source (canonical and audit). Remove previous staged source only AFTER its audit finishes. LEAN_NUM_THREADS=2 lake env lean /tmp/scratch.lean from formal; final LEAN_NUM_THREADS=2 lake build Exact.Module from isolated audit. No umbrella build. New imports wired. Cleanup only owned prefix, preserve root cache.
