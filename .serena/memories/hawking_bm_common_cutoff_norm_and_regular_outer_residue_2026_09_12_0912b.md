# HB common-cutoff joining — 0912b

RH goal active, unbounded, unproved. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Continuation of mem:hawking_bm_outer_pairing_residue_2026_09_12_0912a. Latest user: optimize Lean, no raised heartbeats. No computations, no axiom checks, no Git/launch.sh, no full/umbrella builds. Frontier READ ONLY; universal STATUS untouched. No agents spawned. All owned processes terminal and owned temporary files removed.

## Installed, verified modules — do not re-audit unchanged
1. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFundamentalNormJoin.lean (151 lines).
   Namespace RHTower.D4BMFundamentalNorm.
   - fundamentalNorm_join line119, general nonreal fundamental w=-3/2±Ichi, Rew>-2, T<0:
     incomingNormFinitePart chi (horizonCoordinate T) w + integral_(Ioo T0) normalizable(w,chi,z(t))² = normFinitePart w.
   - physicalFundamentalNorm_join line139: actual q:XiZeroCopy, side:Bool,T<0; no supplied kernel, normalization, residue or interchange premise.
   - Private proof helpers derive incoming first Gauss coefficient=-1/2, incomingPairingFactor=sqrt(1-z)/2 on Icc01 (endpoint1 division totalizes to zero correctly), kernel quadratic remainder=(z/2)*(HalfOrderBeta.core z-core0), bound z²/4.
   - Quad finitePart at upper1 equals (1/2)*HalfOrderBeta.finitePart=existing normFinitePart, by integral congruence/cpow_mul_base.
   - QuadraticEndpointMellin.cutoff_eq cancels common cutoff; original mode_square_integral supplies coordinate change, integral_Ioc_eq_integral_Ioo supplies endpoint equivalence.
   - Scratch warning-free. Exact leaf lake build audit 28 seconds, two jobs, 4415 cached project imports. Source + five artifacts (olean,olean.hash,ilean,ilean.hash,trace) installed and RHTower umbrella wired.

2. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMRegularOuterPairing.lean (136 lines).
   RHTower.D4BMLaplaceRadial.normalizable_horizonRegularCoefficient_analyticAt line16:
   Actual Aplus(u)=horizonRegularCoefficient u chi (normalizable u chi) (normalizableFirst u chi) is analytic at nonreal w.
   Proof uses actual radialBracket at1/2, horizon/first jets at -w composed with negation, normalizable/first entire jets, divides only by -w.
   Lean API notes: AnalyticAt.comp has implicit point; use .comp analyticAt_id.neg (NOT .comp w ...). AnalyticAt.const_mul does not exist here: use explicitly typed analyticAt_const.mul. using! resolves inherited complex module-instance diamonds, no resource increases.

   RHTower.D4BMJointSource:
   - exists_matching_horizon_cutoff line44: each b∈Ioo01 admits T<0 with horizonCoordinate T=b. Uses continuity, actual limit atBot=0, coordinate0=1, intermediate_value_Icc. No inverse formula/normalization assumed.
   - regularOuterPairing chi s a T w line61:
     Aplus(w)*incomingPairingFinitePart s chi a 1 (reducedGreenGradient chi s 1) (z(T)) w + continuedReducedOuterPairing chi s a T w.
   - regularOuterPairingCutoff line67: actual positive-cutoff incoming integral response*horizon/(2z sqrt(1-z)), two derived counterterms, all multiplied by Aplus(w), plus original outer integral.
   - physicalRegularOuterPairing_residue_and_restoration line79:
     q,branch,side,a → ∃T,R, T<0,R>0,
       limit_(u→w0,punctured) (u-w0)*regularOuterPairing(...,T,u)
       = physicalIncomingPoleAmplitude(q,branch,side,a)*normFinitePart(w0),
       and for u in ballw0R with connection≠0, actual cutoff expression tends to regularOuterPairing as e→0+.
     Uses existing incoming restoration/residue, actual Aplus(w0)=1, existing original outer residue, new norm join. Cutoff and frequencyball constructed, no extra premise.
     physicalIncomingPoleAmplitude_eq_cleared retains sourceMoment*clearedOnset/original physicalFundamentalDenominatorSlope.
   - Scratch warning-free. Exact leaf audit 37 seconds, two jobs,4419 cached project imports. Source,five artifacts,umbrella import installed.
   - This is regular horizon branch + FULL OUTER reduced response including outer gradient lift; NOT full restored normalizable/current pairing. Inner explicit lift and opposite horizon branch still missing at same cutoff.

## Next hard mathematical attack
Assemble opposite horizon contribution at SAME cutoff with regular branch; then admit inner explicit lift; then all four source channels, both Einstein contacts. Do not simply take min of cutoffs supplied by separate existence theorems without proving restoration/analyticity holds at smaller cutoff.

Efficient candidate next:
- Generalize incomingPairingFinitePart_horizon_restoration and oppositePairingFinitePart_horizon_restoration to produce R,B and properties for every 0<b≤B. Their private common_data already supplies uniform bounds on Ioc0B and source continuity on Icc0B; restrict bounds to b. Keep old signatures as corollaries. Final audits only modified exact leaves, cached imports; never umbrella builds.
- Then min B_in B_op yields genuine common cutoff; incoming residue derivation uses physicalIncomingQuotient_residue valid every interior b plus analytic N,J,P. Opposite regularity derivation uses analytic L,K,P and actual pole numerator. Aplus analyticity is now available from new module.
- Actual normalizable decomposition = Aplus*horizon + connection/(2w)*horizon(-w). Opposite block has zero physical residue but still needs original integral admission at SAME b.
- Existing incoming/OppositePairingFinitePart files, PhysicalIncomingPairingResidue, PhysicalOppositePairingRegularity read in full this turn; key proofs/signatures in prior mem0912a and installed code.
- Source/onset nonvanishing, retained unprojected pairing/multiplicity/Peierls survival, Hawking extinction and RH remain open.

## Searches and related files
Broad gluing deep, cutoff EndpointMellin, natural-language cutoff mechanism, tortoiseOf hybrid, Wronskian-frequency method deep. Candidates/source_arguments/proof_ideas/ingredient_sets inspected. Exact Quad cutoff_eq useful; generic lattice join suggestions not applicable. Wronskian search retrieved actual jet analytic lemmas; partial request, about57010 inventoriedfiles, compiler44564pending, stale snapshots and semantic coverage unavailable.
Source found inverse tortoiseOf/horizonCoordinate_tortoiseOf in ThetaCuspHawkingBMSelfChannelHorizonJet (first65lines read). That OTHER agent leaf had no cached olean and remains untouched. New norm join instead uses IVT for cutoff existence. HorizonCoordinateJets cached but lint reports unwired. Do not build/change other agents' work blindly.
Broad arxiv transmission/factorization searches, opened July2026 arxiv2607.03475 Landweber unique factorization paper. Its algebraic finite-jet result not used here. No numerical experiment.

## Docs, lint, cleanup
Updated docs/drafts/pipeline/{1-in-progress,3-formalized}/hb-physical-mode-action-contact.md with completed common norm/regular branch, exact audits, true remaining gap. Frontier and universalSTATUS untouched.
Lint ran once, exited1 with outside-edit unreachable modules, including DeningerOriginalGreenGaussianEnvelope, DeningerOriginalGreenXiResolventBound, ThetaCuspHawkingBMHorizonCoordinateJets, PrincipalChannelHorizonJet, SelfChannelHorizonJet, HTGeometry.ElementaryHorizonJets, SecondEndpointMellinLaurentInterchange, UniformSecondOrderJet. Output to stderr was truncated; list not exhaustive. New modules directly wired. Global lint NOT claimed passed. Do not rerun unchanged/fix unrelated work.
No owned Lean/Lake running (exact process filter empty). All handles finished, including searches, audit49349, lint83640, cleanup79283.
Removed10 explicit owned temporaryitems, including /tmp/hb-audit-0912b and helper /tmp/hb-audit-prepare-0912b.py. No scratch/log/search JSON from this phase remains. Never resume old handles.

## Cache-only audit setup for later
Audit isolated /tmp package. Copy lean-toolchain; read real lake-manifest package names. Source-less stubs for dependencies, each lean_lib from top-level existing cached olean namespaces; symlink real dependency lean caches. Path manifest entries/no Git/no fetch/update. Audit root one exact target root. Recursively stage existing GaloisForLFunctions imports by source roots and cached ilean.directImports; hardlink five artifacts, no dependency sources. Unlink target artifacts before compiling (avoid mutating hardlinked real cache). Copy ONLY target source. Run lake build EXACT module. Verify source equals checked scratch and 2-job warning-free completion; install source and five artifacts, wire umbrella without build; remove audit source. Prior helper removed; recreate if needed.