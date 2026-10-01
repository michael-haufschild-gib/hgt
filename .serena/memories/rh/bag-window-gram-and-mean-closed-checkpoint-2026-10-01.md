# BAG current checkpoint
Only focus independent recurrence producer; unconditional RH active/open. No quantitative deterministic common-height return count, full AFE/boundary target event, or RH proof. Keep goal active. No other lane edits/agents/numerics/heartbeats/full builds/commits.

Earlier context: mem:rh/bag-independent-cutoff-gaussian-bridge-checkpoint-2026-10-01 describes F112-F129 and strategy; its runtime is OUTDATED. Working log authoritative. Card docs/drafts/pipeline/1-in-progress/bagchi-quantitative-sparse-recurrence.md, matching working log, frontier BAG row. All new repo leaves under formal/GaloisForLFunctions/RHTower, appended umbrella imports.

## Runtime at checkpoint
Sole owned Lean F130 scratch session74049:
lake --old env lean /tmp/BagSquareScaleWindowSeam.lean > /tmp/bag-square-scale-window-seam-scratch.log 2>&1
workdir formal. Includes four F129 public audits.
F129 final3386 terminal0 warning-free. Index152. Lint38838 terminal1 twelve unrelated unreachable modules, NO proof debt in that run.
All searches terminal/reviewed. No other owned Lean.
Must write_stdin terminal before successor, never infer exit from logs. Final leaf lake --old env lean Foo.lean -o matching .olean. No umbrella builds.
Card/frontier FINAL through F128; F129 pending public audit in current F130. F130-F133 drafts have no repo leaves yet.

## Newly closed since previous memory
F125 SteinhausTruncatedGaussianChannelEnergy final56782 exit0 warning-free, all5auditsF126scratch14923 standard-only, index126 lint84030 eleven unrelated. FINAL.
F126 SteinhausGaussianIndependentCutoffMean final34074 exit0 warning-free, all3auditsF127scratch73418 standard-only, index100 lint25738 ten unrelated. FINAL.
  Public3 exists_sum_norm_gaussian_direct_le gamma∈(0,1): absolute Gaussian mass<=C N^(1-gamma) for allL.
  exists_steinhausGaussianAbelSqrtCost_uniform_cutoff beta∈(0,.5):cost<=C N^(.5-beta) allL.
  eventually_integral_norm_steinhausGaussianWeight_independent_cutoff_le: first mean/N^(.5-beta)<=delta uniformlyALL L.
  First scratch emitted a ring suggestion despiteexit0; final replacedringwithring_nf and warning-free.
F127 SmoothAFEReflectedWindowConditionalEnergy final22680 exit0 warning-free, all3auditsF128scratch87432 standard-only, index81 lint50464 eleven unrelated. FINAL.
  exact conductor/row phase factor; dot-norm identity; exists_reflectedPrimalWindowConditional_energy_cell_lower:
  arbitraryH/logN actual reflected channel Gram floor on one fixed character cell, allL>=N*D, fullcommonheightwindow[5N/4,7N/4],r=1.
  Affine interpretation additionally needsL<Y² fromF124.
F128 SmoothAFEReflectedWindowFirstMean final13628 exit0 warning-free, all5auditsF129scratch57497 standard-only, index128 lint40589 eleven unrelated unreachable AND2unrelatedsorrylines WeilIntegerMassAtomicRigidity logDeriv_atomProduct149/150. NoBAGdebt; laterF129lintno proofdebt.
  GaussianWindow_phase_eq, reflectedWindowCarrier_eq;
  GaussianWindow_div_rpow_le, reflectedWindowCarrier_le uniformlyallL,tau>=N;
  reflectedWindowSmooth_le ANYretainedfiniteS,uniformallL.
  FINAL card/frontier.
F129 SmoothAFEReflectedWindowChannelUpper final3386 exit0 warning-free, auditPENDING.
  public4: exists_truncatedFullGaussianCofactor_norm_bound;
  exists_reflectedPrimalWindowChannel_upper;
  exists_eventually_reflectedPrimalWindowChannel_dot_upper;
  exists_eventually_reflectedPrimalWindowConditional_energy_upper.
  Allphases,ALLpolynomialL,freewindow(N/D,N]: eachactualcolumn O(N^-1/2),directionalenergy O(1/logN).
  Boundedcofactor usesF126 absoluteGaussianmassatintegerU andmonotonicV toboundall0<R<=U.
  copiedprivatepcountboundfromoldmodule; no weightedprime-tail variance needed.

## Pending drafts
F130 /tmp/BagSquareScaleWindowSeam.lean CURRENT.
 Planned SteinhausSquareScaleWindowSeam.lean.
 Public1 eventually_squareScale_cubicCutoff_freeWindow_seam hK B D:
 eventuallyn:0<n,n²<=n³,n²D<=n³,B<=n²/(2K),n³<(n²/(2K))².
 ElementaryNatproof, thresholds n>=1,D,2K(B+1),16K².
 hYprefix via Nat.le_div_iff_mul_le. floor n²<2K(Y+1)<=4KY.
 Square using Nat.pow_lt_pow_left hscale (by decide), nameverifiedmathlibsource.
 Multiply16K²*n³<=n⁴<16K²Y² andcancel.
 Potential final Nat.mul_lt_mul_left h16 API still compiler-unverified.

F131 /tmp/BagFullReflectedCubicTail.lean UNCOMPILED.
 Planned SmoothAFEFullReflectedCubicTail.lean.
 Def steinhausFullReflectedPrimalCarrier d tau N omega :=chi(s)*fullGaussianCofactor(s,N,omega).
 Public3 fullcarrier_eq_tsum original reflectedPrimalCoefficient;
 reflectedPrimalWindowCarrier_eq_chi_mul_truncated actualpositiveIcccarrier;
 exists_fullReflectedPrimal_cubic_tail_le hd hdhalf hq:
 ALL n>=1,tau>=n²,omega, fullcarrier(n²)-finitecarrierthroughn³ norm<=C*n^-q forANYq>0.
 Uses F113 tailA=q+d+2 andchiC/(n²)^d. Exponent becomes-q-.5 then<=-q.
 Explicit Nat-square casts atrealRcallstoavoidcoercionambiguity.
 rpow_natCast_mul verified inmathlib Real.lean515.
 No predecessor audits yet; queueF130auditafterfinal.

F132 /tmp/BagFrozenWindowLocalTarget.lean UNCOMPILED.
 Planned SteinhausFrozenWindowLocalTarget.lean.
 importsSteinhausFreePrimeWindow.
 Public3 primesLE_subset_steinhausWindowRetainedPrimes hBYhYNhNL;
 steinhausHilbertCarrier_freeze_window_eq;
 measureReal_frozenSteinhausWindowCarrier_localTarget_ge.
 Def steinhausHilbertRetainedCarrier a L S omega =WithLp ofliteralS-smoothsums.
 Exactfrozenvectoridentity andoriginalconditionalprobability
 quarterexp(-2norm(t-bg)²/(H/J)), fromactualframe/maxdot/upperconditions.
 AdaptedF101 usingwindowP=largePrimes N Y,channelcutoffL,retainedS=primesLE L minusP.
 Publicabstrconditionalhypotheses are suppliedby F127/F129 plusboundedcentre later.
 Noauditqueueyet.

F133 /tmp/BagReflectedWindowBoundedCentreEvent.lean UNCOMPILED.
 Planned SmoothAFEReflectedWindowBoundedCentreEvent.lean.
 importsF128.
 Def reflectedPrimalRetainedBackground d tau N L S omega literalS-smoothsum.
 Def reflectedPrimalWindowBoundedCentreEvent d b tau N L S :allnodebackgroundnorm<=1.
 Public5 measurableSet event; event_congr_retained; measureReal eventcompl<=summedfirstmean;
 eventually_integral_sum_norm_reflectedPrimalRetainedBackground_le uniformlyL,S,tauwithalltau+b>=N;
 eventually_reflectedPrimalWindowBoundedCentreEvent_inter_mass: anyeventofmass>=m retainshalfaftercentreselection.
 ExactX_congr_of_eqOn_primeFactors signatureverified RouteBFullSupport95; Sieve.mem_smoothUpTo secondcomponentprimefactorssubsetS.
 Noauditqueueyet.

## Assembly still needed
AfterF130-133:
RefineF127celltoanyrequestedminimumB0andmaximumdelta0 (oldF104pattern). Fixedmassrotatedcell intersectsboundedretainedcentres(F133). Retention viaF132prefixinclusionandevent_congr_retained.
UseexistingmeasureReal_prefixEvent_inter_target_ge arbitraryfiniteS(F103), F132conditionaloriginaltargetlaw, F127floor,F129maxdot/energy. Shiftedtargetnorm<=M+sqrtJ (orM+J).
Biascost≤2J(M+sqrtJ)² logN/H; chooseHlarge toobtaincN^-epsilon.
AllL>=NDandL<Y². ChooseN=n²,L=n³ viaF130.
F131tailpointwise makesfull reflectedtargetlaw withsameoriginalprobability; no subtractionofmerelyo(1) meanagainstN^-epsilon.
FullAFEcomplement/boundaryinterpolationanddeterministicquantitativegrowingprimecommonheightreturncountstillOPEN.
Cofinalsquarewindowsmustcarryfullquantitativecount;one returnperwindow insufficient.

## Searches
Deep /tmp/bag-independent-return-count-source.json session15877 terminal0 partial=false completeinventory63581files butcompilermostlypending/stale, warningscoverageoldergeneration/semanticunavailable.
Reviewedall20candidate+20sourceargumentstatements,zeroideas,oneproposedingredient(Gaussiantail+height) irrelevanttodeterministicoccupation.
DoNOTacceptretrieval_assessment model_suggests_sufficient_sources asproof.
Relevantfixed-dimCCMPrimePoleFiniteCoherence quantitativepigeonholetime(Q+1)^d. No growingprimecount.
Narrow /tmp/bag-phase-recurrence-source.json terminal0,178total25displayednames/docsreviewed. Fixed/summable-tailclocksdonotclosegate.
Read prime-logcapacitycard1031-1095: signed near-collision pressure stillopen; crudeinteger-spacinglosesmomentdepth.
Readprimorial-divisor-localREMcard124-192: bulkREMconjectural,notzeroedgesignedpressure.
Noadjacentlaneimportedaspremise,noopinionbasedontrainingliterature.
Tailsearchbroadening6hitsreviewed; F113actualcofactortailalreadyenough.
Otheroldmemoriesruntimeoutdated.
