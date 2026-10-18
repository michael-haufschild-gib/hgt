PAUSED at explicit user request on 2026-10-18. User cleared the active goal, then instructed: finish started Lean work, wire, update docs, then pause. Do not restart research without a new user instruction. Historical research objective: read /Users/michael/.codex/attachments/443ad7c2-bdf2-4684-af7c-2b642bc16ebd/pasted-text-1.txt before automatic continuation. Build BVI Wall1 programme problem3: internal signed bilinear dispersion on literal energy-centered pronic Ramanujan Gram. User correction: use corpus research search; previously missed existing work. No hgtl7, no RH topic work, no numerical experiments, README readonly, no commits, no full/umbrella builds, no heartbeat hacks. One owned foreground Lean process at a time. Final source audit lake --old env lean -j 1 <module>. Public theorems data parameters only, no analytic premises. Read before edits, preserve foreign changes/processes. No subagents.

Persistent card: docs/drafts/pipeline/1-in-progress/bvi-internal-bilinear-dispersion-2026-10-18.md (>890 lines; rg headings before bounded reads). Mission: finite-horizon divisor analysis preserving jumps and non-periodic energy. No docs/architecture.md or docs/testing.md at init. update_plan unavailable. Serena cannot access ignored Lean source; standard patches fallback. No active goal remains. Work paused; full signed tail/dispersion unresolved. No owned processes running as of this checkpoint.

Completed owned BVI leaves (all original sources checked with actual lake --old env lean -j 1, wired, every public API/axiom audit exited0 using only propext/Classical.choice/Quot.sound):
- PrimePacketConditionalTailAndCoherentPrefix.lean:319 lines,24 public,SHA4a1a2b57f61fedf1b2c632acfb503152b7baa563a629d11748e9f588d2368f33. Exact full/head/conditional-tail split and coherent mean/log obstruction.
- PronicResidueGapEnergyAndPrimePairDistance.lean:399 lines,13 public,SHA9dac453a5c826dec6b26e177767de69062899659acffed88855de1355fe73a6b. Pair distance E(p,p+h) ~ h H_floor(p/h)+O(h); exact prefix correction -(h²/p)K²/(K+1). Pairwise only.
- C9 RamanujanDilationProfileResidueGapBudget.lean:257 lines,6 public,SHAcc33a090269d6063e25e5edf197cfc362cbd0e26eb11e1452a7c33e522f78262. Xp(n)=p Re A_(r+2)(floor(n/p))=-sum_(x in divisorsAntidiagonal) mu(x.2)*(n mod p*x.1). Cr=cardS sum mu²*x.1. Exact HasSum and pairwise profile distance<=Cr residue budget; preserve radial mismatch. NOT collective dispersion.
- C10 OrderedPronicGapCellsAndCollectivePrefixEnergy.lean:871 lines,7 public,SHA4f1138da8f4df6349692aacb38070060f73e4269ac003d7b91a27dc6242a43d4. W=rho_p-rho_(p+h)+h on[kp,(k+1)p), kh<=p, mean0, varianceh/k-h²/p, prefixmeans<=0. Ordered disjoint modulus gaps have nonpositive covariance at SAME level/all horizons. Signed cost2; same-parity levels disjoint =>cost4. Chain p_i=K H+offset+1+sum_(j<i)h_j, H=sumh, P=p0>K H. Literal residuepacket prefix n<(K+1)P <=8 harmonic budget+2H/P sum ai²hi. Later tail open.
- C11 RamanujanOrderedGapCollectivePrefixEnergy.lean:322lines,5public,SHA3b073a61ccfa30597681a1db67795b6b1f7aa27c23338f039e2d0c82a1497c80. COMPLETE, corrected noncomputable API wrapper terminal0. Public: pronicResidueGapChain_scaled_prefix_energy_le; ramanujanGapChainPacket; hasSum_ramanujanGapChainPacket_zero; ramanujanGapChainPacket_prefix_energy_le; ramanujanGapChainPacket_bilinear_prefix_sq_le. d-scales chain/cofactor, restrict enlarged cofactorprefix to same physicalT. Finite COFACTOR Cauchy (not primegapCauchy) gives Eprefix sum ai(Xpi-Xqi)<=Cr(8 harmonicK+2H/P)sum ai²hi. Existing pm_tsum_floor_dilation gives each Xp mean-Lambda(r+2), hence differencepacket mean0. Bilinear squared bound product budgets.
- C12 AllLevelPronicResidueGapCentering.lean:433lines,6public,SHA9b2c311bb436accfa90bf1ee993eb36cba443d0331f67547039bb8216578a514. COMPLETE. Public residueGapCellPronicMean, _bounds, _eq; residueGapCellPronicMoments; residueGapCellPronicMean_collective_energy_le; residueGapPacket_energy_le_centered_add_mean_budget. ALL levels: q=p+h,j=floor(kp/q),s=(j+1)q. If s<end=(k+1)p, conditionalpronicmean=-(k-j)(s-kp)/(j+1), variance=(s-kp)(end-s)/((j+1)²p); elsemean=jq-kp,variance0. Always mean in[-h,0]. Arbitrary family pi=P+offseti, meanpacketE<=H/P sum ai²hi at everyhorizon. RawpacketE<=2centeredpacketE+2H/P sum ai²hi. Remaining mixedcell collectiveframe bound open.
- C13 SharedBirthPronicCellCovariance.lean:565lines,8public,SHA90d95301184764fda8da224141956a5b16b946b5b617c922a58ae36a97731805. COMPLETE. Public residueGapCellPronicTail_eq; residueGapProductBirth_centered_covariance_eq_zero; sharedBirthUnitGapCovariance; _eq; _nonneg; _one; _pos_iff; _coherent. Generalcelltail atT in[a=kp,b=(k+1)p]: ifs<b, tail=(b-s)(T-a)/((j+1)pT) forT<=s, else(s-a)(b-T)/((j+1)pT), and0 ifs>=b. Sharedbirth unitgaps: g,l:PNat,k=l+offset,p=g*l,r=g*k,a=kp=lr. Cov>=0, exact piecewise: ifs<b then (b-s)/((j+1)p) whena+l<=s, else(s-a)(g-1)/((j+1)p); else0. Cov>0 iff g>1 ANDs<b. Productbirthg1 covariance0. Coherentfamily k=l+offset+1,g=k+padding+1 yields distinctgaps and positivecov=1/k-1/p. Disproves extension of C10 nonpositive SAMElevel statement to mixedlevels. General minimum-kernel FAMILY corollary is paper-only, notformalized; genericGreenkernel algebra notclaimednovel. g onlyactualgcd whenreducedk,l coprime. No generalprime dispersion claim.

Durable artifacts and cleanup:
logs/bvi-dispersion-history-2026-10-18.tar.gz +manifest archives66ownedC1-C8tmp. C7 transport scratch was unpromoted baseline with Finset.product prooferror; notmissingarithmetictool.
C9 logs/bvi-dilation-profile-gap-2026-10-18-* (16tmp)
C10 logs/bvi-ordered-gap-2026-10-18-* (17tmp)
C11 logs/bvi-dilation-collective-2026-10-18-* (19tmp)
C12 logs/bvi-all-level-cell-2026-10-18-* (15tmp)
C13 logs/bvi-shared-birth-2026-10-18-* (16tmp)
Each contains manifest,source.txt,axioms.txt,index.txt,lint.txt,public-names.txt,axiom-audit.lean.txt,search-and-scratch.tar.gz. All ownedtmp inthese sets SHAverified andremoved afterterminalprocesses. Retrievehistorical/tmp byarchivebasename. LatestC13index0;lint1 ONLY foreign package-root TransHorizonIncidenceMechanics.lean, noownedfinding. PreserveforeignREADMEchanges; oldhashobsolete.

CRITICAL EXISTING REUSE (source statements audited; do not duplicate):
PMRamanujanNearbyPrimeResonance exact nearbyprimePhiresonance/primeinsertion.
TwoPrimeDilationProfileIdentityAndPrimeStarShearCancellation exact4term balancedprimestar.
AllDepthHilbertDilationCubeAndHyperCubeGramFactorization actualweight fullcube/alternatingshell baseLambda cancellation.
DilationProfileIntegerJumpCoupling + ReciprocalJumpKernelAndDilationLagSectors exactprofileintegerGram and finiteGreen1/max-1/(H+1), lagsectorspa-qb.
DilationSuccessorSectorHarmonicClassification additiveRamanujanfiberreciprocity, fulllag1 harmonicselector/remainder; mu(r) ifscalescoprimer else0. Leastseed andfullsuccessorharmonic/digammarenormalization alreadyexist.
NaturalCutoffMultiDepthCofactorAndConditionalTailBridge fullnaturalcutoffhead/tail, exactcofactorcenteredhead, corrected -(H+1)*mean residual. RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence physicaldictionary admission assumesuniformenergy; noestimate.
BirthDelayedInteriorJumpCenteringAndUniformPairBounds existing1/d+2/gcd pairbound retaininginitial/density/delayedmean corrections; signedmodulussumopen.
HTGeometry/FiniteHilbertDispersion andInfiniteHilbertDispersion genericvariance/conditionalnegative-type and Bessel machinery.
EulerDeletionPrimitiveInterference.lean readall128lines: exactpositive physicalresiduekernel andstrict overlap lowerbound forrawEulerdeletioncarrier, differentfromlocalcenteredcells.
EulerDeletionMobiusPeriodCovariance.sum_centeredResidue_mul: completeperiod P*(gcd(m,n)²-1)/12 forpositivem,n|P. centeredResidue=k%m-(m-1)/2. NOTphysicalpronictransfer.
Actual analytic bounds EXIST: RHTower/KuznetsovKloostermanSmallModulus.exists_bilinear_kloosterman_small_le; KuznetsovKloostermanPhaseEnvelope.exists_kloostermanPhaseForm_le_rpow Cdelta sqrt(c)N^(1/2+delta)sum|alpha|² for c<=N,1<=|theta|<=2 and exp(2pi i*2theta sqrt(mn)/c). KuznetsovLargeSieveTheorem.large_sieve_gamma0 has deckfactor card(gamma0Deck L Q)(K²+N^(1+eps)/Q),Q|L+1. NeedexactcostcontrolledconversionofactualGram.
KloostermanCoprimeProductPeriodCompletion removescompletecoprimeblock butkeepsboundary; KloostermanCoprimeCrossPhaseFrequency exactCRT; KloostermanProductFrequencyGcdBound absolutegcd(q,r)*qr*(1+logqr). MobiusSquareResidueFourier exactleastresidueFouriercoefficient/chordnorm thenquadraticpath. VasyuninReciprocityAndExactTailGramProducer exactglobalminushead only,nocotangentevaluation.
ClockWaveletTensorBuchstabL2TelescopeAndShortWindowBridge175lines: unweighteddivisorsieveprefixenergy,notthiscarrier.
BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge448lines: differentlogtaperedweightvarianceO(1/logX), Fermihead/tail, unequalmoduliKloostermanterminalblock+gcd, 0<=logcovcombination<=logN*unknownoriginalenergy, notstrictcontraction.
BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge311lines: logphasecotangenttransport andoddprofileSchurcollar, notmodularinverseGramconversion.
PMPowerDampedMobiusLogConvolution211lines exactenergybalance. MobiusSignedSchurTransferPaper normalizedabs-summablelogtailat sigma>1, differentcarrier.
Firstbirthband existingGreen specialization: p<T<=2p yields prefixpacket L-nM+J(n), J=sum_(p<=n)p*a_p. EvenM=L0 leaves cumulativejumpenergy=sum a_p a_q pq(1/max(p,q)-1/T).

PAUSE CLOSEOUT, 2026-10-18:
User cleared goal and asked finish started Lean, wire, update docs, then pause. Seven completed leaves,69 public declarations. All seven current source SHA256 values match their prior passing actualsource checks; each BVI umbrella import occurs exactlyonce. C11–C13 all19 public API/axiom closures passed standard3. No newLean code was started after C13. C7 old baseline scratch retired/archived; noactiveuncompiled module. C13 family minimumkernel corollary remains paperonly, noLeanproofstarted.
Final scripts/formal_tools.py lint exit1 only foreign package-root TransHorizonIncidenceMechanics.lean; noownedfinding. All owned processes terminal. NoREADMEedit, nofull/umbrella build, nocommit.
20 knownownedtmp files archived/hashverified/removed. Durable logs/bvi-dispersion-pause-2026-10-18-searches.tar.gz plusmanifest.json,verification.json,lint.txt. Maincard haspausecheckpoint,all7leafresulttable,currentlimitations,andTypeI/IIreuseaudit. Historical/tmp paths refer toarchivebasenames. Donotresume withoutnewuserinstruction.

Saved corpus searches inpausearchive:
bvi-mixed-gap-schur-search.json (deep partialfalse74211inventory20candidate+20sourcearguments inspected; noSchurclaim,unmeasuredcoverage).
bvi-gap-sum-existing-search.json (all4 gapSumBoundnames).
bvi-gap-correlation-existing-search.json (all5 gapCorrBoundnames).
bvi-masked-phase-existing-search.json (all4 maskedNdExpnames).
bvi-nd-phase-existing-search.json and-page2.json (all37 names).
bvi-near-diagonal-phase-search.json (all5names/sourcecheckedphase).
bvi-pronic-mellin-typeii-search.json (partialfalse74215inventory,20candidate+20sourcearguments inspected; proposedingredientusesadmissioncriterionthatASSUMESenergy).
bvi-profile-mellin-lexical-search.json (nohits, notabsenceclaim).
bvi-mellin-corpus-lexical-search.json (all3 admissioncriteriahits).
bvi-dilation-spectral-existing-search.json and-page2.json (all29names).
bvi-cotangent-digamma-local-search.json (all19names).
bvi-digamma-cot-reflection-search.json (all4names).
bvi-primitive-reflection-existing-search.json (nohits,notabsenceclaim).
Three saveddeepquery outputs are UNREVIEWED exceptmetadata,allpartialtrue74215inventory20candidates20sourcearguments:
bvi-dilation-mellin-sobolev-search.json (malformedlocalmodelJSON,reranking/decomposition deadlines);
bvi-exact-cotangent-gram-search.json (semanticdeadline);
bvi-periodic-reflection-cotangent-search.json (semanticdeadline).
NoC14conjecture/formalworkwasstarted. Cotangent/reflectiontransferwas onlya prospectivelead, notproofclaim.

Verified EXISTING generic TypeI/II pipeline (RHTower/Sieve; noRHtopicwork):
TypeIIEnergyBound fullyread101lines: ndExp(T,r,m,d)=phaseExp(nearDiagonalPhase T r (m*d));norm1,conjugatesymmetry,actualpaircorr+Cauchy.
NearDiagonalPhaseCurvature actualdefinition: nearDiagonalPhase T r u=T/(2pi)*log(1+r/u). Source1–105read.
ZetaConvolutionTypeI fullyread72lines: ndPhaseExp exactsamephase, exactzeta-convolutionfibers.
TypeIIFibreCorrelation fullyread83lines: fibreIco A B b=Ico((A-1)/b+1)((B-1)/b+1); maskedNdExp retainsA<=dm<B;actualpairintersection.
MaskedSymmetry fullyread57lines: phase/productmask symmetricm,d.
CorrelationGapBound fullyread115lines: gapCorrBound=2500sqrt(Trh/(M0²36piP))+22sqrt(36piM1²/(Trh))*sqrt(Q³);m1!=m2 positivein[M0,M1],4r/mi<=P,curvedLambda(T|r/m1-r/m2|,P)<=1.
TypeIIHybridGapBound fullyread98lines: hybridGapCorrBound=5000sqrt(Trh/(M0²36piP))+75piQ²M1²/(16Trh)+1;dyadicQ<=2P,4r/mi<=P;nocurvedLambda condition.
GapSumSingleSqrt fullyread92lines: gapSumBound=2500sqrt(TrH³/(M0²36piP))+44sqrt(36piM1²Q³H/(Tr)).
GapSumDyadic read1–200,remainingsecondproofunread: unswap<=500sqrt(Tr)BsqrtB/(AP)+1500BsqrtB/sqrt(Tr);swap<=350Psqrt(Tr)/sqrtA+3000BsqrtB/sqrt(Tr),positiveanddyadicconditions.
ReciprocalPhaseStability fullyread: phaseandfirst2derivativesrelativeO(r/u) toX/u,X=Tr/(2pi),explicitconstants.
OffDiagonalTotal read1–77;TypeIIBlockSum read1–90. FibrePowerBound/GapSums/GapWeightedPairSum/TypeIIBlockBounds onlydeclarationinventory.
Thispipelineisalreadyproved; exactcost-controlledliteralpronicGramconversionstillunprovedhere.
DilationSuccessorDigammaRenormalization1–95sourcechecked: finiteprogressionharmonic constantandshiftbound reuseexistingGaussseries.
HTGeometry/GammaLogDeriv1–55and145–205read: digamma_reflection(s,noninteger)=pi*cos(pi*s)/sin(pi*s). Do notduplicate.
C13g1productbirthzero doesnotimplyalllatercoprimeoverlapszero. Fullsignedtailopen.