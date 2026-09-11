Goal ACTIVE, RH NOT PROVED. User forbids #print axioms; no such checks in iterations30–34. One owned foreground Lean process, scratch lake env lean, final targeted leaf build only, no full/umbrella build, no numerical experiments. Preserve other tasks. Cwd /Users/michael/Documents/code/hgt, Lean cwd formal.

Iteration33 COMPLETE and audited:
- ThetaCuspHawkingParikhWilczekGammaAdjointGainTransposition.lean:33 public theorems. Exact checked /tmp/pwb-gamma-forward-response.lean copied, unique RHTower import. Scratch passed no diagnostics; targeted build46s PASS. Logs /tmp/pwb-gamma-forward-response-check.txt and /tmp/pwb-gamma-gain-transposition-build.txt, exitfiles0.
- ThetaCuspHawkingParikhWilczekGammaFullPairedAdjoint.lean:4 public theorems. Exact checked /tmp/pwb-gamma-full-paired-adjoint.lean copied, unique import after gainleaf. Final scratch86481 exit0 no diagnostics. Target build23714 exit0,124s. Logs /tmp/pwb-gamma-full-paired-adjoint-{check,build,index,lint}.txt; exitfiles0.
- Index73629 PASS; all37 public names individually found LEAN_API. Exact source/wiring/link checks PASS. Formal lint79512 PASS onlyexisting sizewarnings. Scoped git diff --check PASS. No owned iteration33 Lean/index/lint process running.
- Stage3 cards pw-b-gamma-adjoint-gain-transposition.md and pw-b-gamma-full-paired-adjoint.md; former fullpairedcard moved fromstage1. Old contact/responsecards, stage1reversiblepairing/currentfrontier/STATUS updated specificcurrentobligations. Main journal iteration33 fullypersisted.
- All33 gainsource names and4 fulladjoint names checked againstAPI, not just samples.

Mathematics:
g_z=M_z/Q, Q=sqrtx exp(-x), w=exp(-x-1/x)/x.
Original coordinate derivative g'_z=g_z-g_(z-1), complete inverse-polynomial bound C(1+1/x)^p, monotone derivativebound overy>=x and meanvalue incrementbound Ch(1+1/x)^r.
ForwardResponse_z(x,h)=exp(-h)(g_z(x+h)-g_zx)/h. Exact admitted integral is parametercurrent TiltCurrent_z(x)/Qx. Weighted two-source kernel bounded C x exp(-x) exp(-h), jointL1; completeforwardcutoff h>d,ALLx>0 tendsactualcurrentpair.
Fullgain K_zv(x,y)=w(x)conjg_z(x)g_v(y)exp(-(y-x))/(y-x).
Atd>0 alloriginalcutoffsections and jointL1; exact measurePreserving_prod_sub shears(x,y)->(x,y-x); fullrectangleindicator→triangle0<x<y-d, admittedFubini. Actualinjectivephi(x)=1/x-1/y derivative -1/x² mapsIoo0(y-d) ontoIoi[d/(y(y-d))]. ActualJacobian+detailedbalance givesfulltransposition to reciprocalgain. Everyrecipientinterval, reciprocalray, bothouterintegrals separatelyL1. No undefinedintegralidentity.
Newpublic pwGammaReversibleDensity_shiftedPower_bound k hx:
w(x)(1+1/x)^k <=2^(k-1)(2!+(k+2)!) x exp(-x).
BackwardGain_decomposition allreal:
(e^-h/h)conj g_z(1/(1/y+h))=conjH_z(1/y,h)+(e^-h/h)conjg_zy.
BackwardGain_integrable z hy ha.

Fullpairedpublic:
pwGammaMobiusPaired_original_cutoff_identity z v hd hd1 (0<d<=1):
F_d=R_d+E_d+(C_d-L_d).
F forwardnativeallx, R backwardnative x>d,h>d, E originaloriented a_d..d response, C pairedcontact, L originalEmptyIncomingLoss.
AllpartsL1. Forwardgain-loss, exacttransposition, backwardresponse+constanttail, differenceoftails, splitP integralatd retainsLwithcorrectsign.
pwGammaMobiusPaired_original_adjoint z v: integral w conjg_z*(TiltCurrent_v/Q) = integral_x integral_h J_zv + integral P_zv*2logx.
pwGammaMobiusPaired_original_current_adjoint z v:
integral w conj(M_z/Q)*(TiltCurrent_v/Q)
= integral w*(M_v/Q)*conj(SameSourceCurrent_z(1/x)/Q(1/x))
+integral wconj(M_z/Q)(M_v/Q)*2logx.
pwGammaMobiusPaired_original_current_admission z v: ALL3originalcurrentouterintegralsL1.
Finalthree haveonlyparameterszv,nobalance/zerolocation/cutoffpremises.
Use integral_complex_ofReal (notgeneric integral_ofReal) fortail; explicitPi.add_apply forintegral_add rewrites. Complex.conjCLE.integrable_comp forconjugation.

RHchain: PWsource -> FE signeddefect -> fullphysicalcommon-domainadjoints + positiveDeninger reflectgaugeWardtransmutation -> actualXioccurrence -> independentfixedgradebalance ->RH.
Now fullpairedsourceintegraladjoint closed. Missingphysicaldomain/closure, sourceforcingpairingclass, DIFFERENT justifiedXioccurrence, independentWardbalance. CorrectedrawGamma scalaransatz excludedallz byiteration30; neverrevive. K=A-B-2log is pairedskewcandidate, correctionis2log NOTlog. Nooperatorspectralclaim.

Iteration33research raw4queries in docs/drafts/pipeline/1-in-progress/pw-b-gamma-forward-gain-searches.json, partial731780(firstretrievalinterrupted),731829,731881,731960(last3noerrors). Generatedideasnotpremiseproofs. DomainqueryonlyfindsDeningerSkewAdjointGraphCore requireschosendomain/skewpremise; noinputsolved.
BroadSep9transportpapers2609.10393 Bothe usesexplicitbalanceanchoringaxiom;2609.10367 HashemiHyun realrootedinput→definitepencil;neitherPWproducer.

LIVE nextattack started:
- New stage1card pw-b-gamma-mellin-dual-domain.md, paperonlyuntilscratchfinished.
- /tmp/pwb-gamma-mellin-dual-domain.lean checking foreground session47820 (ONEcurrentownedLean); log /tmp/pwb-gamma-mellin-dual-domain-check.txt currentlyempty lastread. 5publictheorems plusdef sofar;NOTpromoted, NOTclaimed.
- Newdeepqueries sessions8356 &62757 BOTHterminalexit0. Rawresultsin pw-b-gamma-mellin-dual-searches.json. partial732050,732074,noerrors,0proofideas, proposedingredientsetsdoNOTsolveincidence/domain. FirstreturnsMobiusMellinContinuationWall withanalyticpremise,otherfieldsresidues; secondMellininversionrequiresoriginaladmission,bandconditions. Needdocumentassessment.
- Newpaperderivation literalMellink_s=x^(s-1)Q. Squareddualweight |k_s|²/w = D_Re(s)(x)=x^(2Re(s))*exp(-x+1/x).
ConjectureD L1nearzeroFAIL: choose naturaln>2a+1;0<x<1 givesD>=e^-1/n!*x^(2a-n), nonintegrablepower.
Strongpositive survivor exactdensity,compactadmissionawayzero, andsourceweightedL2forallz (derivefromnormPzz).
Current scratchprovesDpos,Dlower,DnotintegrableonIoo0 1,DcompactL1, allzweightedsource-squareL1. ExactliteralMellindualidentity NOTYET added.
A stronger no-bounded-Mellin-readerclaim needsRiesz/normalizedtests, NOTyetasserted.
- Broadintertwining search2608.01485 ElberLheem primaryintro/proposition2.3.6 read: exactfinitegroupargumentsneedclass-specificcharinvariancebeforeantiinvolution; noPWtransfer.2606.04383 JiangWangWu abstractread,HTMLfailed; noprooftransfer.
Next: finishscratch & exactMellinweightidentity; no-go MUSTretainpositive survivor andnarrow scope. NoRHcompletion.
