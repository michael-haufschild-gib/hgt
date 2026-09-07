# EDQ complete flux weight replacement, formalized (2026-09-07)

Goal ACTIVE/unachieved. Current turn PROGRESS: new unconditional complete aggregate error bound closed in Lean. This is a correction estimate, NOT the missing full EDQ producer or RH proof. Previous turn classified NO PROGRESS; see `mem:rh/edq-full-tail-abel-flux-attempt-2026-09-07`. Frontier map READ ONLY, untouched. No subagents, commits, numerical experiments or remote jobs. No new route-independent STATUS entry: existing aggregate-correction/growth rules cover the general point.

## New leaf, validation complete — do not re-audit
`formal/GaloisForLFunctions/RHTower/EulerDeletionFluxWeightReplacement.lean`, 253-ish lines; namespace RHTower.DeletionFlux.
Five public declarations:
- primitive N k (line26): sum d=1..N of mu(d)*HTGeometry.centeredModularPrimitive d k.
- channels_summable (line131): complete inverse-square and physical-weight channel convergence, requiring only 0<d<=N.
- stepFlux N (line149): sum d<=N mu(d)*sum j>=0 U_N(k)/[k(k+1)], k=d*(N/d+j+1).
- reciprocalFlux N (line155): same exact complete channels with1/k².
- flux_weight_replacement N (line224): |reciprocalFlux N-stepFlux N| <= (harmonic N:Real)/4 for EVERY naturalN, includingemptyN0. No arithmetic/RH premises or numerical inputs.

Each channel samples every multiple ofd strictly greaterthanN, once. No time truncation or periodaverage. Definitions are literal divisor-channel sums; time-index regrouping and later Phi2 representation are PAPER identities, not newLean bridge claims.

Proof: |U_N(k)|<=N(N+1)/16 from |mu|<=1 and|P_d|<=d/8. q=floorN/d>=1, k=d(q+j+1), N<=2dq. 1/k² <=1/[d²(q+j)(q+j+1)]. Gap1/k²-1/[k(k+1)] = (1/k²)/(k+1) <=1/[N d²(q+j)(q+j+1)]. Reciprocalmajoranttelescopes1/q. Complete absolutechannelgap<=N(N+1)/(16N d²q)<=1/(4d). Sumd givesharmonic/4. Genericprivate reciprocal_series_bound provesconvergence BEFORE subtraction.

Imports only CenteredModularAbel and relevantmathlib Moebius,Harmonic.Bounds,InfiniteSum.Real,Normed.Group.InfiniteSum. No RH dependency.
Scratch lake env lean clean. Final `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionFluxWeightReplacement` exit0, onlyleaf compiled3.2sec;3395graphjobs cached otherwise. Wired atRHTower.lean:16068; no umbrella/fullbuild.
Fivepublic-only #printaxioms from /tmp audit: each ONLY propext,Classical.choice,Quot.sound.
Indexonce:6changed0removed includingconcurrentforeignfiles, generatedindexesupdated. Full scripts/formal_tools.py lint PASS, existinglargefilewarningsonly. Scopeddiffcheckpasses. Do not repeat thesechecks withoutnewchanges.

## Direct main-bound attempt / paper survivor
Openingattempt: reciprocalpairing ofdivisor-sampledflux. Both directedkernels are nonpositive, withsame mu(d)mu(e) prefactor afterswap, so pairing(d,e)with(e,d) gives triangleEQUALITY, nocancellation withinpair. This rejects thisspecificcancellationstep, notEDQ orallreciprocity. Nocomputationneeded.
Define completeK(d,e)=sum j>=1 P_e(dj)/(dj)², B2(x)=fract²-fract+1/6, Phi2(x)=sum j>=1 B2(jx)/j². Directsubstitution K=e/(2d²)*(Phi2(d/e)-zeta(2)/6).
Checked primary Balazard--Martin https://arxiv.org/pdf/1305.4395 section5 eq56 (PDFpage29), Proposition28 eq70 (PDFpage33). Their Phi2 hasretainedintegral relationtofractionalpartautocorrelation; doesNOTprovideactualmuaggregatebound. SearchreciprocityBernoulli gave0corpusdeclarations; cotangentcancellationonlyunrelatednames. Paperdoccitesprimary; noneimported intoLean.
Completekernelconversion (paper): reciprocalFlux(N)=sum_(d,e<=N)mu(d)mu(e)K(d,e)+c, c=(M(N)-H_mobius(N))/2. Forphysicalg(k)=sum_(d|k,d<=N)mu(d), g1=1,g2..N=0,U1=-c. Hence removinginitialtimepartadds c. Cannotdrop/assumecsubpower.
One-complementform (paper): reciprocalFlux(N)=-sum_(d>N,e<=N)mu(d)mu(e)K(d,e). Completefirstindexsum sum_d>=1mu(d)K(d,e)=P_e(1) by d*j=k and fullMöbiusdivisoridentity. Absoluteconvergence fixede follows |P_e|<=e/8 andtwoinverse-square-seriesproduct. Sumfinitee =-c. This incorporatesmeanexactly. Remaining rectangle d>N,e<=N stillbalanced d,e~N. Crude|K|<=e*zeta2/(8d²) givesO(N), no signedsubpowerboundfound/formalized. Nextattemptcanattackthis actualcomplementaryrectangle, notredo reciprocalpair orscalarLandau receiver.
Importantboundary: newflux includesk>N. PreviousAbelformulaa=N+1 usesk>=N+2, so subtract/retaink=N+1atom; alternatively choosea=N andfluxmatchesdirectly. Cardexplicitlyretainscoordinate. Notdeclarednegligible.

## Files and cleanup
Newformalcard docs/drafts/pipeline/3-formalized/edq-flux-weight-replacement.md.
Workingcard docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md section613+ now formalizederror plusreciprocitysign,completekernelmean,andone-complementpaperidentity.
Frontier untouched, foreignchangespreserved.
All own handles terminal:37355names,10716scratch,8560scratch,96881scratch,15847scratch,39772cleanScratch,60865finalbuild,27574axiomaudit,52702index,40779lint. Exactpsauditshowsnoownedlean/lakeprocess. Removed3owned /tmp files:edq_flux_names_root.lean,edq_flux_root.lean,edq_flux_axioms_root.lean. No remainingowned scratchorjobs.

## Lean efficiency notes
Nat.div_pos hdN hd avoids an omega failure on a quotientzero subgoal. Rationalringneeds simp only[div_eq_mul_inv,mul_inv_rev,one_mul] before ring for productdenominators. Use Summable.congr(fun j=>by ring) to changeU*(1/w) toU/w; simpa only[div_eq_mul_inv] causeddefeqheartbeattimeout onnestedfunctions. Avoid dsimp whenbetaalreadyreduced. Theseissuesresolved; no maxHeartbeats increase.