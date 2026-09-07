# EDQ full quotient decomposition and harmonic tail-depth bound — complete bridge
Persistent RH/EDQ goal ACTIVE, NOT complete/blocked. Current continuation baseline8,211,279tokens,no budget. Prior turn verified progress: first-tail Mertens identity + uncertain RunPod cutoffexperiment. THIS turn made progress: exact all-quotient identity, sharper complete source bound, unconditional uniform-depth instantiation. No numerical computation this turn; all derived results predictable from paper proof.

Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.
Do not redefine success around this bridge. RH absolute cofinal polynomial-log ceiling remains open.

## NEW AUDITED LEAF
formal/GaloisForLFunctions/RHTower/EulerDeletionQuotientHarmonicBound.lean
~237lines, namespace RHTower.DeletionQuotientTail, imports EulerDeletionFirstTailMertens. autoImplicitfalse.10publictheorems,0defs,2privateharmonichelpers.
17 truncated_floor_hyperbola(f:Nat→Real)(N n): sum_(N<m≤n)f(m)*floor(n/m)=sum_(1≤j≤floor(n/(N+1)))sum_(N<m≤floor(n/j))f(m), ALLf,N,n. Exact finiteFubini, arbitrarysignedcoeff.
52 floorResidual_eq_quotient_mertens(N n)(hn:1≤n): actualresidual R_N(n)=sum_j(M(floor(n/j))-M(N)), active J=floor(n/(N+1)). Includes n≤N viazeroJ.
71 error_eq_quotient_sum(N n)(hn): actualerror1-F_N(n)=nH_N-J*M_N+sum_jM(floor(n/j)). Exactcutoffcountertermretained.
87 floorResidual_le_harmonic:eps≥0 and∀k≥N |M(k)|≤eps*k imply |R_N(n)|≤eps*n*(1+harmonicJ), npositive. Eachquotientuses |M(floor(n/j))|≤eps*n/j, andN*J≤n.
137 floorResidual_le_of_depth: n≤N*L gives |R|≤eps*n*(1+harmonicL).
148 primitive_extended_prefix_le: normprimitive≤1+n*(absH_N+eps*(1+harmonicL)), samewholeextendedprefix.
167 primitiveEnergy_le_harmonic_depth: N,L≥1 gives FULLgenuineenergy
E_N≤4+2*N*L*(absH_N+eps*(1+harmonicL))²+N/L.
184 primitiveEnergy_le_log_depth: replaceharmonicL≤1+logL:
E_N≤4+2*N*L*(absH_N+eps*(2+logL))²+N/L.
198 modular_norm_sq_le_log_depth:actualmodularcarriernorm²inheritsbound.
207 exists_primitiveEnergy_uniform_log_depth_bound: UNCONDITIONAL ∃B≥0,eventuallyN,∀L≥1,
E_N≤4+2NL*(absH_N+B*deningerMertensSaving(N)*(2+logL))²+N/L.
deningerMertensSaving(N)=exp(-(logN)^(1/3)/108), actualcorpusPNTcontourestimate. OneconstantandoneNthresholdworksforALLdepthL. No remainingMertenspremise inthislast theorem. H_Nstillactualscalar; noabsoluteRHceilingclaimed.

## Why progress / boundary
Old full estimate had absH+2epsL inside square. Exactquotientsum improves depthcost toeps*(1+harmonicL)≤eps*(2+logL). This sharpensactualsourceproducer, notmerelyrephrasesgoal. InfiniteN/LtailNEVERomitted. Existingfullsourceo(N/log^qN)remainsvalid. Relative/logarithmic/subexponentialimprovements cannot themselvesremoveNcutoffpower; next stepneeds absolutecancellation acrossquotientscales orfullactual-zero constraints, notanother assertionthat decayfactorisRH.
Fullsourceerror now explicitnH−JMN+sumM(n/j); retaincountertermwhenrearranging. Do notredoone-quotient/firstblockbridge.

## Corpus inspected THIS turn
- EulerDeletionFirstTailMertens full current source.
- MobiusDivisorAbelQuadraticDiagonal first205lines, CCMFUSuzukiMobiusDivisorDilationChannels quotientfactorization around180–275. Their divisor-defectsource differs, no upperboundtransferassumed.
- Sieve.MoebiusHarmonicTailIdentity allneeded: H_N=M_N/N−sum_(i≥0)M(i+N)/((i+N)(i+N+1)), genuineabsoluteMertensseries. Could supportfuturecenteredquadraturelaw, NOTprovedthisturn.
- DeningerMertensSummatory:actualexp(-(logN)^(1/3)/108)rate, explicitlyPNTstrengthnotRHsquare-root.
- Sieve.MoebiusHarmonicArbitraryLogRate relevantsourcebound. Research'harmonic exponential' no readyH_Nstretchedexpboundfound infirst15hits; noexhaustivesuchclaim.
- NEWconcurrent RetainedPrimeSourceMellin.lean first~90lines: uniformconvolution summatorynorm≤24*(sumfinitecoordnorm)*N^(3/2), MellinidentityRe(s)>2, NOstrongerMertensboundforEDQ. RetainedPrimeSourceInterpolation.lean179–end: one-sidedintegerfunctionalpremise givespositivecontinuoussourceray, no uncondpositivity. Notimportedintonewleaf; doNOTtreattheseassolvingEDQ.

## Documentation COMPLETE
Card moved from1-in-progress to docs/drafts/pipeline/3-formalized/edq-quotient-harmonic-tail-bound.md. Dependencyclosedpaperproof+uniformactualprovider+allvalidation, no pendingmarkers.
FrontierCURRENTstate top summary,newparagraph afterFirstTail,EDQrow. Old GlobalLogSavingparagraph retainsvalidasymptoticsandtwo-sidedenergycomparison; removedobsoleteweakerfiniteformula in favor ofnewparagraphbestbound. Nohistory/newroute labels/retirement.
STATUS appended route-independent MUST-RETAIN-THE-DECAY-ACROSS-SCALES: retaindecaybeforecountingtermsexactregroupingcanreplace linearcountlossbyharmonicsum; completeinfinite-tailbalanceandcutoffpowerstillmatter.
IMPORTANT: another task reformatted/shortenedexisting FirstTailfrontierparagraph and removeditscardlink duringthisturn. InitialdoceditassertfailedBEFOREanywrite; rereadactualparagraphandinsertednewpara aftercurrentline. Preservedotheredit; compare-and-swapcheckedfrontierbeforewrite. DoNOTrestorestaleoldFirstTailparagraph.

## Validation COMPLETE — avoidrepeat
- APIchecks,scratch sequentialoneownedLeanprocess. Finalscratch11869exit0 EMPTY /tmp/edq_quotient.scratch.log.
- Finaltargeted LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionQuotientHarmonicBound session49520exit0,ONLYnewleafBuilt7.6s;13111cachedgraphjobs,replayedoldwarningsnotactualnewfailures.
- New-onlyaxioms7259exit0 ALL10exactpropext/Classical.choice/Quot.sound. No addedaxioms/admission/numericalcert. Privatehelperstransitivelycovered.
- UniqueRHTower.leanimportwired;NOfull/umbrellabuild.
- ONEformallint72048exit0,formal lint passed.
- ONEsearch-indexexit0:7changed0removed,33116files404057decl3953gaps.
- Scopedchecks10coverage/exactstdsets,forbiddenproofscans,scratch=source,oneumbrellaimport,doclinks/stage,whitespacepassed.
- NoownedLean/lakeprocessremains. Removed /tmp/edq_quotient.lean,/tmp/edq_quotient_api.lean,/tmp/edq_quotient_axioms.lean. Logsretained /tmp/edq_quotient.{scratch,api,build,axioms,lint,index}.log.
- NonumericalexperimentorRunPodjobthisturn. OldRunPodexperimentfullydownloadedandownedservertemps/workerscleanedlastturn.
- No commits/push,foreignworkingtreefilespreserved.

## APIs and traps
Nat.div_le_div_left(hcb:c≤b)(hc:0<c):a/b≤a/c. hcREQUIRED.
Nat.le_div_iff_mul_le(hk:0<k):x≤y/k ↔x*k≤y.
Nat.cast_div_le(α:=Real)(m:=n)(n:=j):real(floor n/j)≤realn/realj.
Finset.sum_filter p f:filtered sum =sumif. Explicitfilteredsetidentities easeFubini.
harmonic_eq_sum_Icc; harmonic_le_one_add_log(L) validallL. harmonic_mono,harmonic_nonneg UNKNOWN names. Provedprivate realcastsumhelperandfinite-subsetmonotonicity.
CRITICALremember add_le_add_right HEREPREPENDScommonterm (type b≤c→∀a,a+b≤a+c). Forappendingcommontermuse add_le_add _ le_rfl. Relearnedthisafteronescratchfailure; don'trepeat.
Real.exp_le_exp isIFF. Real.rpow_le_rpow needsbase≥0,baseorder,exponent≥0. Real.log_le_log positiveleft,baseorder.
Nat.div_mul_le_self plusnlinarith givesdepthJ≤L fromn≤NL andNJ≤n. No hugecomputationneeded.
