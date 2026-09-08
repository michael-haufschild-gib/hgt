# CCM-FU: corrected coarea also fails every complete order

RH goal ACTIVE, unachieved. Frontier map READ ONLY. Prior turn PROGRESS: exact every-order obstruction for uncorrected B; this turn PROGRESS: 14 new checked theorems exclude corrected Hcorr as well, with sharp positive variance decomposition. No experiments run; results follow from exact corpus conservation/asymptotics. Do not optimize either common head-mass coarea envelope again.

## Mathematical result
C_d actualsource. U=sum|C_d|; S=sum C_d; T=active late mass. t=consumedlate,r=T−t; f=signedhead,a=originalabsolutehead. Remove unprocessed active late singleton labels from all labels, leaving W. Its absolute mass V=U−r, signed mass Y=S+r. Both exact identities now formal. Hcorr=a*sum_W F²/A+Elate. Weighted Cauchy yields t*(S+r)²≤U*Hcorr since a≥t, r≥0,Elate≥0. Holds for every actualstate without mixed-cell dominance or cancellation assumptions.

Sharp positive survivor for ANY finite actual cell collection W, including zero-mass cells:
J=sum_W F²/A = Y²/V + sum_W (F−(Y/V)A)²/A.
Equality J=Y²/V iff every cell F=(Y/V)A, also valid V=0 since zero originalmass forces zero signedmass. Exact actual Hcorr decomposition substitutes V=U−r,Y=S+r, multiplies by a, restores Elate. Mixed cancellation can remove variance only; it cannot remove the forced retained signed-mass square.

Generic quarter-band lemma: x0=0,xk=T>0, all forwardjumps≤T/2 gives some n≤k with T/4≤xn≤3T/4, without monotonicity. Choose first crossing of T/4 via Nat.find; upper bound from previousvalue+halfjump. For actual consumedlate step≤D=(3/5)sqrtM. With D≤T/2 and S≥−T/8, this prefix has t≥T/4,r≥T/4,S+r≥T/8, so T³≤256U Hcorr. These finite bounds are discharged unconditionally at M=4N: prior S/T→0, T/M→∞, and T≥N sqrtN/(80log(2N)). U≤(3/5)M sqrtM. New eventual_cubic lemma proves for every B, eventually B*(4N)²*U(4N)<T(4N)³. Proof uses log(2N)^3/N→0 via mathlib isLittleO_log_rpow_rpow_atTop, not numerical computations.

Capstone: for every real C, eventually for EVERY k,P:Nat→FinsetNat,q:Nat→Nat, with P0 disjoint activeLate(4N), activeLate⊆Pk, and P(n+1)=insert(qn)Pn for n<k, some prefix has Hcorr>C(4N)². Permits arbitrary small/middle-prime interleaving, repeated and nonprime indices. Uniform correctedaction is impossible even under ideal mixed-density cancellation. Raw Q uniformquadratic remains OPEN; this is no RH falsification and no retirement of CCM-FU.

## New files / API
Card docs/drafts/pipeline/5-failed/ccm-fu-corrected-coarea-mass-balance.md has full paper proof, no-go positiveclosure, certificates, audit details. Prior ccm-fu-coarea-all-orders-mass-split.md and ccm-fu-coarea-mass-envelope.md updated to link this stronger obstruction and keep rawQ as open target. STATUS adds route-independent forcedmean/variance constraint; Updated2026-09-08. Frontiermap neveredited.
NamespaceRHTower, three new RHTower leaves, wired:
1 MobiusDivisorFibreCoareaVariance.lean (3public): mobiusDivisorFibre_coarea_cauchy; mobiusDivisorFibre_coarea_variance; mobiusDivisorFibre_coarea_variance_zero_iff.
2 MobiusDivisorCorrectedCoareaMassBalance.lean (7public,1def mobiusDivisorRetainedCoareaLabels): sum_mobiusDivisorFibreAbsoluteMass; sum_mobiusDivisorRetainedCoarea_signed; sum_mobiusDivisorRetainedCoarea_mass; mobiusDivisorCorrectedCoareaAction_eq_retained; mobiusDivisorCorrectedCoareaAction_eq_variance; mobiusDivisorCorrectedCoareaAction_nonneg; mobiusDivisorCorrectedCoareaAction_mass_balance.
3 MobiusDivisorCorrectedCoareaOrderBarrier.lean (4public): exists_prefix_mass_quarter_band; exists_mobiusDivisorCorrectedCoarea_prefix_mass_barrier; eventually_mobiusDivisorLatePrimeMass_cube_gt; eventually_every_mobiusDivisorCorrectedCoarea_order_exceeds_quadratic.

## Validation / cleanup
Allscratch/installedchecks lakeenvleanpassed. Only3newnecessaryoleans. All14publictheorems#printaxiomschecked ONCE:onlypropext,Classical.choice,Quot.sound. Do NOT repeat these audits or prior22/20/10 audits. Finalexactmodulelakebuilds in byte-identical isolatedpackage cacheonlydeps passed serially:variance4.0s,balance4.8s,order6.8s. Onlynew3modulescompiled; nofull/umbrella/depsourcebuild. An informational ringfailed diagnostic in zero-limit convert goal was removed by changing final `ring` to `simp`; only changedorderleaf rechecked/rebuilt before oneaxiomaudit. FinalLeanleavesnowarnings/diagnostics. Cachepackage initialmissingmanifest warningsonlypackaging.

Indexes regenerated once. Global lint --check-generated fails currently solely on foreign missing umbrellaimports FokasLenellsContourJost,FokasLenellsContourScattering,FokasLenellsContourSymmetry (HTGeometry). Previous2Selbergmissingimportsnowpresent. Do not edit other agents' ongoing source. Ownbytecopies/uniqueimports/debtscan/whitespace/cardlinkspassed.

Removed owned /tmp files ccm_balance_names.lean,ccm_fibre_variance.lean,ccm_corrected_balance.lean,ccm_corrected_order.lean,ccm_corrected_balance_axioms.lean,ccm_corrected_balance_lint.log,ccm_corrected_balance_audit_path,ccm_wide_research.json,ccm_mass_balance_research.json,ccm_raw_order_research.json and isolated /var/folders/h4/zrd73pg91clb__kg1kzrlcph0000gn/T/ccm-corrected-balance-audit-y4qg66q3. All ownedLeanprocesshandles terminal; noRunPod work or jobs. No commits.

## Wide search evidence / next hard target
Explicit --any OR searches (never unintentionallyAND) used martingale/discrepancy/rearrangement/cancellation/coupling/coarea:4879decl1587mods; weightedvariance/massconservation/fibresums:133decl86mods; energyorder/energyceiling/partialsubset/rawenergy/primeorder:103decl51mods. Read relevantactualsourceconservation, fullpositive normalization, lateprimeheadasymptotics, weightedCauchy/variancecorpus. Candidate fixedmeancomponent is forced, not a new hopefulupperbound.

Next significant attack must control RAW signed energy/mixed-prime cross terms, not eithercoarea bound. Widerawordersearch exposes MobiusDivisorGrowingSignedPrimeBatches (arbitrarilymanylinearunitsbothsignedsources underfixedquadraticceiling,butmiddleprimesunexhausted); MobiusDivisorSquareRootTerminalOrder and MobiusDivisorSignedPrimeBatches (complete isolated/terminalorders undermaxactualendpoints). PartialSubsetEnergyOrder was read: exists_partialSubsetEnergyOrder ASSUMES safe unused element at every smallsubset, so it is an assembly theorem, not the missing producer. PositivePrimeCubeEnergyBarrier appeared in search but not yetread. Fullendpoint signedboundstillmissing. User demands direct attack everyturn, widecorpussearches, no predictable experiments, no frontieredits.
