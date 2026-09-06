# Dirichlet polynomial surgery scope correction, 2026-09-06

Goal ACTIVE; no qualifying novel RH architecture or RH proof. No RH-producing link closed. Previous goal turn (mixed area) was progress: new remote falsification guidance. This turn made progress by detecting/correcting a false research barrier and checking a premise-free counterexample from existing published math. Do not redefine goal around audit results.

## Exact correction
RHTower.no_polynomial_surgery forbids F=P*G on eventual real right halfline for ordinary Lseries with finite absolute abscissae, nonzeroG, nonconstantpolynomialP. Intro of DirichletRigidity incorrectly generalized this to impossibility of all finite divisor surgery. GoldilocksTrichotomy called this a categorical mechanism and asserted onlymiddlecellviable withouttheorem. Fixed COMMENTS ONLY in formal/GaloisForLFunctions/RHTower/{DirichletRigidity,GoldilocksTrichotomy}.lean. Verified all noncommenttokens IDENTICALtoHEAD (nested-comment-aware scan). No mathbody edits.

Corrected ALL direct downstream problematic citations found by rg: docs/drafts/pipeline/1-in-progress/rhtower-nogo-positive-content-audit.md row88; 3-formalized/not_new_scientific_knowledge/rh-tower-obstruction-language.md historicalDirichletline52; 3-formalized/defect-protection-connected-symmetry.md sectionsD/E. Last falselyinferred upperbound forminimalRHconstraint fromexclusionofonepolynomialplanting; now says necessarynot sufficient andminimalityconjectureunproved. Nootherrouteedited/adopted.

## Closed witness (audit instance, NOT newmath)
Scratch /tmp/hgt-dirichlet-surgery-scope-W2izoY/SingletonDivisor.lean defines rho=3/4+I and D(z)=ifz=rho then1else0. Proves finite-supportlocalfiniteness andsupportRe<1; instantiates RHTower.exists_continuable_phase_with_prescribed_locallyFinite_divisor then identifiesHasProd withordinaryLSeries usingHTGeometry.hasProd_phaseEuler andlSeriesSummable_phaseChar.
SurgeryScopeAudit.ordinary_series_singleton_divisor is PREMISE-FREE: existsa:Nat→*₀Complex andZ:Complex→Complex with |a(n)|=1 n≠0, MeromorphicOnZuniv, ordinaryseriesabsolutelysummableandequalZforRe>1, everymeromorphicorderZz=Dz castWithTopInt. Thussingleoff-line nonrealmeromorphiczero andnootherdivisor. It concernsmeromorphicorder, not arbitrarypointvaluesatremovables. NOFE orliteralζcoefficientsasserted. A knownAnderssoninstance, notnewarchitecture/positivesalvage.

Primary source verified: JohanAndersson, Mittag-Lefflertype theoremsforHelsonzetafunctions, arxiv2408.15713 (2024), abstractstatesentirezero-freefactor andprescribedzeros/polesRe<1. NoHelsonRHrouteadopted.

## Validation
- PolynomialAudit scratch6154exit0: bothno_polynomial_surgeryand_zeta standard3axioms.
- Namesinitial32408failedmissingoneolean, later48096gotactualaxiomsbut universe-polySet.finite_singletonhaveerror. Fixed @Set.finite_singleton Complex. FinalNames44199exit0 standard3forgeneralpolynomialandfullprescribeddivisor.
- Missingdependency census found ONLY XiMassCriticalDiagonalPrimeCoronaZeroDensity.olean inLocallyFinitedivisorimportchain throughAnderssonTheoremOne/Sieveprimewindow. Checked/builtonlythatneededoleanvia lakeenvlean-o...source,5383exit0. NOsourceedits/adoptionofexcludedroute;nofull/umbrellabuild.
- SingletonDivisor93997exit0, axioms[propext,Classical.choice,Quot.sound]. Exactproofpersisted asLeancodeblock in auditcard, excluding#printqueries (thoseONLYscratch). Codeblockmatchescheckedscratch.
- Editedsource lakeenvlean checks: Dirichlet68784exit0;Goldilocks58339exit0.
- Final narrowleafbuilds:Dirichlet2105exit0 built4.3sec;Goldilocks69497exit0 built3.1sec. ExistingumbrellawiringconfirmedRHTowerlines3786/4925;LocallyFinite5636. No newproductionmodule.
- LATESTGLOBAL lint5875PASS withexistingfilesizewarnings; log /tmp/hgt-dirichlet-surgery-scope-W2izoY/lint.log. EarlierThetaTiltunreachablefailure isSTALE (otherwriterresolved); donotkeepreportingit.
- Researchindexrefreshedwith 'polynomial multiplier' --moduleDirichletRigidity, returnscorrectedscope.
- Scopedgitdiffcheckpass;links/cardproofmatchpass. NoownedliveLean/ssh/processhandles. NOmathematicalcomputations thisturn.

## Persistent docs
Auditcard docs/drafts/pipeline/1-in-progress/dirichlet-polynomial-surgery-scope-audit.md includesexactscope,publishedancestry,wholecheckedwitnesscode,allvalidation,broadsearchtransfermatrix. Markedresearch-auditcorrectioncomplete,parentRHsearchinprogress. No newproductionmoduleforroutineknowninstance.
STATUSMUST-SURG1 around5018: onepolynomialoperationno-gonotallfinitezerosurgery;nonzeroordinaryseriesrestriction;extraunitfactorallowsdifferentconclusion;actualcoeffsourceconstraintneeded. Main rh-corpus-architecture-audit-2026-09-05.md Openobligationshascorrectionparagraph. NoRHcompletionclaim.

## Broader current-corpus audit this turn
Usedresearch+rgactualstatements (searchmissesnotenovelty). Queriesarithmeticsurgery,integersubstitution,multiplicativeexchange,finitesurgery,multiplicativeadditiveincompatibility,boundaryintegralinteger,nonlineararithmetic,coefficientsurgery,arithmeticassociator,integernonlinear,integercarry,finiteprimetwist,Helson,finiteEulermodification,Helsonsinglezero,Helsonfinitedivisor. Manyhitsalreadyclassic/excluded,notadopted.
Read EulerCompositionPolynomialRigidity1-210: HTGeometry.exists_polynomial_of_euler_mero_relation requireswholemeroidentity; pointzeroinsufficient.
Read MahlerHomogeneousRigidityfull71: GaloisForLFunctions.mahler_homogeneous_eq_zero requiresentireformalsubstitutionidentity,notpointzero. ModulepathhasHTGeometry.
ReadPrimeCollisionConvolution1-180,PrimeCollisionCoordinateFusionEscapeUniversalityLaw1-125: nativecoeffexactfusion/orderedunequalvaluation;cofiniteTailDenseOnassumption yieldsnewDAfieldlayer,notzero-specificconstraint.
ReadIntegerCarryTransportfull139,alreadySTATUSF20g/earlierbalancedperiodmemory! Donotrediscoverasnew. Transportargessential.
ReadTopologicallyAdmittedCarryPropernessSelection31-85:compactphaseboundCURRENTlocalboundedcharacter/trafficpremise ismissing, phasecompactnessdoesnotproduceit.
Read DirichletAnalyticPostcompositionSignRigidityintro/first62andrgcapstones:realanalyticpostcompcannotmakeone-signfar-righttranslatefromfirstnonconstantmode;notadopted.
ReadAnderssonTheoremTwo186-287,LocallyFiniteDivisorPresentation1-82/433-485,HelsonCharacterLSeriesphaseChar/norm/HasProd/LSeriesdefinitionsandstatements. Sourceactualgeneralprescribeddivisor unconditionallyimplemented,notjustHelsonFactorizationPropertyassumption.

Nextturn MUST beginfullproofchain withproved/missinglinks andwhatworkadvances. Need actualnewsourceoperation+zero-specificidentity, notmoreclassificationwrappers. No successor architecture selected. Alluserclassic/spectral/Gamma/etc exclusionsremain. Goalnotblockedmerelybecausemathhard.