# SQB21: original Maass Cauchy uniqueness and strict slice mass — fully audited

RH remains UNPROVED, unbudgeted goal ACTIVE. Frontier map READ ONLY; no edits to it. No subagents, external numerical experiments, Runpod, web, commit or push. Preserve shared peer changes. Previous SQB20 turn was progress; this turn also changes authoritative Lean state.

Module `formal/GaloisForLFunctions/RHTower/SelbergMaassSliceRigidity.lean`, namespace matching module,20 public declarations(19theorems+modalPotential). Imports CurrentHeightContinuity, MaassBoundaryForm, Mathlib ODE.Gronwall and Measure.OpenPos. Wired once into RHTower.lean. Stage1/stage3 cards `sqb-maass-slice-rigidity.md`; universal STATUS adds distinction whole-trace vs nodal vanishing.

## Exact results
Original MaassCuspEigenform explicitly includes f!=0, original C² PDE, actual congruence invariance, all integral cusp decay. Do not assert exceptional eigenforms exist.

For ALL real eigenvalues:
- `second_order_cauchy_zero`: generic complex second-order u'=v,v'=c*u with c continuous on Ioi0, zero u,v atY>0 -> zero pair at everyy>0. Proof bounded c on compact minYy..maxYy; affine p(t)=Y+t(y-Y), stateW=(u(p),v(p)), derivative norm <= |y-Y|(1+|C|)||W||, Grönwall0..1. Handles both directions. No assumed explicit ODE expansion.
- `modalPotential (lam:=lam) N n y = ((signedFrequency (N+1) n)^2-lam/y²: R):C`. No f parameter on this definition.
- `maassCoefficient_second_eq` actual PDE gives a_n''=potential*a_n.
- `maassCoefficient_cauchy_zero` line107: actual coefficient value and derivative0 at onepositiveheight implyboth0allpositiveheights.
- `mass_eq_zero_iff_slice_zero`: normalized physical squared mass M(y)=0 iff original f(x+iy)=0 forallx. Actual continuity/nonnegativity+interval positivity and periodicrepresentatives prove endpoints/fullline.
- `slice_zero_of_coefficients_zero`: actual Parseval reconstructs wholezero slice.
- `not_all_coefficients_zero`: full all-height zero coefficients contradict f!=0.
- `exists_nonzero_modal_cauchy`: EVERY positiveheight has an index withnonzero valueORnormal derivative.
- `coefficient_zero_of_slice_zero` directactualintegral.
- `exists_nonzero_in_height_band`: every nonemptyopenpositivebandhas actualnonzero sourcepoint. Otherwisecoefflocally0nearbandmidpoint->bothCauchydata0contradiction.
- `exists_mass_pos_in_height_band` samewithM>0.
- `flux_zero_of_slice_zero`: wholezero sourcevalueskilloutgoingΦ, evenifnormalderivativesnot0.
- `boundaryForm_zero_of_slice_zero`: literalFouriertrace0killsactualBesselboundaryform.

For originalexceptional mu in Ioo0(1/4):
- `hyperbolic_tail_mass_pos` line222: forallY>0, int_{Y}^infty M(y)/y²dy>0. Originaltailintegrability; zero nonnegativeintegral -> a.e0 -> actualcontinuousweightedM0onopentail, contradictpreviousbandnonvanishing.
- `exceptional_not_zero_slice`: wholezeroslice atY wouldkillΦYandBY. Originalexisting fullidentity is -ΦY+(mu-1/4)inttailM/y² = BY+sum modeSquareTail>=BY. Strictpositive tail makes leftstrictnegativeifΦY0;right>=0ifBY0. Contradiction. Boundaryformnotassumednonnegativeongeneraltraces!
- `exceptional_slice_mass_pos` line256: M(y)>0 atEVERYpositiveheight.
- `exceptional_exists_nonzero_on_slice`: actualsourcehasnonzerovalueeveryheight.
- `exceptional_compact_slice_mass_floor` line269: forall0<a<=b,existsd>0,forallIccab,M>=d,usingactualmasscontinuity+compactminimum.
- `exceptional_density_pos_in_unit_period`: identitycosetnormSq<=D plusunitDperiodicity producespositiveDpointinIcc01everyheight.
- `exceptional_separated_directions_every_height` line288: everyy>0hasx inIcc01andt withDpositivebothandnormalizedsourcechord²>2. Usesproducedbasepoint+previousactualzeromeans/negativecorrelation, no suppliedpositivebasepointpremise.

## Crucial limits
Wholezero horizontaltrace is STRONGER than havingacommonflatnode. Positive integrated M is NOT pointwise Dzero-freeness, reciprocalamplitudefloor, currentpositivity, or flat-nodeexclusion. A whole bandofZERO CURRENT remains UNEXCLUDED. No generalelliptic UCP/sourceanalyticity or explicitBesselsolutionformula wasassumed. CurrentquartercomparisonandindependentfullXioccurrenceOPEN. Do not claimprogressprovedRH orSelberg gap.

Initialsearchinvestigatedzero-currentbandexclusion. No applicableMaassnodalcontinuationfound; usefulactualPDEclosure wasmodalCauchyuniquenessandwhole-sliceDirichletexclusion. The source-onlyboundaryformandactualtailequationmakeDirichlettracealoneenoughintheexceptionalrange. Keep distinctionexplicit.

## Audits ALL PASS
Scratch `/tmp/sqb21_slice.lean`,log`/tmp/sqb21_slice.log` andcanonicalsource`/tmp/sqb21_slice_source.log` no warnings. Preflightsoleleafstale`/tmp/sqb21_slice_preflight.log`. Final `lake build GaloisForLFunctions.RHTower.SelbergMaassSliceRigidity` compiledonlyleaf3.6s,8821dependencygraphjobsotherscached;`/tmp/sqb21_slice_build.log`. ReplayedEvenL2LogUnitaryringinfo iscachednotfailure. Nofull/umbrellabuild.
20/20axiom inventories onlypropext/Classical.choice/Quot.sound, `/tmp/sqb21_axioms.{lean,log}`,names`/tmp/sqb21_audit_names.txt`.20/20indexedexactlyonce`/tmp/sqb21_indexed_declarations.json`,umbrellaonce.Index/lintPASS`/tmp/sqb21_{index,lint}.log`(existing unrelatedlargefilewarnings).WhitespacePASS,ownedLean/Lakeprocesses0.Allcompiler/index/lintsessionscollected.

## Broad discovery
Fullmetadata OR/no per-modulecap searches:
`/tmp/sqb21_pde_broad.json`3217rows390modules(uniquecontinuation/Cauchy/elliptic/nodal/maxprinciple/zeroregion).
`/tmp/sqb21_coercivity_broad.json`2772rows685modules(Maass/spectralgap/Hardy/groundstate/quarter).
`/tmp/sqb21_uniqueness_broad.json`64rows25modules(Harnack/Hopf/Kato/modeuniqueness/decay/Besselpositive).
`/tmp/sqb21_slice_broad.json`10191rows2571modules(slicenonzero/positive/zerotrace/Cauchy/heightrigidity/vanishingslice/Dirichlet).
Metadataretrieval isnotallproofinspection. Actualreads:MaassCuspAutomorphicCorrespondence definitions, originalFourierModes/Parseval/BoundaryFlux/TailEnergy/BesselBoundaryForm/BoundaryTrace, congruence trace positivity, direction separation; MathlibGronwall/OpenPos/Deriv composition. WaveCauchyUniquenessandDeningerArithmeticLocalCauchyUniquenessnotappliedasMaassPDEtheorems.

## Verified API lessons
- Realparameter->complex HasDerivAt composition withrealinnerfunction needs `.scomp t hd`, not`.comp` (outer-targetscalarfieldmismatch). Pair via`.prodMk`.
- `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` despite name meansinitialLEFTendpointa0; takesContinuousOnIcc, rightHasDerivWithinAtIci onIco,initial0,normderivbound; returnszerowholeIcc.
- `dsimp[w]` alreadyreducesprod normtomax; subsequentrw[Prod.norm_def]fails. Use ring directly.
- Spacesaroundabsolutevaluefollowedmul: `|y-Y| * ...`, else `|*`tokenparseerror.
- When modalpotentialpush_cast changesNat(N+1)torNatN+1insidefrequency, normalizeODEhyp with `simp only [Nat.cast_add,Nat.cast_one] at h` beforelinear_combination. Actualproof `field_simp[hyc];...;linear_combination -h`.
- `MaassCuspEigenform`nonzero atf.2.1 concerns invariantfunction subtype. `apply f.2.1;apply Subtype.ext;funextz;change f.1.1 z=0` avoidszero-coercionmismatch.
- `push Not`, notdeprecatedpush_neg.
- `MeasureTheory.Measure.eqOn_open_of_ae_eq` namespace includesMeasure; args aeeq,isOpen,continuousOnF,continuousOnG. `hall hy` rhs function0evaluate; `Pi.zero_apply`neededforsimpfalse.
- `Filter.EventuallyEq.deriv_eq` and `.eq_of_nhds` verified.
- ActualBesselseamnamespace `SelbergBesselModes.seam`, definedSelbergBesselAdverseModes. `boundaryForm` istsum seam*normSq(formTrace.val n); change directlytomaaassCoefficientat exp(logy),simplifyexp_logandcoeffzero.
- `mass_hasSum` isSelbergMaassFlux, notjustMaassParseval. `hm.unique hasSum_zero` givesmass0.
- `maass_flux_boundary_identity` exactsourcebasedboundarysquareidentity fromMaassBoundaryForm;modeSquareTail_nonneg publicthere.
- `normSq_le_density` identitycoset theorem inCongruenceTrace. `density_slice_periodic` fromRegularizedCusp.

Fullgoalstill originalsource -> independentcurrentcomparisonORfullXioccurrence ->criticalclassification ->RH. Usefulfuturework must addressremainingcurrent-flatnodes/quantitativecomparisonoroccurrence, notmistakepresentintegratedmasspositivityforcurrentpositivity.