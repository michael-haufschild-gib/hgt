# Both constrained parity source kernels and independent joint moments

Goal ACTIVE, actual RH UNPROVED. Previous goal turn was progress (18 source-scalar/nonvanishing theorems). This turn adds15 audited public theorems in two wired named leaf builds. Full chain remains exact source → selected ground's signed forcing control → exclude unique possible zero constrained ground → all finite aperture positive floors → weighted pole exclusion → RH. No experiment, added axiom, oracle, subagent, or commit.

## Analytic source profile:5 publics,3defs
`RHTower.CCMRestrictedWeilPolarParitySourceProfile` imports prior `CCMRestrictedWeilPolarSourceNonvanishing`.
- `ccmPolarBoundaryArithmeticError a x`: A_a(x)=Epsi(exp(a-x))+EM(a+x).
- `abs_ccmPolarBoundaryArithmeticError_le`: on open aperture |A_a(x)|≤C_a=psi(exp(2a))+exp(2a)+log4+5. Uses actual psi_nonneg/psi_mono, positive exp, existing abs EM bound. All prime powers retained.
- `ccmPolarParityBoundaryProfile a r x`: K_r(x)=K(x)+(r:ℂ)*K(-x).
- `ccmPolarParityArithmeticRemainder a r x`: T_r=exp(x/2)A(x)+r exp(-x/2)[A(-x)+Delta(x)], Delta=B(a-x,a+x)-B(a+x,a-x).
- `ccmPolarParityBoundaryProfile_re_decomposition`: K_r.re=[exp(x/2)+r exp(-x/2)]B-T_r; true for all real r,x, with no sign assumptions.
- `abs_ccmPolarParityArithmeticRemainder_le`: r=±1, interior x implies |T_r|≤exp(a/2)[2C_a+log2]. This is a fixed-aperture finite bound for endpoint analysis, NOT the all-aperture positivity estimate needed for RH.
- `polarParityEndpointCoefficient_pos`: exp(a/2)+r exp(-a/2)>0 for both parities.
- `tendsto_ccmPolarParityBoundaryProfile_re_right`: each K_r.re→+∞ as x→a from below. Common B diverges, coefficient tends positive, and T_r bounded.

## Actual reflected source coupling:10 publics,2defs
`RHTower.CCMRestrictedWeilPolarParitySourceCoupling` imports profile leaf and existing `SuzukiTaCovarianceReflection` to REUSE actual `suzukiAperturePhysicalReflection` (no duplicate reflection implementation).
- `ccmPolarParityBoundaryDefect a r`: actual aperture d_r=d+r R_a d, d=prioractualsourceL²defect.
- `ccmPolarParityBoundarySourceFunctional a r`: G_r=F+r F.comp R on complete form domain.
- `ccmPolarParityBoundarySourceFunctional_eq_inner`: G_r(u)=<d_r,Ju>. Uses J R=R_a J, l2Reflection_symmetric, real scalar conjugation.
- `ccmPolarParityBoundaryDefect_coeFn`: actual d_r has AE cutoff coefficient K_r; preserve measure reflection explicitly.
- `ccmPolarParityBoundarySourceFunctional_eq_integral`: G_r(u)=∫cutoffK_r*Ju for ALL complete form u. Actual L² pairing supplies integrability.
- `ccmPolarParityBoundarySourceFunctional_on_parity`: Ru=r u with r=±1 gives G_r(u)=2F(u).
- `ccmPolarBoundarySourceFunctional_on_parity_eq_integral`: F(u)=1/2 ∫cutoffK_r Ju on pure parity, normalization retained.
- `not_ae_bounded_ccmPolarParityBoundaryProfile`: neither profile has essential upper bound.
- `ccmPolarParityBoundaryDefect_ne_forcing`: d_r outside EVERY two-pole vector (bounded continuous pole profile on compact aperture contradicts endpoint divergence).
- `exists_polarParity_boundarySource_ne_zero`: for EACH r=±1, exists actual constrained pure-parity form u with F(u)≠0. If G_r vanished on constraintsector, continuous annihilator theorem plus denseJ would put d_r in pole span. Choose constrained v with G_r(v)≠0, takeu=v+rRv, thenRu=ru andFu=G_rv≠0.
- `exists_polarParity_boundarySource_eq`: everyz:ℂ realized asFu in EACH constrained parity sector by scaling.
- `polarConstrained_jointBoundarySource_surjective`: u↦(F(u),F(Ru)) on complete constrained space surjectiveℂ². Evene hasF=(z1+z2)/2, oddo hasF=(z1-z2)/2, sumgivespair.

## Exact meaning / remaining goal
Parity cannot restore automatic source decoupling. Both constrained parity sectors have nonzero/surjective source coupling; original and reflected moments are jointly independent on their sum. This is NOT a theorem that the selected ground has nonzero moment, and does NOT exclude its forced equation. Mustuse actual variational minimizing equation+normalization with c=F(u)/(2sinh a+2ar). Universal linear signs or vanishing conditions on arbitrary constrained vectors fail even after choosing a parity. Common singular B plus bounded remainder is now available for that ground-specific comparison. Need new producer theorem, not another source/model or RH-equivalent premise.

## Files and audits
Formal card `docs/drafts/pipeline/3-formalized/weil-parity-source-kernels-and-joint-moments.md` containsdependency-closedpaperproofandconjecture/pivot/positivesurvivor. Activecard `1-in-progress/weil-gamma-pole-boundary-action.md` removesparityopenquestionsandkeepsground-specificcomparison. FrontierO anduniversalSTATUSstrengthenedcurrentstateonly.
Scratch `/tmp/hgt-parity-source.91OGyY/Profile.lean`, Physical.lean PASS. NamedfinalleafbuildsPASS6.8s/10s, bothwiredRHTower. Audit.lean prints all15 exactly [propext,Classical.choice,Quot.sound] andactualmathlibRH. Wholeformal lintPASS Lint.txt/.err withonlyexisting sizewarnings. gitdiff--checkPASS. AllownedLean/buildhandles terminal. No full/umbrella build. Defaultrefresh corpusresearchwasrequested atclose; see ResearchRefresh.txt.

## Current-toolchain lessons
`abs_sub_le` is3-argumenttrianglelemma, not|a-b|≤|a|+|b|. For nonnegativea,b useabs_le +linarith (or3argthrough0). `add_neg_eq_sub` unavailable; simp with←sub_eq_add_neg. Forreflectionpairing, implicitrw[l2Reflection_symmetric] failed; explicit congrArg of `(l2Reflection_symmetric d Ju).symm` succeeds. Negative AEcoefficient fromcomp_tendsto keepsFunction.comp; change BOTHsides explicitly to d(-x)=indicatorK(-x). Forparitylift u=v+(r:ℂ)•Rv, dsimp canexposescalarℝ andbreak map_smul. Splitr=±1 insideparityproofandkeepcast `((-1:ℝ):ℂ)` inchange; simplifyofReal_neg/ofReal_one before neg_one_smul/map_neg/abel. `(−1:ℂ)` isnotdefinitionallyidenticaltorealcast−1 inthatgoal.
A transient missingDirichletRigidity.olean occurred duringanotherwriter'srebuild; inspectionshowedfilealreadyrestored. Retriedfailedscratchafterexternalstatechanged, no duplicate/backgroundbuild. DirichletRigiditysourceismodifiedbyanotherwriter; notours. NoLeanprocessesleft.