# PW-B actual Gamma signed endpoint and reconstruction defect — audited 2026-09-11

Active goal remains unconditional closed Lean RH through PW-B; RH NOT proved. Previous turn is verified progress. Chain: literal PW response -> FE partner imbalance -> positive Deninger reflect-gauge Ward transmutation -> independent source-forced fixed-grade balance -> RH. Source-specific global logarithmic-current admission and spectral Ward identification remain open; zero source mass is not RH balance.

## New completed leaf
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusSignedEndpoint.lean`,402lines,22publictheorems1definition. Imports GammaMobiusGlobalAdmission, DeningerMobiusAbel, DeningerMobiusHarmonicZero. Umbrella wired after GlobalAdmission (~15228, may shift). Card `docs/drafts/pipeline/3-formalized/pw-b-gamma-signed-endpoint.md`; artifact `.../1-in-progress/pw-b-gamma-signed-endpoint-searches.json` contains4partialdeepsearches, method audits and recent broad arXiv inspection. Attack card iteration13 audited, frontier PW-B updated, STATUS route-independent reconstruction/interchange constraint added, prior global absolute-admission card updated with actual signed successor.

## Mathematics
Q(x)=sqrt(x)e^-x for x>0. Original M(x)=Sum mu(n)Q(nx). Measure is Lebesgue dx on Ioi0. The previous leaf proves divergence of the ORIGINAL sum of atom L1 norms at coefficient b0; it does not imply nonintegrability of signed M.

New public `pwGammaRaySource_adjacent_norm_le`: for any realr>0,x>0,
 norm(Q((r+1)x)-Q(rx)) <=(1/r+x)*norm(Q(rx)). Direct square-root/exponential factorization, no Schwartz premise: sqrt(r+1)-sqrt(r)<=sqrt(r)/r, 0<e^-x<=1,1-e^-x<=x. Q first moment integrable, integral x|Qx|=Gamma5/2. Exact Q mass Gamma3/2 from parent. Dilation Jacobian gives `pwGammaRaySource_adjacent_integral_norm_le`: integralnorm difference <=(Gamma3/2+Gamma5/2)/r².

Define `pwGammaMobiusAbelAtom n x`=S(n)*(Q(nx)-Q((n+1)x)), whereS(n)=Sieve.mertensM n andS0=0. Each atom integrable; sum of atom norm integrals summable by existing UNCONDITIONAL `deningerMertensM_invSq_summable`: Sum|S(n)|/n² <infinity. Pointwise series also summable using Q's inverse-square bound at n andn+1. No numerical experiment or RH bound.

`pwGammaMobiusAbel_finite`: Sum_(n<N) Bn=Sum_(n<=N) mu(n)Q(nx)-Q(Nx)S(N), valid allN,x. `pwGammaMobiusAbel_boundary_tendsto_zero`: terminal->0 at eachx>0 from|S(N)|<=N+1 andQinv². `pwGammaMobiusPreimage_eq_abel`: actual M=fullAbelsum onpositive ray. `pwGammaMobiusPreimage_integrable` at273 proves signed M inL1 atb0. No stronger source-class assumption.

`pwGammaRaySource_integral`: complex integralQ=Gamma3/2 cast. `pwGammaMobiusAbelAtom_integral` exact =Gamma3/2*S(n)/(n(n+1)). Admitted Bochner interchange reduces source mass to harmonic limit. Existing `deningerHarmonicLimit_eq_zero` uses zeta pole and justified Abelian limit. `pwGammaMobiusPreimage_integral_zero` at307: integralM=0. Existing actual rightinverse gives functional nontriviality.

## Full reconstruction anomaly (new strongest positive survivor)
Z M(x)=Sum_(n>=1)M(nx) is the previously proved actual reconstruction Q(x). New `pwGammaMobiusPreimage_dilation_integral_zero`: everyrealr>0 has integralM(rx)=0. `pwGammaMobiusReconstruction_integrable` and `_integral`: ZM inL1, integralZM=Gamma3/2>0.
`pwGammaMobiusReconstruction_integral_defect` at343:
 integral ZM - Sum_(n>=1) integral M(nx) =Gamma3/2 (complexcast).
Both input and output integrable, every dilation term integrable, but sum/integral interchange FAILS with exact fixed defect. `_not_summable_norm_integrals` proves the reconstruction term norm integrals nonsummable; otherwise Bochner interchange contradictsGamma positivity.
`pwGammaMobiusPreimage_integral_norm_pos`: integralnormM>0. If zero, dilation gives allreconstructionnormintegrals0, contradictingnonsummability. Thus actualM represents a nonzero L1 class, with zero signedmass.
`pwGammaMobiusSignedReconstruction_closed` at386 is premise-free and packages integrability, zero mass, functionalnontriviality, positivefiniteL1norm, reconstructed integrability/Gammamass, allpositivedilationzeromasses, reconstructionnormnonsummability. It does NOT assert actualE current globaladmission, globalparameterderivative, negativebpowergain, criticalfiniteenergy, spectralidentification orRH.

## Validation complete
Scratch `/tmp/pwb-gamma-signed.lean` passed, directleaf `lake env lean` passed. Final targetonly `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusSignedEndpoint` passed(99sec,10975jobs mostlycachedreplay). All22publicaxioms in`/tmp/pwb-gamma-signed-axioms.lean` passed, exactlystandard propext/Classical.choice/Quot.sound. Formal lintpassed;indexgeneratedLEAN_API/GAPS/OVERVIEW with22theorems1def. All23publicnamesunique;taskscopeddiff/newfilewhitespacecheckspassed. Umbrellawired,no full/umbrellabuild,noaxioms/sorry/admit/computations, nocommit/push. AllownedLean/researchprocessesfinished. Logs`/tmp/pwb-gamma-signed-{scratch,direct,build,axioms,lint,index}.txt`.

## Useful Lean details
- Square-root increment: sq_sqrt r, sq_sqrt(r+1), monotonicity; (b-a)(b+a)=1 implies(b-a)*a<=1; multiply bysqrt r. To replace RHS((b-a)*a)*a by(b-a)*r use rw[mul_assoc,←pow_two,ha], NOT rw[←ha] (rewrites r inside roots).
- Moment integrability: explicit `IntegrableOn.congr_fun (h.const_mul r⁻¹)` avoids failed convert on IntegrableOn/Integrable. integral_mono_ae target may retain Pi subtraction/addition; `change` to explicit pointwise inequality, rw[←add_mul], exact bound.
- Finite Abel uses `Finset.sum_range_by_parts F G (N+1)`, converts difference sum to NEGATIVE newAbelsum, final `linear_combination -hparts` (positive sign failed).
- For integral of unapplied atom, `change (∫x, explicit body)=_` before rw[integral_const_mul]. After both dilation identities, simp only[mul_zero,pwGammaRaySource_integral,...] to rewrite BOTH Gamma integrals; rw alone rewrote first only. Supply complex natural denominator nonzero proofs tofield_simp; thenring.
- `Complex.ofRealCLM.map_tsum deningerMertensHarmonic_summable` casts exact real harmonicsum. `deningerHarmonicLimit` is definitionally SumS(n)/(n(n+1)).
- Build commands must use workdir `/Users/michael/Documents/code/hgt/formal`; writes/reads withformal/ prefix must use repo root. Avoid combiningrootrelativewritesandLeancommandunderwrongcwd (diagnosedtwo shellmisroutes).

## Next actual logarithmic-current attack (paper target, NOTproved)
E(x)=Sum -mu(n)log(n)Q(nx)=coefficientderivativeM_b|0=J M, already pointwiseadmitted. Need GLOBAL L1 and integral. Do NOT infer E admission or zero mass from M.
Apply finite Abel to F_n(x)=-log(n)Q(nx) with SAME S(n), avoiding a new log-Mertens sequence. New atom:
 S(n)*(log(n+1)Q((n+1)x)-log(n)Q(nx)).
Split into S(n)*log(n)*(Qn1-Qn)+S(n)*(log(n+1)-logn)*Qn1.
Its norm integral <=|S(n)|*(C*logn+Gamma3/2)/n², C=Gamma3/2+Gamma5/2, since logincrement<=1/n. Need Sum |S(n)|logn/n²; `Sieve/MoebiusHarmonicArbitraryLogRate.lean:61` deningerMertensM_log_pow_rate or `Sieve/MoebiusHarmonicLogRate.lean:65` four-log version makes this <=B/(nlog³n), and existing summable_one_div_mul_log_three gives a shiftedtail. Retain terminal logN Q(Nx)S(N), which vanishes usingQinv² andlogN/N->0 or strongerGamma bound.
The candidate integrated E value isGamma3/2, notzero: `Sieve/MoebiusLogarithmicNormalization.lean:346` public `tendsto_moebiusLogHarmonicPartial_one` gives partials of -mu(n)logn/n ->1. Definition`moebiusLogHarmonicTerm` at21=-mu logn*n^-1, partial atrange(N+1) at25. Private summable_deningerHarmonic_logIncrement there provides a method but is NOT callable. Its proof uses inverse-logharmonicpartial decay and logarithmic increment. All globalcurrentterminal/interchange steps remain to prove.
If EglobalintegralGamma is proved, everyindividualLambda-weighted Mdilation still hasintegral0, giving actualEuler-currentmassdefectGamma as well. This would identify complete source boundary contribution, not automaticallycloseRH. Source/spectralparameteridentification remainsrequired. Negative realb signedL1 admission approaching -1/2 needs strongerpowercancellation (proposed MellinGamma(s+1/2)/zeta(s+b), initial Re(s)>-.5, Re(s+b)>1); PNTstrength endpointb0doesnotyieldthis.

## Searches
Fourdeepqueries: signedAbeldilationGammaendpoint, adjacentdilationwindowintegral, signedAbelzeromassharmoniclimit, logarithmicMobiuspartialsuminv². Allpartial; candidate/sourcearguments/ingredientsinspected, mostlyunrelatedmethodspluscurrentAbel lemmas. Source-textpasses located exact usableproofs above. BroadarXivqueriesrenewal/adhesion/fragmentation/avalanche inspectedabstracts2607.08213(Jul9,viscoelasticcontactlessadhesion) and2609.03368(Sep3,targetfragmentationHERA/EIC). Noforeignphysicaltheorem transferred;modelhypothesesabsent. Oldrenewal/avalanchehits ignored. No externalclaimusedasanaxiom.

Previous memory `mem:rh/pw_gamma_exact_global_absolute_admission_2026_09_11`.