# Batch44 fully audited; broad user goal ACTIVE

55 new theorems +9 definitions /10 modules. Cumulative2065 theorems /263 modules. Evidence /tmp/hgt-gomes/fortyfourth/progress.json and audit files. Previous mem:research/gomes-arxiv-corpus-fortythird-batch-2026-09-10. Root /Users/michael/Documents/code/hgt/formal.

All10 scratch sources passed one combined `LEAN_NUM_THREADS=1 lake env lean /tmp/hgt-gomes/fortyfourth/ClockBatch.lean`, session81876 terminal0 with no warnings/errors. API check output in log preserved. All individual `lake build MODULE` sequential commands passed, build runner session68205 terminal0. Final combined API/#printaxioms audit session40184 terminal0: all64 declarations closed, only propext/Classical.choice/Quot.sound, no added axioms. Global formal lint PASS (session45456); all64 names unique and indexed; targeted git diff whitespace PASS.202 earlier recorded source hashes unchanged. No own active Lean/Lake processes. No full or umbrella builds. All10 modules wired exactly once into HTGeometry.lean. No commits/push. No subagents. Goal remains ACTIVE at checkpoint.

## Result
Let D_N be literal GammaFactorialFock.fockShiftMatrix N. Its full matrix commutant C_N has a unique finite symbol c:FinN→complex, with M=sum c(k)•D_N^k. Includes N0. Exact polynomial map kernel is (X^N). This map is the TRANSPOSE of EXISTING TruncatedToeplitz.toeplitz N p, so actual Fock polynomial calculus equals existing geometric Toeplitz calculus.

For N=n+1, C_N is algebra-equivalent to EXISTING TruncatedArcAlgebra complex n = complex[X]/(X^(n+1)). No fabricated new geometric carrier. Clock variable is quotientX. Reverse top-column observation equals existing truncatedArcLinearEquiv coefficient chart. detM=p(0)^N, charpolyM=(X-Cp(0))^N, dimension(C_N)=N for positiveN. Invertibility iff N0 OR p(0)nonzero. Geometric augmentation determines determinant and actual matrix invertibility.

D_N alone generates C_N as a complex associative algebra; C_N commutative, self-centralizer, equal bicommutant. Literal fockTaylorMatrix N z maps from the truncated exponential polynomial. In existing arc coordinates its kth coefficient=z^k/k!. Geometric augmentation1 and arc multiplication realizes Taylor addition law.

Sharp supplied-group boundary: every symbol acts on constant jets by p(0). In dimension2, clock commutation and fixing all constant jets iff UNIQUE z with M=fockTaylorMatrix2z. In each dimension n+3, explicit H=I+D² is a UNIT, commutes with D, fixes every constant jet, yet H differs from fockTaylorMatrix(n+3)z for EVERY complexz. A theorem produces actual Units witness. This is an extra automorphism beyond the supplied one-parameter Taylor group, despite normalization and constant preservation.

Paper scope: finite concrete extension of symmetry-versus-supplied-structure distinctions in arXiv2607.24901v1. Full clock algebra is an existing geometric arc algebra, whereas supplied Taylor group is smaller from dimension3. This is not a formalization of full gauge categorical theorem. Keep associative algebra versus one-parameter group distinct. arXiv2509.25276v7 withdrew earlier equivalence claims. arXiv2404.10461 restricted common-connection universality supplies no arbitrary Schwartz/Hilbert conjugacy.

## Modules / API
All namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock, path formal/GaloisForLFunctions/HTGeometry.
1 GomesFiniteFockCyclicClock: def gomesFiniteFockCommutant N:=Subalgebra.centralizer complex {D_N}; _mem_iff; gomesFiniteFockShift_pow_apply: (D^k)ij=if i+k=j then1 else0; _top_cyclic: D^(n-i)e_n=e_i; gomesFiniteFockCommutant_top_injective.
2 GomesFiniteFockPolynomialSymbol: gomesFiniteFockPolynomialHom N:complex[X]→algMatrix, toFun(transpose toeplitz). _apply upper coefficient formula; _X=D_N; _mem; _top reverses coefficients using Fin.rev; _eq_aeval; def gomesFiniteFockSymbolHom to carrierC_N.
3 GomesFiniteFockSymbolClassification: def gomesFiniteFockCoefficientPolynomial N c=sum FinN monomial(k,c_k); _coeff; gomesFiniteFockSymbol_reconstruct from reversed top column; gomesFiniteFockSymbolHom_surjective allN; gomesFiniteFock_commute_iff_polynomial; gomesFiniteFockPolynomialHom_eq_iff coefficient equality belowN; gomesFiniteFock_commute_iff_unique_symbol.
4 GomesFiniteFockTruncatedKernel: _eq_iff_dvd p-q byX^N; _zero_iff; _ker=Ideal.span{X^N}; gomesFiniteFockCommutant_commute.
5 GomesFiniteFockTruncatedArcEquiv: def gomesFiniteFockArcHom n quotient lift toC_(n+1); _mk,_injective,_surjective; def gomesFiniteFockArcEquiv n; _mk transpose existing toeplitz; _variable actualD; _top existing coefficient chart reversed.
6 GomesFiniteFockSymmetrySpectrum: polynomialHom_upperTriangular,diagonal,det,charpoly,isUnit_iff positiveN,isUnit_iff_all includingN0; arcEquiv_det,isUnit_iff; commutant_finrank.
7 GomesFiniteFockTaylorArc: polynomialHom_coefficients (actualfiniteDsum), gomesFiniteFock_commute_iff_unique_clock_polynomial; def gomesFiniteFockTaylorSymbol Nz; _matrix literalTaylor; def gomesFiniteFockTaylorArc nz; _matrix,_coefficient,_augmentation,_add.
8 GomesFiniteFockExtraAutomorphisms: def gomesFiniteFockQuadraticShear N=polyHom(1+X²); _eq=I+D²; _commutes; _isUnit positiveN; _constant fixesallscalarjets; _ne_taylor alln+3/z; gomesFiniteFock_missing_taylor_automorphism providesactualunit.
9 GomesFiniteFockAlgebraGeneration: clock_mem,eq_adjoin,centralizer,bicommutant.
10 GomesFiniteFockConstantJetBoundary: polynomialHom_constant, _fixes_constants_iff; gomesFiniteFock_twoJet_taylor_iff; _twoJet_unique_taylor_iff.

## Proof notes / pitfalls
Cyclic top vector avoids Toeplitz recurrence duplication. C_N matrices agreeing on top vector agree everywhere by commuting powers ofD. Polynomial from reverse top column realizes any column. Exact toeplitz kernel via first row and Polynomial.X_pow_dvd_iff. Existing truncatedArcLinearEquiv detects quotient equality. All endpoints unconditional (arbitrary actualmatrix iff/structures); no extra mathematical premises. No omega/norm_num/lia/decide/native_decide in new sources. fin_cases used for exhaustive Fin2 case split, simp symbolic coefficients, no numerical experiments.

Must `open Matrix` for `*ᵥ` notation. In top_injective `change E.val *ᵥ coordVec n = F.val *ᵥ coordVec n at h` before rewrites. Use explicit M,j,i in backward fockMatrix_mulVec_coord rw. Rewrite equivalent ite propositions with simp only, not rw causing dependent Decidable mismatch. Polynomial.coeff_X uses 1=n orientation; compose eq_comm.trans he. Polynomial.coeff_one needed explicitly in quadratic shear contradiction. Polynomial.finsetSum_coeff current name (finset_sum_coeff deprecated). Fin.sum_univ_eq_sum_range requires explicit function AND N. Mathlib names used verified in Api.lean/ApiAudit.lean and final audit. Namespace parser works on explicit full namespace.

## Next priority: reconstruct clock from one Taylor value / general invertible formal coordinate
UNPROVED, NO next-topic Lean code written yet. Conjecture: for nonzeroz, full commutant of SINGLE fockTaylorMatrix N z equals C_N; at z0 it is top. Retain all dimensions includingN0/N1. Build missing finite formal-series evaluation/substitution bridge instead of pivoting.

Stronger mechanism already in Mathlib: PowerSeries.substInvOfIsUnit, constantCoeff_substInvOfIsUnit, HasSubst.substInvOfIsUnit, subst_substInvOfIsUnit_left/right. For formalP with constantCoeff0 and invertible coeff1, inverseQ has Q.substP=X and P.substQ=X. After finite evaluation this should recover D from ANY such symbol, not just exponential. Read Substitution.lean548-599 (conditions included); rest only declaration rg, no next-topic API probes yet. Do not assume exact argument order until scratch #check/have probes.

Need finite PowerSeries→algebra hom to new arc/C_N and substitution compatibility. A natural definition maps F to polynomialHomN(PowerSeries.trunc N F). Trunc itself not multiplicative, but composing with exact moduloX^N matrix map is. Prove using coefficient identities already in Mathlib.PowerSeries.Trunc and the new polynomialHom_eq_iff. Then H(F.substG)=aeval(HG)(truncN F) when G has constant0; requires tails/order or finite substitution sum. This infrastructure is essential, build it. Could also connect infinite formal-series polynomial operator restriction to finitejets, but search first for existing bridge.

Explicit logarithm source ALREADY FOUND:
- RHTower.formalLog_subst_exp_sub_one at SourceNormalClockCurvatureLaw.lean335: (PowerSeries.log rational).subst(exp rational-1)=X.
- RHTower.formalLog_subst_formalMultiplicativeExpCoordinate at379: rescaled rational version=a•X.
- RHTower.derivative_formalLog_mul_one_add_X at325.
- GaloisForLFunctions.HTGeometry.derivative_logOf in ProjectiveHorizonLogPotential.lean498, arbitrary char-zero field: derivative(logOf f)=inversef*derivativef with constcoefff1. one_add_X_mul_derivative_log at487. Use this to generalize explicitlogexp to arbitrarycomplexrescaling, then finite log(T_z)=zD. Mathlib.PowerSeries.Log does not itself prove log-exp inverse. Do not duplicate rational source theorem.
- PowerSeries.derivative.ext atDerivative.lean139 compares derivative and constcoeff, requiring CommRing/IsAddTorsionFree.

Next-topic source reads: Mathlib.PowerSeries.Log ALL101lines; SourceNormalClockCurvatureLaw310-410 plus namespace/import rg (591lines total); ProjectiveHorizonLogPotential478-530 plusnamespace/import rg (988total); Mathlib.PowerSeries.Derivative130-151 plusnames; Mathlib.PowerSeries.Substitution548-599 plusdeclarationrg; Mathlib.PowerSeries.Trunc declarations read43, nofullsource. Everything alreadyread in these regions; avoidreread. New names notyet scratchverified.

Search evidence in/tmp/hgt-gomes/fortyfourth:
- next-taylor-centralizer-search.json:deep30s partialtrue, all20 candidatelemmas +20sourcearguments reviewed, weak irrelevant hits.
- next-log-exp-lexical.json: logOf AND exp, nohits (too narrow); broadened via directPowerSeries.log source search.
- next-formal-log-source-search.json: log OR exp moduleSourceNormalClockCurvatureLaw, ALL13 hits reviewed, confirmedsource rational identity.
- next-nilpotent-lexical.json: nilpotent OR log moduleNilpotent had131eligible, onlyfirst20 reviewed and irrelevant; NOTexhaustive, superseded byprecisequery.
- next-log-owned-hits.txt / next-formal-log-hits.txt contain thousands of ordinaryreal/complexlog falsepositives; noclaim individuallyreviewedall. Exact PowerSeries.log/logOf hits filtered and led to two filesabove.
- Original current duplicatecheck fock-centralizer-current.json at/tmp/hgt-gomes returned0; priorbatch43nextfocksearch20+20 and24lexicalallreviewed, nofullfiniteclassification existed. Existingfiniteexp was reused, notduplicated.

Retain other candidate: all-scalings connection family aD-M_A includinga0 and actualheatShiftPoly t0. Prior infiniteD/reflection/constant-line and current finiteFock classifications COMPLETE; avoidduplicating.

## Operational state
44audit scripts copied/adapted43 in/tmp. install_verified_batch checks ClockBatch API-output log noerrors/warnings and source/bodyhashes. prepare_audit produces all64names; build_modules sequentialskipalreadyexit0; finish_audits combinesApiAudit and#printaxioms, refreshesindexONCE thencheckseverymodule. finalize_batch prioris43. finish_metadata recordsmathstatus/nextcandidates. Every process terminal; do not poll vanishedoldhandles. During44 interruption handle4168 missing, authoritativeps noLean/logerrors, so repaired source; later81876pass. No staleprocesses.

Global lint initially flagged five unrelated unreachable modules (Borisov determinant4 plusFokas polynomial1). Allwerewiredbyotherwork; recheck45456passed. Didnoteditunrelatedsources. Finalpriorhashcheck202unchanged. Last10newhashes build-status.json.

Continue directLean only; no cards/docs. User mandates one foreground Lean/build process peragent, nofullbuilds, scratch first, targetedindividualfinalbuilds, wireumbrella, no addedaxioms/gaps/numericcomputations, do notdiscardinterestingmissinginfra. No subagents absentexplicitrequest. update_plan unavailable; progressJSONtracksplan. Maintaincommentary≤60seconds. KeepgoalACTIVE.
