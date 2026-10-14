# Actual WL critical residue solved

Active unbudgeted experimental OpenAI/math goal remains active,not complete. Scope all16 live+23 candidate routes in docs/reports/rh-current-frontier-map.md and broader corpus applications. User: take proven upstream/corpus proofs as proven; do not pivot from unanswered native problems. Build missing theory. No cards,added axioms,sorry,heartbeat increases,numerical experiments,full/umbrella builds,commits/push. One foreground Lean process per agent. Final plain lake --old env lean leaves. No subagents authorized. hgtl7 previously applied; scientific novelty unassessed.

Current goal turn PROGRESS: six new leaves/25 public theorems solved the actual critical logarithmic residue problem. All six final plain audits warning-free,all25 axiom audits standard-only,25/25 corpus registrations,unique umbrella imports,current own objects and direct dependencies. Audit tmp/hgt-openai-math/critical-residue-audits.json. Plan wl-critical-residue-next.json SOLVED. Manifest all-route-applications.json has wl_critical_residue_batch; WL ledger line46 updated. No overall goal completion claim.

Native results for actual D=sourceOperator-arithmeticOperator:
- MemWeakSchattenClass(1/2)D; explicit admissible bound18/(n+1).
- HasSchattenLogResidue(1/2)D(1/Real.sqrt6),meaning sum_{n<N}approxNumber(D,n)^(1/2)/log(N+1) tends1/sqrt6.
- At every cutoff N+9,the singular-value half-energy minus literal coordinate half-energy lies in[0,1]. No sorting surrogate and no new realization premise.
- Every finite-prefix remainderD-differencePrefixN has the same residue and weak endpoint membership. Its every approximation number is <=that ofD.
- perturbedObservable(delta,circleCoordinate)-arithmeticOperator has the same critical residue for EVERYreal delta. Prior proven lag law changes by delta*N/(3*sqrt(N+3)),with sqrt-scaled limitdelta/3. The residue therefore misses this boundary charge.
- Do not call this an actual Dixmier trace without a functional-calculus/measurability interface; exact existing HasSchattenLogResidue is proved.

Six leaves:
1 HTGeometry/LpDiagonalPartialEnergy.lean (namespace GaloisForLFunctions.HTGeometry),4theorems. Exact truncation p-energy; each truncation approximation number <=full; coordinate prefix energy<=singular prefix energy; for0<p<=1,the reverse bound costsN*norm(discarded tail)^p. Key route:finite-coordinate projection is contraction;finite-rank truncation total energy equals its coefficient energy using prior LpDiagonalSchattenEnergy; approximation-number additive inequality and Real.rpow_add_le_add_rpow. No new sorting infrastructure needed.
2 HTGeometry/HarmonicResidueShift.lean (namespace GaloisForLFunctions),3theorems. Ratios log(n+k)/log(n+l)->1; harmonic coefficient law transfers to denominatorlog(N+1); every fixed coordinate shift preserves logarithmic residue,even for signed sequences.
3 RHTower/PrimePowerLogarithmicDensity.lean(namespaceRHTower),4theorems. Proper prime-power reciprocal weights summable;prime reciprocal sum/log(N+1)->0;all prime-power reciprocal mass/log(N+1)->0;all fixed index shifts too. Reuses summable_properPrimePow_log_rpow(x=1) from PrimeLagLandauPrimesOnly and tendsto_primeRecipSum_sub_logLog from MertensSecondPrimeRecipSum. Proper-power log lower bound log2>0 pays reciprocal comparison.
4 HTGeometry/SchattenLogResiduePowerFiniteRank.lean(namespaceGaloisForLFunctions.HTGeometry),3theorems. Finite-rank perturbations change positive-p energy prefixes by bounded amount and preserve exact logarithmic residue for EVERYp>0. Generalizes existing p=1 result using index interlacing and monotonicity of positive powers.
5 RHTower/PaperLagCayleyCriticalEnergy.lean(namespaceRHTower.PaperLagCayley),5theorems. Native sqrt coefficient bounds,weak endpoint membership,energy gap[0,1],normalized gap->0.
6 RHTower/PaperLagCayleyCriticalResidue.lean(same namespace),6theorems. Actual coordinate residue1/sqrt6;actual operator residue;finite-prefix residue;prefix approximation-number contraction;prefix weak membership;boundary-curvature perturbation residue invariance. Private bulkPhaseGap uses the actual source-minus-arithmetic gap with base phase-1. Its center-squared complex coefficient->1/6. Square root and harmonic transfer give residue1/sqrt6. Full source equals this bulk outside prime powers;absolute half-energy difference<=44/(n+3) on prime powers and0elsewhere. All source/trivial-zero contributions retained.

Validation/freshness:
Initial six leaf+25standard-axiom audits passed in session73583; registrations15403 passed25/25. Final freshness detected two PREEXISTING September22 clean-source/object timestamp mismatches: RHTower/DiagonalEllTwoOperator and RHTower/SchattenLogResidueFiniteRankPerturbation. Both objects explicitly refreshed WITHOUT source edits (first93850=0;second in3996). Affected new objects refreshed and all six plain audits plus25axiom audits rerun successfully under guarded foreground session3996=0. Final registration metadata reused since all source hashes unchanged;freshness checks now no stale direct dependencies. Previous audit saved critical-residue-audits-before-dependency-refresh.json. Index91231=0. Global lint32113=1 ONLYtwo foreign concurrent unwired modules:PaperWoldDirectedCovarianceEnergy andSquareSampleObserverJetOneSidedStrip,plus existing large-file warnings. No owned lint error;do not claim entire repository clean.
All owned sessions terminal. Removed/tmp/wl-residue-api.lean,/tmp/wl-critical-final.py,/tmp/wl-critical-register.py,/tmp/wl-critical-refresh.py;integration helper self-removed. Retain/tmp/wl-critical-residue-axioms.lean as audit witness. Own sources/wires/index current. No commits/push.

Toolchain lessons:
- Opening GaloisForLFunctions then Complex can resolve a different Complex namespace. Use open _root_.Complex to expose I andnorm_ofNat reliably.
- Normalize limit constants with rw[sub_zero] BEFORE convert;ring on equality of nhds can emit a misleading failed-ring info despite succeeding. This was cleaned,final logs empty.
- Actual Filter.tendsto_add_atTop_iff_nat;Filter.Tendsto.atTop_add with a constant Tendsto. No .atTop_add_const.
- Real.log_nonneg requires1<=argument; use norm_cast;omega fornat shifts,not positivity.
- abs_sub_le a b c boundsabs(a-c). To boundabs(A-B) byabsA+absB,useabs_sub_le A 0 B.
- Explicit calc/add_le_add plusring handles44/den=22/den+22/den more reliably thanlinarith over divisions.
- Finite partial-sum linarith needs both RHS sums changed to schattenPowerPartialSum,not onlyLHS.

NEXT ACTIVE NATIVE PROBLEM: tmp/hgt-openai-math/wl-relative-determinant-next.json. This remains unproved. Must identify actual infinite-dimensional RHTower.fredholmDetOp,not stop at a scalar infinite product. Relative unitaryV=sourceOperator*arithmeticOperator.adjoint. Phase lift theta_n=2*(arctan(source_n)-arctan(arithmetic_n)),strictlynegative fromindex9. Absolute tail sum<=1/[3(N+11)];show no wrapping and nontrivial tail determinant. Exact Fredholm determinant formula from exp(i*sumtheta),with trace-class relative operator and quantitative cutoff.
Additional native boundary target:full relative determinant under coordinate-zero perturbationdelta should multiply by realCayley(source0+delta)/realCayley(source0). Prove nonzero full determinant,cancel,and use Cayley injectivity:full determinant injectiveindelta,while critical residue unchanged. Tail determinants aftercutoff>=9 cannotdetectcoordinatezero;do NOT substitute them for full determinant in this claim. Keep literal operator identification.

New proven inputs located and actual proofs read for determinant:
- RHTower.realCayley_eq_neg_exp_two_mul_I_arctan inRHTower/KapustinGaugeSmirnovCollision.lean:83 givesC(x)=-exp((2arctanx)*i).
- RHTower.DQPT.dqpt_arctan_lipschitz inRHTower/DQPTStateError.lean:86 givesabs(arctanx-arctany)<=abs(x-y). Exact namespaceverifiedsource;nextLeanAPIprobe beforeusing. No need reprove either.
- Search wl-relative-phase-search.json partialtrue,total44744 becauseANY;relevant exact hits read,not exhaustive applicability claim.
- Read MertensClockRelativeDeterminant.lean:35-73,101-112. fredholmDetOp b T=entireDet2(coordMatrix b T)(-1)*exp(opTraceT);coordMatrix_apply=inner(bi,Tbj).
- Read ArithmeticDilationTraceClass.lean:173-218,235-286. absoluteMatrixOperator_diagMul_eq_diagonalOperator identifies nuclear and literal bounded diagonal; toOperator_diagMul_apply_basis gives HS realization.
- Prior read ReciprocalRecoveryFactorization.lean has entireDet2_diagMul_neg_one and real exponential fredholmDet_recovery;generalize global identification to complex imaginary phase as needed. Other exact sources/search plans preserved in wl-relative-determinant-next.json.

Prior batch memory mem:research/openai-wl-schatten-2026-10-13 has27theorems/5leaves exactSchatten spectrum(p>1/2),trace norm(0,4],trace cutoff1/[3(N+11)],composite/prime complex channel coefficients. Its formerly proposed critical residue is now SOLVED by this batch. Relative determinant remains active. Overall all39route scope remains intact.
