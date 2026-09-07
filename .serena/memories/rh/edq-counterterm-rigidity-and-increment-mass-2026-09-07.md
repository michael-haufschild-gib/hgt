# EDQ exact mass and finite-energy counterterm rigidity

Persistent RH/EDQ goal ACTIVE, NOT achieved. Verified progress this turn; do not mark blocked for remaining mathematics. Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH. No numerical experiment justified or run.

## Completed bridge
formal/GaloisForLFunctions/RHTower/EulerDeletionCountertermRigidity.lean, namespace RHTower.DeletionCounterterm,143lines. Imports EulerDeletionQuotientHarmonicBound and Sieve.MoebiusHarmonicTailIdentity. Nine public theorems,two definitions,one private reciprocal-mass telescope.
- hasSum_mertensIncrement_mass37: N>=1, HasSum of (M(i+N)-M(N))/((i+N)(i+N+1)) equals -H_N. Genuine absolute real summability.
- harmonic_eq_neg_increment_mass50: exact full compensator.
- error_eq_compensated_quotient_mass57: N,n>=1, 1-F_N(n)=sum_{j<=floor(n/(N+1))}(M(floor(n/j))-M(N)) - n*sum_{k>=N}(M(k)-M(N))/(k(k+1)). All scales and entire mass retained.
- correctedError68: n*c+literal bdMobiusFloorResidual N n.
- correctedEnergyTerm72: correctedError(N,c,j+1)^2/((j+1)(j+2)).
- correctedError_eq76: n*(c-H_N)+(1-F_N(n)), all N,c,n.
- correctedError_div_tendsto83: correctedError/(j+1) -> c-H_N at fixed N.
- correctedEnergyTerm_tendsto102: energy summands -> (c-H_N)^2.
- hasSum_correctedEnergyTerm116: at c=H_N sum exactly bdMobiusFullErrorEnergy N.
- summable_correctedEnergyTerm_iff125: ALL N including0 and realc, summability iff c=H_N.
- summable_floorResidual_energy_iff135: bare quotient field finite energy iff H_N=0; NO claim H_N nonzero.
This is exact unique compensation/classification, not RH proof or absolute cofinal energy ceiling. Finite-window tuning of GLOBAL linear scalar cannot choose different coefficient without destroying full energy. Locally tapered/finite-support corrections are NOT ruled out. Fixed-cutoff finite energy must not be confused with cofinal growth control.

## Validation COMPLETE; don't repeat
Scratch lake env lean final process75020 exit0 no diagnostics (first failed only eta/Function.comp simplification, corrected). Final LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionCountertermRigidity process85134 exit0: ONLY new leaf built4.9s;13112 cached graphjobs. Eleven new public declarations audited ONCE via /tmp, process46178 exit0, each exactly propext/Classical.choice/Quot.sound. No admissions/addedaxioms/numericalcertificates. Umbrella unique import added, no full/umbrella build.
Formal lint process56614 exit1 ONLY FOUR concurrent unrelated unwired leaves: CCMRestrictedWeilPolarBombieriYoshidaQuantitative, FiniteDirichletMellinContinuationObstruction, RetainedPrimeLandauCarrier, RetainedPrimeLandauSeparation. No new-leaf lint error. One search-index refresh exit0:11changed0removed33135files404265decl3953gaps. Scoped source=scratch, forbidden absence, whitespace, unique wiring,auditcoverage,doclinks/stage passed. Owned compiler handles terminal; ps exact executable+owned filename found no owned Lean/lake. Removed /tmp/edq_counterterm.lean,_api.lean,_axioms.lean. Logs remain /tmp/edq_counterterm.{api,scratch,build,axioms,lint,index}.log.
A functions.exec syntax error at final doc/memory update executed NOTHING; subsequent separate calls completed doc finalization and this memory. Not a Lean/build failure.

## Docs
Card moved to docs/drafts/pipeline/3-formalized/edq-counterterm-rigidity.md; no stage1card. Contains dependency-closed paper proof, classification positive survivor, corpus novelty audit, validation. Frontier summary,paragraph after quotient result,and EDQrow updated. STATUS entry MUST-FIX-COMPENSATION-BY-FULL-TAIL-ADMISSIBILITY route-independent; distinguishes full-tail admissibility from cofinal growth. Preserve concurrent source/doc/umbrella edits,no commits.

## Corpus findings for continuation
Read CCMUnitRieszWaveletFrontier1–200: namespace GaloisForLFunctions.RHTower (different root); mobius_compensation60 generic finite algebra with arbitraryfunctions, NOT an actual arithmetic bound. CCMBVMuntzSummation1–145 discrepancy<=u*totalvariation under measurable/bounded/BV source; does not bound actual Mertens variation. MuentzZetaRelationImpossible forbids finite exactinverse but not infiniteapproximation. MobiusMertensFiniteSectionEnergy1–180 exact Abel finite sections; powerbound still requires partial-sum premise.
Read BaezDuarteScaleLaw1–240 and WaveletPairing220–410: exact beta-wavelet norms and weighted Mertens pairing; weighted domain condition supplied. criticalMertensVector HERE uses harmonic Möbius partials, not unconditional square-root Mertens theorem. Don't conflate names.
Read CCMFUSuzukiMobiusDivisorDilationChannels340–510: exact positive/negative signed Mertens-gradient with zero-extended terminalboundary, full/terminaltentsplit, DIFFERENT source; does not close EDQ bound.
Potential matches NOT READ YET: MobiusMertensPrimeRemovalTentLaw,L2MellinUnitary,MobiusLaplaceMellinPlancherelBridge,MellinLinePolarization,CCMConnesConsaniRapidMuntz,DeningerMeyerPoissonMellinFactorization,MobiusIntegerCuspConfinement,PoissonMuntzAbelMeanDefect.
Primary RH objective remains unchanged; bridge classified as derived under scientific-method.md. No new universal conjecture frozen.

## Lean details
Harmonic-tail path is RHTower/Sieve/MoebiusHarmonicTailIdentity.lean, not top-level Sieve. hasSum_stepGram in StepFunctionCarrier126 gives rational-weight series from two bounded sequences. Telescope uses hasSum_iff_tendsto_nat_of_nonneg,Finset.sum_range_sub',tendsto_const_div_atTop_nhds_zero_nat composed with Filter.tendsto_add_atTop_nat. Function.comp_def needed in simp for Tendsto.comp. Generic hasSum_iff_tendsto_nat,unqualified tendsto_add_atTop_iff_nat,HasSum.congr UNKNOWN in probe; avoid. Eta-expand change Tendsto(fun j=>correctedEnergyTerm ... j) or unfold before simp_rw; simp-only may not unfold defs passed as functions.
User disciplines persist: corpus-first,card beforehardwork,oneownedforegroundLean,onlyscratchchecks+finalleafbuild,new-onlyaxioms,nofull/umbrella,cleanup. Numericalexperiments only bounded multicore RunPod with frozen uncertain discriminating protocol,downloadedrecords,never insideLean.
