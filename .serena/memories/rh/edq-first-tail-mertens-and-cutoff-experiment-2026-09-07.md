# EDQ first-tail Mertens field and cutoff-selection experiment
Goal ACTIVE, RH proof/falsification NOT achieved. Current continuation baseline 8,098,189 tokens, no budget. Previous turn was verified progress (weighted prime cancellation); this turn also made progress: new uncertain experiment evidence and independently proved exact arithmetic bridge. Never mark complete/blocked merely for RH difficulty.

Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.
This turn moved from known relative prime-packet cancellation to absolute residual structure. Initial harmonic defect alone is insufficiently understood; first complementary block now explicitly exposes actual Mertens increments.

## NEW COMPLETE LEAN LEAF — no re-audit/rebuild absent new changes
formal/GaloisForLFunctions/RHTower/EulerDeletionFirstTailMertens.lean
~140 lines (ends139), imports EulerDeletionMobiusGlobalLogSaving.
Namespace RHTower.DeletionFirstTail; autoImplicit false; 3 definitions,8 public theorems =11 audited declarations.
16 floorResidual_eq_mertens_increment: N<n≤2N ⇒ bdMobiusFloorResidual N n = Sieve.mertensM n-Sieve.mertensM N. All omitted floors are1.
34 error_eq_harmonic_add_mertens_increment: 1-bdMobiusModularApproximant N n=n*H_N+M(n)-M(N) on same entire block.
42 firstTailErrorEnergy N: sum over Ioc N (2N) of (1-F_N(n))²/[n(n+1)].
46 incrementEnergy N: same weighted sum of (M(n)-M(N))².
50 incrementMoment N: sum over first block of (M(n)-M(N))/(n+1).
54 firstTailErrorEnergy_eq: Efirst=I+2H*B+H²*sum n/(n+1), retains signed cross.
80 firstTailErrorEnergy_le: Efirst≤2I+2NH², ALLN.
96 incrementEnergy_le: I≤2Efirst+2NH², ALLN.
112 firstTailErrorEnergy_le_complementaryTail: Efirst≤bdMobiusComplementaryTailErrorEnergy N N (genuine full infinite tail).
126 incrementEnergy_le_full_tail: I≤2*fullComplement+2NH².
132 incrementEnergy_le_six_fullErrorEnergy: I≤6*bdMobiusFullErrorEnergy N, using prior NH²/2≤fullError.
Private helper harmonic_block_energy_le proves sum(nH)²/[n(n+1)]≤NH².
All independent of numerical outputs. Paper reasoning preceded code and experiment result; [BRIDGE], no new primary conjecture.

Validation COMPLETE:
- Scratch final session62419 exit0, EMPTY /tmp/edq_first_tail.scratch.log.
- Targeted LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionFirstTailMertens session61388 exit0; ONLY this new leaf Built122s,13110 cached graph jobs. Concurrent machine load made wall time slow (~14s scratch CPU over~2minwall); no duplicate compiler was started.
- New-only #print axioms session44273 exit0, all11 exact propext/Classical.choice/Quot.sound. No sorryAx/added axioms/computational certificate; private helper transitively covered.
- Wired unique RHTower.lean import; NO umbrella/full build.
- ONE formal lint session68071 exit1 ONLY unrelated unwired concurrent RHTower.RetainedPrimeMobiusEulerIdentity. EDQ wired/no lint error. Do NOT claim globalpass or modify foreign module.
- ONE search-index session94154 exit0:8changed0removed,33099files403839decl3952gaps.
- Scoped declaration coverage/exactstdsets/forbiddenforms/source=scratch/uniqueumbrella/doclinks/stage/whitespace passed.
- All owned Lean/lake processes exited; removed /tmp/edq_first_tail.lean,/tmp/edq_first_tail_api.lean,/tmp/edq_first_tail_axioms.lean. Logs retained /tmp/edq_first_tail.{scratch,api,build,axioms,lint,index}.log.

## NEW NUMERICAL EXPERIMENT — complete, RunPod only
Directory docs/drafts/pipeline/2-fully-proven/computations/edq-harmonic-cutoff-tail-2026-09-07/
PROTOCOL.md frozen before energy results. For k10...16, inspect everyN in[2^k,2^(k+1)) and choose min/max abs(sqrtN*H_N) plus midpoint3*2^(k-1). 21slots, no energy-based selection. Compute full integer floor sum C_N(n)=sum_{d≤N}µd floor(n/d) via sieve jumps then in-place int64 prefix sums, F=C-nH. Record target-error andraw energy onhead1..N and7dyadicblocks through128N.
Uncertain readout: selected-min tail error / midpoint tail error. All7<.1=>suppression;≥4>.5=>persistent;elsemixed. All7>.5, persistent complementary tail.
Results:
k,Nmin,NH²,selectedtail,midpointtail,ratio,firstblockfraction
10,1558,9.760e-5,.035190,.034415,1.023,.5983
11,2161,4.463e-8,.040004,.034741,1.151,.6926
12,5297,9.947e-7,.038419,.035940,1.069,.5485
13,15045,9.789e-7,.037902,.043930,.8628,.5576
14,30254,1.722e-6,.037625,.056861,.6617,.6285
15,56359,1.154e-12,.036394,.062906,.5785,.5660
16,81017,2.044e-9,.040567,.044557,.9104,.4909
Tail =finite(N,128N] only, NOT fulltailestimate. Omitted rawupper N²/(128N+1), errorupper(N+1)²/(128N+1) recorded but generallytoo large. This doesNOTproveasymptoticfloor, falsifyRH, or ruleoutcofinallogceiling (constant.04compatible). It tells us to retain actualincrementfield ratherthanassumescalarcutoffselection suppressestail.

Correct run2:
prescribed host root@157.157.221.29 port27094 key~/.ssh/id_ed25519.
32availableCPU,8independent Pythonworkerprocesses,NumPyinternal1thread.
runtime2.226672433s, hardtimeout240s withTERM/KILLprocessgroup.
Python3.8.10,NumPy1.24.4, longdouble H/energies, exactint64floor.
ScriptSHA256 4a3c20c683bdb0977d323c4fba78f64dbd9494c16fc1a13504ebc7ce7682efd5.
Allheadflooridentities,ALLfirstblockMertensidentities,6directfloorsumspercutoffpassed; maxcompensatedHdiff8.673617379884035e-18,headenergyidentitydiff2.0194839173657902e-28.
Initial run1 FAILEDvalidation beforeenergyrows: mu[p*p::p]=0 bug incorrectlyzeroedmultiplespafterp². Correct mu[p*p::p*p]=0. Failedscript/log/design preserved separately as experiment-invalid.py,run-invalid.log,design-invalid.json. No modelthresholdchangedafterfailure; frozenprotocolretained.
Downloaded experiment.py,design.json,results.json,run.log,failedrecords,REPORT.md,PROTOCOL.md,SHA256SUMS. Localcodeandhash/bookkeeping only; allnumericwork/analysis onRunPod.
Successfulscript hash anddesignmatchchecked locally. Manifestcovers everyfileexceptitself.
Allownedremoteprocessesconfirmedabsent via/proc exactscriptargv; removed owned /tmp/edq_harmonic_cutoff_20260907.py and both unique run1/run2 dirs afterdownloads. Remote cleanup session52351 exit0. NoownedRunPodjobremains.

## Documentation complete
Card moved to docs/drafts/pipeline/3-formalized/edq-harmonic-cutoff-tail.md; contains paperproof, protocol/report interpretation, actualnewLean APIs andvalidation; no pendingmarkers.
Frontier CURRENTstate top summary,paragraph afterweightedprimecancellation,EDQrow. No newroute labels orhistory/diary, no route retired.
STATUS appended route-independent MUST-COORDINATE-THE-INITIAL-DEFECT-AND-TAIL: checkremainingerroronthesameselectedcutoffs,retaincrossandlaterblocks,do nottransfer scalar smallnesswithoutbound. Numericfiniteclaims separatedfrominfinite.
Preserved concurrentunrelatedfiles; no commits/push.

## Next meaningful direction
Actual Mertens-increment field is exposed on firstblock; quantitative absolute control and all later blocks remain open. The next source mechanism could be a full hyperbola/quotient decomposition of omitted floors into Mertens increments, with exact weights/cross correlations; this is a possible continuation, NOT a proved or frozen newconjecture. Check whole corpus first. Avoid substituting another easybridgeforRH; seeknewsourceboundoruncertaindiscriminatingexperiment.
No further experiment justified merely to repeat these stable finite observations. Any newrun must have uncertainoutcome,change nextapproach,RunPodonly,multicore,boundedruntime anddownloadedrecords.

## API lessons
Nat.div_eq_of_lt_le {k n m} (lo:k*n≤m)(hi:m<(k+1)*n):m/n=k. k1handlesfirstblock.
Nat.div_eq_one_iff andNat.div_eq_iff_lt_le UNKNOWN ontoolchain.
Finset.sum_Ico_eq_sub f (h:m≤n) exactdiffranges. IocNn=Ico(N+1)(n+1).
Nat.card_Ioc, notFinset.card_Ioc.
Do not simp_rw an untyped Finset.sum_congr (metavars); giveexplicit sumidentitythenrw.
linarith doesnotunfold incrementEnergy/firstTailErrorEnergy automatically; dsimp correspondingdef in transitivitytailgoal.
Never restart a liveprocess becausepoll timesout; exactownedhandles terminalbefore nextLean. Parsepsargs executablebasename andownedfilename,notsharedPPID/comm.
