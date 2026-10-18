# THIM strict Möbius margin and uniform damping stability

2026-10-18. Eleventh connected contribution of active indefinite THIM goal; one significant result per continuation. No goal completion. Read attachment and entire 314-line THIM README this turn; README unchanged. User forbids hgtl7, RH focus, numerical experiments, full/umbrella builds, axioms/sorry/admit/opaque/unsafe, heartbeat hacks, commits/push. One owned foreground Lean process at a time, poll terminal. No subagents authorized. Future memory listing filter topic trans-horizon (unfiltered list huge). Docs architecture/testing absent. update_plan unavailable; pipeline card tracks work.

Source: formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/StrictMobiusMarginAndUniformDampingStability.lean (333 lines; 17 public theorems, 2 private helpers).
SHA256 a70c33678dcc8e460f13888494892ac6a4bf3a0250b977e51e16c4960b9e2c90.
Imports IntegerJumpEnergyAndBeyondEnvelope (hash c76159f2aca8104f11afe6ea8dbde3e124bf4b135e5438ebfb49a9d32c4d706e) and Mathlib.NumberTheory.Bertrand. Dependency facts in `mem:trans-horizon/integer-energy-beyond-envelope`.

Results:
- N>=2: Bertrand prime N<p<=2N supplies integer path values 1,0,1,0 at 1,2,p,2p. Hence E>=3+|s_mu(M+1)| when M+1>=4N.
- With prior envelope below4N: N>=2,M>=1, |s_mu(M+1)|<=2 implies D_N(M;mu)<=-1, including M+1<6(N+1).
- Coefficients mu(d)*d^(-eps), responses and each finite defect continuous in eps. Handle index0 separately as constant zero.
- For each N>=2 there exists delta_N>0, uniform in ALL M>=1 with R_N(M+1)<6(N+1), such that |eps|<delta_N gives D_N(M;c_eps)<-1/2. Finite endpoint continuity, radical transport, and rough radical-one comparison to a Bertrand prime. All-N nonpositive version includes N<=1 and M=0. All positive powers share same radius.
- For each prime p>5,N=6p-1,k=30p there exists delta_p>0 such that |eps|<delta_p, every m>=1 has response(k^m)>1 AND D_N(k^m-1;c_eps)<-1/2. Thus actual positive damping interval preserves envelope obstruction while strict defect survivor persists. For eps>=0 old bound below5(N+1) shows base k is first failure. Radius need not be uniform in p.
- Universal unit envelope uniform over every STRICTLY POSITIVE eps still has ratio criterion C<=5 and real additive buffer b<5. Uniform bounds pass to eps=0 by continuity. Does NOT classify each fixed positive eps.
- Full all-eps>=0 nonpositivity for M+1<6(N+1) remains unproved. Qualitative delta is nonexplicit.
Classification: new formulation from classical ingredients; no outside priority claim. Baselines TH10 arxiv1009.5281, CMS16 arxiv1612.03136, Helfgott–Thompson Prop3.2 doi10.1007/s40993-022-00408-8.

Verification:
Full scratch and ACTUAL source compiled exit0 no warnings with lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/TransHorizonIncidenceMechanics/StrictMobiusMarginAndUniformDampingStability.olean GaloisForLFunctions/TransHorizonIncidenceMechanics/StrictMobiusMarginAndUniformDampingStability.lean (from formal).
Axiom scratch imports actual source artifact and enumerates private environment identifiers via mkIdent. All17 public+2 private declarations exactly propext, Classical.choice, Quot.sound; 4 generated helpers standard-only (23 closures audited).
logs/thim-stability-audit.json verifies hashes, fresh artifacts/dependency, all17 API entries and baseline docstrings, unique THIM umbrella import, MainTheorems reachability, whitespace/prohibited declarations. logs/thim-stability-{lean,axioms,index,lint}.txt evidence.
Index exit0. lint --check-generated exit1 with7 external findings: unreachable BiScaleUncertainty.PrimeRawMomentRecovery; unreachable BezoutValuationIncidence.ArithmeticProgressionHarmonicRemainderAndShiftedDivisorBounds and MeanCenteredPronicGramRecurrenceAndCenteringDiscrepancyBridge; existing root research leaf TransHorizonIncidenceMechanics.lean; stale LEAN_API/GAPS/OVERVIEW under concurrent edits. No new-leaf or prohibited-declaration finding; no clean global gate claimed. git diff --check own files passed. All owned jobs terminal incl actual92286, axiom15480, audit59764; never poll old handles. All12 owned /tmp scratch files removed and verified absent. No full builds.

Card: docs/drafts/pipeline/3-formalized/thim-strict-margin-damping-stability.md; all boxes complete, old in-progress card gone. Ledger logs/thim-radical-sawtooth-knowledge.md updated. Failed route docs/drafts/pipeline/5-failed/thim-universal-unit-envelope-beyond-five.md updated with positive-damping obstruction and strongest strict survivor.

Corpus queries: damped-energy and stable-power partial=false74119files,pending0,generations1454592/1454607; positive-envelope partial=false74123,pending0,generation1454675. All ranked candidates/source arguments inspected. Preliminary quantitative-radius query field-filtered partial=TRUE74129files,pending0,generation1454752; all20 candidate+20 source arguments inspected; no explicit-radius result in returned hits. Broaden before next implementation. Compiler coverage mixed.

Next conjecture (NOT Lean verified): for N>=2 explicit delta_N=1/(48*N^2*(N+1)*log N) should ensure D<=-1/2 on nonempty certified radical fibers for 0<=eps<=delta_N. Mechanism: A=sum_{d<=N}|c_eps(d)-mu(d)|<=eps*N*log N, both responses <=N; per-product perturbation leads |D_eps(M)-D_0(M)|<=4*M*N^2*eps*log N. For finite representative M<6(N+1), error<=1/2; extend via radical/rough-prime transfer. Use1-exp(-x)<=x. Constants/edge cases still require paper/corpus/Lean audit. Separate full-all-eps conjecture remains open. No numerical work.

Lean traps: private sum_Icc_split requires1<=b (false at b=0 from Nat truncated subtraction); continuous_finsetSum current name; zero-index continuous coefficient needs exact continuous_const after simp; simplify pow_one in antitone hypothesis before trans_lt. Never textual numeric _private identifiers in #print axioms: enumerate environment and mkIdent. Serena ignores Lean files, use rg/read/patch fallback; tool names verified in scratch.
