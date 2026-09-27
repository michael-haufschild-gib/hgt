# Chronological signed work and exact dilation conservation — 2026-09-27

## Status
Active user goal remains proving RH, specifically square-root control of the complete signed deficit. RH is NOT proved or falsified. This turn made verified formal progress, not completion. Do not mark goal complete or blocked. No upper estimate for complete chronological work or signed Möbius inversion has been proved.

Repo: `/Users/michael/Documents/code/hgt/formal`. No subagents. User forbids computations, new axioms/sorry, heartbeat increases, full/umbrella builds. Use one foreground `lake --old env lean FILE` at a time. Read/search Lean directly; use formal_tools research; no cards. Preserve concurrent work. Existing earlier memories cover Noether action, critical work, product localization, rank-two boundary.

## Finished code and checks
Seven new leaves, all wired exactly once in `GaloisForLFunctions/RHTower.lean`:
- CCMPrimeEntryChronologicalPair.lean (2 public theorems)
- CCMPrimeEntryIntegratedDeficit.lean (2)
- CCMPrimeEntryJumpBudget.lean (5)
- CCMPrimeDeficitChronologicalWork.lean (6)
- CCMPrimeEntryWorkSampling.lean (6)
- CCMPrimeDeficitDilationConservation.lean (2)
- CCMPrimeDeficitDilationInversion.lean (1)
Total 24 public theorems. Existing CCMPrimeDeficitDiagonalControl.lean refactored to reuse the new jump-budget upper bound, removing duplicate proof.
All eight leaves passed final `lake --old env lean FILE -o .lake/build/lib/lean/...olean`; all new objects fresh. Final importer `#print axioms` audit passed all 24 new theorems plus modified old diagonal bound: only propext, Classical.choice, Quot.sound. No sorry/new axioms/numerical experiments. Scratch CheckChronological.lean and AuditChronologicalWork.lean removed. No own Lean processes remain.
Index refresh passed after all seven modules (2 changed in final refresh, concurrent other refreshes already indexed others). `git diff --check` umbrella passed. Corpus-wide lint still running at memory write (session 11753); collect result before final. It may flag unrelated concurrent sources.

## Exact new chronological identity
Notation:
D(T) = ccmLogChebyshevDeficitPrimitive T.
E(T) = exp(-T) D(T)^2.
N = floor(exp T), P = psi(exp T), S = ccmPrimeEntryPrefix N T.
H(N) = sum_{1<=n<=N} Lambda(n)^2/n (Sieve.vonMangoldtHarmonicSquareSum for N>=1).
A(N) = ccmPrimeEntryPrejumpWork N
 = sum_{n<=N} Lambda(n)/n * [D(log n) + 2(n - psi(n) + Lambda(n))].
The +Lambda restores the psi value just before the jump.

`ccmPrimeEntryPairLimit_eq_chronological N`:
PairLimit(N)=2 sum_n Lambda(n)/n [prefix(n,log n)+2 psi(n)] -2H(N).
Proved by symmetric square = twice chronological triangle minus diagonal, induction using Finset.sum_Icc_succ_top.
`ccmPrimeEntryPairLimit_eq_prejumpWork N`:
PairLimit(N)= -2A(N)+2H(N)+6psi(N)-2mertensSum(N).
Both identities valid every natural N, no mathematical premise.

`integral_ccmPrimeEntryPrefix_eq_background T`:
integral_0^T S_N(t)=Background(T,N)+mertensSum(N)-exp(-T)(S+P).
`integral_ccmLogChebyshevDeficitPrimitive_eq_background hT`:
integral D=exp T-1-T-Background-mertensSum+exp(-T)(S+P), T>=0.
These use the existing weighted prefix integral and background overlap, avoiding a new tent integration proof.

L(T) = ccmPrimeDeficitCausalStorage T
 = exp(-T)[(D(T)+exp T-psi(exp T))^2 +(exp T-psi(exp T))^2].
Thus L=(r+q)^2+q^2 for r=exp(-T/2)D, q=exp(-T/2)(exp T-psi).
L>=0, L(0)=2, E(T)<=2L(T), all proved.
W(T) = ccmPrimeDeficitChronologicalWork T
 = integral_0^T D + 2D(T) - A(N).
J(T) = ccmPrimeEntryJumpBudget T =2H(N).

`ccmPrimeDeficitChronologicalWork_balance hT`:
L(T)+integral_0^T E = 2+2W(T)+J(T), T>=0.
Actual balance, no presumed cancellation bound.
`ccmPrimeDeficitChronologicalWork_lower hT`: W>=-1-J/2.
`ccmPrimeDeficitCausalStorage_add_energy_le_work hT`:
L+integral E <= 2W +T^2+78T+52.
This retains unknown signed W. Do NOT present this as square-root control.

## Actual jump budget bound
`ccmPrimeEntryJumpBudget_eq_sum hT`, `_nonneg T`.
`ccmPrimeEntryJumpBudget_le_quadratic hT`: J<=T^2+78T+50.
`quadratic_le_ccmPrimeEntryJumpBudget hT`: T^2-80T-50<=J.
`abs_ccmPrimeEntryJumpBudget_sub_sq_le hT`: |J-T^2|<=80T+50.
Proof lower: 1<=N, L=logN in [0,T], expT<N+1<=2N, log2<=1 -> T<=L+1 -> T^2<=L^2+2T. Combine existing |H-L^2/2|<=39L+25. This is true quadratic growth, not just an upper allowance.

## Sampling convention identity / failed cancellation trick
A_theta(N) = ccmPrimeEntrySampledWork theta N with (1-theta)Lambda in place of Lambda in A.
W_theta(T)=ccmPrimeDeficitSampledWork theta T =integral D+2D-A_theta(N).
`ccmPrimeEntrySampledWork_eq_prejump theta N`: A_theta=A-2theta H.
`ccmPrimeDeficitSampledWork_eq_chronological theta hT`: W_theta=W+theta J.
`ccmPrimeDeficitSampledWork_balance theta hT`:
L+integral E=2+2W_theta+(1-2theta)J.
`ccmPrimeDeficitMidpointWork_balance hT`: theta=1/2 -> L+integral E=2+2W_mid.
`ccmPrimeDeficitMidpointWork_lower hT`: W_mid>=-1.
`abs_ccmPrimeDeficitSampledWork_shift_le theta hT`:
|W_theta-W-theta*T^2|<=|theta|(80T+50).
Changing sampling convention can absorb the entire diagonal into work. It cannot reduce total storage/energy. Positivity supplies a LOWER bound on work, not the needed upper bound.

## Actual arithmetic dilation conservation and signed inversion
`ccmPrimeEntryPrefix_dilation_conservation T`, all real T:
sum_{n<=expT} prefix(floor exp(T-log n), T-log n)
 = sum_{k<=expT} log k (T-log k).
Proof uses Nat.floor_div_natCast and existing `Sieve.sum_Icc_divisorsAntidiagonal_swap F N`, then vonMangoldt_sum. No numerical test.

Define G(T)=ccmPrimeDeficitDilationSource T
 = expT * sum_{1<=n<=floor expT} 1/n - floor(expT)
   - sum_{1<=k<=floor expT} log k (T-log k).
`ccmLogChebyshevDeficitPrimitive_dilation_conservation T`, ALL real T:
sum_{n<=expT} D(T-log n)=G(T).
The coefficient Lambda disappears exactly via sum_{d|k} Lambda(d)=log k.

`ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation hT`, T>=0:
D(T)=sum_{n<=expT} mu(n) G(T-log n).
This is full signed finite reconstruction, not a norm estimate.
Proof imports existing Mollifier.sum_moebius_divisors and BivariateConvolutionSummatorySwap; no new generic inversion surrogate.

## Next mathematical work (NOT yet proved)
Pursue bounds on the literal elementary G, then actual signed inverse stability. Do not treat a small G remainder as control of D without bounding the complete Möbius reconstruction.
Natural slope:
F(T)=expT*H_floor(expT)-sum_{k<=expT} log k.
Expected exact integral G(T)=integral_0^T F(t)dt.
Harmonic and Stirling bounds should directly give |F(T)-(gamma+1)expT|<=O(T+1), hence centered G=O(T^2).
Stronger candidate from Euler--Maclaurin (conjecture here, NOT Lean theorem):
G(T)-(gamma+1)expT+(log(2*pi)/2)T is bounded (even convergent, with small floor oscillation). At integer cutoffs this is the asymptotic of sum log^2(n), whose constant involves zeta''(0). Do not claim it proved or needed before the simpler bound.
Relevant existing sources:
- HarmonicSecondErrorBounds.lean: harmonic_mascheroni_le_half_sub_twelfth; sum_log_Icc_ge_half_log_stirling.
- DivisorUniformSquareRootBound.lean: sum_log_Icc_le_half_log_stirling.
- HarmonicHalfErrorBounds.lean: harmonic_mascheroni_half_bounds.
- MertensFirst.lean: sum_log_le/ge (coarser).
- Existing sum_log_le_stirling and stirling_le_sum_log are also in corpus, locate before use.
- CCMPrimeDeficitPrimeWork has PRIVATE common logarithmic entry sum and indicator-tail integration helpers specialized to Lambda. A generic finite-weight version could be built if necessary for G's integral. Corpus search for 'integral logarithmic cutoff' returned no matching generic result (20 unrelated results).
- CCMFUSuzukiMobiusDivisorDilationChannels has other discrete sqrt-gap transports, not the new literal D(T-log n) conservation law.
- PsiRemainderSignChange.abs_floorSummatory_psiRemainder_add_le already proves an O(sqrtN) transformed discrete remainder. Do not duplicate or confuse that floor transform with pointwise D control.

## Proof lessons
For IntervalIntegrable rewrites, explicitly type the integrand lambda rather than leave Pi subtraction inferred; otherwise rw can fail despite extensional equality.
`simp` does not always solve `(1:Real)+1=2` or `2-1=1`; use ring/norm_num for these symbolic numeral steps.
The generic symmetric triangle proof worked first pass with `simp only [Finset.sum_Icc_succ_top hN, Finset.sum_add_distrib]`, then ih, symmetry of column sum, ring.
All project searches and builds stayed on Lean files; no cards, no full builds, no commits.
