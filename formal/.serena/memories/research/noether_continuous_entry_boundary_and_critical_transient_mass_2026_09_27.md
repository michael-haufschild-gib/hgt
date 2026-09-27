# Continuous entry boundary for the RH deficit route — 2026-09-27

RH remains unproved. Goal remains active. This turn proved cutoff control, not the missing estimate for the continuous signed remainder. Repo /Users/michael/Documents/code/hgt/formal. No subagents, full builds, commits, numerical experiments, heartbeat changes, custom axioms, or sorry.

## Verified new work
Five new leaves, 22 public theorems. Every leaf passed foreground `lake --old env lean FILE -o .lake/build/lib/lean/...`. All fresh objects; exactly one import each in GaloisForLFunctions/RHTower.lean. Separate final `lake --old env lean` axiom audit of all 22 passed, with only [propext, Classical.choice, Quot.sound]. Temporary projectless work/EntryBoundaryAxiomAudit.lean was deleted. No own Lean process remains.

### 1. LogarithmicVariableEntryContinuity.lean (2 theorems)
Defines logarithmicVariableEntrySum f t = sum_{1<=n<=floor(exp t)} f n t.
- common-prefix identity reuses logarithmicEntrySum_eq_common_prefix (no duplicate filter proof).
- continuous_logarithmicVariableEntrySum: if each positive-index profile is continuous and f n (log n)=0, the moving sum is continuous globally. Locally a fixed finite prefix of continuous Ici-indicators suffices.

### 2. CCMPrimeDeficitEntryBoundary.lean (4)
D(T) = ccmLogChebyshevDeficitPrimitive T = integral_0^T (exp t - psi(exp t)).
R(T) = ccmPrimeDeficitDilationRemainder T; L = its already-proved limiting constant.
U(T)=floor(exp(T/2)). B(T)=ccmPrimeDeficitShortQuadraticWork T.
Proves global continuity of the literal dilation source and R, using D continuity and the exact dilation conservation identity.
Defines K(T)=ccmPrimeDeficitShortBoundaryCorrection T = 2 sum_{n<=U(T)} mu(n) R(log n).
Defines W(T)=ccmPrimeDeficitShortBoundaryWork T = B(T)+K(T).
For T>=0 proves exact D(T)-W(T)=2 sum_{n<=U(T)} mu(n)[R(T-log n)-R(log n)]. Stored as a variable-entry sum at T/2. Each summand vanishes at its true activation time T=2log n.
Proves ContinuousOn W (Ici 0), with no arithmetic cancellation assumption.

### 3. CCMPrimeDeficitEntryBoundaryBounds.lean (6)
Defines j_n=ccmPrimeDeficitEntryTransient n=2 mu(n)[R(log n)-L].
- |j_n| <= (log n+14)/(2n), all natural n including zero (zero terms).
- sum_{n<=N}|j_n| <= (log N+14)(1+log N)/2.
- at U(T), sum|j_n| <= (T+28)(T+2)/8 for T>=0.
- exact K(T)-2L sum_{n<=U}mu(n)=sum_{n<=U}j_n.
- combines prior O(T) transient-head bound to prove |D(T)-W(T)| <= (T^2+34T+112)/8.
- Tendsto exp(-T/2)*(D(T)-W(T)) atTop (nhds 0).
Final file audit exited 0 with two informational ring_nf suggestions, no errors or warnings; all theorem axioms checked clean. No need to repeat successful checks merely for the informational suggestions.

### 4. CCMPrimeDeficitBoundaryDilationAction.lean (5)
Defines Atilde(T,z)=ccmPrimeDeficitShortCompletedDilationAction T z + 2*z*K(T). This definition uses explicit arithmetic source terms, not D or W.
- HasDerivAt (Atilde T) (2*W(T)) 0 for T>=0.
- its parameter derivative at zero is continuous in T on [0,infinity).
- exact conservation D(T)=deriv(Atilde T)(0)/2 + 2 sum_{n<=U}mu(n)[R(T-log n)-R(log n)].
- same explicit polynomial discrepancy bound for the half derivative.
- normalized discrepancy tends to zero.
No invariance, stationarity, coercivity, or physical Noether theorem was asserted. Continuity is for the first variation; continuity of the whole two-variable action was NOT proved.

### 5. CCMPrimeDeficitEntryBoundarySummability.lean (5)
Uses existing Sieve.MertensFirst.summable_log_div_sq and the p-series theorem.
- |j_n|/n <= (log n+14)/(2n^2).
- Summable (fun n => |j_n|/n).
- Summable (fun n => j_n/n).
- Summable (fun n => exp(-(2log n)/2)*|j_n|), the literal critical-scale entry weights.
- every finite normalized absolute-entry sum <= its finite total tsum.
The limiting-constant term 2L mu(n) has been separated. Do NOT claim the full boundary has finite normalized absolute mass. Only this transient does.

## Mathematical status / next target
Actual progress: the moving square-root cutoff is removed exactly by a continuous arithmetic correction; its difference from the actual deficit is polynomial in log-radius, strictly below the target exp(T/2) scale. The remaining required estimate is |W(T)|<=C exp(T/2), or the equivalent bound on the corrected action derivative. It is NOT proved. These estimates do not produce RH by themselves.
Keep reflected main, signed correlation, and reciprocal-error terms coupled. Prior isolated Mellin-action invariance and arbitrary-vector source positivity shortcuts are disproved in earlier leaves. Boundary correction is a genuine useful estimate, not a new assumed cancellation premise.

## Lean lessons
- In this namespace, unqualified add_le_add_right can resolve to a corpus declaration with the opposite argument order. Use gcongr or explicitly qualified/root lemmas.
- Nat.one_le_floor_iff has explicit x argument: (Nat.one_le_floor_iff _).mpr.
- Continuous subtraction needs dsimp only [Pi.sub_apply, Function.comp_apply, id_eq] before linarith on pointwise equalities.
- HasDerivAt.congr_deriv is cleaner than convert for changing the derivative scalar. Summable.congr is cleaner than convert on summable function expressions.
- Explicitly annotate Nat.cast_nonneg n as (0:Real)<=n when used in abs_of_nonneg inside simp; otherwise type inference may leave the real cast unresolved.

## Repository validation
Own source whitespace/forbidden-construct checks clean. First generated index refresh succeeded. Global lint reported 16 unrelated unwired modules plus concurrently stale LEAN_API.md and LEAN_OVERVIEW.md. Second/final index refresh succeeded. Final lint reported only those same 16 unrelated unwired modules; no stale generated files remained. No own processes remain. Preserve concurrent work and do not claim global repository lint clean.
