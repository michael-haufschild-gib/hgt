# WL local signed Chebyshev chord work

- **ID:** WL-CW-20260929
- **Stage:** 1-in-progress
- **Type:** THEOREM candidate
- **Source:** WL frontier; `WeilLagQuadraticInterpolation.sqrt_integerLag_chord_exact` and `SuzukiWeilLagTailBridge.sqrt_mul_integerLag_eq_neg_mul_weilLagChebyshevTail_add_arch`.
- **Statement:** With `2<=n<=k<=m`, `u,v>=0`, `u+v=1`, `k=un+vm`, the explicit entropy-minus-prime-charge defect is exactly `un*integral_(n,k] E(t)/t^2 - vm*integral_(k,m] E(t)/t^2`, where `E(t)=psi(t)-t`. The same identity holds with `E(t)-c` for every constant `c`.

## Plan
1. [x] Search current corpus; read exact tail and integrability declarations.
2. [x] Derive dependency-closed paper identity and constant-level cancellation.
3. [x] Verify mathlib names in scratch; formalize local identity, level invariance and closed upper-interpolation capstone.
4. [x] Audit all public axioms, final direct `lake --old env lean`, own umbrella wiring and bounded novelty comparison. Index/lint follow-up remains below.

## Paper proof
Write `T(r)=integral_(r,infinity) E(t)/t^2`. Existing unconditional Mertens/PNT integrability supplies all these integrals for `r>=1`. The existing lag-tail bridge says `sqrt(r)*a_r=-r*T(r)-log(2pi)+S(r)` at integer `r>=2`.

Comparing its barycentric chord balance with the newly proved prime-charge identity cancels the affine constant and the complete trivial-zero chord deficit. Thus `J-Q=un*T(n)+vm*T(m)-k*T(k)`. Since `k=un+vm`, this is `un*(T(n)-T(k))-vm*(T(k)-T(m))`. Splitting each integrable tail at the next endpoint gives exactly the two finite signed integrals in the statement. No estimate has been taken, and the far tail beyond `m` cancels.

Subtracting a constant `c` from `E` changes this work by
`-c*[un*(1/n-1/k)-vm*(1/k-1/m)]`.
The bracket is `u+v-(un+vm)/k=0`. Therefore the receiver depends on variation of the Chebyshev error, not its constant level. The remaining producer must bound this signed difference at `sqrt(k)` scale; no such bound is asserted.

## Prior-research audit
Search artifact `/tmp/wl-signed-chord-search-20260929.json`: deep search, partial deadline, coverage reported pending. Relevant hits include the existing integer-lag tail bridge and a separate cumulative triangular von Mangoldt identity. Existing `RiemannXiSuzukiPointwiseChebyshevError` gives centered log-moment Abel functionals; its kernel and source differ from this two-endpoint natural-scale chord. No inference of universal novelty from partial search. Public-source comparison remains pending.

## Log
- 2026-09-29: C10 follows C1-C9 in `wl-quadratic-lag-interpolation-2026-09-29.md`. Main interpolation leaf is undergoing final artifact/axiom audits before this dependent scratch check. One owned foreground Lean process at a time. No numerical computation, added mathematical premise, heartbeat increase, or full umbrella build.
- 2026-09-29: scratch proof of both local work and arbitrary-constant invariance passed, no warnings. Mathlib names verified with specialized `have := @Name` declarations; tail and integrability dependencies have only `[propext, Classical.choice, Quot.sound]`. Repairs addressed universe specialization, an existing Real instance diamond (`using!`), and integral-expression parsing; no heartbeat change. Production leaf `WeilLagLocalChebyshevChord.lean` now contains the exact proofs and a closed actual-lag upper-interpolation capstone.
- 2026-09-29: extra public searches for Chebyshev error/chord, Weil lag/Chebyshev, and RH/triangular/entropy found no exact match. RB Labs' primary research page was opened: its Chebyshev trace concerns Chebyshev polynomials and cubic Xi descent, distinct from the actual Chebyshev counting-error work here. Existing corpus `ChebyshevLagWindow` is adjacent and supplies a one-interval statistic; this two-endpoint compensated chord and constant cancellation are a new corpus bridge. No universal public/training absence certification.
- 2026-09-29: Production source passed. Targeted `lake --old build +GaloisForLFunctions.RHTower.WeilLagLocalChebyshevChord` passed (12871 dependency jobs; unchanged modules replayed, leaf 60 seconds reported). Own umbrella import wired. Scratch axiom audit passed for all three public declarations: exactly `[propext, Classical.choice, Quot.sound]`, no computation oracle or added mathematical axioms. `/tmp/wl-local-chord-axioms-final.txt` captures the closed capstone signature. Final direct production source check now running; index/lint pending.
- 2026-09-29: Final `lake --old env lean GaloisForLFunctions/RHTower/WeilLagLocalChebyshevChord.lean` exited 0, no warnings or output (`/tmp/wl-local-chord-source-final.txt`). Own source and umbrella whitespace check passed; no forbidden declarations or heartbeat settings. WL frontier now labels the actual local-work bridge Lean-proved. Earlier authoritative global lint failure was entirely unrelated unreachable modules; fresh index/lint for this added leaf still pending. RH remains open and the active goal remains active.
- 2026-09-29: Index refresh exited 0 (`/tmp/wl-local-chord-index-final.txt`), refreshed the new leaf and generated API/gaps/overview. Authoritative lint exited 1 (`/tmp/wl-local-chord-lint-final.txt`): exactly 12 errors, all unrelated unreachable modules, none in either owned interpolation/local-work leaf. Names: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, LiEvenCrossCassiniLogMassPole, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, WeilPolarConeExtremePoint, WeilPolarConeKernelTransformForm, ZetaZeroDensityPowerSaving. No forbidden active declarations reported. Do not claim the global gate passed or modify these out-of-scope files. This card remains in progress while the wider goal and universal-novelty requirement remain unresolved.
