# WL quadratic lag interpolation and arbitrary sampling meshes

- **ID:** WL-QI-20260929
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/rh-current-frontier-map.md`, WL; corpus research searches recorded below.
- **Statement:** Unconditionally, `a_k <= max(0,a_n,a_m)+(m-n)^2/(4k sqrt(k))` for `2<=n<=k<=m`. Arbitrary bracketing meshes with `(m-n)^2<=C n sqrt(n)` carry the one-sided RH criterion.

## Goal
Advance WL's exact upper-order problem using the actual prime-side explicit formula. No claimed positivity producer. No numerical computation, RH assumption, added axiom, or unproved analytic input in the interpolation theorem.

## Plan
1. [x] Read WL frontier, relevant memories and exact lag declarations; search corpus and public primary sources.
2. [x] Prove dependency-closed paper inequality and audit normalization/endpoint cases.
3. [x] Formalize exact arithmetic survivor in a dedicated leaf, with targeted Lean checks.
4. [x] Derive precise mesh criterion; perform bounded novelty and complete axiom audits; wire umbrella and run lint. Global lint remains failed on unrelated unfinished wiring, recorded below.

## Corpus basis
`WeilLagFunctionInteger.integerLag_eq` gives `sqrt(n) a_n = E(n)` where
`E(n) = n(1+gamma) - n log n - log(2pi) + S(n) + R(n)` and
`R(n) = sum_{j<=n} Lambda(j)(n/j-1)`.
`WeilLagFunctionPrimeGap.abs_integerLag_sub_le` only supplies a linear-gap Lipschitz loss.
`LagRatioLawAttained` handles log-dense sets with an attained top; counting-function criteria require analytic continuation. The new candidate instead uses convexity of every nonnegative arithmetic ramp.

Search artifacts: `/tmp/wl-frontier-search-20260929.json` (deep, partial deadline; corpus inventory complete but many compiler statuses pending), `/tmp/wl-interpolation-search-20260929.json` (hybrid, complete retrieval; older coverage snapshot and semantic-coverage warning), `/tmp/wl-chord-lexical-20260929.json` (lexical). Exact `rg` search of Lean sources and Markdown found no lag chord/mesh theorem. The unrelated `ScaleAbscissaDuality.chord_versus_transfer_at_three_quarters` must not be mistaken for this result.

## Conjecture loop
- C1: infer frontier from the full Weil cone. Rejected as route mismatch: WL's receiver is the scalar lag law; HF owns cone stability.
- C2: improve lag interpolation through atom-free prime gaps. Strengthened: prime atoms have nonnegative ramp coefficients, so an upper chord law can hold across every arithmetic interval, without atom-free assumptions.
- C3: for `2<=n<=k<=m`, weights `u=(m-k)/(m-n)`, `v=(k-n)/(m-n)`, prove
  `sqrt(k) a_k <= u sqrt(n) a_n + v sqrt(m) a_m + (k-n)(m-k)/k + 1`.
  Proof candidate: ramp convexity; `log y <= y-1` bounds the logarithmic chord defect by `uv(m-n)^2/k`; `0<=S<=1` controls the remaining series. Handle `n=m` separately.
- C4: bound normalized interior lag by `max(0,a_n,a_m) + ((m-n)^2/(4n)+1)/sqrt(n)`. The square-root chord weights have sum at most one. This exposes the `n^(3/4)` mesh, including the critical exponent.
- C5: remove `+1` using convexity of `S`. **SUCCEEDED in Lean:** every term `x^(-2(j+1))/(2(j+1)(2j+3))` is convex; its positive summable series lies below the chord. The final law has no additive error.
- C6: sharpen the entropy chord constant to `1/2` relative to a positive lower endpoint. Paper proof: `F_r(x)=x^2/(2r)-x log x` is convex for `x>=r>0`, because `F_r''(x)=1/r-1/x>=0`. Its chord inequality gives entropy defect `<=uv(m-n)^2/(2r)`. For `r=n`, this yields `a_k<=M+(m-n)^2/(8n sqrt(k))` and a mesh bound `M+C/8`. Scratch formalization in progress; no sharpness claim for the current coefficient.

## Public-source audit
Initial searches found Suzuki's *Weil's quadratic form via the screw function* (`https://arxiv.org/html/2606.09096v1`) and Mittermeier's 2026 checkpoint handbook (`https://zenodo.org/records/21933784`). Their localized Weil/prime-power interval geometry is adjacent; exact comparison remains pending. Absence from all public literature or model training data cannot be certified. No novelty claim yet.

Text extraction of the Mittermeier handbook was reviewed at its arithmetic interval and convex-dual formulas: its log-scale screw profile is `Psi(t)=A(t)-sum Lambda(q)/sqrt(q)*(t-log q)_+`, with negative slope jumps and interval-minimum certificates. Our natural-scale lag bracket has **positive** ramps `Lambda(j)*(x/j-1)_+`, and its upper chord inequality crosses all jumps. The exact formulas and orientation differ. Suzuki's HTML has no `convex` or `interpolation` match. Targeted public searches for lag quadratic interpolation, arbitrary sampling meshes, and a `3/4` sampling criterion found no exact collision; unrelated Riesz `3/4` exponents were excluded. This is a bounded novelty audit, not universal absence certification.

## Dependency-closed paper proof [PROVED HERE]
For `n<=N`, extending the finite prime sum to `N` adds only zero ramps, so
`R_N(n)=n M(n)-psi(n)`. Each summand `Lambda(j)*max(x/j-1,0)` is convex since `Lambda(j)>=0`. Consequently `R_N(un+vm)<=u R_N(n)+v R_N(m)` for `u,v>=0`, `u+v=1`.

Write `k=un+vm>0`. The logarithmic chord defect is
`un log(n/k)+vm log(m/k)`. Applying `log y<=y-1` to both positive ratios gives
`un(n/k-1)+vm(m/k-1)=uv(m-n)^2/k`.
The affine terms in `E` cancel exactly. Each inverse even power is convex on positive reals and the series is summable on `x>=1`, so `S(k)<=u S(n)+v S(m)`. Thus the strengthened C3 holds **without `+1`**.

The normalized endpoint coefficients have total
`(u sqrt(n)+v sqrt(m))/sqrt(k)<=1`, because the squared deficit is
`k-(u sqrt(n)+v sqrt(m))^2=uv(sqrt(m)-sqrt(n))^2>=0`.
Take `M=max(0,a_n,a_m)`; then `a_k<=M+uv(m-n)^2/(k sqrt(k))`.
For `n<m`, barycentric weights give `uv<=1/4`; since `k>=n`,
`a_k<=M+(m-n)^2/(4k sqrt(k))<=M+(m-n)^2/(4n sqrt(n))`.
When `n=m`, necessarily `k=n` and the inequality follows directly.

An arbitrary set `S` with bracketing endpoints `n,m in S`, `2<=n<=k<=m`,
and `(m-n)^2<=C*n*sqrt(n)` for every `k>=2` therefore satisfies
`a_k<=max(0,sup_S a)+C/4`. By the corpus's exact bounded-above integer lag theorem,
boundedness on this mesh is equivalent to RH. The proof uses no counting-function
continuation, attained zero abscissa, prime gap theorem, or numerical estimate.

## Gates
- [x] 0 → 1: source-pure, exact candidate, arithmetic proof mechanism.
- [x] 1 → 2: complete paper proof.
- [x] 2 → 3: exact Lean theorem, targeted `lake --old env lean`, scratch axiom audit, own umbrella wiring. Whole-tree lint was run and remains failed on unrelated module reachability; no whole-tree-clean claim.

## Log
- 2026-09-29: initialized independent WL loop. Shared tree already contains unrelated ongoing changes; preserve them. Serena's Lean symbol access fails because Lean path is ignored. `update_plan` and `multi_tool_use.parallel` unavailable; plan tracked here and independent reads batched through `Promise.allSettled`.
- 2026-09-29: exact final source compiles with `lake --old env lean GaloisForLFunctions/RHTower/WeilLagQuadraticInterpolation.lean`, exit 0, no warnings. Initial implementation mismatches (zero summand indexing, changed addition-monotonicity API, missing local positivity fact) repaired without increasing heartbeats. Ten public theorems and two definitions; core law and mesh characterization have closed universal statements and no unproved analytic premises. Targeted artifact build/axiom/lint audit still in progress.
- 2026-09-29: targeted artifact build completed (8828 jobs; unchanged imports replayed). Final direct source audit and scratch `#print axioms` for all 12 public declarations passed; each has exactly `[propext, Classical.choice, Quot.sound]`. No `Lean.ofReduceBool`, mathematical computation, extra axioms, or heartbeat increase. Umbrella import registered; indexes regenerated. Repository lint fails on unrelated unwired modules (12 initially, 13 on justified later recheck as concurrent work added another leaf); our module is reachable and no proof-debt error is reported. Do not claim global lint passed. One accidental overlap of scratch checks was corrected by terminating the newer owned Lean PID, verifying exit 143, and waiting for the older owned process to exit 0 before restarting; no owned duplicate remains.
