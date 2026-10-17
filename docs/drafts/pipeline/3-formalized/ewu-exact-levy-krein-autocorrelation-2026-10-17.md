# EWU exact Lévy formula and Krein autocorrelation rigidity

Status: valid theorem package formalized; interval-wide claim disproved; original goal disposition awaits user direction. Source: user attachment `f6f19c37-5edd-4cc0-b363-d81c8374fb0e/pasted-text-1.txt`.

## Exact scope

1. Pole-eliminated Bochner integral formula on real `WeilEvenPolarTestFn`, plus `SmoothEvenPolarTestFn` specialization and pointwise nonnegativity. Prove integrability, do not rely on totalized integrals.
2. Krein increment inequality for every real L² source, without differentiability, support or spectral-second-moment assumptions.
3. Dyadic deficit bound from prime-2 blindness, with no external analytic assumptions.
4. Audit claimed extension over the entire interval. Dyadic reciprocals are not dense; continuity does not itself give this extension.
5. Wire completed modules into RHTower. Final direct `lake --old env lean` audits, scratch axiom audit, formal lint. No full builds, computations, or heartbeat increases.

## Corpus evidence and proof plan

- `WeilArchimedeanExactForm.weilArchRe_eq_exactForm` contains the nonnegative jump integral plus a pole integral.
- `PrimitiveHyperplaneBlindPositivity.re_weilPoleTerm_eq_zero_of_evenPolar` proves the EWU pole vanishes.
- `ArchimedeanAnomalyConstantLaws.integral_sub_shift_sq` gives the translation-energy identity for compact continuous sources; generalize to L² by translation invariance and integrability.
- Apply integral Cauchy–Schwarz to g(u) and g(u+x)-g(u+y) for the increment inequality.
- Split g(u)-g(u+2x) at u+x; integrate the elementary square bound to obtain D(2x) ≤ 4D(x), then induct.
- Search completed over RHTower corpus; partial=false, compiler coverage mostly pending/stale and semantic coverage unmeasured. Verify all used source declarations in this toolchain.

## Progress

- Attachment read and mathematical normalization checked.
- Serena symbol API rejects Lean paths as ignored; use direct source reads/patches.
- Existing unrelated worktree changes left intact.

## Dependency-closed paper proof

Write k(x)=∫g(u)g(u+x)du, D(x)=k(0)-k(x). For g∈L², translates remain in L² and products are integrable by Cauchy–Schwarz. Translation invariance gives ∫(g(u)-g(u+x))²du=2D(x). Consequently D≥0. Expanding the difference k(x)-k(y) and applying Cauchy–Schwarz against g gives |k(x)-k(y)|²≤k(0)∫(g(u+x)-g(u+y))²du=2k(0)D(x-y).

Splitting g(u)-g(u+x+y) at u+x and using (a+b)²≤2a²+2b² yields D(x+y)≤2D(x)+2D(y). Hence D(2x)≤4D(x), and induction gives D(L)≤4^m D(L/2^m). If k(L)=0, the right-hand dyadic deficit is at least 4^(-m)k(0). For every x, the valid complementary-shift bound is D(x)+D(L-x)≥D(L)/2. All these arguments include g=0 and require no derivatives or frequency moments.

For a real EWU source, the existing polar condition is ∫g(u)exp(-u/2)du=0. The cosh pole term factors as twice the product of this moment with ∫g(u)exp(u/2)du, hence vanishes. The corpus Lévy formula then gives exactly gammaBracket(0)k(0)+∫₀∞D(x)exp(x/2)/sinh(x)dx. Its integrand is nonnegative because D≥0 and sinh(x)>0 for x>0. Its Bochner integrability follows from the corpus finite Lévy-energy theorem, not from totalization of the integral.

## Interpolation obstruction and positive survivor

The requested extension from dyadic reciprocals to all interior points is false. Even the continuous positive-definite kernel cos(5πx/(2log 2)) is zero at log 2 and equals its value at zero at 4log 2/5. Its real Gram form is a sum of the squares of the sine and cosine sums.

There is also an actual real L² family. Let d=log 2/10, a=4log 2/5 and g_N be the sum of the indicators of (ja,ja+d], j=0,…,N. Distinct pulses are disjoint. A shift by log 2 overlaps no two pulses: its distance from each integer multiple of a is at least log 2/5>d. A shift by a overlaps exactly N adjacent pairs. Thus k_N(0)=(N+1)d, k_N(log 2)=0, k_N(a)=Nd. Therefore D_N(a)/k_N(0)=1/(N+1), arbitrarily small. This rules out every positive universal bound at the fixed interior point a, not only a quadratic interpolation formula.

Positive survivors: the exact EWU Lévy identity, the full L² Krein increment bound, the dyadic lower bounds, and the complementary-shift lower bound. Paper proofs closed above; Lean verification passed. No external search or novelty claim.


## Final audit, 2026-10-17

- `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/EvenSectorLevyKreinRigidity.olean GaloisForLFunctions/RHTower/EvenSectorLevyKreinRigidity.lean`: exit 0, no diagnostics.
- `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/AutocorrelationBlindInterpolationObstruction.olean GaloisForLFunctions/RHTower/AutocorrelationBlindInterpolationObstruction.lean`: exit 0, no diagnostics.
- Scratch `lake --old env lean /tmp/ewu-levy-api.lean`: exit 0. Mathlib declarations checked via `have := @Name` with explicit universe levels. Nine principal endpoint axiom audits return only `propext`, `Classical.choice`, `Quot.sound`.
- Both modules imported directly by `formal/GaloisForLFunctions/RHTower.lean`. No umbrella or full build run. One owned Lean process at a time; no heartbeat changes or numerical jobs.
- `scripts/formal_tools.py lint`: exit 1, solely 19 unrelated modules unreachable from their theorem-area umbrellas. Neither task module appears among the errors; no proof-debt error remained in the final lint output. Concurrent work elsewhere in the tree was preserved.
- A concurrent targeted build regenerated shared dependencies during auditing; the final imported-module audit succeeded after their artifacts returned.
- Negative interpolation claim and exact positive survivors recorded in `docs/drafts/pipeline/5-failed/ewu-continuous-interpolation-from-prime-two-blindness-2026-10-17.md`.

The original interval-wide positive bound is contradicted by an unconditional L² counterexample family. Do not mark the original goal achieved by silently replacing that false requirement. User was asked whether to accept the proved package plus obstruction or investigate extra EWU structure; no reply had arrived at this audit.

## Smooth EWU continuation

`EvenSectorSmoothBlindInterpolationObstruction.lean` now strengthens the counterexample to `RealSmoothEvenPolarTestFn` itself. A centered train of `evenPolarProfile 20` packets gives `k(0)=(N+1)M`, `k(4 log 2 / 5)=NM`, and `k(log 2)=0`, with `M>0`. Thus the normalized deficit at this fixed interior point tends to zero. Its final no-go theorem has no hypotheses.

Direct `lake --old env lean` compilation and scratch API/axiom checks passed. Six audited declarations use only `propext`, `Classical.choice`, `Quot.sound`. Third module wired into `RHTower.lean`. Latest formal lint fails on 15 unrelated HTGeometry umbrella omissions and the package-root BiScaleUncertainty module; no task-module failures. No heartbeat increases or numerical experiments. Full proof and gate record: `ewu-smooth-polar-interpolation-obstruction-2026-10-17.md` in this directory.

The narrower EWU investigation is resolved negatively. Third consecutive goal turn revalidated the original attachment, current no-go source, and umbrella wiring. Same mathematical blocker persists; `update_goal(status="blocked")` succeeded. Goal is blocked pending user correction of the false interval requirement, not complete.
