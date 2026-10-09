# Native lag curvature: first-moment regularization

Status: formalized and axiom-audited. RH remains unresolved.

Objective: advance the unconditional RH investigation by isolating exactly which part of the native lag curvature survives endpoint-growing Green weights. This does not assume or establish RH.

Prior corpus audit (search tool only): `SuzukiCriticalOrderedJordanCancellation` already proves ordered convergence and failure of unconditional summability at critical damping. Re-proving scalar convergence would not close the affine-current gap. `WeilLagNativeCurvatureSign` supplies the exact native curvature decomposition but only a coarse pointwise error bound.

Conjecture: the difference between native scaled lag curvature at center c=n+3 and (vonMangoldt c - 1)/c has absolutely summable first moment.

Paper argument:
1. For g(x)=x log x, subtract x²/(2c) and add (x-c)³/(6c²). The resulting second derivative is (x-c)²/(c²x), between zero and 1/(c²(c-1)) on [c-1,c+1]. Midpoint convexity bounds the centered second difference: 0 ≤ Δ²g(c)-1/c ≤ 1/(c²(c-1)). Multiplication by c leaves a summable O(c^-2) bound.
2. For the trivial-zero correction S, existing corpus results give nonnegative, decreasing, convex values. Its nonnegative second differences have bounded first-moment prefixes by discrete summation by parts: sum c Δ²S(c) = b(S(b+1)-S(b))-S(b)-2S(3)+3S(2) ≤ 3S(2)-2S(3).
3. Exact native decomposition then gives the claimed weighted absolute summability. The prime term remains signed and unbounded in total variation; this does not supply the RH-bearing uniform Green bound.

Plan: verify derivative/convexity and summability APIs in a scratch leaf; formalize the bounds and weighted summability; extract the endpoint-growing Green consequence; compile the finished leaf, audit axioms, wire the module, and run formal lint. No web or direct research-file reads. No novelty claim beyond comparison with corpus search hits.

Verified progress: `WeilLagCurvatureFirstMoment.lean` compiled with `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilLagCurvatureFirstMoment.olean GaloisForLFunctions/RHTower/WeilLagCurvatureFirstMoment.lean`, exit 0, no warnings. The complete absolute first moment is at most 2: logarithmic part contributes at most 1/2; the trivial-zero part contributes at most 3*S(2)-2*S(3) ≤ 3/2.

Additional paper consequence: for any correction e with finite absolute first moment, the difference between sum_{n<N}(N-n)e(n) and N*sum_n e(n) is bounded by sum_n(n+3)|e(n)|. Split into finite prefix and shifted infinite tail; bound the two pieces together by the same full first moment. For the native correction the bound is 2. Discrete Green reconstruction then expresses sqrt(N+3)*integerLag(N+3) as the centered prime Green sum plus the exact affine normalization, with absolute error at most 2. The prime Green term itself remains uncontrolled.

Final Lean artifacts:
- `formal/GaloisForLFunctions/RHTower/WeilLagCurvatureFirstMoment.lean`: centered logarithmic bound, exact trivial-zero first-moment telescope, absolute first-moment summability and budget at most 2.
- `formal/GaloisForLFunctions/RHTower/WeilLagCurvatureGreenRegularization.lean`: general first-moment Green estimate, source-free correction identity, exact native Green reconstruction, and integer-lag reconstruction with absolute error at most 2.
- Both modules are wired into `formal/GaloisForLFunctions/RHTower.lean` and discoverable through corpus search.

Verification: both final leaves compiled using `lake --old env lean -o ...`, exit 0. The Green leaf emitted an informational ring tactic suggestion; no compiler error. The proof stays within default heartbeats after replacing ambiguous norm inference with an explicit function argument. A separate scratch import printed axioms for all 17 public theorems: only `propext`, `Classical.choice`, `Quot.sound`; no added axioms or proof holes. Scratch files removed after audit. `git diff --check` passed for umbrella edits. `scripts/formal_tools.py index` completed.

Global gate: `scripts/formal_tools.py lint` exited 1 on nine unrelated unreachable HTGeometry modules: ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra, MontelOpenSetSubsequence, PaperTraceConeBasic, PaperTraceConeFiniteIdeal, PaperTraceConeIdealTransport. No new-module proof-debt or wiring errors were reported. Unrelated modules were not modified.

Admission boundary: the correction is now fully controlled even under growing Green weights. The RH-bearing gap is the centered-prime Green expression with its exact affine normalization. Neither scalar convergence, local curvature sign, nor this uniform correction budget establishes its square-root-scale bound. No external novelty claim; all research reading was limited to Lean corpus search results.
