# Signed prime–polar transport — 2026-10-17

Mission: quantitative coupling of the actual von Mangoldt atomic measure and both branches of the continuum polar measure, retaining signed correlations. Independent BiScaleUncertainty topic; do not work on RH, use hgtl7, or run numerical experiments. The user's attachment `/Users/michael/.codex/attachments/e9ef520a-4498-4562-99e8-1c42812df597/pasted-text-1.txt` governs the ongoing research goal. Read it before continuing if context is missing.

## Goal and state

100 significant theorem packages requested; **9/100 verified**, 91 remain. Goal ACTIVE. Latest turn: verified progress. Count one coherent mathematical package, never helpers or reformulations. Primary ledger: `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport-FACTS.md`. Parent card: `docs/drafts/pipeline/1-in-progress/signed-prime-polar-transport-2026-10-17.md`.

Authoritative `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` was read fully including Trap 10; READ-ONLY. Stay on Section 3.3. Trap 10 prioritizes explicit unconditional producers and forbids subtracting the discrete linear counterterm before floor summation. Do not replace real-ratio continuum cutoffs by floored ones. No commit/push; preserve other lanes' concurrent work. No agents spawned.

## Verified packages 1–8

1. C1 annular average and exact signed Chebyshev coupling, retaining origin, upper endpoint and exp(-x/2) polar shadow.
2. Actual signed source packet, both negative mixed Gram terms, Q≤M²h(0), and transport.
3. Full-half-line scalar admission and actual source cutoffs; not full packet stabilization.
4. Coherent collar source, double Gram energy and joint Schur lower certificate.
5. Rough-source gauge upper estimate with genuine M²||f-g||² remainder; no original source derivative assumed.
6. Exact gauge energy 2(R-h(d))/d²+B/4, position invariance and support budget removing the constructed gauge norm.
7. Signed scalar collar coefficient optimized exactly, including degenerate cases; fixed-width scalar trial only, no residual closure.
8. Real-ratio factorial lift R_K(x)=exp(x/2) sum_{j=1}^K 1_[0,log(K/j)](x). Actual atomic sum T(K), polar integral K H_K−K+KlogK−T(K). W_N=(R_4N−4R_2N+4R_N)/sqrtN has pairing (2B_N−C_N)/sqrtN, 0≤C_N≤1 and unconditional bound (10log(4N+1)+3)/sqrtN. W_N(0)=0, W_N(log4N)=2, so not an autocorrelation. Package8 verified through three leaves and twelve standard-axiom checks; historic evidence in ledger.

## Package 9 — verified continuous producer

Paper: `docs/reports/BiScaleUncertainty/SignedPrimePolarContinuousFactorialProducer.md`.
Card: `docs/drafts/pipeline/3-formalized/signed-prime-polar-grid-preserving-smoothing-2026-10-17.md`.

ε=1/(4N); qε(t)=min(1,max(0,(1+ε−t)/ε)); Uε,K(x)=exp(x/2) sum_{j=1}^K qε(j exp(x)/K). Define S_N=(Uε,4N−4Uε,2N+4Uε,N)/sqrtN globally. It is continuous, supported in [0,log(4N+1)], and S_N(log n)=W_N(log n) for every integer n≥1, including all endpoints. Actual atomic sequence remains finite and absolutely summable; polar integrand is globally integrable.

Piecewise FTC gives the extra polar correction ε K H_K/2+Kρ(ε), ρ=((1+ε)log(1+ε)−ε)/ε. Linear ρ terms cancel. Exact pairing:
ν(S_N)=[2B_N−(1+1/(8N))C_N]/sqrtN,
|ν(S_N)|≤[10log(4N+1)+3+1/(8N)]/sqrtN.

A finite antitone sequence stencil lies in [-2,1], proving S_N²≤4exp(x)/N. On the CLOSED band [log(2N+1),log(4N)], S_N=exp(x/2)/sqrtN. Therefore 1≤∫ℝ S_N²≤16. Small pairing is not caused by vanishing L² norm. Still not an autocorrelation; no uniform signed-packet control or positivity follows.

Namespace `GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar`.
Actual C_c object: `continuousFactorialProducer (n : ℕ)` uses N=n+1.
Main numeric-index-only endpoint: `continuousFactorialProducer_certificate` bundles grid preservation, pairing bound, and both squared L² bounds. Exact pairing: `fullPairing_smoothFactorialBiNull_eq`; domain: `smoothFactorialBiNull_admissible`; boundary: `continuousFactorialProducer_ne_autocorr`.

Five leaves pass final direct `lake --old env lean <leaf> -o <olean>` checks with empty diagnostics: AntitoneDyadicStencil, ClampedExponentialRamp, SignedPrimePolarContinuousFactorialLift, SignedPrimePolarContinuousFactorialProducer, SignedPrimePolarContinuousFactorialEnergy. Antitone helper imports were narrowed and rechecked. Fourteen #print axioms reports use only propext/Classical.choice/Quot.sound. Main #check confirms only n:ℕ input. All imports wired exactly once; index refresh exit0 and endpoint present in LEAN_API.
Evidence `/tmp/spp9-*-final.log`, `/tmp/spp9_final_axioms.lean`, `/tmp/spp9-final-axioms.log`, `/tmp/spp9-index.log`, `/tmp/spp9-lint.log`. Global lint exit1 for eight unrelated unwired modules: DiscrepancyTransformLaw, NyquistPolarDecomposition, NyquistPolarSourceEscape, NyquistResidualKernel, NyquistResidualMass, NyquistResidualOperator, NyquistResidualPartition, SelbergSieveTailQuadraticFormAndTruncatedDivisorGram. No task-local error. No full/umbrella builds. All owned Lean/search/index/lint processes are terminal.

## Next uncounted candidate

`docs/drafts/pipeline/0-backlog/signed-prime-polar-factorial-source-factorization-2026-10-17.md`.
Aim for actual compact continuous sources with explicit energy cost, not another scalar receiver or formal polarization identity. Candidate: A=1+1/(4N), δ=logA/3, k(t)=exp(3t/2)1_[0,δ](t)/(expδ−1), H_N=W_N*k*k*k. Potential sources F(u)=(W_N*k)(−u), G(u)=(k*k)(u). Mixed correlation should be H_N; supports on opposite half-lines should give equal origin energies for F±G and autocorrelation difference 2H_N on x≥0. Product dilation remains ≤A, suggesting exact grid preservation and explicit mean dilation [(1+expδ)/2]^3. ALL of this is a candidate, not proved/countable yet. Quantify source norm growth from shrinking collars; do not infer uniform packet control.

`/tmp/spp9-next-search.json` is partial with interrupted text/source retrieval. Candidates and source arguments were inspected. Before code inspect `exists_sourceTranslate_local_cross_zero` in FiniteSourceEnergyScalarization.lean, `ChebyshevGauge.continuous_windowedTranslate`, and neighboring UnconditionalCoprimeFactorialLiftAndSpectralLaplaceProducer.lean. Broaden documented search to mathlib convolution continuity, associativity, support, L² bounds. No source factorization paper audit yet. Multiple-collar receiver candidate remains parked.

## Lean workflow and reusable details

One owned foreground Lean process at a time; finite checks only; no heartbeat increases. Verify new mathlib names in /tmp with this toolchain. #print axioms only /tmp. `update_plan` unavailable; cards track work. Serena active Python project cannot extract Lean symbols; use precise read-before-edit patches.

Use typed literal lambdas before integral_add/sub rewrites. `Continuous.intervalIntegrable` needs both endpoints explicitly. `HasCompactSupport.mul_left` has implicit multiplier: use `(f := ...)`, not a positional argument. `HasCompactSupport.of_support_subset_isCompact` uses binder K. For squared compact integrability, `apply continuous_sq.integrable_of_hasCompactSupport` before supplying support avoids competing Real measurable-space instances inferred by an untyped `simpa using`.

`Summable.tsum_add/sub`, `tsum_div_const`, `tsum_mul_left`; finite sum division is `Finset.sum_div`. Use `summable_of_ne_finset_zero`, not nonexistent finite-support method. `open _root_.RHTower` for floorSummatory when shadowed. Real cast products sometimes need explicit equalities. C_c coercions need whole-expression type annotations. Shared .olean files vanished during package8; restore only actual unchanged dependency leaves if needed, never full build. No overlay currently needed.
