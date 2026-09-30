# Actual LI current: uniform positive small-mass window

- **ID:** LI-CURRENT-WINDOW
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); no novelty claim
- **Parent:** `../1-in-progress/li-actual-current-small-mass-sinc-scaling.md`
- **Objective:** preserve the actual transfer cancellation and prove a growing positive current prefix without an RH premise or signs of higher source moments.

## Exact statement

Let `C_n(v)=liEvenCrossSquareMassAdjacentCurrent v n`, `N=n+1`, and `A=xiShiftAbsoluteMass 0>0`. For every natural `n` and real `v>0`,

`N²v≤25 ⇒ C_n(v)/(2N²) ≥ (787/6552)A >0`.

Consequently every positive-mass current zero satisfies `N²v>25`. All modes `n≤9` are strictly positive throughout `0<v≤1/4`. Constant 25 is certified, not sharp. This leaves arbitrarily large modes at each fixed mass uncontrolled and proves no RH endpoint.

## Dependency-closed paper proof

1. Define `F_N(x)=U_(2N−1)(1−2x)/(2N)`. Its exact finite coefficient is
   `a_j=(-1)^j 4^j ∏_{i=1}^j(4N²−i²)/(2j+1)!`.
   The product vanishes when `j≥2N`; before then each factor lies between zero and `4N²`. Hence `|a_j|≤(16N²)^j/(2j+1)!`. The installed Chebyshev endpoint recurrence is `(2j+3)U^(j+1)(1)=[4N²−(j+1)²]U^j(1)`, with `U(1)=2N`. Taylor's finite polynomial identity supplies the coefficient formula. The weaker bound `(4N²)^j/(j!)²` is also valid.
2. For every actual multiplicity copy, set `λ=xiZeroCopyReciprocalSquare q` and `x=vλ/(1+vλ)`. The exact odd-Chebyshev current atom divided by `2N²` is `λ(1−x)²F_N(x)`. Both factors of `1−x` are retained: one comes from shifted reciprocal and one from unit flux. Existing unconditional `Re λ>0` and `|λ|<1/150` give `|1−x|≤1`, `|x|≤v/150` and `|(1−x)²−1|≤2d+d²`, where `d=v/150`.
3. Set `t=16N²v/150`. For `j≥1`, the factorial majorant's successive ratio is at most `t/20`; thus `|F_N(x)−1|≤(t/6)/(1−t/20)`. Under `N²v≤25`, `t≤8/3`, this is at most `20/39`. Also `N≥1` implies `v≤25`, so `2d+d²≤13/36`. Atom error from `λ` is bounded by `(409/468)|λ|`.
4. Absolute reciprocal summability and the exact complete-copy current identity permit summing every atom. Therefore `|C_n(v)/(2N²)−M_0|≤(409/468)A`. Existing source sector theorem gives `M_0≥(167/168)A`; subtraction yields the stated `787/6552` margin. No signs of later moments enter.

## Verified source and audit scope

- Actual current and complete sum: `LiEvenCrossCompletedAbelInteriorFirstZero.lean`, definitions/theorems at 118 and 123. Exact flux atom: `LiEvenCrossCompletedAbelExteriorFlowNoGo.lean:263`.
- Source absolute mass, summability and strict positivity: `PrimeArchValuationSectorCones.lean:31–45`; source sector lower bound at 70. Source radius: `XiReciprocalSquareSecondMomentRadius.lean:30`.
- Installed `Mathlib/RingTheory/Polynomial/Chebyshev.lean:996` supplies `iterate_derivative_U_eval_one_recurrence`; root directly checked its source. Every name used in the implementation still requires this toolchain's scratch check.
- Independent read-only audit checked normalization, all coefficients including truncation, complete-source domination, rational margin and corollaries. Root spot-checked current, atom and sector declarations and endpoint recurrence. No numerical experiments.
- Corpus deep query `Chebyshev current uniform positive small mass degree square node gap`, cached generation 1143209: `partial=false`, inventory complete, but most compiler metadata pending or stale. Candidate lemmas and source arguments inspected; retrieved bounds concerned other Chebyshev/trace families, plus the already-known two-scale source law. This supports no global absence claim.
- Generic Chebyshev identity is classical: [DLMF 18.5.2](https://dlmf.nist.gov/18.5#E2). This exact actual-source window is a certified quantitative survivor, not claimed significant original mathematics.

## Log

- 2026-09-29 — Independent paper audit closed the requested constant-one window and sharpened it to the exact constant-25 theorem above. Recorded before formal implementation. Lean remains pending.
- 2026-09-29 — `LiEvenCrossActualCurrentEndpointCoefficients.lean` proves exact all-degree finite coefficients, factorial majorant and literal multiplicity-copy normalized flux identity, preserving the squared radial factor. `LiEvenCrossActualCurrentPositiveWindow.lean` proves the exact `787/6552` complete-source margin, strict positivity, exclusion of every current zero from the certified window and all modes through nine positive on `(0,1/4]`. Both named `lake build --old` builds and both final exact source checks passed with no own diagnostics. Scratch API checks and all seven theorem axiom audits passed, using only `propext`, `Classical.choice`, `Quot.sound`. Root spot-checked coefficient normalization and all four current capstones; both leaves wired. No RH conclusion or sharpness claim.
