# Finite Weil joint quantile convergence in every finite moment

Status: formalised and audited. The explicit common-uniform joint realization and the actual joint Gaussian coupling converge in every positive integer error moment and every finite Lp order, for every sequence of nonnegative quadratic-index offsets.

## Objective

Upgrade the same actual common-uniform joint quantile realization from pointwise, compact-uniform and quadratic-mean convergence to every positive moment. Derive all tail/integrability assumptions from the actual finite Weil laws at `k = 2(r+1)^2+t(r)`.

## Corpus evidence

- `WeilLogShiftRawConvexMoments`: raw correction even/exponential moments are dominated by raw index moments.
- `WeilLogShiftCanonicalMassProfile`: pointwise distortion from the arithmetic profile.
- `WeilLogShiftProfileLowerBound`: profile normalization is at least half the arithmetic mass.
- `WeilLogShiftMidpointProfile`: exact normalized midpoint profile and binomial normalization.
- `WeilLogShiftEdgeMidpoint`: midpoint law is the average of the two endpoints of each actual transport edge.
- `WeilLogShiftEdgeMeanBinomialBound`: actual mean differs from the arithmetic center by at most `sqrt((r+2)/2)`.
- `HTGeometry.BinomialTailBetaThreshold`: unconditional binomial exponential-moment estimate.
- Existing joint quantile realization and uniform transverse bound.

Only local Lean sources used. No computations or external papers.

## Proof mechanism under audit

1. Pointwise profile distortion and normalization imply midpoint probability is at most four times the binomial probability.
2. Convexity of the exponential and the exact endpoint pairing transfer midpoint exponential bounds to centered edges. Binomial Hoeffding bound at scale `sqrt(r+1)` is `exp(a^2/8)`.
3. Recenter at the actual edge mean; its normalized shift has absolute value at most one. Obtain the uniform actual scalar bound `E exp(a X_r) ≤ 4 exp(|a|+a^2/8)`.
4. The two signs at `a=1` dominate `exp(|X_r|)` and every integer absolute moment. Use these bounds to control the tails of quantile differences on the common uniform probability space.
5. Combine a.e. convergence with truncation and uniform higher moments. Transfer scalar limits to joint limits via the uniform transverse bound. Any real finite order can then be controlled between positive integer orders.

## Work state

Formalised `WeilLogShiftBinomialExponential`, `WeilLogShiftMidpointDomination`, `WeilLogShiftEdgeExponential`, `WeilLogShiftProjectedMomentBounds`, `WeilLogShiftProjectedMomentLimit`. All five native builds and fourteen axiom audits passed. Stage result and verification details: `../3-formalized/finite-weil-uniform-exponential-scalar-moments.md`. Global lint has ten unrelated errors and no findings in these leaves.

The exact new moment bound is `E |X_r|^p ≤ p! * 8 exp(9/8)` for every natural `p`, every rank and every nonnegative offset. The derivation uses `exp(|x|) ≤ exp(x)+exp(-x)` and the corpus's factorial domination of powers by the exponential. These bounds discharge the existing weak-to-moment-convergence receiver, yielding `tendsto_finiteWeilCanonicalProjectedIndex_moment t p` for every natural `p`.

Next: transport these exact source moment bounds to the common uniform quantile space and combine with its already-proved a.e. joint convergence. A generic truncation argument with uniform higher moments, or a variable-envelope argument using the corpus's nonnegative L1 convergence theorem, should discharge uniform integrability. This step is not yet formalised. Do not infer it from compact probability convergence alone.

## Current proof closure

Use a variable envelope. If `0 ≤ f_r ≤ g_r`, `f_r → 0` a.e., `g_r → g` a.e., `g ≥ 0` is integrable, and `∫g_r → ∫g`, the local nonnegative L1 theorem gives `∫|g_r-g| → 0`. Fixed-envelope dominated convergence gives `∫min(f_r,g) → 0`. The inequality `f_r ≤ |g_r-g| + min(f_r,g)` proves `∫f_r → 0`.

For integer order `m+1`, let `f_r` be that power of the joint quantile distance. The joint diagonal bound and its 2-Lipschitz diagonal map give `distance ≤ 2 + 2|X_r-X|`, a.e. on the common unit interval. Repeated elementary power bounds dominate this by a fixed polynomial in `X_r^(2(m+1))` and `X^(2(m+1))`. Its integrals converge by the newly formalised scalar moment theorem and the exact quantile pushforward. This closes the integer-order paper argument. The finite-real-order extension will use the monotonicity of Lp norms on this probability space after checking the local API.

Native state: all six leaves compile with empty logs: `HTGeometry.IntegralVariableEnvelope`, `RHTower.WeilLogShiftQuantileMoments`, `RHTower.WeilLogShiftQuantileMomentEnvelope`, `RHTower.WeilLogShiftQuantileEnvelopeIntegral`, `RHTower.WeilLogShiftJointQuantileMomentLimit`, and `RHTower.WeilLogShiftJointQuantileLpLimit`. Each is imported exactly once by its theorem-area umbrella. All nine direct dependencies are fresh; all eleven incoming imports were checked. Verification uses the six native leaf builds and a native scratch audit.

The explicit polynomial envelope at order `p` is `2^p * (2^p * (1 + 2^p * (2 + x^(2p) + y^(2p))))`. Its bound and its integral identity are proved. The checked Lp extension identifies the integer Lp norm with the positive root of the checked error moment, then bounds any finite order by a larger integer order using monotonicity on the unit-interval probability measure. Exact joint pair pushforward transfers the same statement to the already-constructed actual joint Gaussian coupling. The exponent ranges over `NNReal`.

## Formal roots and verification

- `RHTower.tendsto_finiteWeilCanonicalJointQuantile_moment_gap_zero` and `RHTower.tendsto_finiteWeilCanonicalJointGaussianCoupling_moment_gap_zero`: every positive integer error moment tends to zero.
- `RHTower.tendsto_finiteWeilCanonicalJointQuantile_eLpNorm_nat_zero`: every positive integer Lp norm tends to zero.
- `RHTower.tendsto_finiteWeilCanonicalJointQuantile_eLpNorm_zero` and `RHTower.tendsto_finiteWeilCanonicalJointGaussianCoupling_eLpNorm_zero`: every finite Lp order tends to zero.
- `RHTower.finiteWeilCanonicalJointQuantile_eLpNorm_coupling`: exact transfer of the norm through the joint pair pushforward, for any `ENNReal` exponent.

The increment contains 28 theorems and one definition. `/tmp/hgt-joint-all-moments-final-audit.lean` checks all 29 declarations and 29 local API references. Native exit 0; the axiom audit found only `propext`, `Classical.choice`, and `Quot.sound`. Metadata audit issues: none. Refreshed local lexical index contains all six listed roots and reports no proof markers.

Global `scripts/formal_tools.py lint` reports three unrelated errors and 367 warnings: unreachable `RHTower.CCMPolarOddPrimeJumps`, unreachable `HTGeometry.QKrawtchoukCompanionTriangular`, and `sorry` in `CCMPolarOddPrimeJumps.lean:104`. None concerns the six increment leaves. Logs and audit summaries use `/tmp/hgt-joint-all-moments-*`.

All mathematical sources for this increment are local Lean declarations. Native proof repairs: beta-reduce the pointwise integrands before rewriting `ofReal_norm`; use the order-topology squeeze theorem for `ENNReal`, since `squeeze_zero` is real-valued.
