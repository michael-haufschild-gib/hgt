# Literal critical Suzuki limit for the untruncated collared source, general moving apertures, and RH-complete family transfer

- **ID:** sz-collared-source-infinite-head-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Source:** collared critical-family calculus, real-lag integration by parts, regularized polar normalization, general moving-aperture Gamma-liminf, and RH-complete grid-tent transfer.
- **Statement:** The untruncated collared critical source has full literal Suzuki first variation equal to its complete extended energy, general moving apertures satisfy strong-L² Gamma-liminf both under uniform supercritical correlation decay and under coupled shift-aperture regimes without correlation decay, and complete Suzuki first-variation nonnegativity on `factorialTentPattern` and `gridTentPattern` is unconditionally equivalent to the Riemann Hypothesis with uniform finite-shift deficits across all five known positivity regimes.

## Exact target

For `g=criticalCollaredSource S b`, prove

`(autocorr(g,0)-suzukiCriticalSourcePairing(g,ω))/ω`
`  → criticalCollaredCompleteEnergy S b` as `ω→0+`, in EReal,

together with:
1. Uniform moving-aperture / infinite-aperture shift thresholds `ω₀ > 0` independent of `V ∈ [V₀, ∞]` and normalized pattern `b` across high dyadic blocks, polynomial scale windows `[M, LM]` (`L ≤ M^δ`), and arbitrary-depth lacunary block unions.
2. Coupled general moving-aperture Gamma-liminf `W_ext(g) ≤ liminf_j Q_{ω_j}(f_j)` whenever `A_j > 2 R_j` and `ω_j A_j exp(A_j/2) ||f_j-g||₂ → 0` (without requiring supercritical correlation decay on the approximants `f_j`).
3. Exact real-valued complete first variation and two-way `RiemannHypothesis` sign equivalence across the RH-complete families `factorialTentPattern` and `gridTentPattern`, plus grid-scale-uniform (`n`-independent) finite-shift literal Suzuki deficits across `[-3/10, 3/10]`, odd `[-181/500, 181/500]` past `(log 2)/2`, dyadic blocks, polynomial windows, and lacunary block unions.

## Failed direct attempt and learned boundary

The source definition is
`g(x)=1_(x≤0) σ(exp(-x)-1) exp(x/2) B(exp(-x))`.
Its pointwise envelope has only exponent 1/2. A claim of exponent 3/2 from that
envelope is incorrect. Bounding both correlation factors absolutely gives only
critical half-decay and does not pay the growing pole or infinite prime head.

The corpus supplies the missing oscillatory structure:

- `criticalFactorialPhasePrimitive_hasDerivAt` and
  `criticalFactorialPhasePrimitive_bound` give a bounded primitive G of B,
  with `|G|≤12 sum |b_n|/(n+1)`.
- `abs_realPhaseCombination_sub_le` gives a global Lipschitz bound for B.
- `criticalCollarWeight` is σ(v-1)/v²; its derivative is integrable and it
  vanishes at v=1 and at infinity.
- `integral_criticalCollaredSource_mul_dilate` identifies the integer-lag
  correlation. Its clock-change proof extends to every real r≥2.

## Correlation decay from the bounded primitive — proved on paper and in Lean

For fixed S,b, there is K≥0 (`criticalCollaredDecayConstant S b`) such that

`|autocorr(g,t)| ≤ K exp(-3t/2)` for every t≥0,

and uniformly across all `V ≥ 1` for both the sharp truncation
`criticalCollaredSharpTruncation V S b` and the smooth upper-collared source
`criticalTruncatedSource V S b`.

For r=exp(t)≥2, the clock change gives the exact formula

`autocorr(g,log r)=r^(-1/2) integral_1^infinity H(v) B(rv) dv`,
`H(v)=criticalCollarWeight(v) B(v)`.

H is locally absolutely continuous, vanishes at both endpoints, and
`||H'||₁ ≤ ||B||∞ ||ψ'||₁ + Lip(B)||ψ||₁`.
Integration against `G(rv)/r` gives

`|integral H(v)B(rv)dv| ≤ ||G||∞ ||H'||₁/r`.

This pays the extra factor through actual phase cancellation. Restricting to
`[1,X]`, the Lipschitz phase and smooth weight are absolutely continuous there,
as is their product (`AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`).
Letting `X → ∞`, `H(X)G(rX) → 0` while both integrands are absolutely integrable.

## Absolute infinite-head assembly — proved on paper and in Lean

The inspected exact coefficient is
`c_ω(n)=n^ω product_(p|n)(1-p^(-2ω))`.
For n≥2 and ω>0, choosing one prime divisor while all other factors lie in `[0,1]`
and `1-exp(-2ω log p)≤2ω log p` yields the uniform divided-coefficient bound

`0≤c_ω(n)/ω≤2 n^ω log n` (`suzukiShiftedCoefficient_div_bounds`).

If a source correlation obeys `|C(t)|≤K exp(-βt)` with `β>1/2`, the primary and
pole bounds give `|sourceCusp_ω(u)|≤K' exp(-βu)` uniformly for small positive ω.
Choosing `0<δ<(β-1/2)/2` and restricting `ω≤δ`, every divided non-unit arithmetic
term is dominated by a constant times `log(n) / n^(β+1/2-δ)`, a summable series.
Absolute Fubini identifies the pairing with the infinite cusp sum, and dominated
series convergence yields the full von Mangoldt sum.

## Polar normalization retains the regularized endpoint — proved on paper and in Lean

`criticalCollaredPolarEndpoint` is explicitly the primitive regularization
`-integral ρ'(v)G(v)`, where `ρ(v)=σ(v-1)/v`. It is not an absolutely integrable
physical half-exponential moment; absolute Fubini is never applied to that moment.

Using the sharp L² truncation `g_V = g · 1_[-log V, 0]` (`criticalCollaredSharpTruncation V S b`),
for `r ≥ 2` and `V/r ≥ 1`, integration by parts retains the exact moving upper boundary
`H(V/r)G(V)/r` and gives the `V`-uniform bound

`|C_V(log r)| ≤ K r^(-3/2)`.

Each compact L² truncation has absolutely integrable weighted moments, so ordinary
Fubini gives its exact polar product `(∫_1^V σ(v-1)B(v)/v²) (∫_1^V σ(v-1)B(v)/v)`.
Passing `V = k + 1 → ∞` under the `V`-uniform `O(e^{-3t/2})` correlation envelope
identifies `4 ∫_0^∞ C(t) cosh(t/2) dt = 2 R_c E_c` without any absolute Fubini on
the untruncated half-exponential moment.

## Gates

- [x] Actual source definition, bounded primitive, Lipschitz phase, and regularized polar endpoint inspected.
- [x] Paper proof of real-lag decay and its uniform sharp-truncation and smooth-cutoff versions.
- [x] Paper proof of coefficient domination and absolute infinite-head assembly.
- [x] Paper proof of the physical polar expression and regularized polar product.
- [x] All analytic inputs derived from the concrete finite phase combination.
- [x] Canonical Lean checks (`lake --old env lean`) and transitive `#print axioms` audits across all 100 public declarations.
- [x] Owning umbrella (`formal/GaloisForLFunctions/RHTower.lean`) imports all finished leaves once.

Verdict: **BRIDGE**. Closes the untruncated collared first-variation limit, general moving-aperture Gamma-liminf (uncoupled supercritical decay and coupled shift-aperture regimes), and RH-complete `factorialTentPattern` / `gridTentPattern` sign equivalence and uniform deficit transfer. Universal arithmetic positivity across arbitrary receiver apertures remains open.

## Lean certification

All four modules passed canonical `lake --old env lean` checks with zero warnings and zero heartbeat modifications, and all 100 public declarations (`17 + 21 + 43 + 19`) depend exclusively on `[propext, Classical.choice, Quot.sound]`:

1. `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalMovingWindowDeficit.lean` (17 public declarations):
   - `RHTower.suzukiCriticalExtendedWeilEnergy_le_liminf_joint_ae_window`
   - `RHTower.eventually_suzukiCriticalDeficit_of_joint_window_L2`
   - `RHTower.exists_suzukiCriticalUniformShift_of_compact_window_family`
2. `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalMovingAperture.lean` (21 public declarations):
   - `RHTower.suzukiShiftedCoefficient_div_bounds`
   - `RHTower.suzukiCriticalSourcePairing_eq_tsum_of_exp_decay`
   - `RHTower.suzukiCriticalExtendedWeilEnergy_le_liminf_of_exp_decay_tendsto`
   - `RHTower.tendsto_suzukiCriticalSourcePairing_extended_firstVariation_of_exp_decay`
   - `RHTower.suzukiCriticalExtendedWeilEnergy_le_liminf_of_coupled_moving_aperture`
   - `RHTower.eventually_suzukiCriticalDeficit_of_coupled_moving_aperture`
3. `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalCollaredFirstVariation.lean` (43 public declarations):
   - `RHTower.intervalIntegral_realLag_phase_ibp`, `RHTower.integral_Ioi_realLag_phase_ibp`
   - `RHTower.autocorr_criticalCollaredSharpTruncation_eq_ibp`
   - `RHTower.abs_autocorr_criticalCollaredSource_le`, `RHTower.abs_autocorr_criticalCollaredSharpTruncation_le`, `RHTower.abs_autocorr_criticalTruncatedSource_le`
   - `RHTower.integral_polar_autocorr_criticalCollaredSource`, `RHTower.four_mul_integral_autocorr_cosh_criticalCollaredSource`
   - `RHTower.suzukiCriticalExtendedWeilEnergy_criticalCollaredSource`, `RHTower.tendsto_suzukiCriticalCollaredSource_firstVariation`
   - `RHTower.exists_dyadic_uniform_movingAperture_suzukiDeficit`, `RHTower.exists_polynomial_window_uniform_movingAperture_suzukiDeficit`, `RHTower.exists_lacunary_uniform_movingAperture_suzukiDeficit`
4. `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.lean` (19 public declarations):
   - `RHTower.tendsto_suzukiCriticalSourcePairing_factorialTentPattern_firstVariation`, `RHTower.tendsto_suzukiCriticalSourcePairing_gridTentPattern_firstVariation`
   - `RHTower.riemannHypothesis_iff_factorialTentPattern_suzukiFirstVariation_nonneg`, `RHTower.riemannHypothesis_iff_eventually_gridTentPattern_suzukiFirstVariation_nonneg`
   - `RHTower.exists_gridTentPattern_uniform_suzukiDeficit`, `RHTower.exists_gridTentPattern_uniform_suzukiDeficit_explicit_scale`
   - `RHTower.exists_gridTentPattern_suzukiDeficit_of_support_le_threeTenths`, `RHTower.exists_gridTentPattern_suzukiDeficit_of_odd_support_le_threeHundredSixtyTwoThousandths`
   - `RHTower.exists_dyadic_gridTentPattern_suzukiDeficit`, `RHTower.exists_polynomial_window_gridTentPattern_suzukiDeficit`, `RHTower.exists_lacunary_gridTentPattern_suzukiDeficit`
