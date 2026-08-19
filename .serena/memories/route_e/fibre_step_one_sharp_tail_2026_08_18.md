---
name: route-e-fibre-step-one
description: Route E cards 3-5 — the Turán-Kubilius ceiling is removed; the gate is now Halász's mean value theorem
metadata:
  type: project
---

Three stage-2 Route E cards (`route-e-reciprocal-marker-mobius-hall-law`,
`route-e-growing-reciprocal-marker-low-breadth-transport`,
`route-e-coprime-square-root-mobius-product-sign-law`) share one gate. Cards 1-2
(`route-e-cofactor-amplified-e3-token-supply`, `route-e-forbidden-support-e3-stability`) have a
different one. Full detail: `docs/drafts/pipeline/1-in-progress/moebius-halasz-log-saving-programme.md`.

**The requirement is `o(1/log x)`, not "a small fraction of √x".** The marker join discards bad
fibres from a dyadic block carrying `≍ √x/log x` primes, so a constant tolerance is useless however
small. Do not build a positive-proportion statement and mistake it for progress.

**Done (2026-08-18): the `1/log log x` ceiling is gone.** It came from Turán-Kubilius, not from
anything intrinsic: `Sieve/OmegaSpectralFibre` writes `∑ μ ≈ (1/W)∑ μ·ω_P` and pays the variance
through Cauchy-Schwarz, and that square root turns a relative error `W` into `1/W` with
`W ≤ log log x + O(1)`. Replaced by the exact Ramaré route, where the rough term enters **squared**:
`Sieve/FibreNonRoughSpectral` → `FibreNonRoughKernel` → `NonRoughBilinearExact` (the factorisation is
an *identity* — the square-multiple diagonal vanishes since `μ(pm)=0` when `p∣m`) →
`FibreBilinearCapstone` → `FibreRamareBilinearBridge`, which lands on the corpus's own
`ramareBilinear`, so `Sieve/RamareBlockSplit` applies unchanged.

**The gate is the perturbed Möbius contour, not Halász.** `OmegaBudgetLadderTail`'s `hU` needs a *saving* on
the cofactor polynomial; the `ω_P` normalisation left a plain Möbius cofactor (bounded by
`Sieve/CofactorLowFreqBound`), the exact Ramaré route leaves the damped `μ(m)/(ω_P(m)+1)`. All of
Halász's arithmetic inputs are now owned: `RHTower/MoebiusPretentiousGap` (distance for `μ`, uniform
in frequency — replaces the corpus's much weaker `exists_antiscale_frame`),
`RHTower/DampedPretentiousGap` (same for the damped function, uniform in `t`),
`Sieve/DampedMultiplicative` + `DampedEulerSeriesBound` + `DampedPrimeTerm` + `DampedTsumCompare`.
Halász would also do it, and all of its *arithmetic* inputs are owned, but its analytic core
(Perron + large-values dichotomy) has no cheap form: trivial Perron loses a full `log x`, giving a
bound above 1 at these parameters. Prefer the contour: `hU` only needs a saving on the **low window**
`|w| ≤ w₀`, i.e. a long sum with a small twist, which is exactly the zero-free-region regime
`Sieve/CofactorLowFreqBound` already handles for the plain cofactor. Extending it needs only that
`G_t(s) = (1/ζ(s))·∏_{p∈P} dampedEulerFactor t p s` is holomorphic where `1/ζ` is and bounded by a
`t`-uniform polylog — and `Sieve/DampedEulerCorrection.norm_prod_dampedEulerFactor_le` already proves
that on `Re s ≥ 1/2`, which contains the whole contour region. So each of the six contour modules
(`MoebiusContourBound`, `PerronSharpSubstitution`, `MellinAbscissaDecay`, `MoebiusContourKappaTwo`,
`MoebiusSaving`, `MoebiusKappaTwoRate`) gains one bounded multiplier per edge. Next brick: the Euler
product identity `∑'_m μ(m)t^{ω_P(m)}m^{-s} = (1/ζ(s))·∏_{p∈P} dampedEulerFactor t p s` on `Re s > 1`.

Dead ends, do not retry: restricting to `ω_P = 1` globally (the two discards pull `P` in opposite
directions); expanding `t^{ω_P(m)} = ∑_{d∣gcd(m,∏P)}(t−1)^{ω(d)}` (`2^{|P|}` terms, no gain);
the corpus's long-range Möbius savings (`MoebiusKappaTwoRate`, exponent 1/3) at window
`exp((log x)^{0.99})`.

**Cards 1-2 are a separate, harder gate.** They need Matomäki-Teräväinen Theorem 1.2 itself, whose
Type I estimates rest on Watt / Deshouillers-Iwaniec twisted fourth moments. Card 2's own gate says
so. No rearrangement of corpus assets avoids it. See [[mt-e3-programme]].

Zeta assets built on the way, reusable: `RHTower/ZetaNearOneLineBound` (growth left of the one-line),
`ZetaDerivNearOneLineBound` (`ζ' ≪ log²|t|`), `ZetaOneLineLogPowerLowerBound`
(`|ζ(σ+it)| ≥ c(log|t|)^{-11}` for `σ ≥ 1`, abscissa-free — three-four-one alone only gives
`δ^{3/4}(log|t|)^{-1/4}`).
