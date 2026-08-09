# ULF-INV-10 certification chain state — end of 2026-08-09 marathon session (Claude)

Paper theorem: `2-fully-proven/universal-law-field/eigen-pair-prime-identification-derivation.md`
(promoted; single-pole form; all convention pins passed; six in-flight corrections logged).

## Certified this session (all green, standard axioms, wired, indexed)

1. `RHTower.XiWeilSourceInvolution` — sharp realization, hypothesis-free (N8-J).
2. `RHTower.ThetaCuspSeedZeroMean` — D4a zero-mean cancellation.
3. `HTGeometry.FiniteAmplifierPatternCap` — Page rho(Z/2)=1, circle witness, width cap.
4. `HTGeometry.MultiplicativeRegularizationBlind` (extended) — forced compensation +
   cross-system blindness engine (INV-1 core).
5. `RHTower.VonMangoldtLineSeriesSwap` — stage 1: termwise LSeries line integration.
6. `RHTower.XiCDerivStripDecay` — stage 2A: Cauchy transfer of substrip decay to deriv XiC.
7. `HTGeometry.VerticalEdgeVanishing` — stage 2B: exponentially dominated vertical edges vanish
   (both sides).
8. `RHTower.HedenmalmLineTransformBridge` — 5a-1: T α z = 𝓕(tilted flow)(z.re/(2π)) — the
   e^{-izx} ↔ 𝓕 convention linchpin.
9. `RHTower.EigenPairLineIntegrable` — 5a-2: pair-product line integrability from (18a),
   doubled rate.

## Corpus-owned (verified in source, no new modules needed)

- Stage 3: `rectIntegral_cauchyFormula_entire` (+ relative/local/two-pole variants;
  `rectIntegral` def read: bottom − top + i·right − i·left, intervalIntegral edges).
- Hermitian half: fiber-delta evaluations (XiWeilPolarization:212-228) + antidiagonal Gram
  (XiThetaEigenGramLaw).
- Tilted integrability on the WHOLE |Im z| < 1 strip: integrable_hedenmalmThetaEigen_mul_exp
  (rate-1 uniform — Y ∈ (1/2,1) valid, pair-dependent height NOT needed).
- L¹ convolution: fourier_mul_convolution_eq_L1 (XiGuinandWeilRectangularFourier).
- logDeriv split: logDeriv_completed_split. Decay: exists_norm_xiThetaEigenFourier_horizontal_le
  (18a), exists_norm_XiC_horizontal_le.

## Remaining new modules (exactly two)

- **5a-3 (next):** inversion application — express the pair-line product as
  𝓕(convolution of tilted flows) via 5a-1 + fourier_mul_convolution_eq_L1 (both factors'
  tilted integrability corpus-owned; note the conjugate-reflected factor needs the
  sourceInvolution/sharp identity from module 1 to become a genuine 𝓕 of a real-side
  function); then Fourier inversion at ξ = log n/(2π) evaluates the frequency integral of
  stage 1 to the time-side pairing. Watch: mathlib inversion needs continuity of the
  convolution + integrability of both sides (all available: (18a) product integrable = 5a-2;
  convolution of L¹ with bounded-continuous is continuous).
- **5b:** rectangle assembly — corners ±X ± iY, Y ∈ (1/2,1); bottom edge = Λ-series region via
  stage 1 with F := pair-line (5a-2 supplies integrability); top edge folds by XiC evenness;
  verticals by 2B instantiated with 2A + (18a) + linear denominator; interior by stage 3;
  X → ∞ limit. Output: prime-sum form of the eigen-span equivalence; record ULF-INV-9
  decisive-class death; close the lane's gate machine-checked.

## Hygiene protocol used (keep)

Foreground builds, one process; per-file `lake env lean` then `lake build +module`;
`#print axioms` via /tmp scratch; wire umbrella immediately; `formal_tools.py index` after each
batch (background OK); verify no owned processes remain.
