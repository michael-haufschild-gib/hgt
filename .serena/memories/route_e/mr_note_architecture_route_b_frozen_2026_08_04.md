# MR-note architecture read; route (B) frozen for the corridor (2026-08-04)

Card: `docs/drafts/pipeline/1-in-progress/mr-splice-wide-range-mean-square.md` (full detail there).
Source: arXiv:1502.02374 (MR expository note), fetched and read in full; text extracted to
scratchpad. It proves exactly the corridor target (λ, windows X^δ, variance ≪ X/(logX)^{1/3−ε})
in 12 pages.

**Two routes:**
- (A) §4, λ-specific: one Ramaré range P = exp((logX)^{2/3+ε}), Q = X^{δ/3}; short prime
  polynomial pointwise ≪ (logX)^{-A} on ALL (logX)^{10} ≤ |t| ≤ X via Perron + log ζ in the
  Vinogradov–Korobov region. BLOCKED for the corpus: needs zero-free exponent κ < 1; corpus's
  3-4-1/DLVP layer is κ = 1 (this is a proof, not a guess: log P ≥ (logX)^κ loglogX vs
  log P ≤ logQ ≪ logX). Littlewood region would give (loglog)^{-1} saving; VK gives
  (logX)^{-1/3+ε}. Both are heavy classical builds (Weyl/Vinogradov sums).
- (B) appendix, general f, NO zero-free region: saving (logX)^{-1/48}. H = (logX)^{1/48},
  logP = (logX)^{1−1/48}, logQ = logX/loglogX. Mechanism: split t at
  |Q_{j,H}| ≶ (logX)^{-100}; small side MVT; large side = well-spaced 𝒯 with
  |𝒯| ≪ exp((logX)^{1/48+o(1)}) (adapted-moment count, [4,L8]), paid by Halász sup of the long
  factor ((logX)^{-1/24}, [4,L3] — the MoebiusUniformFrequency mechanism) and the prime
  large-value refinement ([4,L11]) whose spacing factor exp(−(logX)^{1/5}) absorbs |𝒯|
  (1/5 > 1/48). All corpus-technology-class.

**Also corrected:** my stage-3b model mis-charged the Ramaré rough remainder as a squared
per-window Brun count; the correct cost is the rough DENSITY logP/logQ inside the MVT coefficient
mass — linear, fundamental-lemma constant. And the earlier 3b′ "range induction" guess is
unnecessary for polynomial windows — it is the h→∞-slowly machinery only.

**Frozen next Lean unit (licensed, certified consumer):** variable-ℓ adapted moment for short
prime polynomials — ℓ-fold generalization of `PrimeCubeSupport` (ordered ℓ-tuple of primes with
fixed product: fibre ≤ ℓ^{ℓ−1}; mass ≤ ℓ!(∑|b_p|²)^ℓ), feeding the spaced-count bound.
Then: audit `DirichletLargeValuesCount`/`AlmostOrthogonality` for the Halász–Montgomery duality
piece; the sharp-cutoff Halász sup ([4,L3]) is the known "mean-value Halász" frontier.
