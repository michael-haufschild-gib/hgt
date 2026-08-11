# Attempt 6: the truncation exchange of the H-mass open core is PROVED (2026-08-11)

Card `hodge-sign-wall-constructed-pairing`, module `RHTower/GaussHodgeVerticalExtraction.lean`
(wired, built, axiom-clean, 6 theorems).

The open core after attempts 4–5 was a limit exchange: extract the conjugate-pair diagonal of
a squared explicit formula over the infinite divisor. Attempt 6 proved the exchange itself:
- `tendsto_tsum_pencil_cesaro_star_mul` / `_norm_sq`: for ANY ℓ¹ coefficient family on ANY
  index and ANY unimodular modes — no gap, separation, injectivity or correlation input — the
  Cesàro mean of the squared pencil converges to the equal-mode pair diagonal. Dominated
  convergence over ℓ¹×ℓ¹ coefficient pairs; scalar geometric Cesàro law per pair. Externally:
  Bohr almost-periodic Parseval [REDISCOVERED]; corpus-new at infinite index.
- `tendsto_cesaro_divisorCharPencil_norm_sq`: instantiation over the FULL Xi divisor with the
  vertical flow exp(i·Im ρ) and Burnol characters; strip placement gives the uniform bound.
- `xiZeroCopyVerticalMode_lineConjEquiv`: the reflected partner 1−conj ρ shares the ordinate —
  each reflection pair aggregates in one mode fiber.
- `charPair_oddBlock`: the reflection-odd 2×2 block of the extracted diagonal is EXACTLY the
  centered cosh defect p^{2Re−1}+p^{1−2Re}−2 — the extracted diagonal carries the Hodge/seam
  mass. `tsum_pencil_pairDiagonal_re_nonneg`: the extracted diagonal is ≥ 0.

**Open core, final form:** the only unproven step in the whole chain (sign, mass = seam,
prime-side evaluation, extraction, truncation, positivity, RH-equivalence all Lean-proved) is
SOURCING the ℓ¹ vertical pencil `Σ_ρ v_ρ·char_p(ρ)·e^{i n Im ρ}` from prime-side data. The
vertical mode is a conjugate-pair (bilinear) divisor sample; the formalized information-gap
theorem says no holomorphic channel supplies it. Candidate shapes for the sourcing: squared/
autocorrelated explicit formulas (Montgomery-type, MRBilinear lane) or a definitizable Krein
intertwiner (attempt-2 survivor; Connes–Consani Sonin compression arXiv:2006.13771).

Key reusable corpus interfaces discovered: `FiniteExponentialPencilMeanSquare` (scalar/finite
Cesàro layer + tsum dominant-packet survival), `GeneralizedDirichletMeanValue` (finite
Bohr–Parseval with explicit error), seam layer (`XiPrimeSeamReflectionEnergy`), and
`xiZeroCopyLineConj_support` (CCMClosedXiConformalKreinLaw, namespace
GaloisForLFunctions.RHTower).
