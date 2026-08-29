# JAS Möbius Half-Density Weak-Schatten Boundary

- **ID:** JAS-W2-BDY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `HedenmalmThetaMobiusPrimeNormalHalfDensityDomainNoGo.lean` · `IndexedDiagonalWeakSchatten.lean` · `JointAncestryGammaThetaBooleanClosedCreation.lean`
- **Statement:** For every Xi copy, the literal Möbius prime-normal half-density diagonal lies unconditionally in weak Schatten `S_{2,∞}`; it is Hilbert--Schmidt exactly on a neutral copy, and global Hilbert--Schmidt admission is equivalent to RH.

## Goal

Construct the exact weak-`ℓ²` boundary carrier demanded by the corpus no-go, without assuming
neutrality or RH. This is not an RH proof by itself. Its intended full chain is:

`physical half-density weak-S₂ diagonal`
→ `Gamma--theta creator × boundary diagonal compensated codiagonal`
→ `divisor-independent source-linear prime-Poisson reflection sewing`
→ `XiPrimePoissonReflectionSewing ρ`
→ `xiPrimePoissonReflectionSewing_iff_internalOnly`
→ `xiDivisorSyndromeIsInternalOnly_iff_re_eq_half`
→ RH.

This theorem closes boundary admission for the first arrow and sharply prevents replacing it by
ordinary Hilbert-space admission: that strengthening is already exactly the RH-bearing neutrality
condition.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, leaf build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus derivation

`HedenmalmThetaMobiusPrimeNormalHalfDensityDomainNoGo` proves that the existing adaptive `ℓ¹`
codiagonal admits the physical half-density exactly when boundary flux vanishes, and explicitly
identifies weak-`ℓ²` or quadratic finite-packet completion as the surviving source law.
`thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap` identifies each coefficient as
the signed universal-minus-twisted Gamma channel gap.
`routeNGammaSewnTwistedCriticalChannelAmplitude_le_universal` bounds its modulus by the universal
critical amplitude `p⁻¹ᐟ²`.
`nthPrimeSubtype_index_add_two_le` gives the ordered decay needed by
`memWeakSchattenClass_ellTwoDiagonal_of_reindex_pow_le`.
`thetaMobiusPrimeNormalProfileHalfDensityAmplitude_sq` and
`thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_mobiusPrimeNormalProfileEnergy`, together
with the boundary-flux criterion, give the exact Hilbert--Schmidt wall through
`isHilbertSchmidt_ellTwoDiagonal_iff`.

Corpus search found no theorem applying weak Schatten membership to this literal physical
half-density amplitude.

## Result

Module:
`GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPrimeNormalHalfDensityWeakSchattenBoundary`

Main declarations:

- `abs_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_le_universal`
- `thetaMobiusPrimeNormalHalfDensityDiagonalSymbol_nthPrime_sq_le`
- `thetaMobiusPrimeNormalHalfDensityDiagonal_memWeakSchattenClass_two`
- `summable_sq_thetaMobiusPrimeNormalProfileHalfDensityAmplitude_iff_boundaryFlux_zero`
- `thetaMobiusPrimeNormalHalfDensityDiagonal_isHilbertSchmidt_iff_boundaryFlux_zero`
- `everyThetaMobiusPrimeNormalHalfDensityDiagonalHilbertSchmidt_iff_riemannHypothesis`

Paper proof: the channel-gap formula and positivity of the twisted amplitude give
`|a_p(q)| ≤ p⁻¹ᐟ²`; after ordered-prime reindexing, `n+2 ≤ p_n` gives
`|a_{p_n}(q)|² ≤ 1/(n+1)`, hence weak `S₂`. The exact square-energy identity converts
Hilbert--Schmidt summability into Route-P node positivity, which the existing theta Green theorem
identifies with zero boundary flux. Quantifying over all copies gives RH exactly. `[PROVED HERE]`

## Novelty audit

Search through 2026-08-29 found general weak-Schatten/operator-RH and Möbius spectral literature,
including [Roesler's eigenvalue formulation](https://doi.org/10.1016/0024-3795%2886%2990255-7),
[Báez-Duarte's Nyman--Beurling criteria](https://doi.org/10.1155/s0161171202013248), and
[Lapidus's spectral-operator criterion](https://arxiv.org/abs/1501.05362), but no source matching
this Gamma channel-gap diagonal, its unconditional weak-`S₂` admission, or its exact
Hilbert--Schmidt/RH wall. Status: `[NOVELTY UNVERIFIED]` pending expert review.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/HedenmalmThetaMobiusPrimeNormalHalfDensityWeakSchattenBoundary.lean` — PASS
- `lake build GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPrimeNormalHalfDensityWeakSchattenBoundary` — PASS (`12791/12791`)
- `#print axioms` on six capstones — only `propext`, `Classical.choice`, `Quot.sound`
- `scripts/formal_tools.py lint` — no forbidden declaration in new module; unrelated pre-existing umbrella reachability failures remain
- umbrella import added to `GaloisForLFunctions/RHTower.lean`

## Next open core

Build a source-defined compensated codiagonal from the weak-`S₂` boundary diagonal and the
Gamma--theta support creator. It must retain divisor coefficients and produce the source-linear
reflection sewing; weak membership alone does not imply neutrality.

## Log

- 2026-08-29 — created directly in 1-in-progress after corpus and literature audits.
- 2026-08-29 — paper proof closed and formalized in Lean; promoted to 3-formalized.
