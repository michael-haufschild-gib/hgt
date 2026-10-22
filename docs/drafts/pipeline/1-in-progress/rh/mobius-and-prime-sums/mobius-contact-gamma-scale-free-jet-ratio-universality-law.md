# Möbius-contact Gamma scale-free jet-ratio universality law

- **ID:** mobius-contact-gamma-scale-free-jet-ratio-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `tendsto_gammaFactorialFirstJetDefect_div_mobiusContactHarmonicScale` and
  `mobiusContactGammaHigherJet_completeResidueHierarchyUniversality`
- **Statement:** At every nonzero Gamma microscope point, eliminating the common Möbius-contact
  harmonic/factorial scale produces four intrinsic cross-observable limits: ordinary second jet
  over first jet tends to `-3/x`, projective second jet over first jet tends to `-1/x²`,
  projective third jet over squared first jet tends to `-3/(2x²)`, and log-curvature over the
  exponential-envelope defect tends to `x⁶`.

## Goal

Use the shared arithmetic normalization exposed by independently terminal first- and higher-jet
laws to derive scale-free transition invariants between Gamma hypersurface defects.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `tendsto_gammaFactorialFirstJetDefect_div_mobiusContactHarmonicScale`
- `mobiusContactGammaHigherJet_completeResidueHierarchyUniversality`
- `mobiusContactGammaHarmonicMicroscopeScale_eq`
- `mobiusContactGammaHigherJetHarmonicScale_eq`
- `mobiusContactGammaHigherJetFactorialScale_eq`
- `gammaHarmonicMicroscopeScale_ne_zero`
- `reciprocalGammaFactorialScale_ne_zero`

## Proof

**[PROVED HERE]** Fix `x ≠ 0`. Write `Hₙ` for the common contact-harmonic scale and `Sₙ` for
the common contact-factorial scale. Existing terminal laws give

`D₁/Hₙ → -2/x`,
`D₂/Hₙ → 6/x²`,
`P₂/Hₙ → 2/x³`,
`P₃/Hₙ² → -6/x⁴`,
`L/Sₙ² → -4π²/x⁴`, and
`E/Sₙ² → -4π²/x¹⁰`.

All six limiting denominators are nonzero when `x ≠ 0`. Continuity of division therefore gives

`(D₂/Hₙ)/(D₁/Hₙ) → -3/x`,
`(P₂/Hₙ)/(D₁/Hₙ) → -1/x²`,
`(P₃/Hₙ²)/(D₁/Hₙ)² → -3/(2x²)`, and
`(L/Sₙ²)/(E/Sₙ²) → x⁶`.

For every `n ≥ 1`, `Hₙ ≠ 0`; for every `n`, `Sₙ ≠ 0`. Field cancellation identifies these
normalized quotients respectively with `D₂/D₁`, `P₂/D₁`, `P₃/D₁²`, and `L/E`. Hence the four
raw scale-free quotient limits follow. No computation is used. ∎

## Strict gain over corpus endpoints

The first-jet law and higher-jet hierarchy report six separately normalized limits. Neither
compares different defect strata. Their common contact normalization can be eliminated, revealing
four intrinsic transition invariants independent of the factorial and harmonic microscope scales.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.MobiusContactGammaScaleFreeJetRatioUniversalityLaw`
- Main theorem:
  `mobiusContactGamma_scaleFreeJetRatioUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/MobiusContactGammaScaleFreeJetRatioUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Arithmetic connector:
  `mobiusContactGammaDefect_mul_harmonic_eq_gammaHarmonicMicroscopeScale`.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for reciprocal-Gamma pole scaling, harmonic/polygamma Laurent expansions, Gamma Schwarzian jets,
and scale-free higher-jet defect ratios found no exact collision. Closest primary sources:

- D. P. H. Ulgenes, *Series and Product Representations of Gamma, Pseudogamma and Inverse Gamma
  Functions*, <https://arxiv.org/abs/2301.09699>, derives series and Taylor-coefficient formulas
  for Gamma and reciprocal Gamma, not factorial pole microscopes or cross-defect quotient limits.
- S. Sekatskii, *Summation rules for the values of the Riemann zeta-function and generalized
  harmonic numbers obtained using Laurent developments of polygamma functions and their
  products*, <https://arxiv.org/abs/2112.04380>, uses Laurent expansions to obtain harmonic/zeta
  summation identities, not the projective first/second/third-jet transition ratios here.
- J. K. Langley, *The Schwarzian derivative and the Wiman--Valiron property*,
  <https://arxiv.org/abs/1307.3042>, studies value-distribution properties of Schwarzians of
  general meromorphic functions, not reciprocal-factorial Gamma blow-ups or their Möbius-contact
  normalization.

## Log

- 2026-07-23 — terminal theorem-body scan exposed a shared normalization not eliminated by either
  endpoint.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
