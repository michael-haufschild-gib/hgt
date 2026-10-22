# Xi centered reciprocal-Laurent parity/source universality law

- **ID:** xi-centered-reciprocal-laurent-parity-source-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `xiSpectralPoint_reflect`,
  `summable_norm_xiSpectralPoint_inv_sq`,
  `tsum_xiZeroCopyReciprocalSquare_pow`,
  `xiCentralReciprocalMoment_eq_rawDyadicTraces`, and
  `primeArchSourceMoment_eq_xiCentralReciprocalMoment`
- **Statement:** The complete multiplicity-exact centered reciprocal-power trace of Xi has
  vanishing odd part at every absolutely summable order, while its even part is exactly the
  central reciprocal-square moment tower, the fixed prime--Gamma source tower, and the explicit
  raw-endpoint dyadic transform.

## Goal

Restore the signed reciprocal coordinate suppressed by functional-equation square folding and
identify the resulting parity-complete Laurent trace with both endpoint and source charts.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `xiSpectralPoint`
- `xiSpectralPoint_reflect`
- `xiZeroCopyReflectEquiv`
- `summable_norm_xiSpectralPoint_inv_sq`
- `xiZeroCopyReciprocalSquare`
- `summable_xiZeroCopyReciprocalSquare_pow`
- `tsum_xiZeroCopyReciprocalSquare_pow`
- `xiCentralReciprocalMoment_eq_rawDyadicTraces`
- `primeArchSourceMoment_eq_xiCentralReciprocalMoment`

## Proof

**[PROVED HERE]** For a multiplicity copy `q` of the Xi divisor, set
`u(q) = xiSpectralPoint(q)⁻¹`. The exact functional-equation involution satisfies
`xiSpectralPoint(reflect q) = -xiSpectralPoint(q)`, hence
`u(reflect q) = -u(q)`.

The corpus proves summability of `‖u(q)‖²`. Its verified zero-free central interval also gives
`4 < ‖xiSpectralPoint(q)‖`, so `‖u(q)‖ < 1`. Therefore for every `k ≥ 2`,
`‖u(q)^k‖ ≤ ‖u(q)‖²`, proving absolute summability of the full signed reciprocal-power trace
`Lₖ = Σq u(q)^k`.

Reindexing the absolutely convergent sum by functional-equation reflection gives
`Lₖ = (-1)^k Lₖ`. Thus `Lₖ = 0` for every odd `k ≥ 3`. At even order
`k = 2(m+1)`,

`u(q)^(2(m+1)) = (u(q)^2)^(m+1)
                = xiZeroCopyReciprocalSquare(q)^(m+1)`.

Summing identifies `L₂₍ₘ₊₁₎` with `xiCentralReciprocalMoment m`. Existing bridges then identify
this same value with the normalized fixed prime--Gamma source moment and with the explicit dyadic
negative-binomial transform of all raw endpoint reciprocal traces. No computation is used. ∎

## Strict gain over corpus endpoints

The finite secular theorem treats positive centered powers in bounded zero sets. Reciprocal
folding deliberately squares away the functional-equation sign. Endpoint reflection acts in a
nonlinear Möbius coordinate. This closure constructs the missing globally summable signed
reciprocal Laurent tower, proves its complete odd vacuum, and shows that its even quotient is
precisely the already occupied prime--Gamma/endpoint source tower.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiCenteredReciprocalLaurentParitySourceUniversalityLaw`
- Main theorem:
  `xi_completeCenteredReciprocalLaurentParitySourceUniversality`
- Odd-vacuum theorem:
  `xiCenteredReciprocalLaurentTrace_odd_eq_zero`
- Even-source theorem:
  `xiCenteredReciprocalLaurentTrace_even_eq_centralMoment`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/XiCenteredReciprocalLaurentParitySourceUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for centered reciprocal sums of Xi zeros, superzeta parity, reciprocal Laurent moments, and
prime--Gamma source identities found no exact collision. Closest primary sources:

- A. Voros, *Zeta functions over zeros of Zeta functions and an exponential-asymptotic view of
  the Riemann Hypothesis*, <https://arxiv.org/abs/1403.4558>, reviews superzeta functions and
  expansion coefficients centered at `1/2`, but not the multiplicity-exact signed reciprocal
  Laurent tower or its prime--Gamma/raw-endpoint atlas.
- D. W. Farmer and S. M. Gonek, *Pair correlation of the zeros of the derivative of the Riemann
  ξ-function*, <https://arxiv.org/abs/0803.0425>, studies correlations and gaps for zeros of
  `ξ'`, not functional-equation cancellation of reciprocal-power traces.
- G. Chavez and A. Allawala, *Prime zeta function statistics and Riemann zero-difference
  repulsion*, <https://arxiv.org/abs/2102.02280>, relates prime-zeta statistics to zero
  differences, not an exact dyadic transform between reciprocal Xi traces and a fixed
  prime--Gamma source germ.

## Log

- 2026-07-23 — FE reciprocal, secular parity, and endpoint/source bridge terminal scan exposed
  the missing signed Laurent tower.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
