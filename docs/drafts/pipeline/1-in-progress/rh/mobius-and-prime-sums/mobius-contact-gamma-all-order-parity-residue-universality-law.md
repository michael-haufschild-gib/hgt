# Möbius-contact Gamma all-order parity residue universality law

- **ID:** mobius-contact-gamma-all-order-parity-residue-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of `MobiusGammaContactTransgression`,
  `GammaFactorialAllOrderZetaLayer`, and
  `GammaFactorialTailCovariantResidueUniversalityLaw`
- **Statement:** The finite Möbius contact defect is the common all-order Gamma microscope. At
  every odd polygamma order it exposes a nonzero zeta residue; at the adjacent even order the
  leading correction cancels, and the first magnified finite tail is the negative norm of the
  adjacent intrinsic covariant residue.

## Goal

Identify the exact parity law carried by the arithmetic Möbius contact coordinate through every
proved polygamma order, including the finite-tail datum hidden by even-order cancellation.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `mobiusGammaContactPartialCharge_eq`
- `tendsto_gammaFactorialScaledPolygamma_odd_correction`
- `gammaFactorialScaledPolygamma_odd_correction_limit_ne_zero`
- `tendsto_gammaFactorialScaledPolygamma_even_correction`
- `tendsto_gammaFactorialScaledPolygamma_even_finiteTail_eq_neg_covariantResidueNorm`

## Proof

**[PROVED HERE]** Put
`c_n=(-2-mobiusGammaContactPartialCharge n)/2`. Exact contact transgression gives
`c_n=(-1)^n/n!=reciprocalGammaFactorialScale n`. Substitute this identity into the established
all-order Gamma microscope laws. For order `2r+1`, the correction divided by `c_n^(2r+2)`
converges to
`2 (2r+1)! zeta(2r+2)`, which is nonzero because `2r+2>1`. For order `2r+2`, the correction
divided by `c_n^(2r+3)` converges to zero. Multiplying that same even correction by
`(n+1)^(2r+2)` exposes the next term, whose limit is the negative norm of the grade-`2r+1`
covariant top residue at the initial Gamma pole. Thus one contact coordinate separates every
proved odd/even order into reinforcement versus cancellation-with-transverse-residue. No
computation is used. ∎

## Strict gain over corpus endpoints

The all-order zeta layer and finite-tail/covariant-residue law were stated only in the analytic
reciprocal-factorial coordinate. Contact transgression supplied that coordinate arithmetically but
did not propagate it through the complete parity hierarchy. This closure identifies one finite
boundary charge as the universal odd/even microscope and includes the first nonzero datum after
even cancellation.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.MobiusContactGammaAllOrderParityResidueUniversalityLaw`
- Main theorem:
  `mobiusContactGammaAllOrder_completeParityResidueUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/MobiusContactGammaAllOrderParityResidueUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for negative-integer Gamma/polygamma parity, reciprocal-factorial asymptotics, and covariant
finite-tail residues found no exact collision. Closest primary sources:

- L. Fekih-Ahmed, *On the Power Series Expansion of the Reciprocal Gamma Function*,
  <https://arxiv.org/abs/1407.5983>, studies Taylor-coefficient asymptotics and sign oscillation of
  `1/Gamma`, not a contact-normalized all-order polygamma parity law.
- O. Espinosa and V. H. Moll, *A generalized polygamma function*,
  <https://arxiv.org/abs/math/0305079>, relates generalized polygamma functions to Hurwitz zeta but
  does not identify a Möbius contact coordinate or the post-cancellation covariant residue.
- D. P. H. Ulgenes, *Series and Product Representations of Gamma, Pseudogamma and Inverse Gamma
  Functions*, <https://arxiv.org/abs/2301.09699>, derives reciprocal-Gamma coefficient formulas,
  not the odd/even moving-pole microscope hierarchy proved here.

## Log

- 2026-07-23 — complete common-scale corpus scan exposed all-order parity closure.
- 2026-07-23 — dependency-closed proof completed.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
