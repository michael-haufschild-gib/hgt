# Polynomial orbit carriers meet a sharp Gamma dimension wall, formalized

- **ID:** `suzuki-polynomial-carrier-gamma-dimension-wall`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PAPER-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:** `./suzuki-polynomial-carrier-gamma-dimension-wall.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/SuzukiPolynomialCarrierGammaWall.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiPolynomialCarrierGammaDimensionWall.lean`
  - `formal/GaloisForLFunctions/RHTower/PolyDistortedHomogeneousThreshold.lean`
  - `formal/GaloisForLFunctions/RHTower/PolyCarrierForcedClosure.lean`
  - `formal/GaloisForLFunctions/RHTower/WallOneBlockEstimate.lean`
  - `formal/GaloisForLFunctions/RHTower/WallBlockSeries.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)` lattice embedding threshold `κ > d/2` | `summable_latticeBracket_two_kappa_iff` |
| `(2)` Gamma threshold `κ < σ` | `integrable_suzukiGammaDistortedNormSq_iff` |
| `(3)` a common exponent exists exactly when `d ≤ 1` | `exists_gamma_dimension_window_iff`, `suzukiPolynomialGammaDimensionWindow_iff` |
| `(4)` the rank-two wall | `no_gamma_dimension_window_of_two_le` |
| `(5)`, `(7)` the distorted squared Gamma carrier | `suzukiGammaDistortedNormSq`, `suzukiPolynomialDistortedGammaNormSq` |
| `(6)`, `(8)` the exact distorted tail exponent | `suzukiGammaDistortedNormSq_rpow_tendsto`, `suzukiPolynomialDistortedGammaNormSq_rpow_tendsto` |
| `(9)` the sharp `L¹` threshold, both halves | `integrable_suzukiGammaDistortedNormSq`, `not_integrable_suzukiGammaDistortedNormSq`, `integrable_suzukiGammaDistortedNormSq_iff` |
| `(10)`, `(11)` the lattice sum and the joint window | `summable_latticeBracket_two_kappa_iff`, `exists_gamma_dimension_window_iff` |
| `(12)`, `(13)` the concrete rank-one window `(κ,σ) = (2/3,3/4)` | `summable_rankOne_window`, `summable_suzukiOnePrimePolynomialWeightSq`, `suzukiOnePrimePolynomialGammaWindow` |
| `(14)` the distorted homogeneous density and its threshold | `integrableOn_polyDistortedDensity_iff`, `not_integrableOn_polyDistortedDensity`, `lintegral_sq_polyDistorted_ne_top` |
| `(15)` the corrected direct theorem | `memLp_two_of_polyCarrier_and_forced`, with the forced half `memLp_forcedProfile_blockSource` and `exists_bound_lintegral_sq_forcedProfile_oneBlock` |

## Notes

`(14)` is an exact threshold, not an estimate: the distorted homogeneous density is
`|x|^{-1-2σ+2κ}`, and integrability on a terminal ray is `-1-2σ+2κ < -1`, i.e. `κ < σ`.  Both
directions are recorded, because the card's point is the *negative* one — an arbitrary polynomial
group degree is not enough, and at `κ ≥ σ` no constant rescues the homogeneous component, since
forcing only changes the particular solution.

`(15)` is the composition of the two halves.  Its forced half is the Gamma-wall block transfer: the
one-block estimate `‖u‖₂ ≤ C(‖c‖ + e^{max(0,−m)}‖g‖₂)` and the summation of the blocks in `L²`.

`(16)` and `(17)` are the card's survivor list and novelty boundary — route statements, not
theorems.

Every declaration audits to `[propext, Classical.choice, Quot.sound]`.
