# Suzuki Neumann-dominated shift-cone obstruction, formalized

- **ID:** `suzuki-neumann-dominated-shift-cone-obstruction`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-neumann-dominated-shift-cone-obstruction.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiStrongResolventLimit.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiEdgeDataInterface.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiDiagonalResolventInstantiation.lean`
  - `formal/GaloisForLFunctions/RHTower/IntervalL2ResolventCoordinate.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiIntervalEdgeData.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiScrewKernelRegularity.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiScrewShiftConeAssembly.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiLargeNegativeShiftCentralFlux.lean`
  - analytic layer: `formal/GaloisForLFunctions/HTGeometry/CompactFourierSineKernel.lean`,
    `SignedCharFunCentralJet.lean`, `PrimitiveAverageLimit.lean`, `StrongConvergenceDense.lean`,
    `CfcNormBound.lean`, `CompactOperatorDiscreteSpectrum.lean`, `CompactIntervalL2Pairing.lean`,
    `IntervalL2Density.lean`

## Formal content

| Card | Lean |
|---|---|
| `(2)` strong resolvent limit | `tendsto_resolventFamily_id` (bounded resolvent coordinate; no unbounded operator, no Friedrichs extension) |
| `(4)` endpoint-atom limit value | `neg_integral_exp_mul_deriv`, `neg_integral_expNeg_mul_deriv`, `exponentialEdge_atomCoefficients`, `exponentialSourceCombination_pairing` |
| `(5)` edge-pair transform | `exponentialEdgePair_transform` |
| `(6)` central jet | `deriv_edgePairKernel_zero`, `integral_edgeDenominatorSum` |
| `(7)` endpoint-atom pairing | `integral_endpointAtomPair`, `exponentialSourceCombination_primitive_pairing` |
| `(8)` Weyl normalization | `normalizedEdgeRatio`, `tendsto_normalizedEdgeQuotient` |
| `(2) ⇒ (10)` assembled | `tendsto_normalizedEdgeQuotient_of_resolventFamily`, `SuzukiEdgeData.tendsto_normalizedQuotient` |
| `(9)` dyadic intercept | `suzukiRealAffineZeroIntercept_neg_two_neg_one`, `tendsto_suzukiDyadicNegativeShiftIntercept_atTop` |
| `(11)` small-aperture screw average | `tendsto_xiLineScrewAperture_average_zero` (actual critical ordinates, no hypotheses) |
| `(12)` / Theorem C conclusion | `exists_aperture_eventually_XiC_curvature_lt_intercept_cesaro`, and inhabited end to end: `suzukiScrewShiftCone_obstruction` |
| triangle instantiation | `suzukiScrewIntervalEdgeData`, `suzukiScrewEdgeJet`, `tendsto_suzukiScrewEdgeJet_atBot` |
| resolvent instantiation | `tendsto_harmonicResolventFamily_id`, `intervalHarmonicCoordinate` (compact, self-adjoint, injective, spectrum in `Icc 0 M` on `L²[-a,a]`) |

## What the card actually closes

The passage `(2) ⇒ (10)` — strong resolvent limit, transport to pairings, quotient of limits,
`-i` normalization — is one unconditional theorem, and it is *inhabited*: on `L²[-a,a]` with the
compact harmonic-multiplier coordinate along the polynomial Hilbert basis (built through an
explicit countable Hilbert basis, since mathlib has no `Lp` separability), with pairing vectors
that are the `L²` elements of the named weights `edgeNumeratorWeight`/`edgeDenominatorWeight`
whose values `2 cosh a · H(2a)` and `4a cosh a` are integral identities, at the primitive of the
critical-ordinate screw series.  Composing with the unconditional small-aperture limit `(11)` and
the strictly negative Xi curvature threshold yields Theorem C's conclusion with no hypothesis:

```text
suzukiScrewShiftCone_obstruction :
  ∃ A > 0, ∀ᶠ L in atTop,  (XiC''(0)/XiC(0)).re < 2·q_A(-L) - q_A(-2L)
```

— at some positive aperture, every sufficiently negative dyadic shift pair puts the normalized
affine intercept on the side forbidden by the central Herglotz sign.

## Hypotheses

None beyond object data.  No RH, no numerical certificate, no `sorry`, `axiom`, `opaque`, or
`unsafe`.  Every theorem named above audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The identification of this edge data with Suzuki's own restricted resolvent and physical
numerator/denominator functionals is the source-matching item the whole folder carries as its open
core ("identify the restricted-Weil trace"); it is research about Suzuki's construction, not
missing Lean, and it is deliberately not introduced as an axiom or wrapper.  The remaining open
gates are research: the source-selected nonescaping pair with full jump Pick kernel, and RH.
