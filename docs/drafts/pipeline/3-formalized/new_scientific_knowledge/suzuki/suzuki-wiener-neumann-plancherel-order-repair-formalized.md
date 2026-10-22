# Uniform Wiener domination repairs the ℓ¹–Plancherel order, formalized

- **ID:** `suzuki-wiener-neumann-plancherel-order-repair`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-wiener-neumann-plancherel-order-repair.md`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/DiscreteL1Convolution.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiWienerNeumannMajorant.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiWienerMixedNormCarrier.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiWienerOrderSwapCounterexample.lean`

## Formal content

| Card | Lean |
|---|---|
| `(5)`–`(9)` explicit counterexample | `swapFreqFamily`, `lintegral_sq_tsum_swapFreqFamily` (`(7)`), `norm_swapPositionFamily` (`(8)`), `measurePos_not_summable_swapPositionFamily` (`(9)`), capstone `suzukiWiener_orderSwap_counterexample` |
| `(10)`–`(13)` symbol structure | `wienerHighPassSymbol`, `wienerRelativeKernel`, `wienerStarKernel`, `wienerHighPassSymbol_eq` |
| `(14)` majorant mass | `discreteMass_wienerStarKernel` (with equality), `discreteMass_wienerStarKernel_lt_half` |
| `(15)` coefficientwise domination | `enorm_wienerRelativeKernel_le`, `enorm_discreteConvPow_le` (the induction), `enorm_discreteConv_le` |
| `(16)` Neumann inverse | `wienerNeumannInverse`, and the actual two-sided inverse identity `discreteConv_wienerHighPassSymbol_neumannInverse` / `discreteConv_delta_add_neumannSeries` |
| `(17)` uniform coefficient bound | `enorm_wienerNeumannInverse_le`, `enorm_discreteNeumannSeries_le` |
| `(18)` inverse-kernel mass | `discreteMass_wienerInverseKernel`, `discreteMass_neumannKernel` (exactly `(1-M)⁻¹`) |
| `(19)`–`(21)` mixed norm | `eLpNorm_le_two_kernel` (`(20)` per coordinate), `tsum_eLpNorm_le_twoKernel` (`(21)`) |
| `(22)` scalar Plancherel | mathlib `MeasureTheory.Lp.fourierTransformₗᵢ` (the `L²` Fourier isometry) |
| `(23)`–`(24)` position carrier | `suzukiWienerTwoRootCarrier` (summable in `L²_x`, sum bounded by the kernel masses) |
| `(25)`–`(26)` bounded componentwise operators | `summable_tsum_norm_clm_comp` |
| discrete Young layer | `discreteConv`, `discreteEConv`, `discreteMass_discreteEConv` (mass exactly multiplicative), `discreteMass_discreteEConvPow` |

## What the card actually closes

The general `L²_ξ(ℓ¹)` Plancherel order swap is `[FALSIFIED]` by an explicit obstruction: a
band-limited bump translated along the lattice with harmonic amplitudes has finite `L²(ℓ¹)`
frequency norm, while its coordinatewise inverse transforms are unimodular modulations of one
fixed profile whose `ℓ¹` sums diverge on a set of positive measure.  The repair is the uniform
coefficient domination theorem: above the widened high-pass threshold the Wiener symbol's Neumann
inverse — proved to be an actual two-sided convolution inverse — is dominated coefficientwise by
one frequency-independent geometric kernel of mass exactly `L₀⁻¹(1-(C+M)/L₀)⁻¹`, so the two-root
carrier is `ℓ¹_ν(L²_ξ)`, coordinatewise Plancherel is legal, and the position carrier sums
absolutely in the physical Hilbert space with the same bound.  Bounded componentwise operators
preserve the legal evaluation.

## Hypotheses

Object data only: the lattice is any additive group with decidable equality, the symbol data
carries its stated bounds (`|q| ≤ C`, `L₀ ≤ |L|`, threshold inequality), and the carrier
domination is the a.e. two-kernel estimate the Neumann majorant supplies.  No RH, no numerical
certificate, no `sorry`, `axiom`, `opaque`, or `unsafe`.  Every theorem named above audits to
`[propext, Classical.choice, Quot.sound]`.

## Open boundary

Section 5's representation legality — the widened low port is entire of finite exponential type,
hence Gamma-subcritical in every physical boundary chart — is the qualitative context consumed by
the downstream realization cards and is a stated scope note, not a silent gap.  The open gates
are research: composing the repaired carrier with the paired Carleman normal form, the trace-zero
weighted root derivative, and RH or a genuine whole-Connes no-go.
