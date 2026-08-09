# Formalized: Burnol Gamma--Bockstein first-wall extraction law

- **ID:** `burnol-gamma-bockstein-first-wall-extraction-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-gamma-bockstein-first-wall-extraction-law.md` (same directory)

## Lean modules

| Module | Role |
|---|---|
| `GaloisForLFunctions.RHTower.BurnolGammaSteinCollarKernel` | `A`, `γ`, `κ_ε`, `κ̇`, sign chambers |
| `GaloisForLFunctions.RHTower.BurnolGammaSteinMoments` | the exact Bockstein moment `2∫κ̇ e^{-r/2} = 1` |
| `GaloisForLFunctions.RHTower.BurnolDyadicCommutatorStaircase` | the dyadic commutator staircase and its norm difference |
| `GaloisForLFunctions.RHTower.BurnolFirstWallCrossingCorrelation` | the crossing correlation, its positive-lag collapse and the residue |
| `GaloisForLFunctions.RHTower.BurnolReflectedDividedShift`, `…ReflectedPotential` | the reflected orientation and its residue |
| `GaloisForLFunctions.RHTower.BurnolBocksteinLimit` | the negative-lag collapse, the uniform majorant, and the Bockstein limits |

## Formal theorem chain

1. `burnolSteinA`, `burnolCollarGamma`, `burnolSteinA_burnolCollarH` — `(1)`--`(3)`.
2. `burnolCollarKernelDeformed`, `integral_burnolCollarKernelDeformed_mul_mode` — `(4)`, `(5)`.
3. `hasDerivAt_burnolCollarKernelDeformed`, `burnolBocksteinKernel_eq_steinCombination` — `(6)`;
   `integral_burnolBocksteinKernel_mul_mode` — **`(7)`**: `2∫κ̇ e^{-r/2} = 1`.
4. `integral_burnolCollarGamma_mul_mode` — `(9)`; `burnolBocksteinKernel_apply` — `(11)`;
   `burnolBocksteinKernel_pos_iff` — `(12)`: exactly one sign change.
5. **`tendsto_burnolCrossingDepthProfile`** — `(13)`: `q^{-n} W_G(nL+r) → r_G e^{-r/2}` for every
   aperture-constant integrable source; `xiDivisor_tendsto_burnolCrossingDepthProfile` is the
   `ρ`-instance.
6. `burnolBocksteinReading` — `(14)`.
7. **`tendsto_burnolBocksteinReading`** — `(15)`: `𝔅_n(G) → Res_{1/2}(G)`, by dominated
   convergence.  The majorant is uniform in `n`: the correlation collapses explicitly for both
   signs of the lag (`burnolCrossingCorrelationW_eq_of_head`,
   `burnolCrossingCorrelationW_eq_of_head_neg`), giving
   `norm_burnolCrossingCorrelationW_le : ‖W_G(s)‖ ≤ ‖c‖ M e^{-s/2}`, hence
   `norm_burnolDepthProfile_le`; and `abs_burnolBocksteinKernel_mul_mode_le` bounds
   `|κ̇(r)e^{-r/2}|` by `400 e^{-|r|}`, so `burnolIntegrable_bocksteinKernel_mul_mode`.
   Measurability comes from `continuous_burnolCrossingCorrelationW`, proved by gluing the two
   collapsed branches, which agree at `s = 0` because the tail primitive vanishes there.
   The two physical instances are `xiDivisor_tendsto_burnolBocksteinReading_forward` and
   `xiDivisor_tendsto_burnolBocksteinReading_reflected`.
8. **`xiDivisor_tendsto_burnolBocksteinHeadFlux`** — `(16)`: the reflection-odd Bockstein limit is
   exactly the Route-R current `burnolCartierDividedShiftHeadFlux ρ`.
9. `burnolAperturePart`, `burnolDyadicLadder`, `burnolApertureCommutator`,
   `burnolApertureCommutator_shell`, `lintegral_burnolApertureCommutator_normSq` — `(17)`--`(20)`;
   `burnolApertureCommutator_normSq_difference` — `(21)`.
10. **`xiDivisor_tendsto_burnolBocksteinStokes`** — `(22)`: the Bockstein limit equals the
    same-fibre dyadic boundary norm difference.

## Verification

- `lake build GaloisForLFunctions.RHTower.BurnolBocksteinLimit` clean, no warnings.
- Imported by `GaloisForLFunctions.RHTower`.
- `#print axioms` on the numbered theorems: `propext`, `Classical.choice`, `Quot.sound` only.

## Open beyond the card

The card's own producer — the sign `(23)` of the reflection-odd Bockstein limit — is not a theorem
of this card and is not formalized here.
