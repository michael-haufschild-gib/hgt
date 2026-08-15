# Prime-free aperture characteristic pair — formalized closure

- **ID:** `ccm-prime-free-aperture-characteristic-pair-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-prime-free-aperture-characteristic-pair-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCMPrimeFreeApertureCharacteristicPair`

Standing on three pre-existing corpus layers:

- `RHTower/DigammaQuarter` — Gauss's value `ψ(1/4) = -γ - π/2 - 3log2` and `archRatioCharge_pos`;
- `RHTower/DigammaVerticalLogGrowth` — `re_digamma_vertical_ge`, the explicit logarithmic
  coercivity of `Re ψ` on a vertical line;
- `RHTower/ArchEnvelope` — continuity of `Complex.digamma` on the right half-plane;
- `HTGeometry/ReflectedDigammaAnomaly` — `digamma_conj`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)` | `ccmArchSymbol`, `ccmPolarMultiplier`, `ccmPrimeCutoffSum`, `ccmCorrectedSymbol` | the full real symbol, including the finite prime cutoff over `Finset.Icc 2 ⌊exp(2a)⌋₊` |
| `(2)` | `ccmPrimeFreeAperture`, `ccmPrimeFreeAperture_pos`, `arsinh_pos_of_pos` | `a₀ = min((log2)/2, arsinh(-m₀/8))` and `a₀ > 0` |
| `(4)`–`(5)` | `ccmArchSymbol_zero`, `ccmArchSymbol_zero_neg` | `m₀ = ψ(1/4) − log π = −archRatioCharge < 0`, from Gauss's quarter value |
| `(6)` | `ccmPolarMultiplier_zero` | `P_a(0) = 8 sinh a` |
| prime-free | `ccmPrimeCutoffSum_eq_zero` | below `(log 2)/2` the cutoff index set is empty, so the prime-power sum vanishes identically |
| `(7)` | `ccmCorrectedSymbol_zero_neg` | `W_a(0) = m₀ + 8 sinh a < 0` throughout the aperture range, by strict monotonicity of `sinh` |
| evenness | `conj_quarterLine`, `ccmArchSymbol_even`, `ccmPolarMultiplier_even`, `ccmPrimeCutoffSum_even`, `ccmCorrectedSymbol_even` | the symbol is even; the archimedean half through `digamma_conj` |
| continuity | `continuous_ccmArchSymbol`, `continuous_ccmPolarMultiplier`, `continuous_ccmPrimeCutoffSum`, `continuous_ccmCorrectedSymbol` | continuity in the frequency |
| `(8)` | `ccmArchSymbol_ge`, `tendsto_ccmArchSymbol_atTop` | `m(ξ) ≥ log(2 + \|ξ/2\|) − C − log π`, hence `m(ξ) → +∞` |
| `(8)`, polar half | `abs_ccmPolarMultiplier_le` | a *uniform* bound `\|P_a(ξ)\| ≤ 8\|sinh a\| + 4 cosh a`. Only boundedness is needed to beat a divergent archimedean part, so no decay statement is required |
| choice of `R` | `exists_pos_ccmCorrectedSymbol` | some `R > 0` with `W_a(R) > 0` |
| `(3)` | `exists_characteristic_pair` | a `τ > 0` with `W_a(τ) = W_a(−τ) = 0`, by the intermediate value theorem on `[0,R]` and evenness |

The Lean statement is slightly stronger than the card: no positivity of `a` is needed, only
`a < a₀`.

## Axioms

`#print axioms` on all 21 declarations returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

The Suzuki–Yoshida small-aperture positivity and screw injectivity quoted in the card's "Positive
CCM consequence", and the card's own open gates (the source-defined exterior-trace Evans relation
and its injectivity through every prime-entry aperture).

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMPrimeFreeApertureCharacteristicPair`: success.
- `#print axioms` on every theorem: clean.
- Umbrella import added.
