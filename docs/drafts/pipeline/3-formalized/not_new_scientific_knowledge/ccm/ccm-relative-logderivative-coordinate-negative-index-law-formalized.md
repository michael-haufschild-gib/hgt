# Every active CCM Fourier coordinate contributes one relative logarithmic negative square — formalized closure

- **ID:** `ccm-relative-logderivative-coordinate-negative-index-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-relative-logderivative-coordinate-negative-index-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

`GaloisForLFunctions.RHTower.CCMRelativeLogDerivCoordinateIndex` (new), over the Pick-cluster
modules.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(8)` | `cauchyFeature`, `conj_cauchyFeature` | the Cauchy feature and its conjugate form |
| `(9)` | `cauchyFeature_pick` | each Cauchy feature is a rank-one Pick square |
| `(7)`, `(10)` | `relativeLogDeriv`, `relativeLogDeriv_pick_decomp` | the exact signed Cauchy decomposition of the Pick kernel |
| section 3 residue | `cauchyFeature_residue` | multiplying by `w − i t_k` isolates the `k`-th coefficient |
| section 3 independence | `cauchyFeature_coeff_eq_zero` | Cauchy features at distinct real nodes are independent |
| `(23)` | `card_active_ge` | the active-coordinate count floor `2K + 1` |

## Axioms

`#print axioms` on all six declarations returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The CCM relative-determinant formula `(15)` and reality of the perturbed spectrum.
- The Pontryagin-space realization and Sylvester inertia that convert the signed decomposition into
  the exact index `(11)`, `(17)`.
- Proposition 5.9's residual-lattice rule feeding the support floor `(22)`.
- The card's open gates: an unconditional support floor for the true CCM ground vector, the
  index-matched positive background carrier, cofinal Euler-kernel positivity, and RH.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCMRelativeLogDerivCoordinateIndex`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.
