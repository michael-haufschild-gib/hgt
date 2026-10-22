# One real Euler ray carries the complete shifted-Xi negative index — formalized closure

- **ID:** `ccm-real-euler-ray-loewner-index-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-real-euler-ray-loewner-index-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

`GaloisForLFunctions.RHTower.CCM.CCMEulerRayLoewner` (new), over
`CCMEulerRayLogDerivativeIndex`, `CCMDiagonalFockLift`, `CCMHalfUnitCauchySeam`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(13)` | `ray_cauchy_denominator` | `i/(iy − conj(ix)) = 1/(x+y)` |
| `(9)` → `(2)` | `schur_ray_eq_loewner` | the ray restriction of the Schur kernel is the real Cauchy–Loewner kernel |
| `(2)` | `loewnerKernel`, `loewnerKernel_diagonal` | the kernel and its diagonal `(1 − f(x)²)/(2x)` |
| scalar/kernel separation | `contractionMatrix`, `det_contractionMatrix`, `not_posSemidef_contractionMatrix` | `det(1 − rᵢrⱼ) = −(r₁−r₂)²`; pointwise bounds are insufficient |
| `(15)`, `(16)` | `eulerFactor_arch_pos`, `eulerFactor_polar_pos`, `eulerFactor_gamma_pos`, `eulerFactor_local_mem` | every displayed factor is positive; the local factors lie in `(0,1)` |
| infinitesimal closure | `hasDerivAt_loewnerKernel` (companion card) | the cofinal shift family collapses to one log-derivative kernel |

## Axioms

`#print axioms` on all nine declarations returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The generalized Schur index theorem `(11)` and locality of negative squares in the
  reproducing-kernel Pontryagin space `(14)` — the analytic core the card imports.
- Principal-matrix interlacing plus density of the rational sections, i.e. `(6)`.
- The Euler product `(15)` for `ξ` itself; the Lean statements cover positivity of each factor.
- The card's open gates: `L_ω ⪰ 0` cofinally as `ω ↓ 0`, and RH.

## Verification performed

- `lake env lean` on the module: no errors, no warnings.
- `lake build GaloisForLFunctions.RHTower.CCM.CCMEulerRayLoewner`: success.
- `#print axioms` on every declaration: clean.
- Umbrella import added.
