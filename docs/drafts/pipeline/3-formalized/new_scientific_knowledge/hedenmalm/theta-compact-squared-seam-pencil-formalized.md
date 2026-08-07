# Formalization certificate: theta compact squared-seam pencil

- **ID:** `theta-compact-squared-seam-pencil-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `theta-compact-squared-seam-pencil.md`

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/HedenmalmThetaCompactDivisorEigenmode.lean
formal/GaloisForLFunctions/RHTower/HedenmalmThetaSquaredSeamPencil.lean
```

Namespace `RHTower`; reachable from `GaloisForLFunctions.RHTower`.

## Formal theorem chain

| # | card statement | Lean declaration |
|---|---|---|
| — | every multiplicity copy lies in the theta-source strip | `thetaXiSpectralPoint_mem_sourceStrip` |
| — | the Xi divisor is the divisor of the source transform | `xiC_thetaSource_xiSpectralPoint_eq_zero` |
| — | the canonical divisor vector `v_q` and its nonvanishing | `thetaXiDivisorEigenvector`, `thetaXiDivisorEigenvector_ne_zero` |
| `(1)` | **`B v_q = lambda v_q`** | `thetaCompactSourceInverse_thetaXi_eigen` |
| — | `B^2 v_q = lambda^2 v_q` | `thetaCompactSourceInverse_sq_thetaXi_eigen` |
| — | `lambda^2 = z^{-2}` is the unshifted reciprocal-square atom | `thetaXiReciprocalEigenvalue_sq_eq_reciprocalSquare` |
| — | `mu_q = lambda^2/(1+lambda^2)` | `xiSquaredSeamOneCoordinate_eq_thetaXi_pencilRatio` |
| — | the denominator never vanishes | `one_add_thetaXiReciprocalEigenvalue_sq_ne_zero` |
| `(3)` | `v_q + B^2 v_q != 0` | `thetaXiDivisorEigenvector_add_sq_ne_zero` |
| `(2)` | **`B^2 v_q = mu_q (v_q + B^2 v_q)`** | `thetaCompactSourceInverse_sq_pencil` |
| `(3)` | uniqueness of the pencil eigenvalue on the line | `thetaCompactSourceInverse_sq_pencil_unique` |

## Verification

```bash
cd formal
lake build GaloisForLFunctions.RHTower.HedenmalmThetaSquaredSeamPencil
```

Clean.  `#print axioms` on every declaration in the table reports only `propext`,
`Classical.choice` and `Quot.sound`.
