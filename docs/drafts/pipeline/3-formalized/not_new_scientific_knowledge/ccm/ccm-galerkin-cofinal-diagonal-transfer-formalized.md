# Galerkin cofinal diagonal transfer — formalized closure

- **ID:** `ccm-galerkin-cofinal-diagonal-transfer-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-galerkin-cofinal-diagonal-transfer.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCM.CCMGalerkinDiagonalTransfer`
- `GaloisForLFunctions.RHTower.CCM.CCMRayleighExcessAngle` — the spectral inequality it stands on.

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(2)`, first assertion | `tendsto_of_antitone_of_approx` | the Ritz values, antitone, bounded below by `epsilon_lambda`, and approximating it from the form core, converge to it |
| `(2)`, third assertion | `gap_le_rayleighExcess_of_weight_eq_zero`, `weight_ne_zero_of_lt` | a trial vector orthogonal to the ground vector has Rayleigh value at least `epsilon_lambda^(2)`, so a Ritz value strictly below `epsilon_lambda^(2)` forces nonzero overlap — exactly what rules out an odd Ritz ground vector. It is a corollary of `gap_mul_one_sub_le_rayleighExcess` at `w i₀ = 0`, not a new spectral argument |
| `(2)`, second assertion | `norm_sub_smul_sq_eq`, `norm_sub_sq_eq_of_inner_real_nonneg`, `norm_sub_sq_le_of_inner_real_nonneg` | with the card's phase convention `⟪xi_{lambda,M}, xi_lambda⟫ ≥ 0` the identity phase attains the projective distance, so `‖xi_{lambda,M} - xi_lambda‖² = 2(1 - ⟪·,·⟫)` exactly and no infimum over phases is involved; the gap estimate `(3)` then bounds it by `2 delta / gap` |
| `(4)`–`(5)` | `tendstoUniformlyOn_inner_of_tendsto` | Cauchy–Schwarz against an evaluation family bounded on the compact set turns `L²` convergence of the ground vectors into genuine `TendstoUniformlyOn` convergence of the transforms, not merely pointwise convergence. Stated for an arbitrary complex inner-product space |
| `(7)`–`(8)` | `exists_diagonal_lt`, `tendsto_of_dist_lt_inv` | the diagonal selection with `M_j > j` and error below `1/(j+1)`, and the conclusion that the diagonal has the same limit. Stated in an arbitrary pseudometric space, so it applies to the local uniform metric on each compact exhausting set |

None of the statements is finite dimensional: the spectral half is a `HasSum` statement over an
arbitrary index type.

## Axioms

`#print axioms` on every theorem returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

Consumed by the card as inputs, not proved in it: the closed lower-semibounded Weil form, its
compact resolvent, and the form-core property of the logarithmic Fourier modes; min–max itself; and
the CCM finite determinant theorem placing the zeros of a simple-even finite Ritz pair on the real
spectral axis.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
- Every declaration named in the card's Lean status section exists in the tree.
