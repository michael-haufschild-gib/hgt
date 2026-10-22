# Rayleigh-excess angle bound and determinant transfer — formalized closure

- **ID:** `ccm-rayleigh-excess-determinant-transfer-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-rayleigh-excess-determinant-transfer.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCM.CCMRayleighExcessAngle`

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(4)` | `gap_mul_one_sub_le_rayleighExcess` | with nonnegative spectral weights summing to one and every non-ground eigenvalue at least `Gap` above the bottom, `Gap (1 - w i₀) ≤ r - eps_0`. Proved by exhibiting the difference as a sum of manifestly nonnegative terms, so no reordering and no separate positivity of the tail sum is needed. Stated with `HasSum` over an arbitrary index type: not finite dimensional, no eigenbasis cardinality assumption |
| `(5)` | `norm_sub_smul_sq_eq`, `two_sub_two_mul_norm_le_norm_sub_smul_sq`, `exists_unit_norm_sub_smul_sq_eq` | for unit vectors, `‖g - c ξ‖² = 2 - 2 Re(c ⟪g,ξ⟫)`; `2(1 - |⟪g,ξ⟫|)` is a lower bound over all unit phases; and it is *attained* at `c = conj⟪g,ξ⟫/|⟪g,ξ⟫|`. The card writes `(5)` as an infimum "after choosing the phase" — both halves are proved, so the bound is on a genuine attained minimum |
| `(3)` | `projectiveDistSq_le_two_mul_excess_div_gap` | the angle bound `‖g - c ξ‖² ≤ 2 delta / Gap` at the attaining phase; the step `2(1-t) ≤ 2(1-t²)` is Cauchy–Schwarz for unit vectors |
| `(6)`–`(8)` | `tendsto_sqrt_of_tendsto_zero` | the squared-rate hypothesis transfers to the unsquared projective distance |
| `(9)`–`(10)` | `rayleighExcess_le_of_lower_bound` | any proved lower bound for the ground energy bounds the excess, so no two-sided estimate of the unknown eigenvalue is needed |

The bridge between the spectral and geometric halves is Parseval, `w i₀ = |⟪g, ξ⟫|²`, which is why
the spectral inequality is stated with the abstract ground weight and the angle bound with the
overlap.

## Axioms

`#print axioms` on every theorem returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Deliberately outside the Lean statement

Not theorems of this card: the exterior-tail radical identity `(12)` (imported from
`ccm-weil-exterior-tail-quotient-gate.md`) and the growing Mellin evaluation interface of
`ccm-growing-aperture-mellin-determinant-transfer.md`, which *consumes* `(7)` rather than proving it.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
- Every declaration named in the card's Lean status section exists in the tree.
