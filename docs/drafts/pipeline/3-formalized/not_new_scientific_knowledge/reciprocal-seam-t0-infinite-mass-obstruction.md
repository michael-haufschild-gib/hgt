# Reciprocal Seam Zeroth-Moment Obstruction

- **ID:** reciprocal-seam-t0-infinite-mass-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/revision01/proof-route.md`
- **Statement:** The reciprocal zero-divisor measure has infinite zeroth moment. Therefore the unshifted Hankel tower `[T_{i+j}]_{i,j=0}^d` in the proof route is not an ordinary finite Stieltjes moment matrix unless `T_0` is regularized/replaced or the test domain is restricted.

## Goal
Correct the proof route before attacking all-order positivity. The ordinary finite moment object is the shifted tower `[T_{i+j+1}]`, corresponding to the finite total-variation measure obtained by weighting reciprocal atoms by one power of `y`.

## Proof
Let

```text
y_rho = -(rho - 1/2)^(-2).
```

The divisor has infinitely many nontrivial zeros, so the formal zeroth moment

```text
T_0 = sum_rho 1
```

diverges.

For every `k >= 1`, the reciprocal sums are absolutely convergent. By Riemann-von Mangoldt, the number of zeros with `|Im rho| <= R` is `O(R log R)`. On a dyadic shell `R <= |Im rho| < 2R`, the contribution to

```text
sum_rho |rho - 1/2|^(-2k)
```

is `O(R log R * R^(-2k)) = O((log R) R^(1-2k))`, which is summable over dyadic shells for `k >= 1`.

Thus positive-order reciprocal moments are finite, but `T_0` is infinite. The classical finite Stieltjes moment matrix beginning at `T_0` is therefore not literally available for the full zero divisor.

The shifted moments

```text
T_{i+j+1}
```

are the ordinary finite moments of the weighted object `dnu = y dmu` in the reciprocal coordinate, whenever the positivity/sign issue is separately settled.

## Consequence
The proof route should not state the unshifted and shifted Hankel towers as parallel ordinary finite PSD conditions without specifying one of:

1. a finite-window/truncated limiting theorem;
2. a renormalized finite part for `T_0`;
3. a restricted quadratic-form domain, e.g. test polynomials vanishing at `0`;
4. a shifted finite-measure formulation using `[T_{i+j+1}]`.

## Computation
Toy model `y_n=1/n^2` confirms the same structure: `T_0(N)=N -> infinity`, while `T_k -> zeta(2k)` for `k >= 1`, and shifted Hankel determinants converge to finite positive values.

Artifacts:

- `computations/2026-06-21-penrose-proof-r01-hankel-t0-obstruction.py`
- `computations/2026-06-21-penrose-proof-r01-hankel-t0-obstruction.txt`

## Log
- 2026-06-21 -- Penrose: created after user correction that passport-only findings indicated stuckness. This is the first proof-route finding under the `proof-route.md` repository.

## Lean formalization

Module: `formal/GaloisForLFunctions/RHTower/ReciprocalSeamZerothMoment.lean`
(namespace `RHTower`), wired into the `GaloisForLFunctions.RHTower` umbrella.

| Paper statement | Lean declaration |
|---|---|
| the reciprocal seam atom `y = -(rho-1/2)^(-2)` | `reciprocalSeamAtom`, `reciprocalSeamAtom_eq`, `norm_reciprocalSeamAtom` |
| the seam weights are summable | `summable_norm_reciprocalSeamAtom` |
| every weight is bounded by the total seam mass | `norm_reciprocalSeamAtom_le` |
| `T_k` converges absolutely for every `k >= 1` | `summable_norm_reciprocalSeamAtom_pow`, `summable_reciprocalSeamAtom_pow` |
| `T_0 = sum_rho 1` diverges | `not_summable_reciprocalSeamZerothMoment` (with the `Infinite XiZeroCopy` instance) |
| the exact dichotomy | `reciprocalSeamMoment_dichotomy` |

The convergence input is the corpus genus-one condition
`RHTower.xiSpectralPoint_inv_sq_summable` (`Summable (fun q => 1/‖ρ - 1/2‖²)` over divisor copies)
rather than the Riemann–von Mangoldt count used on paper; it is the same fact in its unconditional
Hadamard form, and it already carries the divisor multiplicities. Divergence of `T_0` comes from
`RHTower.xiDivisorSupport_infinite`.

Audit: direct `lake env lean` check clean, targeted module build clean, umbrella import wired,
`#print axioms` returns only `propext`, `Classical.choice`, `Quot.sound`.
