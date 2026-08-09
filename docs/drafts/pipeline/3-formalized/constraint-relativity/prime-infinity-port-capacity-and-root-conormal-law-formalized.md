# Prime–infinity port capacity and root-conormal law — formalized

- **ID:** `prime-infinity-port-capacity-and-root-conormal-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `prime-infinity-port-capacity-and-root-conormal-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.PortCapacity` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/PortCapacity.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Realization

The card's Leibniz computation reduces the transgression to the matrix normal form
`Ω = I_N + B Mᵀ` of `(7)`; that normal form is the Lean starting point (`transgression`), and every
statement of the card after it is a statement about matrices over a field.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 1 — sharp port capacity:

1. `transgression` — `Ω = I_N + B Mᵀ`, card `(7)`.
2. `ker_transgression_le` — `ker Ω ⊆ im B`, the card's step `v = −B Mᵀ v`.
3. `rank_transgression_ge` — **`rank Ω ≥ N − r`**.  Consequences 1–4 of the card are immediate
   arithmetic reformulations: `Ω = 0` (all valuations descend) needs `N − r ≤ 0`; `rank Ω = 1`
   needs `r ≥ N − 1`; no fixed `r` works for all `N`; one port gives `rank ≥ N − 1`.
4. `exists_transgression_rank_eq` — **sharpness**: for every `r ≤ N` the standard inclusion port
   matrices give `Ω = diag(0_r, I_{N−r})` and `rank Ω = N − r`.

Theorem 2 — radial stabilizer:

5. `radial_stabilizer` — the set of radial parameters fixing every relation is `ℝ` when the weight
   vector `log p + Mκ` vanishes and `{0}` otherwise, card `(9)`.

Theorem 3 — the symmetric one-port transgression:

6. `symTransgression` — `Ω = I_N + b 𝟙𝟙ᵀ`; `symTransgression_mulVec` is its action.
7. `symTransgression_ones` — eigenvalue `1 + N b` on the constants.
8. `symTransgression_meanZero` — eigenvalue `1` on the mean-zero hyperplane.
9. `symTransgression_injective` — for `1 + N b ≠ 0` the transgression is injective, so the rank is
   `N`; the minimum is attained only at `b = −1/N`.
10. `symTransgression_ker_eq_span` — at `b = −1/N` the kernel is exactly the constants.
11. `symTransgression_range_eq_meanZero` — the image is exactly the mean-zero (type-`A_{N−1}` root)
    space, card `(11)`.
12. `rank_symTransgression` — the rank is `N − 1`.
13. `symTransgression_two` — card `(10)`: for `N = 2` the minimal symmetric transgression is
    `½ ( 1 −1 ; −1 1 )`, the antisymmetric half-density projection.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/PortCapacity.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                            # green
```

`#print axioms` on `rank_transgression_ge`, `exists_transgression_rank_eq`, `radial_stabilizer`,
`rank_symTransgression`, `symTransgression_two` returns only
`[propext, Classical.choice, Quot.sound]`.
