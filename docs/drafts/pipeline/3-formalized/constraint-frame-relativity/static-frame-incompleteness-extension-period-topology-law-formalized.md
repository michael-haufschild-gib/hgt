# Static-frame incompleteness: extension, period, and topology — formalized

- **ID:** `cfr-static-frame-incompleteness-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `static-frame-incompleteness-extension-period-topology-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.StaticFrameIncompleteness` | new |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 1.1 — period closure is not oriented trivially-valuated support, card `(1)`–`(4b)`:

1. `det_signs_first`, `det_signs_second` — the six ordered `2 × 2` minors of `(1, i, 1+i)` and
   `(1, i, √2+i)`, with the same sign pattern `(+, +, −)`; with the trivial valuation the two
   triples therefore realise the same oriented `U(2,3)` frame.
2. `closed_integer_periods` — `Γ_v ∩ ℝ = ℤ` is a closed subgroup of the line.
3. `dense_sqrt_two_periods` — `Γ_w ∩ ℝ = ℤ + √2 ℤ` is dense, proved from
   `AddSubgroup.dense_or_cyclic` and the irrationality of `√2`: a cyclic generator would make
   `√2` rational.
4. `period_closure_nonidentifiable` — the theorem: same frame, one closed period group and one
   dense one, so the frame does not determine the period closure, the Hausdorff phase quotient, or
   the existence of a discrete lattice.

Theorem 2.1 — the affine first extension is not determined by the positive Hankel face, card
`(5)`–`(10a)`:

5. `factorialMoment` — the factorial moments of a two-atom carrier.
6. `carriers_positive` — both carriers have strictly positive weights and nodes.
7. `shared_moments` — `s₀ = s₁ = s₂ = 1` for both, so both have the identical singular size-two
   Hankel face `!![1,1;1,1]` and the same null polynomial `X - 1`.
8. `opposite_crossings` — `s₃⁺ = 31/24` and `s₃⁻ = 11/12`, so the first Krein crossings
   `[P, XP] = s₃ - s₂` are `7/24 > 0` and `-1/12 < 0`: opposite signs.

Theorem 3.1 — the cofinal topology is not determined by the algebraic tower, card `(11)`–`(14)`:

9. `augmentOn`, `lpNormPowOn` — the augmentation and the `p`-th power of the `ℓ^p` norm on a finite
   index set.
10. `abs_augmentOn_le_l1` — the augmentation is `1`-Lipschitz for the `ℓ¹` norm, so in `ℓ¹` its
    kernel is closed and, being surjective, it identifies the Hausdorff quotient with a line: card
    `(12)`.
11. `correction`, `correction_cancels` — the correction of card `(14)` spreading the deficit over
    `N` fresh coordinates.
12. `correction_lp_pow`, `tendsto_correction_lp_pow` — its `ℓ^p` size is `|S|^p N^{1-p} → 0` for
    every `p > 1`; `tendsto_correction_sup` gives the `c₀` case `|S|/N → 0`.
13. `correction_l1_norm` — its `ℓ¹` size is exactly `|S|`, so the same correction does *not* work
    in `ℓ¹`: this is the sharp dichotomy.
14. `freshBlock`, `freshBlock_card`, `disjoint_freshBlock`,
    `exists_augmentation_zero_approx` — the augmentation ideal is dense in every `ℓ^p` with
    `p > 1`, so the Hausdorff quotient there is zero: card `(13)`.
15. `cofinal_topology_nonidentifiable` — the theorem: the identical finite augmentation tower has
    a `1`-Lipschitz nonvanishing augmentation in `ℓ¹` and a dense augmentation ideal in every
    `ℓ^p`, `p > 1`.

Theorem 4.1 — the combined impossibility is the conjunction of items 4, 8 and 15: each of the three
outputs is independent of its corresponding static shadow, so no invariant factoring through those
shadows recovers all three.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/StaticFrameIncompleteness.lean  # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
