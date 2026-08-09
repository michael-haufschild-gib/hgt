# Heterogeneous triangle identity and singular-holonomy law — formalized

- **ID:** `heterogeneous-triangle-singular-holonomy-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `heterogeneous-triangle-singular-holonomy-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.TriangleHolonomy` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/TriangleHolonomy.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Section 3 — the exact triangle law:

1. `cyclicDefect_eq` — **Theorem 3.1 / card `(3.1)`**:
   `Ω₀ = T₂₀T₁₂ e₀₁ + T₂₀ e₁₂ + e₂₀`, over an arbitrary ring, for arbitrary linear transports.
2. `cyclicDefect_eq_zero` — **Corollary 3.2**: exactly compatible edges force a flat cycle.
3. `norm_cyclicDefect_le` — **card `(3.2)`**: the operator-norm bound.

Section 4 — singular amplification:

4. `norm_cyclicDefect_le_three_mul` — **Theorem 4.1 / card `(4.3)`**: `‖Ω₀‖ ≤ 3 M ε` with
   `M ≥ max{1, ‖T₂₀‖, ‖T₂₀T₁₂‖}` and `ε ≥ max` of the three edge defects.
5. `cyclicDefect_tendsto_zero_of_bounded` — **item 1**: uniformly bounded amplification plus
   vanishing edge accuracy forces the cyclic defect to vanish.
6. `amplification_ge` — **item 2 / card `(4.5)`**: a cyclic defect bounded below by `κ` at edge
   accuracy `ε > 0` forces `M ≥ κ/(3ε)`; the card states the weaker `κ/(6ε)` after halving `κ`
   along a tail, and the Lean statement gives the sharp per-stage inequality it is derived from.

Section 5 — the equicontinuous completion law:

7. `cyclicDefect_tendsto_zero_of_equicontinuous` — **Theorem 5.1**: for arbitrary topological
   abelian groups, if the two transport families are equicontinuous at the origin (written in its
   defining form: one source zero-neighbourhood suffices for each target zero-neighbourhood,
   uniformly in the family) and the three edge defects tend to zero, the cyclic defect tends to
   zero.  Linearity is not needed for this argument, so the Lean statement is stated for arbitrary
   families of maps and covers the card's continuous-linear case.

Corollary 4.2 of the card is an enumeration of the ways the hypotheses of a single normed triangle
can fail; the card itself states that only items 1–2 follow numerically, and those are items 5 and
6 above.  Corollary 5.2 is the Banach–Steinhaus specialization, which the card explicitly notes
"adds no new theorem"; it is mathlib's uniform boundedness principle applied to item 7.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/TriangleHolonomy.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                                # green
```
