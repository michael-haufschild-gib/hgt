# Boundary-strip weak-limit energy transfer — formalized closure

- **ID:** `ccm-boundary-strip-weak-compactness-transfer-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-boundary-strip-weak-compactness-transfer-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

- `GaloisForLFunctions.RHTower.CCMBoundaryStripTransfer` — the weak-limit, graph-core, and
  four-unit layers.
- `GaloisForLFunctions.RHTower.MobiusFisherContactWardBudget` — pre-existing entrywise lower
  semicontinuity of the Hilbert–Schmidt energy (`hsNormSq_le_of_tendsto_entries`) and the budget
  transfer it feeds (`completedSourceWardBudget`).

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(3)`, semicontinuity step | `norm_le_of_weak_limit`, `norm_le_of_weak_limit_complex` | a weak limit inherits every *eventual* norm bound; proof is Cauchy–Schwarz against the limit itself, `‖x‖² = lim ⟪x, A n⟫ ≤ ‖x‖ c`. Stated with an eventual bound rather than a `liminf`, so it composes directly with the card's `limsup` hypothesis `(7)` |
| `(3)`, assembled | `hsNormSq_le_of_weak_limit` | the card's conclusion in the corpus `lp 2` realization of `S_2`: a family of Hilbert–Schmidt kernels whose pairings against the limit converge, with energies eventually at most `B`, has a limit of energy at most `B` |
| `(4)`–`(5)` | `eq_of_graphCore` | a continuous map agreeing with `Q ∘ D` on a graph core agrees with it on the whole domain. Only the approximation property is used: no closedness of `D`, no density, no linearity |
| `(8)`–`(9)` | `fourMulCDF_pos`, `tendsto_one_sub_exp_neg_div`, `tendsto_div_fourMulCDF`, `eventually_div_le_one_add_of_le_fourMulCDF` | a profile with `Delta(u) ≤ 4(1 - e^{-u}) + r(u)`, `r(u) = o(u)`, satisfies `limsup_{u→0+} Delta(u)/(4(1-e^{-u})) ≤ 1`, in epsilon form so no extended-real junk values appear. The two analytic inputs — the slope of `1 - e^{-u}` at the origin and `u/(4(1-e^{-u})) → 1/4` — are proved in the module |

## Strengthening relative to the card

The card's own proof extracts a weakly convergent subsequence from a bounded family in `S_2`. The
Lean route bounds each finite piece directly and never uses weak compactness, so `(3)` is reached
from a strictly weaker hypothesis set than the paper argument. Eberlein–Šmulian and separability of
`S_2` are therefore not needed and are not assumed.

## Axioms

`#print axioms` on every theorem of `CCMBoundaryStripTransfer` returns exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
- Every declaration named in the card's Lean status section exists in the tree.
