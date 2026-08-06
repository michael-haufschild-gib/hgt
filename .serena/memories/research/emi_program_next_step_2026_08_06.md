# Card `projective-ht-horizon-symmetric-space-boundary`: EMI is DONE

Metric layer done (`mem:research/observer_metric_space_complete_2026_08_06`).  As of 2026-08-06 the
**asymptotic layer's analytic core is also done**: three more modules in the `HTGeometry` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`.

| module | content |
|-|-|
| `LieTrotterProduct.lean` | `norm_exp_le_exp_norm`, `norm_pow_sub_pow_le`, **`tendsto_pow_exp_smul_inv`** — `(exp (A/n) exp (B/n))^n → exp (A+B)` in any Banach algebra |
| `GoldenThompsonNorm.lean` | `nonneg_exp`, `sqrt_exp`, **`norm_exp_half_mul_exp_half_sq_le`** (Cordes at 1/2), **`norm_exp_add_le`** (`‖exp (x+y)‖ ≤ ‖exp x exp y‖`) |
| `ExponentialMetricIncreasing.lean` | `norm_toCLM_diagOp_le`, `invSqrtOp_metricRay`, **`eigenvector_le_observerDist`** (EMI), **`exists_pos_le_observerDist_metricRay`** |

```text
(S - T) v = μ • v, v ≠ 0  →  μ ≤ observerDist (exp T) (exp S)
tr (S - T) = 0, S ≠ T     →  ∃ c > 0, ∀ t ≥ 0, c*t ≤ observerDist (exp (tT)) (exp (tS))
```

So **rays with distinct traceless directions diverge linearly, with no commutativity assumption** —
the card's boundary-faithfulness statement as a metric fact.

## Why the elementary routes fail (do not re-attempt)
The flat computation (`observerDist_diagOp`) is blind to two directions with the *same spectrum in
different frames* — exactly where the curvature lives.  Every elementary test-vector estimate
(a single eigenvector, or a compound/Ky Fan test vector) returns rate 0 there, because the optimal
test vector depends on `t`.  Only EMI settles it.

## Lean facts worth keeping
- mathlib has **Löwner–Heinz** (`CFC.rpow_le_rpow`, `CFC.sqrt_le_sqrt`) — the entry point to Cordes.
- `NormedAlgebra ℚ A` does not follow from `NormedAlgebra ℝ A`: use
  `letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A`.
- `CStarAlgebra A` gives `NormedAlgebra ℝ A` + `CompleteSpace A` but **not** `NormOneClass A`.
- `E →L[ℂ] E` is a `CStarAlgebra` with `PartialOrder`/`StarOrderedRing`; `NormOneClass` needs
  `Nontrivial E`, which is available from any nonzero vector or from `Module.finrank_pos`.
- `congr 1` on `diagOp b f = diagOp b g` unfolds to `pieceOperator` and introduces
  `algebraMap ℝ ℝ`; do `funext` on the weight function *first*.
- The corpus coercion `((x : ℝ) : ℂ)` and mathlib's `RCLike.ofReal` are not syntactically equal —
  pass `(w := …)` explicitly to `metricRay_eq_diagOp` / `eq_diagOp_of_apply`, and finish scalar
  goals with `simp` rather than `Complex.ofReal_mul`.

## What is left on the card
Only the *construction* of the boundary object: asymptote classes of rays as a set, the Tits
(angle) metric on them, and the equivariant identification with the horizon building.  The metric
inputs those need are now all present.
