# Card `projective-ht-horizon-symmetric-space-boundary`: state of the EMI program

Metric layer **done** (`mem:research/observer_metric_space_complete_2026_08_06`): `observerDist` is
a `MetricSpace`, flats are isometrically Euclidean, rays are geodesic lines, and inside one flat
distinct directions diverge linearly.

Analytic core of the asymptotic layer **done** (2026-08-06), two new modules in the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

| module | content |
|-|-|
| `LieTrotterProduct.lean` | `norm_exp_le_exp_norm`, `norm_pow_sub_pow_le`, **`tendsto_pow_exp_smul_inv`** — `(exp (A/n) exp (B/n))^n → exp (A+B)` in any Banach algebra |
| `GoldenThompsonNorm.lean` | `exp_add_of_commute'`, `exp_neg_mul_exp`, `nonneg_exp`, `sqrt_exp`, **`norm_exp_half_mul_exp_half_sq_le`** (Cordes at 1/2), **`norm_exp_add_le`** (`‖exp (x+y)‖ ≤ ‖exp x exp y‖`) |

Mathlib has neither; it does have **Löwner–Heinz** (`CFC.rpow_le_rpow`, `CFC.sqrt_le_sqrt`), which
is what makes Cordes cheap. `NormedAlgebra ℚ A` does **not** follow from `NormedAlgebra ℝ A` — use
`letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A` (the corpus already does this in
`FiniteHorizonCStarPerturbationLaw.lean`). `CStarAlgebra A` gives `NormedAlgebra ℝ A` and
`CompleteSpace A` but **not** `NormOneClass A` — add it as a hypothesis.

## What remains: the EMI bridge

Target: for symmetric `T S : E →ₗ[ℂ] E`,
`observerDist (exp T) (exp S) ≥ λmax (S − T)`, hence
`observerDist (exp (tT)) (exp (tS)) ≥ t · λmax (S − T) → ∞` for `T ≠ S` traceless
(a nonzero traceless symmetric operator has a positive eigenvalue), which is the general
(non-flat) form of `exists_pos_observerDist_metricRay_diagOp`.

Chain, all of it bridging rather than new mathematics:
1. `observerDist P Q = ‖log λ(rel)‖₂ ≥ max_i |log λ_i| ≥ log λmax(rel)` — ℓ² dominates ℓ^∞.
2. `λmax a = ‖a‖` for a positive-definite operator — prove from `diagOp` (‖diagOp b w‖ = max |w|).
3. `rel (exp T) (exp S) = exp(-T/2) exp S exp(-T/2)` — from `sqrtOp_eq_diagOp`, `invOp_eq_diagOp`,
   `metricRay_eq_diagOp` in `FlatGeodesicIsometry.lean`.
4. `‖exp(-T/2) exp S exp(-T/2)‖ = ‖exp(S/2) exp(-T/2)‖² ≥ ‖exp((S−T)/2)‖² = ‖exp (S−T)‖`
   — C⋆-identity plus **`norm_exp_add_le`**.
5. `‖exp M‖ = exp (λmax M)` for symmetric `M` — spectral.

Bridging instances needed: `E →L[ℂ] E` is a `CStarAlgebra` with `PartialOrder`/`StarOrderedRing`
(and `NormOneClass` when `E` is nontrivial); `LinearMap.toContinuousLinearMap` is the ring iso to
use; `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` bridges the two self-adjointness notions.
Handle `n = 0` (trivial `E`) separately — `NormOneClass` fails there and everything is `0 ≤ 0`.
