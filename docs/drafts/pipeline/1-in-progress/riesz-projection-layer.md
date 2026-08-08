# The Riesz projection layer

- **ID:** `riesz-projection-layer`
- **Stage:** 1-in-progress
- **Type:** MISSING INFRASTRUCTURE (Lean)
- **Parent blocker:** `entire-regularized-fredholm-determinant.md`

## Why this card exists

`entire-regularized-fredholm-determinant.md` now proves

```text
order of vanishing of det_2 at z_0  =  eventual algebraic multiplicity of the *block* eigenvalue
```

(`eventually_schurCount_eq_analyticOrder` + `finrank_maxGenEigenspace_eq_schurCount`).  What the
three hedenmalm cards quote is the algebraic multiplicity of the eigenvalue **of the operator**,
i.e. `dim` of its generalized eigenspace.  Passing from the finite sections to the operator is the
Riesz-projection argument, and mathlib has no Riesz projection.

## What mathlib supplies

* `resolvent`, `resolventSet`, `spectrum.isOpen_resolventSet`
* `spectrum.hasDerivAt_resolvent_const_left` — the resolvent is differentiable on the resolvent set
* `circleIntegral` for Banach-space-valued integrands, and Cauchy's theorem
  `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`

Absent: the Riesz projection, its idempotence, the identification of its range with the generalized
eigenspace, and the continuity of the projection under norm perturbation.

## Built so far

`formal/GaloisForLFunctions/HTGeometry/RieszProjection.lean`

| statement | Lean declaration |
|---|---|
| the projection `P = (2 pi i)^-1 int (lam - a)^-1 dlam` | `rieszProjection` |
| the resolvent is circle-integrable on a contour in the resolvent set | `circleIntegrable_resolvent` |
| a spectrum-free disc gives the zero projection (Cauchy) | `rieszProjection_eq_zero_of_closedBall_subset` |
| `R(l) (l - a) = 1` and `(l - a) R(l) = 1` | `resolvent_mul_sub`, `sub_mul_resolvent` |
| **the resolvent identity** `R(l) - R(m) = (m - l) R(l) R(m)` | `resolvent_sub_resolvent` |
| multiplication passes through a circle integral | `circleIntegral_mul_left`, `circleIntegral_mul_right` |
| the resolvent commutes with the element | `commute_resolvent` |
| **the projection commutes with the element** | `rieszProjection_commute` |

## Route

1. **Resolvent identity** `R(l) - R(m) = (m - l) R(l) R(m)`, from `resolvent` and `Ring.inverse`.
2. **Idempotence** `P^2 = P`, by the standard two-contour argument (radii `r < r'`, both in the
   resolvent set except for the enclosed spectral point), using 1 and Fubini for the double circle
   integral.
3. **`P` commutes with `a`**, since each resolvent does; needs
   `L (int f) = int (L o f)` for the bounded maps `x |-> a x` and `x |-> x a`.
4. **`ran P` is the generalized eigenspace** when the contour encircles one isolated spectral point
   of a compact operator, and is finite-dimensional.
5. **Finite-section stability**: `‖a_n - a‖ -> 0` gives `‖P_n - P‖ -> 0` on a fixed contour in the
   resolvent set of `a`, hence eventually `rank P_n = rank P`.

Step 5 is the one the determinant card needs; 1--4 are its prerequisites.

## Gates
- [x] definition, circle integrability, and the Cauchy vanishing
- [x] resolvent identity (`resolvent_sub_resolvent`); mathlib has none
- [ ] idempotence
- [x] commutation with `a` (`rieszProjection_commute`)
- [ ] range = generalized eigenspace
- [ ] finite-section stability of the rank

## Log
- 2026-08-08 — created; definition and the Cauchy vanishing formalized.
- 2026-08-08 — commutation with `a` formalized, together with the two lemmas pulling
  multiplication through a Banach-valued circle integral (`ContinuousLinearMap.mul` and its `flip`,
  then `ContinuousLinearMap.intervalIntegral_comp_comm`).
- 2026-08-08 — the resolvent identity formalized.  mathlib has `resolvent` and
  `spectrum.hasDerivAt_resolvent_const_left` but **no resolvent identity**; it follows in three
  lines from `Ring.inverse_mul_cancel`/`Ring.mul_inverse_cancel` and
  `Algebra.algebraMap_eq_smul_one`.
