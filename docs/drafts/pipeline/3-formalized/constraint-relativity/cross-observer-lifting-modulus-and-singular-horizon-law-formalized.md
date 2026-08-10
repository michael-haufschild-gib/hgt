# Cross-observer lifting modulus and singular horizon law — formalized

- **ID:** `cross-observer-lifting-modulus-and-singular-horizon-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `cross-observer-lifting-modulus-and-singular-horizon-law.md`
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.CrossObserverModulus` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/CrossObserverModulus.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.  The modulus is valued in
`ℝ≥0∞`, so the infinite case of card `(9)` and `(12)` is a genuine value, not a side condition.

1. `liftingModulus` — **card `(1)`**; `le_liftingModulus`, `liftingModulus_le` are the two
   supremum interfaces; `eq_top_of_forall_ofReal_le` is the extended-real helper.
2. `liftingModulus_mono` — monotonicity in the scale.
3. `dist_le_liftingModulus` — **card `(4)`**: every source trajectory is controlled by the modulus
   at its own observed separation.
4. `liftingModulus_zero_eq_zero_iff` — **card `(2)`**: the zero-scale modulus vanishes exactly when
   the interior observer is constant on the fibres of the boundary observer.
5. `liftFactor`, `liftFactor_comp` — the factoring map in that case.
6. `dist_le_of_lipschitz_factor` — **cards `(17)`, `(18)` boxed**: a `K`-Lipschitz decoder forces
   `|ΔL| ≤ K·δ`, i.e. `K ≥ |ΔL|/δ`.
7. `liftingModulus_comp` — **card `(5)`**: the modulus composes.
8. `liftingModulus_le_of_lipschitz` — **card `(6)`**: coarsening by a `1`-Lipschitz map can only
   increase the modulus.
9. `liftingModulus_eq_zero_scale` — **cards `(7)`, `(8)`**: a finite exact observer has a
   resolution floor, below which the modulus is exactly its zero-scale value.
10. `liftingModulus_eq_top_of_ker` — **card `(9)`**: a nonzero kernel makes the modulus infinite at
    every scale.
11. `sigmaMin`, `sigmaMin_nonneg`, `sigmaMin_le_of_norm_one`, `sigmaMin_mul_le`,
    `exists_norm_eq_sigmaMin` — the least singular value, defined as an infimum over the unit
    sphere and *attained* (compactness of the sphere in finite dimension).
12. `liftingModulus_id_linear` — **card `(10)`, boxed**: `Λ_{id|J}(ε) = ε/σ_min(J)` exactly, both
    inequalities.
13. `liftingHorizon` — **card `(12)`**: the cofinal horizon invariant.
14. `liftingHorizon_eq_top` — **card `(15)`**: the criterion for infinite horizon.
15. `norm_exp_mul_I_sub_one` — the exact circle-chord identity
    `‖e^{iθ} − 1‖ = 2|sin(θ/2)|`, proved by the half-angle factorization; mathlib does not have it.
16. `recurrenceInterior`, `recurrenceBoundary`, `norm_recurrenceBoundary_sub` — **cards `(13)`,
    `(14)`**: the exact wrap-around chord of the recurrence family.
17. `liftingHorizon_recurrence_eq_top` — **card `(15)`**: the recurrence family has infinite cofinal
    horizon, even though every member is injective and every interior observer factors exactly.
    Card `(16)`, the diverging decoder Lipschitz constant, is item 6 applied to this family.

## Scope

The card's "Physical and arithmetic consequences" and "No-go closure" are readings of the theorems
above.  The card states plainly that the result does not select the critical line and that a useful
source theorem would have to control the condition modulus of the literal arithmetic deformation
map; nothing of that kind is claimed or formalized.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/CrossObserverModulus.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.CrossObserverModulus          # green
```
