# Charge cancellation preserves the certified floor

- **ID:** A162-charge-cancellation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1311/obstacles-summary.md`, A162.
- **Statement:** For `R≥1`, `Q≥2`, every nonempty window with `50J ≤ 53R` has floor `1/5000`
  above its positive ground vector. Charge cancellation preserves the full
  hyperplane floor in a Schur complement.

## Proof

Let `c=1/5000`, `Mφ=λφ`, and `φ>0`. If `λ≥c`, the Perron ground-state
bound gives `M≥c`. Otherwise shift by `−c`. For `z⊥φ`, cancel its total
charge by adding a multiple of `φ`. The cross term vanishes and the added
energy is nonpositive. The certified zero-charge floor then gives
`zᵀMz≥c‖z‖²`. This includes `J<R`.

For a middle `M` with unit ground vector `φ` and eigenvalue `−μ<0`, put
`g=M⁻¹Pe`, `t=ℓ(−g,e)/ℓ(φ,0)`, and `m=−g−tφ`. Then `ℓ(m,e)=0` and
the full block form equals `eᵀSe−μt²`. A nonnegative charge-free floor
`d` gives `d(‖m‖²+‖e‖²)≤eᵀSe−μt²`, hence `S≥d`.

Finally `Mm+Pe=0` identifies the neutral form with its Schur complement.
The existing Schur index law therefore gives the local criterion on the
neutral-orthogonal complement of the dyadic middle.

## Lean

Module: `GreenCalculusOfThePrimeFreeWindow/ChargeCancellationPreservesTheCertifiedFloor.lean`.

- `exists_groundVector_with_floor_of_short`
- `eigenvalue_ge_of_ne_ground_of_short`
- `schur_floor_of_charge_cancellation`
- `hermNegIndex_neutralWindow_eq_one_iff_harmonic_nonneg`

Direct `lake --old env lean` check passed. All four transitive audits list
only `propext`, `Classical.choice`, `Quot.sound`. Umbrella import added.
