# Source–norm–support forgetful tower law — formalized

- **ID:** `source-norm-support-forgetful-tower-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `source-norm-support-forgetful-tower-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.ForgetfulTower` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/ForgetfulTower.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Realization

| Card `(1)`–`(4)` | Lean |
|---|---|
| `τ` | `legSwap = !![0,1;1,0]` |
| `T_δ` | `legTwist δ = !![0,1;δ,0]` |
| `L_c` | `legScale c = !![c,0;0,c]` |
| `a = c(δ−1)` | `sourceScalar δ c` |
| `D = T_δ L_c − L_c τ` | `transportDefect δ c` |
| `Γ : ℂ²⊕ℂ² → ℂ²` | `legCarrier δ c : Matrix (Fin 2) (Fin 2 ⊕ Fin 2) ℂ` |
| `Γ†` | `legCarrierPseudoInverse δ c = ‖a‖⁻²·Γᴴ` |

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

1. `transportDefect_eq` — **(3)** first half: `D = a E₂₁`.
2. `legTwist_mul_transportDefect` — **(3)** second half: `T_δ D = a E₁₁`.
3. `legCarrier_mulVec` — **(8)**: `Γ(x,y) = a(y₀e₀ + x₀e₁)`.
4. `legCarrier_mul_conjTranspose` — **(5)** the exact Gram identity `Γ Γ* = |a|² I`.
5. `det_legCarrier_mul_conjTranspose` — **(7)** second half: `det(Γ Γ*) = |a|⁴`.
6. `legCarrier_eq_zero`, `legCarrier_surjective` — **(6)**: the range is `0` when `a = 0` and all of
   `ℂ²` when `a ≠ 0`.
7. `legCarrierPseudoInverse`, `legCarrier_mul_pseudoInverse` — `Γ Γ† = I` for `a ≠ 0`.
8. `sum_normSq_conjTranspose_mulVec` — `‖Γ*x‖² = |a|² ‖x‖²`: the adjoint scales every vector by
   exactly `|a|`.
9. `sum_normSq_pseudoInverse_mulVec` — **(7)** first half: `‖Γ†x‖² = ‖x‖²/|a|²` for every `x`, i.e.
   `Γ†` scales every vector by exactly `|a|⁻¹`, so `‖Γ†‖ = |a|⁻¹`.  The pointwise statement is
   sharper than the operator-norm statement of the card and implies it.
10. `shadow_tower` — **(13)**: the support shadow factors through the magnitude shadow.
11. `normSq_forgets_phase` — the magnitude shadow loses the phase and coorientation.
12. `support_forgets_magnitude` — the support shadow loses the magnitude.
    Items 10–12 are the three-shadow theorem: the three route outputs are successive functions of
    the one framed scalar `a`, so their product cannot create selection.
13. `relative_channel_central_twist` — **(14)**: `(δT_j) f (δT_i)⁻¹ = T_j f T_i⁻¹`.
14. `det_central_twist` — the same twist does change the determinant holonomy, so exact-category
    data alone cannot select `δ = 1` while framed determinant data can.

The arithmetic instantiation `(9)`–`(12)` of the card substitutes the corpus residue for `a` in
items 4, 5 and 9; the substitution is a specialization of the formalized identities and carries no
further mathematical content, which is why the card itself directs formalization of the matrix
identity independently of the arithmetic instantiation.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ForgetfulTower.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                              # green
```

`#print axioms` on `legCarrier_mul_conjTranspose`, `sum_normSq_pseudoInverse_mulVec`,
`relative_channel_central_twist` returns only `[propext, Classical.choice, Quot.sound]`.
