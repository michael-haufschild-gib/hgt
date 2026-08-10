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

The arithmetic instantiation `(9)`–`(12)` is formalized as well:

15. `wallParameter`, `cycleTransport` — **cards `(9)`, `(11)`**: `κ = (2 Re ρ − 1) log n` and the
    prime-cycle transport `δ_n(ρ) = e^κ`.
16. `wallParameter_eq_zero_iff` — for cycle level `n ≥ 2` the wall parameter vanishes exactly on
    the critical line, so "exact wall" means `Re ρ = 1/2`.
17. `normSq_sourceScalar_cycleTransport`, `legCarrier_mul_conjTranspose_wall` — **card `(10)`**:
    `|a_ρ|² = |c_ρ|² (e^κ − 1)²`, so `Γ_ρ Γ_ρ* = |a_ρ|² I`.
17b. `sourceScalar_cycleTransport_eq_zero_iff`, `legCarrier_cycleTransport_eq_zero_iff`,
    `legCarrier_cycleTransport_surjective` — the degeneration locus: for cycle level `n ≥ 2` and
    `c_ρ ≠ 0`, the framed residue vanishes, equivalently the two-column carrier is the zero matrix,
    **exactly when `Re ρ = 1/2`**; off the critical line the carrier is surjective.  This is the
    same equation as `(19)` of
    `identity-sector-radial-gauge-blindness-and-cross-grade-selection-law`.
18. `sum_normSq_pseudoInverse_wall` — the exact squared pseudo-inverse gain
    `1/(|c_ρ|² (e^κ − 1)²)`.
19. `tendsto_exp_sub_one_div_atZero`, `tendsto_pseudoInverse_gain_ratio` — **card `(12)`**: the
    ratio of the exact gain to the model `1/(|c_ρ|² κ²)` tends to one as `κ → 0`.  The card's `∼`
    is thus a proved limit, not a heuristic; the slope input is the derivative of `exp` at `0`.
20. `tendsto_pseudoInverse_gain_atTop` — **card `(12)`, the reading**: the gain blows up as
    `κ → 0`, so the exact wall is a singular-conditioning wall.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ForgetfulTower.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                              # green
```

`#print axioms` on `legCarrier_mul_conjTranspose`, `sum_normSq_pseudoInverse_mulVec`,
`relative_channel_central_twist` returns only `[propext, Classical.choice, Quot.sound]`.
