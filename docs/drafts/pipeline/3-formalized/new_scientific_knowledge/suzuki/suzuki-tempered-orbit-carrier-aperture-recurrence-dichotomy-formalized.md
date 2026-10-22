# The tempered orbit carrier and its aperture-recurrence barrier, formalized

- **ID:** `suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PAPER-PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiOrbitWeightSummability.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiOrbitCarrier.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiApertureRecurrence.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiApertureAlmostEvery.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiLiouvilleAperture.lean`
  - weighted shifts (pre-existing): `formal/GaloisForLFunctions/HTGeometry/WeightedShiftEnergy.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)` lattice, `ℓ¹` length | `orbitLength`, `orbitLength_add_le` |
| `(2)` weight and lift | `orbitWeight`, `orbitTranslate`, `norm_orbitTranslate` |
| `(9)` exact lattice mass | `tsum_pow_natAbs` (`(1+x)/(1-x)`), `tsum_pow_orbitLength` (rank product in `ℝ≥0∞`), `tsum_orbitWeight_sq`, `summable_orbitWeight_sq` |
| `(3)`, `(10)` lift energy | `tsum_sq_orbitLift` |
| `(11)` bounded-profile lift | `tsum_sq_orbitLift_const` |
| `(4)` root reconstruction | `orbitTranslate_zero` |
| `(12)`–`(15)` intertwining | `orbitShiftRatio`, `orbitTranslate_add`, `orbitLift_translate` |
| `(16)`–`(17)` edge ratio and shift bound | `orbitWeight_le_ratio`, `abs_orbitShiftRatio_le`, `tsum_sq_orbitWeightedShift_le` |
| `(18)`–`(19)` finite adjacency | `tsum_sq_orbitWeightedShift_le_of_le` |
| `(5)`, `(20)`–`(22)` terminal coercivity | `abs_re_inner_le_norm_mul_sq`, `re_inner_terminal_le` |
| `(23)` depth | `apertureDefect`, `apertureDepth` |
| `(24)`–`(26)` finite-type summability | `weighted_activation_le`, `summable_weighted_apertureActivation`, `summable_weighted_apertureActivation_grade` |
| `(27)` full measure | `orbitLevel`, `card_orbitLevel_le`, `volume_apertureApproxSet_le`, `summable_apertureMajorant`, `ae_finite_apertureApprox` |
| `(28)` dense Liouville apertures | `liouvilleStage`, `dense_longDisplacements`, `dense_liouvilleStage`, `dense_liouvilleApertures` |
| `(29)`–`(30)` tempered lower bound | `orbitLength_sub_unit`, `weight_ge_of_edge_bound` |
| `(31)` sharp no-go | `sq_lt_apertureDepth`, `tendsto_liouvilleBarrier`, `liouville_activation_unbounded` |

## What the card actually closes

The positive half is exact.  The lattice mass of the exponential weight is computed rather than
estimated — `((1+ρ²)/(1-ρ²))^{#P}` — by splitting the `ℓ¹` length coordinatewise in `ℝ≥0∞`, where
the first-coordinate split is unconditional; physical translation is an isometry of `L²`, so the
orbit lift costs exactly that mass and the root coordinate returns the profile untouched.  Prime
translation intertwines with a weighted coordinate shift whose edge ratios are pinched by
`ρ^{±|s|₁}`, so the adjacency is bounded in energy without any self-adjointness, and the terminal
bracket `2L - κ - ‖T‖` is coercive on a far enough ray purely from the numerical-range inequality.

The dichotomy is equally exact.  At finite recurrence type the weighted activations are dominated
by the orbit weight of the smaller ratio `e^{-(κ-σR)}`, hence square summable — and stay so against
any bounded grade.  Almost every aperture is of finite type: the apertures approximated to depth
`e^{-cN}` by a valuation of length `N` are covered by at most `(2N+1)^{#P}` intervals of length
`e^{-cN}`, a summable majorant, so Borel–Cantelli leaves only finitely many approximations almost
surely.  Yet the exceptional set is dense: each approximation stage is open and dense — density
survives deleting the finitely many short valuations — so Baire produces a dense set of apertures
approximated infinitely often at the super-exponential rate `e^{-N²}`.  There, any weight with
bounded inverse edge ratios satisfies `w(ν) ≥ w₀ C^{|ν|₁}` and the activation
`e^{σ L_ν} w(ν) ≥ w₀ e^{σN²} C^N` is unbounded: no exponentially tempered orbit carrier holds all
endpoint activations in a positive Gamma strip.

## Hypotheses

Object data only: a finite alphabet `P`, a ratio `0 ≤ ρ < 1`, a displacement map `ℓ` (injective and
with dense range for the Liouville half — properties of the prime-log map, not assumptions about
Suzuki's operator), the finite-type bound `L_ν ≤ R |ν|₁`, the margin `σR < κ`, and the edge bound
`w μ ≤ C w(μ + e)` for unit steps.  No RH, no self-adjointness, no `sorry`, `axiom`, `opaque`, or
`unsafe`.  Every theorem named above audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The card's own open gates stay open: `SUZUKI-TEMPERED-ORBIT-NORMAL-IDENTITY`, passage across the
exceptional apertures (or a nontempered relation), trace-zero `H¹₀`, completed Evans injectivity,
and RH.
