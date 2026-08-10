# Complex Gaussian fixed law, positive erasure, metaplectic history — Lean certification

- **ID:** ULF-ACTION-1
- **Paper card:** `complex-gaussian-fixed-law-positive-erasure-and-metaplectic-history-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveMetaplecticActionHistory`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Model

`rotatingAction θ z = ½ e^{iθ} z²` (equation 1) and `descentLine θ y = e^{-iθ/2} y` (equation 2).
The amplitude is defined as the honest pullback of `e^{-S}dz` along the oriented parametrization,
with `descentLine_hasDerivAt` certifying the Jacobian `dz = e^{-iθ/2} dy`; the value is then
*computed*, not assumed.

## Certified declarations

| Card clause | Lean |
|---|---|
| Crit(S_θ) = {0} | `rotatingAction_hasDerivAt`, `deriv_rotatingAction`, `crit_rotatingAction` |
| `H_θ = e^{iθ}` | `rotatingHessian`, `deriv_rotatingAction_eq`, `secondDeriv_rotatingAction` |
| `H_θ^* H_θ = 1` | `rotatingHessian_gram`, `rotatingHessian_norm` |
| `S_θ(ι_θ(y)) = y²/2` | `rotatingAction_descentLine` |
| `dz = e^{-iθ/2} dy` | `descentLine_hasDerivAt` |
| `∫ e^{-y²/2} = √(2π)` | `gaussian_integral_half` (from mathlib `integral_gaussian`) |
| (3) `Z(θ) = √(2π) e^{-iθ/2}` | `thimbleAmplitude`, `thimbleAmplitude_eq` |
| `Z(θ) ≠ 0` | `thimbleAmplitude_ne_zero` |
| action `2π`-periodic | `rotatingAction_periodic` |
| critical locus `2π`-periodic | `crit_periodic` |
| Hessian `2π`-periodic | `rotatingHessian_periodic` |
| **unoriented** line `2π`-periodic | `descentLine_range_add_two_pi` |
| (4) `ι_{θ+2π} = −ι_θ` | `descentLine_add_two_pi` |
| (4) `Z(θ+2π) = −Z(θ)` | `thimbleAmplitude_add_two_pi` |
| history does not close at `2π` | `thimbleAmplitude_add_two_pi_ne` |
| history closes at `4π` | `thimbleAmplitude_add_four_pi` |
| capstone | `positive_shadow_does_not_determine_orientation` |

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveMetaplecticActionHistory.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,425 jobs.  `#print axioms` on
`crit_rotatingAction`, `secondDeriv_rotatingAction`, `rotatingHessian_gram`,
`rotatingAction_descentLine`, `descentLine_hasDerivAt`, `thimbleAmplitude_eq`,
`descentLine_range_add_two_pi`, `thimbleAmplitude_add_two_pi`, `thimbleAmplitude_add_four_pi`, and
`positive_shadow_does_not_determine_orientation` reports only `propext`, `Classical.choice`, and
`Quot.sound`.  No project axiom, placeholder, hypothesis interface, or computation proof is used.

## Scope, honestly stated

The card classifies itself as a **bridge**, not field core: the mechanism is classical
Picard–Lefschetz and metaplectic behaviour.  The Lean module certifies exactly that finite
statement and nothing more — no hypertranscendence, no arithmetic selection, no completion.  What it
does establish unconditionally is the split: on one fixed one-parameter family of quadratic laws,
the critical locus and the positive Gram shadow of the Hessian are strictly `2π`-periodic while the
oriented cycle and the Gaussian determinant require the double cover.

## Exact field consequence

The datum that positivity loses here is not curvature and not a higher jet: it is the square-root
lift of a loop in the space of nondegenerate quadratic laws.  Any doctrine that reports only
`conj(H) H` has, provably, thrown that lift away.
