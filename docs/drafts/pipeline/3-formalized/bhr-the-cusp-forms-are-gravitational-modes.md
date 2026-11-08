# BHR — the cusp forms are gravitational modes at the universal damping

- **ID:** bhr-cusp-gravitational-modes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** A26 (metric of `L²` horizon data, cusp sector); `modular-horizon-general-data-cusp-spin-two.md` (spin two
  for the zeros); `bhr-a-weyl-lower-bound-for-the-cusp-spectrum.md`.
- **Statement:** Let `U` be a level-one cusp form, `-y²ΔU = λU`, and `ν² = ¼ − λ`.
  1. `U` is `C^∞`.
  2. `U` gives exact vacuum perturbations of the massless topological black hole with horizon `PSL₂(ℤ)\ℍ`: vector
     sector with time factors `e^{(−½+ν)t}` (Neumann) and `e^{(−3/2+ν)t}` (Dirichlet), scalar sector with
     `e^{(−3/2+ν)t}`; the vector modes are not pure gauge.
  3. Since `λ ≥ ¼`, `Re ν = 0`: every cusp mode is at the base damping `½` or `3/2` of its sector.
  4. The zeta modes `w = p − ½`, `s = p − 3/2`, `p = (ρ−1)/2`, are strictly deeper: `Re(p − ½) ∈ (−1, −½)`; RH ⟺ every
     zeta mode is exactly `¼` deeper.
  5. `#{zeta modes of frequency ≤ T} / #{cusp modes of frequency ≤ T} → 0`.

## Paper proof
1. In the chart `F(x+iy) = U(x+iy)` satisfies `Δ_{euc}F = −(λ/y²)F` with smooth potential on `y > 0`; planar elliptic
   regularity (`PlanarElliptic.smooth_of_equation`) gives `F ∈ C^∞`.
2. In horizon coordinates `(x, y)`, `y²(∂ₓ² + ∂ᵧ²)F = −λF` (chain rule through the linear chart). With `λ = −w(w+1)`,
   `−λ = (w+1)(w+2)`, `−λ = (s+1)(s+2)` for `w = −½+ν`, `w = −3/2+ν`, `s = −3/2+ν`, the corpus reconstructions
   (`vectorMetricField_vacuum` with the radial masters `fN`, `gP`; `field_residual_zero`) apply verbatim. If the
   gradient vanished on `y > 0`, the eigenvalue equation would give `λF = 0`, impossible as `λ ≥ ¼` and `F ≢ 0`.
3. `ν² = ¼ − λ ≤ 0` real forces `Re ν = 0`.
4. `−½ < Re p < 0` at a zero; `Re p = −¼` ⟺ `Re ρ = ½`.
5. Weyl lower bound: cusp modes with `t ≤ T` number `≥ c(¼ + T²)`; zeros with ordinate in `[0, 2T]` number
   `≤ c'·2T log 2T`; the ratio is `O(log T/T)`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheCuspFormsAreGravitationalModes.lean`, wired into `BlackHoleRingdown.lean`,
checked with `lake --old env lean`, no messages. Axioms of `cusp_gravitational_modes`, `tendsto_zeroModes_div_cuspModes`,
`riemannHypothesis_iff_zero_modes_quarter_deeper`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspGravity`) |
|---|---|
| Chart calculus | `chartL`, `coordDeriv_comp`, `coordDeriv_two_comp`, `fderiv_fderiv_clm` |
| (1) | `compField_eq`, `contDiffOn_compField_top` |
| Horizon equation | `horizonField`, `contDiffAt_horizonField`, `horizonField_eigen` |
| (2) | `vector_mode_neumann`, `vector_mode_dirichlet`, `scalar_mode`, `exists_gradCovector_ne_zero`, `cusp_gravitational_modes` |
| (3) | `exists_spectralParameter`, `re_eq_zero_of_sq` |
| (4) | `zero_modes_lie_deeper`, `riemannHypothesis_iff_zero_modes_quarter_deeper` |
| (5) | `tendsto_zeroModes_div_cuspModes` |

## Scope
Separated modes of single cusp forms; the metric of a general `L²` cusp datum (a convergent superposition) is not treated.

## Log
- 2026-11-08 — created and formalized.
