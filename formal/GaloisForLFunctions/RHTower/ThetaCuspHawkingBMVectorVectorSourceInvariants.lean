import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorVectorQuadraticSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticAngularSource

/-!
# Invariant decomposition of the vector–vector quadratic Einstein source

The quadratic Einstein source `Quadratic.einstein J K` of the coexact vector jet
`K = coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy` (the vector partner of the fundamental scalar
`S`, `ΔS = (s+1)(s+2)S` on the hyperbolic plane, so `S_yy = λS/y² − S_xx`) over the
Birmingham–Mokhtari background is built from angular invariants of `S` only: the orbit block
carries `S²`, `|∇S|² = y²(S_x² + S_y²)` and the covariant Hessian square
`|∇∇S|² = y⁴(H_xx² + 2H_xy² + H_yy²)` with `H_xx = S_xx − S_y/y`, `H_xy = S_xy + S_x/y`,
`H_yy = S_yy + S_y/y`; the mixed block is the gradient of a combination of `S²` and `|∇S|²`
(both components from the same potential); the angular block is a trace part in the same three
scalars plus a trace-free part spanned by `(∇S⊗∇S)^{tf}` and `tfHess(S²)`. No third derivative
of `S` survives. Each statement is the closed vector–vector source component with the coexact
substitution and a rational identity (`B²` times radial coefficients in `(s, r)`).
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMQuadraticAngularSource
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet D4BMVectorLinearEquation
noncomputable section
variable {s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ}

/-- Vector–vector source, orbit `(0,0)` component, as angular invariants of `S`. -/
theorem coexactJet_quadratic_einstein_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 0 =
      B ^ 2 * ((((-1 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 6)) * (y ^ 4 * ((Sxx - Sy / y) ^ 2 + 2 * (Sxy + Sx / y) ^ 2 + (((s + 1) * (s + 2)) * S / y ^ 2 - Sxx + Sy / y) ^ 2)) + (((9 / 2 : ℂ) * s ^ 2 + (-9 / 2 : ℂ) * s ^ 2 * r ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 4 + (3 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6)) * (y ^ 2 * (Sx ^ 2 + Sy ^ 2)) + (((2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (6 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 3 * r ^ 2 + (13 / 2 : ℂ) * s ^ 4 + (13 / 2 : ℂ) * s ^ 4 * r ^ 2 + (3 : ℂ) * s ^ 5 + (3 : ℂ) * s ^ 5 * r ^ 2 + (1 / 2 : ℂ) * s ^ 6 + (1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6)) * (S ^ 2)) := by
  rw [coexactJet, vectorJet_quadratic_einstein_0_0 hr hy hf]
  field_simp
  ring

/-- Vector–vector source, orbit `(0,1)` component, as angular invariants of `S`. -/
theorem coexactJet_quadratic_einstein_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 1 =
      B ^ 2 * ((0 : ℂ) * (y ^ 4 * ((Sxx - Sy / y) ^ 2 + 2 * (Sxy + Sx / y) ^ 2 + (((s + 1) * (s + 2)) * S / y ^ 2 - Sxx + Sy / y) ^ 2)) + (((2 : ℂ) * s ^ 2 + (6 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4) / (r ^ 5 * (r ^ 2 - 1))) * (y ^ 2 * (Sx ^ 2 + Sy ^ 2)) + (((4 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3 + (13 : ℂ) * s ^ 4 + (6 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1))) * (S ^ 2)) := by
  rw [coexactJet, vectorJet_quadratic_einstein_0_1 hr hy hf]
  field_simp
  ring

/-- Vector–vector source, orbit `(1,1)` component, as angular invariants of `S`. -/
theorem coexactJet_quadratic_einstein_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 1 =
      B ^ 2 * ((((-1 : ℂ) * s ^ 2) / (r ^ 6 * (r ^ 2 - 1))) * (y ^ 4 * ((Sxx - Sy / y) ^ 2 + 2 * (Sxy + Sx / y) ^ 2 + (((s + 1) * (s + 2)) * S / y ^ 2 - Sxx + Sy / y) ^ 2)) + (((11 / 2 : ℂ) * s ^ 2 + (-19 / 2 : ℂ) * s ^ 2 * r ^ 2 + (6 : ℂ) * s ^ 2 * r ^ 4 + (7 : ℂ) * s ^ 3 + (-5 : ℂ) * s ^ 3 * r ^ 2 + (3 / 2 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2)) * (y ^ 2 * (Sx ^ 2 + Sy ^ 2)) + (((2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (6 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 3 * r ^ 2 + (13 / 2 : ℂ) * s ^ 4 + (13 / 2 : ℂ) * s ^ 4 * r ^ 2 + (3 : ℂ) * s ^ 5 + (3 : ℂ) * s ^ 5 * r ^ 2 + (1 / 2 : ℂ) * s ^ 6 + (1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 2)) * (S ^ 2)) := by
  rw [coexactJet, vectorJet_quadratic_einstein_1_1 hr hy hf]
  field_simp
  ring

/-- Vector–vector source, mixed `(0,2)` component, as angular invariants of `S`. -/
theorem coexactJet_quadratic_einstein_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 2 =
      B ^ 2 * ((((1 : ℂ) * s ^ 3) / (r ^ 4)) * (2 * y ^ 2 * (Sx * Sxx + Sy * Sxy)) + (((3 : ℂ) * s ^ 2 + (11 / 2 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 5) / (r ^ 4)) * (2 * S * Sx)) := by
  rw [coexactJet, vectorJet_quadratic_einstein_0_2 hr hy hf]
  field_simp
  ring

/-- Vector–vector source, mixed `(0,3)` component, as angular invariants of `S`. -/
theorem coexactJet_quadratic_einstein_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 0 3 =
      B ^ 2 * ((((1 : ℂ) * s ^ 3) / (r ^ 4)) * (2 * y * (Sx ^ 2 + Sy ^ 2) + 2 * y ^ 2 * (Sx * Sxy + Sy * (((s + 1) * (s + 2)) * S / y ^ 2 - Sxx))) + (((3 : ℂ) * s ^ 2 + (11 / 2 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 5) / (r ^ 4)) * (2 * S * Sy)) := by
  rw [coexactJet, vectorJet_quadratic_einstein_0_3 hr hy hf]
  field_simp
  ring

/-- Vector–vector source, mixed `(1,2)` component, as angular invariants of `S`. -/
theorem coexactJet_quadratic_einstein_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 2 =
      B ^ 2 * ((((2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3) / (r ^ 5 * (r ^ 2 - 1))) * (2 * y ^ 2 * (Sx * Sxx + Sy * Sxy)) + (((3 : ℂ) * s ^ 2 + (11 / 2 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1))) * (2 * S * Sx)) := by
  rw [coexactJet, vectorJet_quadratic_einstein_1_2 hr hy hf]
  field_simp
  ring

/-- Vector–vector source, mixed `(1,3)` component, as angular invariants of `S`. -/
theorem coexactJet_quadratic_einstein_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 1 3 =
      B ^ 2 * ((((2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3) / (r ^ 5 * (r ^ 2 - 1))) * (2 * y * (Sx ^ 2 + Sy ^ 2) + 2 * y ^ 2 * (Sx * Sxy + Sy * (((s + 1) * (s + 2)) * S / y ^ 2 - Sxx))) + (((3 : ℂ) * s ^ 2 + (11 / 2 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1))) * (2 * S * Sy)) := by
  rw [coexactJet, vectorJet_quadratic_einstein_1_3 hr hy hf]
  field_simp
  ring

/-- Vector–vector source, angular `(2,3)` component, as angular invariants of `S`. -/
theorem coexactJet_quadratic_einstein_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 2 3 =
      B ^ 2 * ((((11 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4) / (r ^ 4)) * (Sx * Sy) + (0 : ℂ) * (2 * S * (Sxy + Sx / y) + 2 * Sx * Sy)) := by
  rw [coexactJet, vectorJet_quadratic_einstein_2_3 hr hy hf]
  field_simp
  ring

/-- Vector–vector source, angular `(2,2)` component, as angular invariants of `S`. -/
theorem coexactJet_quadratic_einstein_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 2 2 =
      B ^ 2 * (((0 : ℂ) * (y ^ 4 * ((Sxx - Sy / y) ^ 2 + 2 * (Sxy + Sx / y) ^ 2 + (((s + 1) * (s + 2)) * S / y ^ 2 - Sxx + Sy / y) ^ 2)) + (((6 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (7 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 4) / (r ^ 4)) * (y ^ 2 * (Sx ^ 2 + Sy ^ 2)) + (((-2 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3 + (-13 / 2 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 4)) * (S ^ 2)) / y ^ 2 + (1 / 2 : ℂ) * ((((11 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4) / (r ^ 4)) * (Sx ^ 2 - Sy ^ 2) + (0 : ℂ) * (2 * S * (2 * Sxx - ((s + 1) * (s + 2)) * S / y ^ 2 - 2 * Sy / y) + 2 * (Sx ^ 2 - Sy ^ 2)))) := by
  rw [coexactJet, vectorJet_quadratic_einstein_2_2 hr hy hf]
  field_simp
  ring

/-- Vector–vector source, angular `(3,3)` component, as angular invariants of `S`. -/
theorem coexactJet_quadratic_einstein_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.einstein (D4BMBackground.jet r y) (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) 3 3 =
      B ^ 2 * (((0 : ℂ) * (y ^ 4 * ((Sxx - Sy / y) ^ 2 + 2 * (Sxy + Sx / y) ^ 2 + (((s + 1) * (s + 2)) * S / y ^ 2 - Sxx + Sy / y) ^ 2)) + (((6 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (7 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 4) / (r ^ 4)) * (y ^ 2 * (Sx ^ 2 + Sy ^ 2)) + (((-2 : ℂ) * s ^ 2 + (-6 : ℂ) * s ^ 3 + (-13 / 2 : ℂ) * s ^ 4 + (-3 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 4)) * (S ^ 2)) / y ^ 2 - (1 / 2 : ℂ) * ((((11 : ℂ) * s ^ 2 + (12 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 4) / (r ^ 4)) * (Sx ^ 2 - Sy ^ 2) + (0 : ℂ) * (2 * S * (2 * Sxx - ((s + 1) * (s + 2)) * S / y ^ 2 - 2 * Sy / y) + 2 * (Sx ^ 2 - Sy ^ 2)))) := by
  rw [coexactJet, vectorJet_quadratic_einstein_3_3 hr hy hf]
  field_simp
  ring

end
end RHTower.D4BMQuadraticAngularSource
