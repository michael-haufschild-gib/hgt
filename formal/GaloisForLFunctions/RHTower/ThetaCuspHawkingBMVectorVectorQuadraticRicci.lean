import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorVectorQuadraticCurvature

/-!
# The vector–vector quadratic Ricci variation of the fundamental Birmingham–Mokhtari vector jet

Every component `Quadratic.ricci J K i j` (`i ≤ j`) of the quadratic Ricci variation of the
fundamental vector metric jet `K = vectorJet s r y B A C P Q R U W` over the Birmingham–Mokhtari
background `J`, and its background trace, in closed form: each is a sum of a few terms
`B² · P(s, r)/(r^a (r² − 1)^b) · (quadratic covector-jet monomial) · y^k`. The proofs sum the four
closed Riemann traces; no heartbeat limit is raised.
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMVectorLinearEquation
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet D4BMScalarLinearEquation
noncomputable section
variable {s r y B A C P Q R U W : ℂ}

/-- Vector–vector quadratic Ricci variation, component `(0, 0)`. -/
theorem vectorJet_quadratic_ricci_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 =
      B ^ 2 * ((1 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 4 + (2 : ℂ) * s ^ 2 * r ^ 6 + (2 : ℂ) * s ^ 3 + (-6 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 3 * r ^ 4 + (1 : ℂ) * s ^ 4 + (-4 : ℂ) * s ^ 4 * r ^ 2 + (3 : ℂ) * s ^ 4 * r ^ 4) / (r ^ 6 * (r ^ 2 - 1)) * A ^ 2 * y ^ 2 + B ^ 2 * ((1 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 2 * r ^ 4 + (2 : ℂ) * s ^ 2 * r ^ 6 + (2 : ℂ) * s ^ 3 + (-6 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 3 * r ^ 4 + (1 : ℂ) * s ^ 4 + (-4 : ℂ) * s ^ 4 * r ^ 2 + (3 : ℂ) * s ^ 4 * r ^ 4) / (r ^ 6 * (r ^ 2 - 1)) * C ^ 2 * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 2) / (r ^ 6) * Q * R * y ^ 4 + B ^ 2 * ((1 : ℂ) * s ^ 2) / (r ^ 6) * Q ^ 2 * y ^ 4 + B ^ 2 * ((1 : ℂ) * s ^ 2) / (r ^ 6) * R ^ 2 * y ^ 4 := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, vectorJet_quadratic_curvature_0_0_0 hr hy hf, vectorJet_quadratic_curvature_1_0_0 hr hy hf, vectorJet_quadratic_curvature_2_0_0 hr hy hf, vectorJet_quadratic_curvature_3_0_0 hr hy hf]
  field_simp
  ring

/-- Vector–vector quadratic Ricci variation, component `(0, 1)`. -/
theorem vectorJet_quadratic_ricci_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 =
      B ^ 2 * ((-2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (-6 : ℂ) * s ^ 3 + (10 : ℂ) * s ^ 3 * r ^ 2 + (-4 : ℂ) * s ^ 3 * r ^ 4 + (-2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A ^ 2 * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (-6 : ℂ) * s ^ 3 + (10 : ℂ) * s ^ 3 * r ^ 2 + (-4 : ℂ) * s ^ 3 * r ^ 4 + (-2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * C ^ 2 * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 2) / (r ^ 5 * (r ^ 2 - 1)) * Q * R * y ^ 4 + B ^ 2 * ((1 : ℂ) * s ^ 2) / (r ^ 5 * (r ^ 2 - 1)) * Q ^ 2 * y ^ 4 + B ^ 2 * ((1 : ℂ) * s ^ 2) / (r ^ 5 * (r ^ 2 - 1)) * R ^ 2 * y ^ 4 := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, vectorJet_quadratic_curvature_0_0_1 hr hy hf, vectorJet_quadratic_curvature_1_0_1 hr hy hf, vectorJet_quadratic_curvature_2_0_1 hr hy hf, vectorJet_quadratic_curvature_3_0_1 hr hy hf]
  field_simp
  ring

/-- Vector–vector quadratic Ricci variation, component `(0, 2)`. -/
theorem vectorJet_quadratic_ricci_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * P * y ^ 2 + B ^ 2 * ((3 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * Q * y ^ 2 + B ^ 2 * ((-3 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-3 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * R * y ^ 2 := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, vectorJet_quadratic_curvature_0_0_2 hr hy hf, vectorJet_quadratic_curvature_1_0_2 hr hy hf, vectorJet_quadratic_curvature_2_0_2 hr hy hf, vectorJet_quadratic_curvature_3_0_2 hr hy hf]
  field_simp
  ring

/-- Vector–vector quadratic Ricci variation, component `(0, 3)`. -/
theorem vectorJet_quadratic_ricci_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 =
      B ^ 2 * ((-3 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-3 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * Q * y ^ 2 + B ^ 2 * ((3 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * R * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A ^ 2 * y + B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * P * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C ^ 2 * y := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, vectorJet_quadratic_curvature_0_0_3 hr hy hf, vectorJet_quadratic_curvature_1_0_3 hr hy hf, vectorJet_quadratic_curvature_2_0_3 hr hy hf, vectorJet_quadratic_curvature_3_0_3 hr hy hf]
  field_simp
  ring

/-- Vector–vector quadratic Ricci variation, component `(1, 1)`. -/
theorem vectorJet_quadratic_ricci_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 1 =
      B ^ 2 * ((-11 : ℂ) * s ^ 2 + (26 : ℂ) * s ^ 2 * r ^ 2 + (-21 : ℂ) * s ^ 2 * r ^ 4 + (6 : ℂ) * s ^ 2 * r ^ 6 + (-12 : ℂ) * s ^ 3 + (22 : ℂ) * s ^ 3 * r ^ 2 + (-10 : ℂ) * s ^ 3 * r ^ 4 + (-3 : ℂ) * s ^ 4 + (4 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 4 * r ^ 4) / (r ^ 6 * (r ^ 2 - 1) ^ 3) * A ^ 2 * y ^ 2 + B ^ 2 * ((-11 : ℂ) * s ^ 2 + (26 : ℂ) * s ^ 2 * r ^ 2 + (-21 : ℂ) * s ^ 2 * r ^ 4 + (6 : ℂ) * s ^ 2 * r ^ 6 + (-12 : ℂ) * s ^ 3 + (22 : ℂ) * s ^ 3 * r ^ 2 + (-10 : ℂ) * s ^ 3 * r ^ 4 + (-3 : ℂ) * s ^ 4 + (4 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 4 * r ^ 4) / (r ^ 6 * (r ^ 2 - 1) ^ 3) * C ^ 2 * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 2) / (r ^ 4 * (r ^ 2 - 1) ^ 2) * Q * R * y ^ 4 + B ^ 2 * ((1 : ℂ) * s ^ 2) / (r ^ 4 * (r ^ 2 - 1) ^ 2) * Q ^ 2 * y ^ 4 + B ^ 2 * ((1 : ℂ) * s ^ 2) / (r ^ 4 * (r ^ 2 - 1) ^ 2) * R ^ 2 * y ^ 4 := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, vectorJet_quadratic_curvature_0_1_1 hr hy hf, vectorJet_quadratic_curvature_1_1_1 hr hy hf, vectorJet_quadratic_curvature_2_1_1 hr hy hf, vectorJet_quadratic_curvature_3_1_1 hr hy hf]
  field_simp
  ring

/-- Vector–vector quadratic Ricci variation, component `(1, 2)`. -/
theorem vectorJet_quadratic_ricci_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 2 =
      B ^ 2 * ((-4 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 2 * r ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 4 + (-2 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A * P * y ^ 2 + B ^ 2 * ((3 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * C * Q * y ^ 2 + B ^ 2 * ((-7 : ℂ) * s ^ 2 + (11 : ℂ) * s ^ 2 * r ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 4 + (-3 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * C * R * y ^ 2 := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, vectorJet_quadratic_curvature_0_1_2 hr hy hf, vectorJet_quadratic_curvature_1_1_2 hr hy hf, vectorJet_quadratic_curvature_2_1_2 hr hy hf, vectorJet_quadratic_curvature_3_1_2 hr hy hf]
  field_simp
  ring

/-- Vector–vector quadratic Ricci variation, component `(1, 3)`. -/
theorem vectorJet_quadratic_ricci_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 3 =
      B ^ 2 * ((-7 : ℂ) * s ^ 2 + (11 : ℂ) * s ^ 2 * r ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 4 + (-3 : ℂ) * s ^ 3 + (3 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A * Q * y ^ 2 + B ^ 2 * ((3 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3 + (-1 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A * R * y ^ 2 + B ^ 2 * ((-4 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 2 * r ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 4 + (-2 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A ^ 2 * y + B ^ 2 * ((4 : ℂ) * s ^ 2 + (-8 : ℂ) * s ^ 2 * r ^ 2 + (4 : ℂ) * s ^ 2 * r ^ 4 + (2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * C * P * y ^ 2 + B ^ 2 * ((-4 : ℂ) * s ^ 2 + (8 : ℂ) * s ^ 2 * r ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 4 + (-2 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * C ^ 2 * y := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, vectorJet_quadratic_curvature_0_1_3 hr hy hf, vectorJet_quadratic_curvature_1_1_3 hr hy hf, vectorJet_quadratic_curvature_2_1_3 hr hy hf, vectorJet_quadratic_curvature_3_1_3 hr hy hf]
  field_simp
  ring

/-- Vector–vector quadratic Ricci variation, component `(2, 2)`. -/
theorem vectorJet_quadratic_ricci_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 2 =
      B ^ 2 * ((-2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * Q * y + B ^ 2 * ((-2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * R * y + B ^ 2 * ((-3 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 6 + (-4 : ℂ) * s ^ 3 + (8 : ℂ) * s ^ 3 * r ^ 2 + (-4 : ℂ) * s ^ 3 * r ^ 4 + (-1 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 4 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1) ^ 2) * A ^ 2 + B ^ 2 * ((4 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * P * y + B ^ 2 * ((-8 : ℂ) * s ^ 2 + (10 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-8 : ℂ) * s ^ 3 + (8 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * P ^ 2 * y ^ 2 + B ^ 2 * ((-1 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * Q ^ 2 * y ^ 2 + B ^ 2 * ((-1 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * R ^ 2 * y ^ 2 := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, vectorJet_quadratic_curvature_0_2_2 hr hy hf, vectorJet_quadratic_curvature_1_2_2 hr hy hf, vectorJet_quadratic_curvature_2_2_2 hr hy hf, vectorJet_quadratic_curvature_3_2_2 hr hy hf]
  field_simp
  ring

/-- Vector–vector quadratic Ricci variation, component `(2, 3)`. -/
theorem vectorJet_quadratic_ricci_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 3 =
      B ^ 2 * ((-11 : ℂ) * s ^ 2 + (22 : ℂ) * s ^ 2 * r ^ 2 + (-11 : ℂ) * s ^ 2 * r ^ 4 + (-12 : ℂ) * s ^ 3 + (24 : ℂ) * s ^ 3 * r ^ 2 + (-12 : ℂ) * s ^ 3 * r ^ 4 + (-3 : ℂ) * s ^ 4 + (6 : ℂ) * s ^ 4 * r ^ 2 + (-3 : ℂ) * s ^ 4 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1) ^ 2) * A * C := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, vectorJet_quadratic_curvature_0_2_3 hr hy hf, vectorJet_quadratic_curvature_1_2_3 hr hy hf, vectorJet_quadratic_curvature_2_2_3 hr hy hf, vectorJet_quadratic_curvature_3_2_3 hr hy hf]
  field_simp
  ring

/-- Vector–vector quadratic Ricci variation, component `(3, 3)`. -/
theorem vectorJet_quadratic_ricci_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 3 =
      B ^ 2 * ((-2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * Q * y + B ^ 2 * ((-2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * R * y + B ^ 2 * ((-8 : ℂ) * s ^ 2 + (10 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-8 : ℂ) * s ^ 3 + (8 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A ^ 2 + B ^ 2 * ((4 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * P * y + B ^ 2 * ((-3 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (-2 : ℂ) * s ^ 2 * r ^ 6 + (-4 : ℂ) * s ^ 3 + (8 : ℂ) * s ^ 3 * r ^ 2 + (-4 : ℂ) * s ^ 3 * r ^ 4 + (-1 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 4 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1) ^ 2) * C ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * P ^ 2 * y ^ 2 + B ^ 2 * ((-1 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * Q ^ 2 * y ^ 2 + B ^ 2 * ((-1 : ℂ) * s ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * R ^ 2 * y ^ 2 := by
  simp only [Quadratic.ricci, Fin.sum_univ_four, vectorJet_quadratic_curvature_0_3_3 hr hy hf, vectorJet_quadratic_curvature_1_3_3 hr hy hf, vectorJet_quadratic_curvature_2_3_3 hr hy hf, vectorJet_quadratic_curvature_3_3_3 hr hy hf]
  field_simp
  ring

/-- Background trace of the vector–vector quadratic Ricci variation. -/
theorem vectorJet_quadratic_ricci_trace (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    (∑ u, ((D4BMBackground.jet r y).metric u u)⁻¹ *
      Quadratic.ricci (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) u u) =
      B ^ 2 * ((-4 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1)) * A * Q * y ^ 3 + B ^ 2 * ((-4 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1)) * A * R * y ^ 3 + B ^ 2 * ((-7 : ℂ) * s ^ 2 + (14 : ℂ) * s ^ 2 * r ^ 2 + (-7 : ℂ) * s ^ 2 * r ^ 4 + (-10 : ℂ) * s ^ 3 + (20 : ℂ) * s ^ 3 * r ^ 2 + (-10 : ℂ) * s ^ 3 * r ^ 4 + (-3 : ℂ) * s ^ 4 + (6 : ℂ) * s ^ 4 * r ^ 2 + (-3 : ℂ) * s ^ 4 * r ^ 4) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * A ^ 2 * y ^ 2 + B ^ 2 * ((8 : ℂ) * s ^ 2 + (-8 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1)) * C * P * y ^ 3 + B ^ 2 * ((-7 : ℂ) * s ^ 2 + (14 : ℂ) * s ^ 2 * r ^ 2 + (-7 : ℂ) * s ^ 2 * r ^ 4 + (-10 : ℂ) * s ^ 3 + (20 : ℂ) * s ^ 3 * r ^ 2 + (-10 : ℂ) * s ^ 3 * r ^ 4 + (-3 : ℂ) * s ^ 4 + (6 : ℂ) * s ^ 4 * r ^ 2 + (-3 : ℂ) * s ^ 4 * r ^ 4) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * C ^ 2 * y ^ 2 + B ^ 2 * ((-4 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1)) * P ^ 2 * y ^ 4 + B ^ 2 * ((2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1)) * Q * R * y ^ 4 + B ^ 2 * ((-3 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1)) * Q ^ 2 * y ^ 4 + B ^ 2 * ((-3 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1)) * R ^ 2 * y ^ 4 := by
  simp only [Fin.sum_univ_four, vectorJet_quadratic_ricci_0_0 hr hy hf, vectorJet_quadratic_ricci_1_1 hr hy hf,
    vectorJet_quadratic_ricci_2_2 hr hy hf, vectorJet_quadratic_ricci_3_3 hr hy hf,
    D4BMBackground.jet_metric_0_0, D4BMBackground.jet_metric_1_1, D4BMBackground.jet_metric_2_2,
    D4BMBackground.jet_metric_3_3]
  field_simp
  ring

end
end RHTower.D4BMVectorLinearEquation
