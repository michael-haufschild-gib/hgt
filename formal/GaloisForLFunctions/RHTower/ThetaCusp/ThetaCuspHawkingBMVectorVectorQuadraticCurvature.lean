import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorJetLinearConnectionTable
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorJetQuadraticConnectionTable
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorJetSpatial0ConnectionTable
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorJetSpatial1ConnectionTable
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorJetSpatial2ConnectionTable
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorJetSpatial3ConnectionTable

/-!
# The vector–vector quadratic Riemann traces of the fundamental Birmingham–Mokhtari vector jet

Every Riemann trace `Quadratic.curvature J K u i u j` of the quadratic curvature variation of the
fundamental vector metric jet `K = vectorJet s r y B A C P Q R U W` over the Birmingham–Mokhtari
background `J` is evaluated in closed form: a rational function of `(s, r)` times a quadratic
monomial in the covector jet `(A, C, P, Q, R, U, W)` times a power of `y`, summed over at most a
few such terms. The proofs assemble the Christoffel variation tables through the index-collapsed
Riemann formula over a diagonal background and one power-cancellation pass; no summand is expanded
through the jet algebra and no heartbeat limit is raised. These traces are the input of the
vector–vector block of the `++` quadratic source of route HB.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHTower.D4BMVectorLinearEquation
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet D4BMScalarLinearEquation
noncomputable section
variable {s r y B A C P Q R U W : ℂ}

/-- Vector–vector quadratic Riemann trace, indices `(0, 0, 0, 0)`. -/
theorem vectorJet_quadratic_curvature_0_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 0 0 =
      0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ (2 : ℕ) - 1 = F)
  all_goals (try ring_nf)

/-- Vector–vector quadratic Riemann trace, indices `(0, 0, 0, 1)`. -/
theorem vectorJet_quadratic_curvature_0_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 0 1 =
      B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(0, 0, 0, 2)`. -/
theorem vectorJet_quadratic_curvature_0_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 0 2 =
      B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * R * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(0, 0, 0, 3)`. -/
theorem vectorJet_quadratic_curvature_0_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 0 3 =
      B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) * y + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(0, 1, 0, 1)`. -/
theorem vectorJet_quadratic_curvature_0_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 0 1 =
      B ^ (2 : ℕ) * ((-7 / 2 : ℂ) * s ^ (2 : ℕ) + (9 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-15 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ) + (7 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-7 / 2 : ℂ) * s ^ (2 : ℕ) + (9 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-15 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ) + (7 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(0, 1, 0, 2)`. -/
theorem vectorJet_quadratic_curvature_0_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 0 2 =
      B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-5 / 2 : ℂ) * s ^ (2 : ℕ) + (9 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * R * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(0, 1, 0, 3)`. -/
theorem vectorJet_quadratic_curvature_0_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 0 3 =
      B ^ (2 : ℕ) * ((-5 / 2 : ℂ) * s ^ (2 : ℕ) + (9 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) * y + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(0, 2, 0, 2)`. -/
theorem vectorJet_quadratic_curvature_0_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 0 2 =
      B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (7 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(0, 2, 0, 3)`. -/
theorem vectorJet_quadratic_curvature_0_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 0 3 =
      B ^ (2 : ℕ) * ((-7 / 2 : ℂ) * s ^ (2 : ℕ) + (5 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ) + (7 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * C := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(0, 3, 0, 3)`. -/
theorem vectorJet_quadratic_curvature_0_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 0 3 =
      B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) + (3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (7 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(1, 0, 1, 0)`. -/
theorem vectorJet_quadratic_curvature_1_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 0 1 0 =
      B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (9 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (9 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(1, 0, 1, 1)`. -/
theorem vectorJet_quadratic_curvature_1_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 0 1 1 =
      0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ (2 : ℕ) - 1 = F)
  all_goals (try ring_nf)

/-- Vector–vector quadratic Riemann trace, indices `(1, 0, 1, 2)`. -/
theorem vectorJet_quadratic_curvature_1_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 0 1 2 =
      B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-5 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * R * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(1, 0, 1, 3)`. -/
theorem vectorJet_quadratic_curvature_1_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 0 1 3 =
      B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-5 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) * y + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(1, 1, 1, 1)`. -/
theorem vectorJet_quadratic_curvature_1_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 1 1 1 =
      0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ (2 : ℕ) - 1 = F)
  all_goals (try ring_nf)

/-- Vector–vector quadratic Riemann trace, indices `(1, 1, 1, 2)`. -/
theorem vectorJet_quadratic_curvature_1_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 1 1 2 =
      B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ)) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ)) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * R * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(1, 1, 1, 3)`. -/
theorem vectorJet_quadratic_curvature_1_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 1 1 3 =
      B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ)) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ)) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) * y + B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(1, 2, 1, 2)`. -/
theorem vectorJet_quadratic_curvature_1_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 2 1 2 =
      B ^ (2 : ℕ) * ((-9 / 2 : ℂ) * s ^ (2 : ℕ) + (11 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-17 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (8 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) + B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(1, 2, 1, 3)`. -/
theorem vectorJet_quadratic_curvature_1_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 2 1 3 =
      B ^ (2 : ℕ) * ((-9 / 2 : ℂ) * s ^ (2 : ℕ) + (11 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-13 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (9 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * C := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(1, 3, 1, 3)`. -/
theorem vectorJet_quadratic_curvature_1_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 1 3 1 3 =
      B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-9 / 2 : ℂ) * s ^ (2 : ℕ) + (11 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-17 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) + (8 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-5 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(2, 0, 2, 0)`. -/
theorem vectorJet_quadratic_curvature_2_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 0 2 0 =
      B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-7 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Q * R * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Q ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * R ^ (2 : ℕ) * y ^ (4 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(2, 0, 2, 1)`. -/
theorem vectorJet_quadratic_curvature_2_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 0 2 1 =
      B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) + (7 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (4 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(2, 0, 2, 2)`. -/
theorem vectorJet_quadratic_curvature_2_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 0 2 2 =
      0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ (2 : ℕ) - 1 = F)
  all_goals (try ring_nf)

/-- Vector–vector quadratic Riemann trace, indices `(2, 0, 2, 3)`. -/
theorem vectorJet_quadratic_curvature_2_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 0 2 3 =
      B ^ (2 : ℕ) * ((-5 / 2 : ℂ) * s ^ (2 : ℕ) + (5 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) * y + B ^ (2 : ℕ) * ((1 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(2, 1, 2, 1)`. -/
theorem vectorJet_quadratic_curvature_2_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 1 2 1 =
      B ^ (2 : ℕ) * ((-15 / 2 : ℂ) * s ^ (2 : ℕ) + (17 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-23 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-7 : ℂ) * s ^ (3 : ℕ) + (13 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * Q * R * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * Q ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * R ^ (2 : ℕ) * y ^ (4 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(2, 1, 2, 2)`. -/
theorem vectorJet_quadratic_curvature_2_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 1 2 2 =
      0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ (2 : ℕ) - 1 = F)
  all_goals (try ring_nf)

/-- Vector–vector quadratic Riemann trace, indices `(2, 1, 2, 3)`. -/
theorem vectorJet_quadratic_curvature_2_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 1 2 3 =
      B ^ (2 : ℕ) * ((-9 / 2 : ℂ) * s ^ (2 : ℕ) + (13 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (2 : ℕ) + (5 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) * y + B ^ (2 : ℕ) * ((3 : ℂ) * s ^ (2 : ℕ) + (-5 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (2 : ℕ) + (5 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(2, 2, 2, 2)`. -/
theorem vectorJet_quadratic_curvature_2_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 2 2 2 =
      0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ (2 : ℕ) - 1 = F)
  all_goals (try ring_nf)

/-- Vector–vector quadratic Riemann trace, indices `(2, 2, 2, 3)`. -/
theorem vectorJet_quadratic_curvature_2_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 2 2 3 =
      B ^ (2 : ℕ) * ((3 : ℂ) * s ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * C := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(2, 3, 2, 3)`. -/
theorem vectorJet_quadratic_curvature_2_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 2 3 2 3 =
      B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * Q * y + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * R * y + B ^ (2 : ℕ) * ((-5 : ℂ) * s ^ (2 : ℕ) + (7 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) + B ^ (2 : ℕ) * ((4 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * P * y + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * P ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(3, 0, 3, 0)`. -/
theorem vectorJet_quadratic_curvature_3_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 0 3 0 =
      B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-7 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Q * R * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * Q ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * R ^ (2 : ℕ) * y ^ (4 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(3, 0, 3, 1)`. -/
theorem vectorJet_quadratic_curvature_3_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 0 3 1 =
      B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (2 : ℕ) + (6 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) + (7 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (4 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(3, 0, 3, 2)`. -/
theorem vectorJet_quadratic_curvature_3_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 0 3 2 =
      B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-5 / 2 : ℂ) * s ^ (2 : ℕ) + (5 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * R * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(3, 0, 3, 3)`. -/
theorem vectorJet_quadratic_curvature_3_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 0 3 3 =
      0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ (2 : ℕ) - 1 = F)
  all_goals (try ring_nf)

/-- Vector–vector quadratic Riemann trace, indices `(3, 1, 3, 1)`. -/
theorem vectorJet_quadratic_curvature_3_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 1 3 1 =
      B ^ (2 : ℕ) * ((2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-15 / 2 : ℂ) * s ^ (2 : ℕ) + (17 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-23 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (6 : ℕ) + (-7 : ℂ) * s ^ (3 : ℕ) + (13 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)) * C ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * Q * R * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * Q ^ (2 : ℕ) * y ^ (4 : ℕ) + B ^ (2 : ℕ) * ((1 / 2 : ℂ) * s ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * R ^ (2 : ℕ) * y ^ (4 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(3, 1, 3, 2)`. -/
theorem vectorJet_quadratic_curvature_3_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 1 3 2 =
      B ^ (2 : ℕ) * ((-3 : ℂ) * s ^ (2 : ℕ) + (5 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * A * P * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((3 / 2 : ℂ) * s ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * Q * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-9 / 2 : ℂ) * s ^ (2 : ℕ) + (13 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-3 / 2 : ℂ) * s ^ (3 : ℕ) + (3 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * C * R * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(3, 1, 3, 3)`. -/
theorem vectorJet_quadratic_curvature_3_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 1 3 3 =
      0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ (2 : ℕ) - 1 = F)
  all_goals (try ring_nf)

/-- Vector–vector quadratic Riemann trace, indices `(3, 2, 3, 2)`. -/
theorem vectorJet_quadratic_curvature_3_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 2 3 2 =
      B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * Q * y + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A * R * y + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * A ^ (2 : ℕ) + B ^ (2 : ℕ) * ((4 : ℂ) * s ^ (2 : ℕ) + (-4 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C * P * y + B ^ (2 : ℕ) * ((-5 : ℂ) * s ^ (2 : ℕ) + (7 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) + (4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * C ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-2 : ℂ) * s ^ (2 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * P ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 : ℂ) * s ^ (2 : ℕ) + (1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q * R * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * Q ^ (2 : ℕ) * y ^ (2 : ℕ) + B ^ (2 : ℕ) * ((-1 / 2 : ℂ) * s ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * R ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (5 : ℕ) * y⁻¹ * F ^ (6 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

/-- Vector–vector quadratic Riemann trace, indices `(3, 2, 3, 3)`. -/
theorem vectorJet_quadratic_curvature_3_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 2 3 3 =
      0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ (2 : ℕ) - 1 = F)
  all_goals (try ring_nf)

/-- Vector–vector quadratic Riemann trace, indices `(3, 3, 3, 3)`. -/
theorem vectorJet_quadratic_curvature_3_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.curvature (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 3 3 3 3 =
      0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_curvature_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetTable, bmVectorTable, bmJetEntry, bmVectorEntry, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ (2 : ℕ) - 1 = F)
  all_goals (try ring_nf)

end
end RHTower.D4BMVectorLinearEquation
