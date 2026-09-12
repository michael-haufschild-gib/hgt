import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetEntries
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorJetEntries

/-!
# Christoffel variation table of the fundamental vector jet: spatial0 part

Closed forms of the spatial derivative `Quadratic.connectionSpatial J K 0 u i j` of the quadratic
Christoffel variation (derivative index `0`) for the fundamental vector metric jet over the
Birmingham–Mokhtari background, in every index order (64 entries; vanishing entries recorded), by the
index-collapsed forms over a diagonal background, the entry tables and one power-cancellation pass,
at the default heartbeat limit.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHTower.D4BMVectorLinearEquation
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet D4BMScalarLinearEquation
noncomputable section
variable {s r y B A C P Q R U W : ℂ}

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 0 0 =
      B ^ 2 * ((-4 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 4) / (r ^ 4 * (r ^ 2 - 1)) * A ^ 2 * y ^ 2 + B ^ 2 * ((-4 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 4) / (r ^ 4 * (r ^ 2 - 1)) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 0 1 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-6 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A ^ 2 * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3 + (-6 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 0 2 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 4 * (r ^ 2 - 1)) * C * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 4 * (r ^ 2 - 1)) * C * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 0 3 =
      B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 4 * (r ^ 2 - 1)) * A * Q * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 4 * (r ^ 2 - 1)) * A * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 1 0 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-6 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A ^ 2 * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3 + (-6 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 1 1 =
      B ^ 2 * ((-4 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 4) / (r ^ 4 * (r ^ 2 - 1) ^ 3) * A ^ 2 * y ^ 2 + B ^ 2 * ((-4 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 4) / (r ^ 4 * (r ^ 2 - 1) ^ 3) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 1 2 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * C * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * C * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 1 3 =
      B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * A * Q * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * A * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 2 0 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 4 * (r ^ 2 - 1)) * C * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 4 * (r ^ 2 - 1)) * C * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 2 1 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * C * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * C * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 2 2 =
      B ^ 2 * ((4 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * A ^ 2 + B ^ 2 * ((4 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * C ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 3 0 =
      B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 4 * (r ^ 2 - 1)) * A * Q * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 4 * (r ^ 2 - 1)) * A * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 3 1 =
      B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * A * Q * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * A * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_0_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 0 3 3 =
      B ^ 2 * ((4 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * A ^ 2 + B ^ 2 * ((4 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * C ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 0 0 =
      B ^ 2 * ((4 : ℂ) * s ^ 3 * r ^ 2 + (-4 : ℂ) * s ^ 4) / (r ^ 3) * A ^ 2 * y ^ 2 + B ^ 2 * ((4 : ℂ) * s ^ 3 * r ^ 2 + (-4 : ℂ) * s ^ 4) / (r ^ 3) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 0 1 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A ^ 2 * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 0 2 =
      B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 3) * C * Q * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 3) * C * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 0 3 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 3) * A * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 3) * A * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 1 0 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A ^ 2 * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 1 1 =
      B ^ 2 * ((4 : ℂ) * s ^ 3 * r ^ 2 + (-4 : ℂ) * s ^ 4) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * A ^ 2 * y ^ 2 + B ^ 2 * ((4 : ℂ) * s ^ 3 * r ^ 2 + (-4 : ℂ) * s ^ 4) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 1 2 =
      B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * C * Q * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * C * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 1 3 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * A * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * A * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 2 0 =
      B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 3) * C * Q * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 3) * C * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 2 1 =
      B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * C * Q * y ^ 2 + B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * C * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 2 2 =
      B ^ 2 * ((-4 : ℂ) * s ^ 3) / (r) * A ^ 2 + B ^ 2 * ((-4 : ℂ) * s ^ 3) / (r) * C ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 3 0 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 3) * A * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 3) * A * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 3 1 =
      B ^ 2 * ((-2 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * A * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1)) * A * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_1_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 1 3 3 =
      B ^ 2 * ((-4 : ℂ) * s ^ 3) / (r) * A ^ 2 + B ^ 2 * ((-4 : ℂ) * s ^ 3) / (r) * C ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 0 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 0 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 0 2 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 0 3 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * C * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 1 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 1 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 1 2 =
      B ^ 2 * ((6 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 3 * r ^ 4 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 1 3 =
      B ^ 2 * ((6 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 3 * r ^ 4 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A * C * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 2 0 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 2 1 =
      B ^ 2 * ((6 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 3 * r ^ 4 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 2 2 =
      B ^ 2 * ((-4 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * C * y + B ^ 2 * ((4 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * P * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 2 3 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * R * y ^ 2 + B ^ 2 * ((4 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A ^ 2 * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 3 0 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * C * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 3 1 =
      B ^ 2 * ((6 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 3 * r ^ 4 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A * C * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 3 2 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * R * y ^ 2 + B ^ 2 * ((4 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A ^ 2 * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_2_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 2 3 3 =
      B ^ 2 * ((4 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * C * y + B ^ 2 * ((-4 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * P * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 0 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 0 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 0 2 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * C * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 0 3 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 1 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 1 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try ring_nf)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 1 2 =
      B ^ 2 * ((6 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 3 * r ^ 4 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A * C * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 1 3 =
      B ^ 2 * ((6 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 3 * r ^ 4 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 2 0 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * C * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 2 1 =
      B ^ 2 * ((6 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 3 * r ^ 4 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * A * C * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 2 2 =
      B ^ 2 * ((4 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * P * y ^ 2 + B ^ 2 * ((-4 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C ^ 2 * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 2 3 =
      B ^ 2 * ((4 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * C * y + B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 3 0 =
      B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 3 1 =
      B ^ 2 * ((6 : ℂ) * s ^ 3 + (-10 : ℂ) * s ^ 3 * r ^ 2 + (4 : ℂ) * s ^ 3 * r ^ 4 + (2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 4 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * C ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 3 2 =
      B ^ 2 * ((4 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * A * C * y + B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * Q * y ^ 2 + B ^ 2 * ((2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * R * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmVectorTable] theorem vectorJet_quadConnectionSpatial_0_3_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (vectorJet s r y B A C P Q R U W) 0 3 3 3 =
      B ^ 2 * ((-4 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C * P * y ^ 2 + B ^ 2 * ((4 : ℂ) * s ^ 3 + (-4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1)) * C ^ 2 * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, bmVectorEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

end
end RHTower.D4BMVectorLinearEquation
