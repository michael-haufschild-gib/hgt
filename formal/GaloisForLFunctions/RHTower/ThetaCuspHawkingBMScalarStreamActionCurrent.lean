import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMActionSymplecticForm
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamEntries
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetEntries

/-!
# The Einstein action symplectic current between two Kodama–Ishibashi scalar streams

All four components of the volume-weighted Einstein symplectic current `actionSymplectic J H K a`
between two scalar-stream metric jets over the Birmingham–Mokhtari background (rates `w`, `v`, free
radial jets `F0, F1, F2, H` and `G0, G1, G2, L`, free angular jets `P`, `Q`), in closed form: a
bilinear expression in the two first jets with rational coefficients in `r`, at the default
heartbeat limit through the diagonal collapse of the symplectic form. The radial component is the
boundary current whose horizon and boundary values enter the integrated `++−` coefficient of the
scalar–scalar sector; no second jet enters any component.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet D4BMScalarLinearEquation
open RHTower.D4BMMixedActionCurrent RHTower.D4BMActionSymplecticForm
noncomputable section
variable {w v r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy G0 G01 G02 G1 G11 G12 G2 G21 G22 L L1 L2 Q Qx Qy Qxx Qxy Qyy : ℂ}

/-- The temporal component of the symplectic current between two scalar streams. -/
theorem streamCurrent_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (metricJet v r y G0 G01 G02 G1 G11 G12 G2 G21 G22 L L1 L2 Q Qx Qy Qxx Qxy Qyy) 0 =
      ((-1 : ℂ)) / (r * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * F0 * G1 * P * Q + ((1 / 2 : ℂ)) / ((r ^ (2 : ℕ) - 1)) * F0 * G11 * P * Q + ((1 / 2 : ℂ)) / ((r ^ (2 : ℕ) - 1)) * F01 * G1 * P * Q + ((1 : ℂ)) / (r * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * F1 * G0 * P * Q + ((-1 / 2 : ℂ)) / ((r ^ (2 : ℕ) - 1)) * F1 * G01 * P * Q + ((-1 : ℂ)) / (r) * F1 * G2 * P * Q + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ (2 : ℕ)) * F1 * G21 * P * Q + ((4 : ℂ) * r) / ((r ^ (2 : ℕ) - 1)) * F1 * L * P * Q + ((-2 : ℂ)) * F1 * L1 * P * Q + ((-1 / 2 : ℂ)) / ((r ^ (2 : ℕ) - 1)) * F11 * G0 * P * Q + ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ (2 : ℕ)) * F11 * G2 * P * Q + ((2 : ℂ)) * F11 * L * P * Q + ((1 : ℂ)) / (r) * F2 * G1 * P * Q + ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ (2 : ℕ)) * F2 * G11 * P * Q + ((2 : ℂ) * v + (-2 : ℂ) * w) * F2 * L * P * Q + ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ (2 : ℕ)) * F21 * G1 * P * Q + ((-4 : ℂ) * r) / ((r ^ (2 : ℕ) - 1)) * G1 * H * P * Q + ((2 : ℂ)) * G1 * H1 * P * Q + ((-2 : ℂ)) * G11 * H * P * Q + ((2 : ℂ) * v + (-2 : ℂ) * w) * G2 * H * P * Q + ((4 : ℂ) * v + (-4 : ℂ) * w) / ((r ^ (2 : ℕ) - 1)) * H * L * P * Q := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  have hdet : (D4BMBackground.jet r y).metric.det ≠ 0 := by
    change (D4BMBackground.metric r y).det ≠ 0
    rw [D4BMBackground.metric_det r y hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ (inv_ne_zero hy)))
  rw [actionSymplectic_eq_form _ _ _ hdet]
  simp only [weightedInverse_apply_of_diagonal hd, hd.linearization_connection_eq]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  field_simp
  ring

/-- The radial component of the symplectic current between two scalar streams. -/
theorem streamCurrent_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (metricJet v r y G0 G01 G02 G1 G11 G12 G2 G21 G22 L L1 L2 Q Qx Qy Qxx Qxy Qyy) 1 =
      ((-1 / 2 : ℂ) * v + (-1 / 2 : ℂ) * w) / ((r ^ (2 : ℕ) - 1)) * F0 * G1 * P * Q + ((1 : ℂ) + (-1 : ℂ) * r ^ (2 : ℕ)) / (r) * F0 * G2 * P * Q + ((-2 : ℂ) + (4 : ℂ) * r ^ (2 : ℕ)) / (r * (r ^ (2 : ℕ) - 1)) * F0 * L * P * Q + ((2 : ℂ)) * F0 * L1 * P * Q + ((-2 : ℂ)) * F01 * L * P * Q + ((1 / 2 : ℂ) * v + (1 / 2 : ℂ) * w) / ((r ^ (2 : ℕ) - 1)) * F1 * G0 * P * Q + ((-1 / 2 : ℂ) * v + (1 / 2 : ℂ) * v * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * w + (1 / 2 : ℂ) * w * r ^ (2 : ℕ)) * F1 * G2 * P * Q + ((-2 : ℂ) * v + (2 : ℂ) * w) * F1 * L * P * Q + ((-1 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r) * F2 * G0 * P * Q + ((1 / 2 : ℂ) * v + (-1 / 2 : ℂ) * v * r ^ (2 : ℕ) + (1 / 2 : ℂ) * w + (-1 / 2 : ℂ) * w * r ^ (2 : ℕ)) * F2 * G1 * P * Q + ((-2 : ℂ) + (6 : ℂ) * r ^ (2 : ℕ) + (-4 : ℂ) * r ^ (4 : ℕ)) / (r) * F2 * L * P * Q + ((2 : ℂ) + (-4 : ℂ) * r ^ (2 : ℕ)) / (r * (r ^ (2 : ℕ) - 1)) * G0 * H * P * Q + ((-2 : ℂ)) * G0 * H1 * P * Q + ((2 : ℂ)) * G01 * H * P * Q + ((-2 : ℂ) * v + (2 : ℂ) * w) * G1 * H * P * Q + ((2 : ℂ) + (-6 : ℂ) * r ^ (2 : ℕ) + (4 : ℂ) * r ^ (4 : ℕ)) / (r) * G2 * H * P * Q + ((4 : ℂ) + (-4 : ℂ) * r ^ (2 : ℕ)) * H * L1 * P * Q + ((-4 : ℂ) + (4 : ℂ) * r ^ (2 : ℕ)) * H1 * L * P * Q := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  have hdet : (D4BMBackground.jet r y).metric.det ≠ 0 := by
    change (D4BMBackground.metric r y).det ≠ 0
    rw [D4BMBackground.metric_det r y hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ (inv_ne_zero hy)))
  rw [actionSymplectic_eq_form _ _ _ hdet]
  simp only [weightedInverse_apply_of_diagonal hd, hd.linearization_connection_eq]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  field_simp
  ring

/-- The angularX component of the symplectic current between two scalar streams. -/
theorem streamCurrent_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (metricJet v r y G0 G01 G02 G1 G11 G12 G2 G21 G22 L L1 L2 Q Qx Qy Qxx Qxy Qyy) 2 =
      ((1 / 2 : ℂ)) / (r ^ (2 : ℕ)) * F0 * G2 * P * Qx * y ^ (2 : ℕ) + ((-1 / 2 : ℂ)) / (r ^ (2 : ℕ)) * F0 * G2 * Px * Q * y ^ (2 : ℕ) + ((1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * F0 * L * P * Qx * y ^ (2 : ℕ) + ((-1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * F0 * L * Px * Q * y ^ (2 : ℕ) + ((-1 : ℂ)) / (r ^ (2 : ℕ)) * F1 * G1 * P * Qx * y ^ (2 : ℕ) + ((1 : ℂ)) / (r ^ (2 : ℕ)) * F1 * G1 * Px * Q * y ^ (2 : ℕ) + ((1 / 2 : ℂ)) / (r ^ (2 : ℕ)) * F2 * G0 * P * Qx * y ^ (2 : ℕ) + ((-1 / 2 : ℂ)) / (r ^ (2 : ℕ)) * F2 * G0 * Px * Q * y ^ (2 : ℕ) + ((1 : ℂ) + (-1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * F2 * L * P * Qx * y ^ (2 : ℕ) + ((-1 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * F2 * L * Px * Q * y ^ (2 : ℕ) + ((1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G0 * H * P * Qx * y ^ (2 : ℕ) + ((-1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G0 * H * Px * Q * y ^ (2 : ℕ) + ((1 : ℂ) + (-1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G2 * H * P * Qx * y ^ (2 : ℕ) + ((-1 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G2 * H * Px * Q * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  have hdet : (D4BMBackground.jet r y).metric.det ≠ 0 := by
    change (D4BMBackground.metric r y).det ≠ 0
    rw [D4BMBackground.metric_det r y hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ (inv_ne_zero hy)))
  rw [actionSymplectic_eq_form _ _ _ hdet]
  simp only [weightedInverse_apply_of_diagonal hd, hd.linearization_connection_eq]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  field_simp
  ring

/-- The angularY component of the symplectic current between two scalar streams. -/
theorem streamCurrent_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    actionSymplectic (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (metricJet v r y G0 G01 G02 G1 G11 G12 G2 G21 G22 L L1 L2 Q Qx Qy Qxx Qxy Qyy) 3 =
      ((1 / 2 : ℂ)) / (r ^ (2 : ℕ)) * F0 * G2 * P * Qy * y ^ (2 : ℕ) + ((-1 / 2 : ℂ)) / (r ^ (2 : ℕ)) * F0 * G2 * Py * Q * y ^ (2 : ℕ) + ((1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * F0 * L * P * Qy * y ^ (2 : ℕ) + ((-1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * F0 * L * Py * Q * y ^ (2 : ℕ) + ((-1 : ℂ)) / (r ^ (2 : ℕ)) * F1 * G1 * P * Qy * y ^ (2 : ℕ) + ((1 : ℂ)) / (r ^ (2 : ℕ)) * F1 * G1 * Py * Q * y ^ (2 : ℕ) + ((1 / 2 : ℂ)) / (r ^ (2 : ℕ)) * F2 * G0 * P * Qy * y ^ (2 : ℕ) + ((-1 / 2 : ℂ)) / (r ^ (2 : ℕ)) * F2 * G0 * Py * Q * y ^ (2 : ℕ) + ((1 : ℂ) + (-1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * F2 * L * P * Qy * y ^ (2 : ℕ) + ((-1 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * F2 * L * Py * Q * y ^ (2 : ℕ) + ((1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G0 * H * P * Qy * y ^ (2 : ℕ) + ((-1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G0 * H * Py * Q * y ^ (2 : ℕ) + ((1 : ℂ) + (-1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G2 * H * P * Qy * y ^ (2 : ℕ) + ((-1 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G2 * H * Py * Q * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  have hdet : (D4BMBackground.jet r y).metric.det ≠ 0 := by
    change (D4BMBackground.metric r y).det ≠ 0
    rw [D4BMBackground.metric_det r y hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ (inv_ne_zero hy)))
  rw [actionSymplectic_eq_form _ _ _ hdet]
  simp only [weightedInverse_apply_of_diagonal hd, hd.linearization_connection_eq]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  field_simp
  ring

end
end RHTower.D4BMScalarStream
