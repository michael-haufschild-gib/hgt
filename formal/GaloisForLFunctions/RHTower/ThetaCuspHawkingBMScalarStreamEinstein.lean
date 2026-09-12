import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamEntries
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetEntries

/-!
# The linearized cosmological Einstein operator on the scalar-stream jet

All sixteen components of the linearized Ricci variation, the linearized scalar variation, and the
ten components of the linearized cosmological Einstein operator `Linearization.cosmological J K (-3)`
of the Kodama–Ishibashi-gauge scalar-stream jet over the Birmingham–Mokhtari background, in closed
form: each is linear in the free radial jets `F0, F1, F2, H` and their derivatives and linear in the
free angular jet `Ψ`. No angular eigen-equation or radial field equation is imposed. This is the
scalar-sector analogue of the vector master curl and the operator the scalar–scalar `++` source is
matched against; the trace-free angular components are `½ (F0/(r²−1) − (r²−1) F2)` times the
covariant Hessian of `Ψ`, the standard Kodama–Ishibashi algebraic relation.
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet D4BMScalarLinearEquation
noncomputable section
variable {w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy : ℂ}

@[bmStreamTable] theorem metricJet_linRicci_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 0 0 =
      ((-1 : ℂ) * r ^ 2) / ((r ^ 2 - 1)) * F0 * P +
        ((-1 / 2 : ℂ)) / (r ^ 2) * F0 * Pxx * y ^ 2 +
        ((-1 / 2 : ℂ)) / (r ^ 2) * F0 * Pyy * y ^ 2 +
        ((1 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) / (r) * F01 * P +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F02 * P +
        ((-2 : ℂ) + (3 : ℂ) * r ^ 2) / (r) * F1 * P * w +
        ((-1 : ℂ) + (1 : ℂ) * r ^ 2) * F11 * P * w +
        ((-3 : ℂ) + (7 : ℂ) * r ^ 2 + (-4 : ℂ) * r ^ 4) * F2 * P +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * P * w ^ 2 +
        ((-1 / 2 : ℂ) * r + (1 : ℂ) * r ^ 3 + (-1 / 2 : ℂ) * r ^ 5) * F21 * P +
        ((-2 : ℂ)) * H * P * w ^ 2 +
        ((-2 : ℂ) * r + (2 : ℂ) * r ^ 3) * H1 * P := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 0 1 =
      ((-3 : ℂ)) * F1 * P +
        ((-1 / 2 : ℂ)) / (r ^ 2) * F1 * Pxx * y ^ 2 +
        ((-1 / 2 : ℂ)) / (r ^ 2) * F1 * Pyy * y ^ 2 +
        ((-1 : ℂ) + (1 : ℂ) * r ^ 2) / (r) * F2 * P * w +
        ((2 : ℂ)) / (r * (r ^ 2 - 1)) * H * P * w +
        ((-2 : ℂ)) * H1 * P * w := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 0 2 =
      ((1 : ℂ) * r) * F1 * Px +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F11 * Px +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Px * w +
        ((-1 : ℂ)) * H * Px * w := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 0 3 =
      ((1 : ℂ) * r) * F1 * Py +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F11 * Py +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Py * w +
        ((-1 : ℂ)) * H * Py * w := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 1 0 =
      ((-3 : ℂ)) * F1 * P +
        ((-1 / 2 : ℂ)) / (r ^ 2) * F1 * Pxx * y ^ 2 +
        ((-1 / 2 : ℂ)) / (r ^ 2) * F1 * Pyy * y ^ 2 +
        ((-1 : ℂ) + (1 : ℂ) * r ^ 2) / (r) * F2 * P * w +
        ((2 : ℂ)) / (r * (r ^ 2 - 1)) * H * P * w +
        ((-2 : ℂ)) * H1 * P * w := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 1 1 =
      ((1 : ℂ)) / ((r ^ 2 - 1) ^ 3) * F0 * P +
        ((-1 / 2 : ℂ) * r) / ((r ^ 2 - 1) ^ 2) * F01 * P +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F02 * P +
        ((-1 : ℂ) * r) / ((r ^ 2 - 1) ^ 2) * F1 * P * w +
        ((-1 : ℂ)) / ((r ^ 2 - 1)) * F11 * P * w +
        ((-2 : ℂ) + (3 : ℂ) * r ^ 2) / ((r ^ 2 - 1)) * F2 * P +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F2 * P * w ^ 2 +
        ((-1 / 2 : ℂ)) / (r ^ 2) * F2 * Pxx * y ^ 2 +
        ((-1 / 2 : ℂ)) / (r ^ 2) * F2 * Pyy * y ^ 2 +
        ((-1 : ℂ) + (3 / 2 : ℂ) * r ^ 2) / (r) * F21 * P +
        ((4 : ℂ) + (-6 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1)) * H1 * P +
        ((-2 : ℂ)) * H2 * P := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 1 2 =
      ((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2) * F0 * Px +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F01 * Px +
        ((-1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F1 * Px * w +
        ((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r) * F2 * Px +
        ((-1 : ℂ)) * H1 * Px := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 1 3 =
      ((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2) * F0 * Py +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F01 * Py +
        ((-1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F1 * Py * w +
        ((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r) * F2 * Py +
        ((-1 : ℂ)) * H1 * Py := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 2 0 =
      ((1 : ℂ) * r) * F1 * Px +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F11 * Px +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Px * w +
        ((-1 : ℂ)) * H * Px * w := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 2 1 =
      ((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2) * F0 * Px +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F01 * Px +
        ((-1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F1 * Px * w +
        ((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r) * F2 * Px +
        ((-1 : ℂ)) * H1 * Px := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 2 2 =
      ((-1 : ℂ) * r ^ 2) / ((r ^ 2 - 1)) * F0 * P * y⁻¹ ^ 2 +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Pxx +
        ((-1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Py * y⁻¹ +
        ((1 / 2 : ℂ) * r) * F01 * P * y⁻¹ ^ 2 +
        ((-1 : ℂ) * r) * F1 * P * w * y⁻¹ ^ 2 +
        ((1 : ℂ) + (-5 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 4) * F2 * P * y⁻¹ ^ 2 +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Pxx +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F2 * Py * y⁻¹ +
        ((1 / 2 : ℂ) * r + (-1 : ℂ) * r ^ 3 + (1 / 2 : ℂ) * r ^ 5) * F21 * P * y⁻¹ ^ 2 +
        ((2 : ℂ) + (-6 : ℂ) * r ^ 2) * H * P * y⁻¹ ^ 2 +
        ((1 : ℂ) * r ^ 2) / ((r ^ 2 - 1)) * H * P * w ^ 2 * y⁻¹ ^ 2 +
        ((-1 : ℂ)) * H * Pxx +
        ((-1 : ℂ)) * H * Pyy +
        ((4 : ℂ) * r + (-6 : ℂ) * r ^ 3) * H1 * P * y⁻¹ ^ 2 +
        ((1 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 4) * H2 * P * y⁻¹ ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 2 3 =
      ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Px * y⁻¹ +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Pxy +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Px * y⁻¹ +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Pxy := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 3 0 =
      ((1 : ℂ) * r) * F1 * Py +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F11 * Py +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Py * w +
        ((-1 : ℂ)) * H * Py * w := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 3 1 =
      ((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2) * F0 * Py +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F01 * Py +
        ((-1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F1 * Py * w +
        ((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r) * F2 * Py +
        ((-1 : ℂ)) * H1 * Py := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 3 2 =
      ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Px * y⁻¹ +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Pxy +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Px * y⁻¹ +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Pxy := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem metricJet_linRicci_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) 3 3 =
      ((-1 : ℂ) * r ^ 2) / ((r ^ 2 - 1)) * F0 * P * y⁻¹ ^ 2 +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Py * y⁻¹ +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Pyy +
        ((1 / 2 : ℂ) * r) * F01 * P * y⁻¹ ^ 2 +
        ((-1 : ℂ) * r) * F1 * P * w * y⁻¹ ^ 2 +
        ((1 : ℂ) + (-5 : ℂ) * r ^ 2 + (4 : ℂ) * r ^ 4) * F2 * P * y⁻¹ ^ 2 +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Py * y⁻¹ +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Pyy +
        ((1 / 2 : ℂ) * r + (-1 : ℂ) * r ^ 3 + (1 / 2 : ℂ) * r ^ 5) * F21 * P * y⁻¹ ^ 2 +
        ((2 : ℂ) + (-6 : ℂ) * r ^ 2) * H * P * y⁻¹ ^ 2 +
        ((1 : ℂ) * r ^ 2) / ((r ^ 2 - 1)) * H * P * w ^ 2 * y⁻¹ ^ 2 +
        ((-1 : ℂ)) * H * Pxx +
        ((-1 : ℂ)) * H * Pyy +
        ((4 : ℂ) * r + (-6 : ℂ) * r ^ 3) * H1 * P * y⁻¹ ^ 2 +
        ((1 : ℂ) * r ^ 2 + (-1 : ℂ) * r ^ 4) * H2 * P * y⁻¹ ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 7 * y⁻¹ * F ^ 7 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

/-- Linearized scalar variation of the scalar-stream jet. -/
theorem metricJet_linScalar (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.scalar (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) =
      ((6 : ℂ) + (-4 : ℂ) * r ^ 2) / ((r ^ 2 - 1) ^ 2) * F0 * P +
        ((1 : ℂ)) / (r ^ 2 * (r ^ 2 - 1)) * F0 * Pxx * y ^ 2 +
        ((1 : ℂ)) / (r ^ 2 * (r ^ 2 - 1)) * F0 * Pyy * y ^ 2 +
        ((-2 : ℂ) + (1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1)) * F01 * P +
        ((1 : ℂ)) * F02 * P +
        ((4 : ℂ) + (-6 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1)) * F1 * P * w +
        ((-2 : ℂ)) * F11 * P * w +
        ((2 : ℂ) + (-18 : ℂ) * r ^ 2 + (18 : ℂ) * r ^ 4) / (r ^ 2) * F2 * P +
        ((1 : ℂ)) * F2 * P * w ^ 2 +
        ((1 : ℂ) + (-1 : ℂ) * r ^ 2) / (r ^ 2) * F2 * Pxx * y ^ 2 +
        ((1 : ℂ) + (-1 : ℂ) * r ^ 2) / (r ^ 2) * F2 * Pyy * y ^ 2 +
        ((2 : ℂ) + (-5 : ℂ) * r ^ 2 + (3 : ℂ) * r ^ 4) / (r) * F21 * P +
        ((4 : ℂ)) / (r ^ 2) * H * P +
        ((4 : ℂ)) / ((r ^ 2 - 1)) * H * P * w ^ 2 +
        ((-2 : ℂ)) / (r ^ 2) * H * Pxx * y ^ 2 +
        ((-2 : ℂ)) / (r ^ 2) * H * Pyy * y ^ 2 +
        ((12 : ℂ) + (-20 : ℂ) * r ^ 2) / (r) * H1 * P +
        ((4 : ℂ) + (-4 : ℂ) * r ^ 2) * H2 * P := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.scalar, Fin.sum_univ_four, metricJet_linRicci_0_0 hr hy hf, metricJet_linRicci_0_1 hr hy hf, metricJet_linRicci_0_2 hr hy hf, metricJet_linRicci_0_3 hr hy hf, metricJet_linRicci_1_0 hr hy hf, metricJet_linRicci_1_1 hr hy hf, metricJet_linRicci_1_2 hr hy hf, metricJet_linRicci_1_3 hr hy hf, metricJet_linRicci_2_0 hr hy hf, metricJet_linRicci_2_1 hr hy hf, metricJet_linRicci_2_2 hr hy hf, metricJet_linRicci_2_3 hr hy hf, metricJet_linRicci_3_0 hr hy hf, metricJet_linRicci_3_1 hr hy hf, metricJet_linRicci_3_2 hr hy hf, metricJet_linRicci_3_3 hr hy hf, hd.linearization_inverse_apply,
    hd.inv_apply, D4BMBackground.jet_ricci r y hr hy hf, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.metric, Matrix.diagonal_apply,
    Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the scalar-stream jet, component `(0, 0)`. -/
theorem metricJet_cosmological_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 0 0 =
      ((-1 : ℂ) + (7 : ℂ) * r ^ 2 + (-11 : ℂ) * r ^ 4 + (5 : ℂ) * r ^ 6) / (r ^ 2) * F2 * P +
        ((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2 + (-1 / 2 : ℂ) * r ^ 4) / (r ^ 2) * F2 * Pxx * y ^ 2 +
        ((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2 + (-1 / 2 : ℂ) * r ^ 4) / (r ^ 2) * F2 * Pyy * y ^ 2 +
        ((-1 : ℂ) + (3 : ℂ) * r ^ 2 + (-3 : ℂ) * r ^ 4 + (1 : ℂ) * r ^ 6) / (r) * F21 * P +
        ((-2 : ℂ) + (2 : ℂ) * r ^ 2) / (r ^ 2) * H * P +
        ((1 : ℂ) + (-1 : ℂ) * r ^ 2) / (r ^ 2) * H * Pxx * y ^ 2 +
        ((1 : ℂ) + (-1 : ℂ) * r ^ 2) / (r ^ 2) * H * Pyy * y ^ 2 +
        ((-6 : ℂ) + (14 : ℂ) * r ^ 2 + (-8 : ℂ) * r ^ 4) / (r) * H1 * P +
        ((-2 : ℂ) + (4 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4) * H2 * P := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_0_0 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the scalar-stream jet, component `(0, 1)`. -/
theorem metricJet_cosmological_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 0 1 =
      ((-1 / 2 : ℂ)) / (r ^ 2) * F1 * Pxx * y ^ 2 +
        ((-1 / 2 : ℂ)) / (r ^ 2) * F1 * Pyy * y ^ 2 +
        ((-1 : ℂ) + (1 : ℂ) * r ^ 2) / (r) * F2 * P * w +
        ((2 : ℂ)) / (r * (r ^ 2 - 1)) * H * P * w +
        ((-2 : ℂ)) * H1 * P * w := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_0_1 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the scalar-stream jet, component `(0, 2)`. -/
theorem metricJet_cosmological_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 0 2 =
      ((1 : ℂ) * r) * F1 * Px +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F11 * Px +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Px * w +
        ((-1 : ℂ)) * H * Px * w := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_0_2 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the scalar-stream jet, component `(0, 3)`. -/
theorem metricJet_cosmological_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 0 3 =
      ((1 : ℂ) * r) * F1 * Py +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F11 * Py +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Py * w +
        ((-1 : ℂ)) * H * Py * w := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_0_3 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the scalar-stream jet, component `(1, 1)`. -/
theorem metricJet_cosmological_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 1 1 =
      ((2 : ℂ)) / ((r ^ 2 - 1) ^ 2) * F0 * P +
        ((-1 / 2 : ℂ)) / (r ^ 2 * (r ^ 2 - 1) ^ 2) * F0 * Pxx * y ^ 2 +
        ((-1 / 2 : ℂ)) / (r ^ 2 * (r ^ 2 - 1) ^ 2) * F0 * Pyy * y ^ 2 +
        ((-1 : ℂ)) / (r * (r ^ 2 - 1)) * F01 * P +
        ((2 : ℂ)) / (r * (r ^ 2 - 1)) * F1 * P * w +
        ((1 : ℂ) + (-3 : ℂ) * r ^ 2) / (r ^ 2) * F2 * P +
        ((-2 : ℂ)) / (r ^ 2 * (r ^ 2 - 1)) * H * P +
        ((-2 : ℂ)) / ((r ^ 2 - 1) ^ 2) * H * P * w ^ 2 +
        ((1 : ℂ)) / (r ^ 2 * (r ^ 2 - 1)) * H * Pxx * y ^ 2 +
        ((1 : ℂ)) / (r ^ 2 * (r ^ 2 - 1)) * H * Pyy * y ^ 2 +
        ((-2 : ℂ) + (4 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1)) * H1 * P := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_1_1 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the scalar-stream jet, component `(1, 2)`. -/
theorem metricJet_cosmological_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 1 2 =
      ((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2) * F0 * Px +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F01 * Px +
        ((-1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F1 * Px * w +
        ((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r) * F2 * Px +
        ((-1 : ℂ)) * H1 * Px := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_1_2 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the scalar-stream jet, component `(1, 3)`. -/
theorem metricJet_cosmological_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 1 3 =
      ((1 / 2 : ℂ) + (-1 : ℂ) * r ^ 2) / (r * (r ^ 2 - 1) ^ 2) * F0 * Py +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F01 * Py +
        ((-1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F1 * Py * w +
        ((-1 / 2 : ℂ) + (1 : ℂ) * r ^ 2) / (r) * F2 * Py +
        ((-1 : ℂ)) * H1 * Py := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_1_3 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the scalar-stream jet, component `(2, 2)`. -/
theorem metricJet_cosmological_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 2 2 =
      ((-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2) * F0 * P * y⁻¹ ^ 2 +
        ((-1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Py * y⁻¹ +
        ((-1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Pyy +
        ((1 / 2 : ℂ) * r) / ((r ^ 2 - 1)) * F01 * P * y⁻¹ ^ 2 +
        ((-1 / 2 : ℂ) * r ^ 2) * F02 * P * y⁻¹ ^ 2 +
        ((-1 : ℂ) * r + (2 : ℂ) * r ^ 3) / ((r ^ 2 - 1)) * F1 * P * w * y⁻¹ ^ 2 +
        ((1 : ℂ) * r ^ 2) * F11 * P * w * y⁻¹ ^ 2 +
        ((4 : ℂ) * r ^ 2 + (-5 : ℂ) * r ^ 4) * F2 * P * y⁻¹ ^ 2 +
        ((-1 / 2 : ℂ) * r ^ 2) * F2 * P * w ^ 2 * y⁻¹ ^ 2 +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F2 * Py * y⁻¹ +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F2 * Pyy +
        ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * F21 * P * y⁻¹ ^ 2 +
        ((-1 : ℂ) * r ^ 2) / ((r ^ 2 - 1)) * H * P * w ^ 2 * y⁻¹ ^ 2 +
        ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * H1 * P * y⁻¹ ^ 2 +
        ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * H2 * P * y⁻¹ ^ 2 := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_2_2 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the scalar-stream jet, component `(2, 3)`. -/
theorem metricJet_cosmological_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 2 3 =
      ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Px * y⁻¹ +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Pxy +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Px * y⁻¹ +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Pxy := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_2_3 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the scalar-stream jet, component `(3, 3)`. -/
theorem metricJet_cosmological_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 3 3 =
      ((-2 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) / ((r ^ 2 - 1) ^ 2) * F0 * P * y⁻¹ ^ 2 +
        ((-1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Pxx +
        ((1 / 2 : ℂ)) / ((r ^ 2 - 1)) * F0 * Py * y⁻¹ +
        ((1 / 2 : ℂ) * r) / ((r ^ 2 - 1)) * F01 * P * y⁻¹ ^ 2 +
        ((-1 / 2 : ℂ) * r ^ 2) * F02 * P * y⁻¹ ^ 2 +
        ((-1 : ℂ) * r + (2 : ℂ) * r ^ 3) / ((r ^ 2 - 1)) * F1 * P * w * y⁻¹ ^ 2 +
        ((1 : ℂ) * r ^ 2) * F11 * P * w * y⁻¹ ^ 2 +
        ((4 : ℂ) * r ^ 2 + (-5 : ℂ) * r ^ 4) * F2 * P * y⁻¹ ^ 2 +
        ((-1 / 2 : ℂ) * r ^ 2) * F2 * P * w ^ 2 * y⁻¹ ^ 2 +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ 2) * F2 * Pxx +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ 2) * F2 * Py * y⁻¹ +
        ((-1 / 2 : ℂ) * r + (3 / 2 : ℂ) * r ^ 3 + (-1 : ℂ) * r ^ 5) * F21 * P * y⁻¹ ^ 2 +
        ((-1 : ℂ) * r ^ 2) / ((r ^ 2 - 1)) * H * P * w ^ 2 * y⁻¹ ^ 2 +
        ((-2 : ℂ) * r + (4 : ℂ) * r ^ 3) * H1 * P * y⁻¹ ^ 2 +
        ((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4) * H2 * P * y⁻¹ ^ 2 := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_3_3 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

end
end RHTower.D4BMScalarStream
