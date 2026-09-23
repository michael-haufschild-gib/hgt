import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGradientStreamEntries
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetEntries

/-!
# The linearized cosmological Einstein operator on the gradient-tensor stream jet

All sixteen components of the linearized Ricci variation, the linearized scalar variation and the
ten components of `Linearization.cosmological J K (-3)` for the gradient-tensor stream jet
`2 r² G (∇S⊗∇S)^{tf}` over the Birmingham–Mokhtari background. The orbit block vanishes, the
mixed block is `(s+1)(s+2) w G` times the gradient of `S²`, and the trace-free angular block is a
radial wave operator on `G` times `(∇S⊗∇S)^{tf}`: this is the second angular structure of the
scalar–scalar `++` response.
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet D4BMScalarLinearEquation
noncomputable section
variable {w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ}

@[bmStreamTable] theorem gradientJet_linRicci_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 0 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals ring_nf

@[bmStreamTable] theorem gradientJet_linRicci_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 0 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals ring_nf

@[bmStreamTable] theorem gradientJet_linRicci_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 0 2 =
      ((3 : ℂ)) * G * S * Sx * s * w +
        ((1 : ℂ)) * G * S * Sx * s ^ (2 : ℕ) * w +
        ((2 : ℂ)) * G * S * Sx * w := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 0 3 =
      ((3 : ℂ)) * G * S * Sy * s * w +
        ((1 : ℂ)) * G * S * Sy * s ^ (2 : ℕ) * w +
        ((2 : ℂ)) * G * S * Sy * w := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 1 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals ring_nf

@[bmStreamTable] theorem gradientJet_linRicci_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 1 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals ring_nf

@[bmStreamTable] theorem gradientJet_linRicci_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 1 2 =
      ((2 : ℂ)) * G1 * S * Sx +
        ((3 : ℂ)) * G1 * S * Sx * s +
        ((1 : ℂ)) * G1 * S * Sx * s ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 1 3 =
      ((2 : ℂ)) * G1 * S * Sy +
        ((3 : ℂ)) * G1 * S * Sy * s +
        ((1 : ℂ)) * G1 * S * Sy * s ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 2 0 =
      ((3 : ℂ)) * G * S * Sx * s * w +
        ((1 : ℂ)) * G * S * Sx * s ^ (2 : ℕ) * w +
        ((2 : ℂ)) * G * S * Sx * w := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 2 1 =
      ((2 : ℂ)) * G1 * S * Sx +
        ((3 : ℂ)) * G1 * S * Sx * s +
        ((1 : ℂ)) * G1 * S * Sx * s ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 2 2 =
      ((4 : ℂ)) * G * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) +
        ((12 : ℂ)) * G * S ^ (2 : ℕ) * s * y⁻¹ ^ (2 : ℕ) +
        ((13 : ℂ)) * G * S ^ (2 : ℕ) * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) +
        ((6 : ℂ)) * G * S ^ (2 : ℕ) * s ^ (3 : ℕ) * y⁻¹ ^ (2 : ℕ) +
        ((1 : ℂ)) * G * S ^ (2 : ℕ) * s ^ (4 : ℕ) * y⁻¹ ^ (2 : ℕ) +
        ((2 : ℂ) + (-3 : ℂ) * r ^ (2 : ℕ)) * G * Sx ^ (2 : ℕ) +
        ((3 : ℂ)) * G * Sx ^ (2 : ℕ) * s +
        ((1 : ℂ)) * G * Sx ^ (2 : ℕ) * s ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sx ^ (2 : ℕ) * w ^ (2 : ℕ) +
        ((2 : ℂ) + (3 : ℂ) * r ^ (2 : ℕ)) * G * Sy ^ (2 : ℕ) +
        ((3 : ℂ)) * G * Sy ^ (2 : ℕ) * s +
        ((1 : ℂ)) * G * Sy ^ (2 : ℕ) * s ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sy ^ (2 : ℕ) * w ^ (2 : ℕ) +
        ((1 : ℂ) * r + (-2 : ℂ) * r ^ (3 : ℕ)) * G1 * Sx ^ (2 : ℕ) +
        ((-1 : ℂ) * r + (2 : ℂ) * r ^ (3 : ℕ)) * G1 * Sy ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * r ^ (4 : ℕ)) * G2 * Sx ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * r ^ (4 : ℕ)) * G2 * Sy ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 2 3 =
      ((-6 : ℂ) * r ^ (2 : ℕ)) * G * Sx * Sy +
        ((1 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sx * Sy * w ^ (2 : ℕ) +
        ((2 : ℂ) * r + (-4 : ℂ) * r ^ (3 : ℕ)) * G1 * Sx * Sy +
        ((1 : ℂ) * r ^ (2 : ℕ) + (-1 : ℂ) * r ^ (4 : ℕ)) * G2 * Sx * Sy := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 3 0 =
      ((3 : ℂ)) * G * S * Sy * s * w +
        ((1 : ℂ)) * G * S * Sy * s ^ (2 : ℕ) * w +
        ((2 : ℂ)) * G * S * Sy * w := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 3 1 =
      ((2 : ℂ)) * G1 * S * Sy +
        ((3 : ℂ)) * G1 * S * Sy * s +
        ((1 : ℂ)) * G1 * S * Sy * s ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 3 2 =
      ((-6 : ℂ) * r ^ (2 : ℕ)) * G * Sx * Sy +
        ((1 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sx * Sy * w ^ (2 : ℕ) +
        ((2 : ℂ) * r + (-4 : ℂ) * r ^ (3 : ℕ)) * G1 * Sx * Sy +
        ((1 : ℂ) * r ^ (2 : ℕ) + (-1 : ℂ) * r ^ (4 : ℕ)) * G2 * Sx * Sy := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

@[bmStreamTable] theorem gradientJet_linRicci_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.ricci (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) 3 3 =
      ((4 : ℂ)) * G * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) +
        ((12 : ℂ)) * G * S ^ (2 : ℕ) * s * y⁻¹ ^ (2 : ℕ) +
        ((13 : ℂ)) * G * S ^ (2 : ℕ) * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) +
        ((6 : ℂ)) * G * S ^ (2 : ℕ) * s ^ (3 : ℕ) * y⁻¹ ^ (2 : ℕ) +
        ((1 : ℂ)) * G * S ^ (2 : ℕ) * s ^ (4 : ℕ) * y⁻¹ ^ (2 : ℕ) +
        ((2 : ℂ) + (3 : ℂ) * r ^ (2 : ℕ)) * G * Sx ^ (2 : ℕ) +
        ((3 : ℂ)) * G * Sx ^ (2 : ℕ) * s +
        ((1 : ℂ)) * G * Sx ^ (2 : ℕ) * s ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sx ^ (2 : ℕ) * w ^ (2 : ℕ) +
        ((2 : ℂ) + (-3 : ℂ) * r ^ (2 : ℕ)) * G * Sy ^ (2 : ℕ) +
        ((3 : ℂ)) * G * Sy ^ (2 : ℕ) * s +
        ((1 : ℂ)) * G * Sy ^ (2 : ℕ) * s ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sy ^ (2 : ℕ) * w ^ (2 : ℕ) +
        ((-1 : ℂ) * r + (2 : ℂ) * r ^ (3 : ℕ)) * G1 * Sx ^ (2 : ℕ) +
        ((1 : ℂ) * r + (-2 : ℂ) * r ^ (3 : ℕ)) * G1 * Sy ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * r ^ (4 : ℕ)) * G2 * Sx ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * r ^ (4 : ℕ)) * G2 * Sy ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.ricci, Fin.sum_univ_four]
  simp only [hd.linearization_curvature_eq]
  simp only [hd.linearization_connectionSpatial_eq, hd.linearization_connection_eq,
    hd.linearization_inverseSpatial_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  generalize hF : r ^ (2 : ℕ) - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ (9 : ℕ) * r⁻¹ * y ^ (7 : ℕ) * y⁻¹ * F ^ (7 : ℕ) * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_mul_self hr,
    InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_mul_self hy,
    InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_mul_self hF0]
  subst hF
  ring

/-- Linearized scalar variation of the gradient-tensor stream jet. -/
theorem gradientJet_linScalar (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.scalar (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) =
      ((8 : ℂ)) / (r ^ (2 : ℕ)) * G * S ^ (2 : ℕ) +
        ((24 : ℂ)) / (r ^ (2 : ℕ)) * G * S ^ (2 : ℕ) * s +
        ((26 : ℂ)) / (r ^ (2 : ℕ)) * G * S ^ (2 : ℕ) * s ^ (2 : ℕ) +
        ((12 : ℂ)) / (r ^ (2 : ℕ)) * G * S ^ (2 : ℕ) * s ^ (3 : ℕ) +
        ((2 : ℂ)) / (r ^ (2 : ℕ)) * G * S ^ (2 : ℕ) * s ^ (4 : ℕ) +
        ((4 : ℂ)) / (r ^ (2 : ℕ)) * G * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((6 : ℂ)) / (r ^ (2 : ℕ)) * G * Sx ^ (2 : ℕ) * s * y ^ (2 : ℕ) +
        ((2 : ℂ)) / (r ^ (2 : ℕ)) * G * Sx ^ (2 : ℕ) * s ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((4 : ℂ)) / (r ^ (2 : ℕ)) * G * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((6 : ℂ)) / (r ^ (2 : ℕ)) * G * Sy ^ (2 : ℕ) * s * y ^ (2 : ℕ) +
        ((2 : ℂ)) / (r ^ (2 : ℕ)) * G * Sy ^ (2 : ℕ) * s ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  simp only [Linearization.scalar, Fin.sum_univ_four, gradientJet_linRicci_0_0 hr hy hf, gradientJet_linRicci_0_1 hr hy hf, gradientJet_linRicci_0_2 hr hy hf, gradientJet_linRicci_0_3 hr hy hf, gradientJet_linRicci_1_0 hr hy hf, gradientJet_linRicci_1_1 hr hy hf, gradientJet_linRicci_1_2 hr hy hf, gradientJet_linRicci_1_3 hr hy hf, gradientJet_linRicci_2_0 hr hy hf, gradientJet_linRicci_2_1 hr hy hf, gradientJet_linRicci_2_2 hr hy hf, gradientJet_linRicci_2_3 hr hy hf, gradientJet_linRicci_3_0 hr hy hf, gradientJet_linRicci_3_1 hr hy hf, gradientJet_linRicci_3_2 hr hy hf, gradientJet_linRicci_3_3 hr hy hf, hd.linearization_inverse_apply,
    hd.inv_apply, D4BMBackground.jet_ricci r y hr hy hf, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.metric, Matrix.diagonal_apply,
    Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the gradient-tensor stream jet, component `(0, 0)`. -/
theorem gradientJet_cosmological_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) 0 0 =
      ((-4 : ℂ) + (4 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * S ^ (2 : ℕ) +
        ((-12 : ℂ) + (12 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * S ^ (2 : ℕ) * s +
        ((-13 : ℂ) + (13 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * S ^ (2 : ℕ) * s ^ (2 : ℕ) +
        ((-6 : ℂ) + (6 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * S ^ (2 : ℕ) * s ^ (3 : ℕ) +
        ((-1 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * S ^ (2 : ℕ) * s ^ (4 : ℕ) +
        ((-2 : ℂ) + (2 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-3 : ℂ) + (3 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * Sx ^ (2 : ℕ) * s * y ^ (2 : ℕ) +
        ((-1 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * Sx ^ (2 : ℕ) * s ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-2 : ℂ) + (2 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-3 : ℂ) + (3 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * Sy ^ (2 : ℕ) * s * y ^ (2 : ℕ) +
        ((-1 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r ^ (2 : ℕ)) * G * Sy ^ (2 : ℕ) * s ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  simp only [Linearization.cosmological, Linearization.einstein, gradientJet_linRicci_0_0 hr hy hf,
    gradientJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the gradient-tensor stream jet, component `(0, 1)`. -/
theorem gradientJet_cosmological_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) 0 1 =
      0 := by
  simp only [Linearization.cosmological, Linearization.einstein, gradientJet_linRicci_0_1 hr hy hf,
    gradientJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the gradient-tensor stream jet, component `(0, 2)`. -/
theorem gradientJet_cosmological_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) 0 2 =
      ((3 : ℂ)) * G * S * Sx * s * w +
        ((1 : ℂ)) * G * S * Sx * s ^ (2 : ℕ) * w +
        ((2 : ℂ)) * G * S * Sx * w := by
  simp only [Linearization.cosmological, Linearization.einstein, gradientJet_linRicci_0_2 hr hy hf,
    gradientJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the gradient-tensor stream jet, component `(0, 3)`. -/
theorem gradientJet_cosmological_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) 0 3 =
      ((3 : ℂ)) * G * S * Sy * s * w +
        ((1 : ℂ)) * G * S * Sy * s ^ (2 : ℕ) * w +
        ((2 : ℂ)) * G * S * Sy * w := by
  simp only [Linearization.cosmological, Linearization.einstein, gradientJet_linRicci_0_3 hr hy hf,
    gradientJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the gradient-tensor stream jet, component `(1, 1)`. -/
theorem gradientJet_cosmological_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) 1 1 =
      ((-4 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * S ^ (2 : ℕ) +
        ((-12 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * S ^ (2 : ℕ) * s +
        ((-13 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * S ^ (2 : ℕ) * s ^ (2 : ℕ) +
        ((-6 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * S ^ (2 : ℕ) * s ^ (3 : ℕ) +
        ((-1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * S ^ (2 : ℕ) * s ^ (4 : ℕ) +
        ((-2 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * Sx ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-3 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * Sx ^ (2 : ℕ) * s * y ^ (2 : ℕ) +
        ((-1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * Sx ^ (2 : ℕ) * s ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-2 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * Sy ^ (2 : ℕ) * y ^ (2 : ℕ) +
        ((-3 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * Sy ^ (2 : ℕ) * s * y ^ (2 : ℕ) +
        ((-1 : ℂ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * G * Sy ^ (2 : ℕ) * s ^ (2 : ℕ) * y ^ (2 : ℕ) := by
  simp only [Linearization.cosmological, Linearization.einstein, gradientJet_linRicci_1_1 hr hy hf,
    gradientJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the gradient-tensor stream jet, component `(1, 2)`. -/
theorem gradientJet_cosmological_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) 1 2 =
      ((2 : ℂ)) * G1 * S * Sx +
        ((3 : ℂ)) * G1 * S * Sx * s +
        ((1 : ℂ)) * G1 * S * Sx * s ^ (2 : ℕ) := by
  simp only [Linearization.cosmological, Linearization.einstein, gradientJet_linRicci_1_2 hr hy hf,
    gradientJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the gradient-tensor stream jet, component `(1, 3)`. -/
theorem gradientJet_cosmological_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) 1 3 =
      ((2 : ℂ)) * G1 * S * Sy +
        ((3 : ℂ)) * G1 * S * Sy * s +
        ((1 : ℂ)) * G1 * S * Sy * s ^ (2 : ℕ) := by
  simp only [Linearization.cosmological, Linearization.einstein, gradientJet_linRicci_1_3 hr hy hf,
    gradientJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the gradient-tensor stream jet, component `(2, 2)`. -/
theorem gradientJet_cosmological_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) 2 2 =
      ((1 / 2 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sx ^ (2 : ℕ) * w ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sy ^ (2 : ℕ) * w ^ (2 : ℕ) +
        ((1 : ℂ) * r + (-2 : ℂ) * r ^ (3 : ℕ)) * G1 * Sx ^ (2 : ℕ) +
        ((-1 : ℂ) * r + (2 : ℂ) * r ^ (3 : ℕ)) * G1 * Sy ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * r ^ (4 : ℕ)) * G2 * Sx ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * r ^ (4 : ℕ)) * G2 * Sy ^ (2 : ℕ) := by
  simp only [Linearization.cosmological, Linearization.einstein, gradientJet_linRicci_2_2 hr hy hf,
    gradientJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the gradient-tensor stream jet, component `(2, 3)`. -/
theorem gradientJet_cosmological_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) 2 3 =
      ((1 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sx * Sy * w ^ (2 : ℕ) +
        ((2 : ℂ) * r + (-4 : ℂ) * r ^ (3 : ℕ)) * G1 * Sx * Sy +
        ((1 : ℂ) * r ^ (2 : ℕ) + (-1 : ℂ) * r ^ (4 : ℕ)) * G2 * Sx * Sy := by
  simp only [Linearization.cosmological, Linearization.einstein, gradientJet_linRicci_2_3 hr hy hf,
    gradientJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

/-- Linearized cosmological Einstein operator on the gradient-tensor stream jet, component `(3, 3)`. -/
theorem gradientJet_cosmological_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy) (-3) 3 3 =
      ((-1 / 2 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sx ^ (2 : ℕ) * w ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * r ^ (2 : ℕ)) / ((r ^ (2 : ℕ) - 1)) * G * Sy ^ (2 : ℕ) * w ^ (2 : ℕ) +
        ((-1 : ℂ) * r + (2 : ℂ) * r ^ (3 : ℕ)) * G1 * Sx ^ (2 : ℕ) +
        ((1 : ℂ) * r + (-2 : ℂ) * r ^ (3 : ℕ)) * G1 * Sy ^ (2 : ℕ) +
        ((-1 / 2 : ℂ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * r ^ (4 : ℕ)) * G2 * Sx ^ (2 : ℕ) +
        ((1 / 2 : ℂ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * r ^ (4 : ℕ)) * G2 * Sy ^ (2 : ℕ) := by
  simp only [Linearization.cosmological, Linearization.einstein, gradientJet_linRicci_3_3 hr hy hf,
    gradientJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

end
end RHTower.D4BMScalarStream
