import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetEntries

/-!
# Christoffel variation table of the fundamental Birmingham–Mokhtari scalar jet: spatial1 part

Closed forms of the spatial derivative `Quadratic.connectionSpatial J K 1 u i j` of the quadratic Christoffel variation (derivative index `1`) for the fundamental scalar metric jet `K` over the
Birmingham–Mokhtari background `J`, in every index order (64 entries; vanishing entries recorded).
Each entry is a rational function of `(s, r)` times a monomial in the angular jet times a power of
`y`. The proofs use the index-collapsed forms over a diagonal background, the `bmJetEntry` tables and
one power-cancellation pass, at the default heartbeat limit; every entry carries the `bmJetTable`
simp attribute. The family is split across small files so that one file never holds more than 64
elaborations.
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarLinearEquation
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet
noncomputable section
variable {s r y B S Sx Sy Sxx Sxy : ℂ}

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 0 0 =
      B ^ 2 * (((-2 : ℂ) * s ^ 2 * r ^ 2 + (4 : ℂ) * s ^ 2 * r ^ 4 + (5 : ℂ) * s ^ 3 + (-15 : ℂ) * s ^ 3 * r ^ 2 + (11 : ℂ) * s ^ 3 * r ^ 4 + (-4 : ℂ) * s ^ 3 * r ^ 6 + (21 / 2 : ℂ) * s ^ 4 + (-43 / 2 : ℂ) * s ^ 4 * r ^ 2 + (12 : ℂ) * s ^ 4 * r ^ 4 + (7 : ℂ) * s ^ 5 + (-9 : ℂ) * s ^ 5 * r ^ 2 + (1 : ℂ) * s ^ 5 * r ^ 4 + (3 / 2 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 0 1 =
      B ^ 2 * (((5 / 2 : ℂ) * s ^ 2 + (-21 / 2 : ℂ) * s ^ 2 * r ^ 2 + (33 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-21 / 2 : ℂ) * s ^ 2 * r ^ 6 + (6 : ℂ) * s ^ 2 * r ^ 8 + (29 / 4 : ℂ) * s ^ 3 + (-25 : ℂ) * s ^ 3 * r ^ 2 + (121 / 4 : ℂ) * s ^ 3 * r ^ 4 + (-33 / 2 : ℂ) * s ^ 3 * r ^ 6 + (15 / 2 : ℂ) * s ^ 4 + (-37 / 2 : ℂ) * s ^ 4 * r ^ 2 + (12 : ℂ) * s ^ 4 * r ^ 4 + (13 / 4 : ℂ) * s ^ 5 + (-7 / 2 : ℂ) * s ^ 5 * r ^ 2 + (-7 / 4 : ℂ) * s ^ 5 * r ^ 4 + (1 / 2 : ℂ) * s ^ 6 + (1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 3) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 0 2 =
      B ^ 2 * (((-1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 0 3 =
      B ^ 2 * (((-1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 0 =
      B ^ 2 * (((5 / 2 : ℂ) * s ^ 2 + (-21 / 2 : ℂ) * s ^ 2 * r ^ 2 + (33 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-21 / 2 : ℂ) * s ^ 2 * r ^ 6 + (6 : ℂ) * s ^ 2 * r ^ 8 + (29 / 4 : ℂ) * s ^ 3 + (-25 : ℂ) * s ^ 3 * r ^ 2 + (121 / 4 : ℂ) * s ^ 3 * r ^ 4 + (-33 / 2 : ℂ) * s ^ 3 * r ^ 6 + (15 / 2 : ℂ) * s ^ 4 + (-37 / 2 : ℂ) * s ^ 4 * r ^ 2 + (12 : ℂ) * s ^ 4 * r ^ 4 + (13 / 4 : ℂ) * s ^ 5 + (-7 / 2 : ℂ) * s ^ 5 * r ^ 2 + (-7 / 4 : ℂ) * s ^ 5 * r ^ 4 + (1 / 2 : ℂ) * s ^ 6 + (1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 3) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 1 =
      B ^ 2 * (((4 : ℂ) * s ^ 2 * r ^ 2 + (-16 : ℂ) * s ^ 2 * r ^ 4 + (18 : ℂ) * s ^ 2 * r ^ 6 + (-1 : ℂ) * s ^ 3 + (6 : ℂ) * s ^ 3 * r ^ 2 + (-4 : ℂ) * s ^ 3 * r ^ 4 + (-6 : ℂ) * s ^ 3 * r ^ 6 + (-1 / 2 : ℂ) * s ^ 4 + (-1 / 2 : ℂ) * s ^ 4 * r ^ 2 + (2 : ℂ) * s ^ 4 * r ^ 4 + (1 : ℂ) * s ^ 5 + (-2 : ℂ) * s ^ 5 * r ^ 2 + (-2 : ℂ) * s ^ 5 * r ^ 4 + (1 / 2 : ℂ) * s ^ 6 + (1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 4) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 2 0 =
      B ^ 2 * (((-1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 2 2 =
      B ^ 2 * (((4 : ℂ) * s * r ^ 4 + (-9 : ℂ) * s ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (1 : ℂ) * s ^ 3 * r ^ 4 + (1 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * S ^ 2 * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 3 0 =
      B ^ 2 * (((-1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_0_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 3 3 =
      B ^ 2 * (((4 : ℂ) * s * r ^ 4 + (-9 : ℂ) * s ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (1 : ℂ) * s ^ 3 * r ^ 4 + (1 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * S ^ 2 * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 0 0 =
      B ^ 2 * (((-5 / 2 : ℂ) * s ^ 2 + (11 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 6 + (-2 : ℂ) * s ^ 2 * r ^ 8 + (-29 / 4 : ℂ) * s ^ 3 + (12 : ℂ) * s ^ 3 * r ^ 2 + (3 / 4 : ℂ) * s ^ 3 * r ^ 4 + (-7 / 2 : ℂ) * s ^ 3 * r ^ 6 + (-15 / 2 : ℂ) * s ^ 4 + (15 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 4 * r ^ 6 + (-13 / 4 : ℂ) * s ^ 5 + (1 / 2 : ℂ) * s ^ 5 * r ^ 2 + (11 / 4 : ℂ) * s ^ 5 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1)) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 0 1 =
      B ^ 2 * (((2 : ℂ) * s ^ 2 * r ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 4 + (-3 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 3 * r ^ 2 + (-1 : ℂ) * s ^ 3 * r ^ 4 + (-11 / 2 : ℂ) * s ^ 4 + (17 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-4 : ℂ) * s ^ 4 * r ^ 4 + (-3 : ℂ) * s ^ 5 + (3 : ℂ) * s ^ 5 * r ^ 2 + (1 : ℂ) * s ^ 5 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 0 =
      B ^ 2 * (((2 : ℂ) * s ^ 2 * r ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 4 + (-3 : ℂ) * s ^ 3 + (7 : ℂ) * s ^ 3 * r ^ 2 + (-1 : ℂ) * s ^ 3 * r ^ 4 + (-11 / 2 : ℂ) * s ^ 4 + (17 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-4 : ℂ) * s ^ 4 * r ^ 4 + (-3 : ℂ) * s ^ 5 + (3 : ℂ) * s ^ 5 * r ^ 2 + (1 : ℂ) * s ^ 5 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 6 + (-1 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 1 =
      B ^ 2 * (((5 / 2 : ℂ) * s ^ 2 + (-21 / 2 : ℂ) * s ^ 2 * r ^ 2 + (33 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-25 / 2 : ℂ) * s ^ 2 * r ^ 6 + (29 / 4 : ℂ) * s ^ 3 + (-25 : ℂ) * s ^ 3 * r ^ 2 + (117 / 4 : ℂ) * s ^ 3 * r ^ 4 + (-15 / 2 : ℂ) * s ^ 3 * r ^ 6 + (15 / 2 : ℂ) * s ^ 4 + (-43 / 2 : ℂ) * s ^ 4 * r ^ 2 + (18 : ℂ) * s ^ 4 * r ^ 4 + (-5 : ℂ) * s ^ 4 * r ^ 6 + (13 / 4 : ℂ) * s ^ 5 + (-17 / 2 : ℂ) * s ^ 5 * r ^ 2 + (29 / 4 : ℂ) * s ^ 5 * r ^ 4 + (1 / 2 : ℂ) * s ^ 6 + (-3 / 2 : ℂ) * s ^ 6 * r ^ 2) / (r ^ 6 * (r ^ 2 - 1) ^ 3) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 2 =
      B ^ 2 * (((-1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 3 =
      B ^ 2 * (((-1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 2 1 =
      B ^ 2 * (((-1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 2 2 =
      B ^ 2 * (((-1 : ℂ) * s * r ^ 2 + (-2 : ℂ) * s * r ^ 4 + (3 : ℂ) * s * r ^ 6 + (3 / 2 : ℂ) * s ^ 2 + (-13 / 2 : ℂ) * s ^ 2 * r ^ 2 + (9 : ℂ) * s ^ 2 * r ^ 4 + (19 / 4 : ℂ) * s ^ 3 + (-43 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 : ℂ) * s ^ 3 * r ^ 4 + (11 / 2 : ℂ) * s ^ 4 + (-6 : ℂ) * s ^ 4 * r ^ 2 + (1 : ℂ) * s ^ 4 * r ^ 4 + (11 / 4 : ℂ) * s ^ 5 + (-11 / 4 : ℂ) * s ^ 5 * r ^ 2 + (1 / 2 : ℂ) * s ^ 6) / (r ^ 4 * (r ^ 2 - 1)) * S ^ 2 * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 3 1 =
      B ^ 2 * (((-1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_1_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 3 3 =
      B ^ 2 * (((-1 : ℂ) * s * r ^ 2 + (-2 : ℂ) * s * r ^ 4 + (3 : ℂ) * s * r ^ 6 + (3 / 2 : ℂ) * s ^ 2 + (-13 / 2 : ℂ) * s ^ 2 * r ^ 2 + (9 : ℂ) * s ^ 2 * r ^ 4 + (19 / 4 : ℂ) * s ^ 3 + (-43 / 4 : ℂ) * s ^ 3 * r ^ 2 + (1 : ℂ) * s ^ 3 * r ^ 4 + (11 / 2 : ℂ) * s ^ 4 + (-6 : ℂ) * s ^ 4 * r ^ 2 + (1 : ℂ) * s ^ 4 * r ^ 4 + (11 / 4 : ℂ) * s ^ 5 + (-11 / 4 : ℂ) * s ^ 5 * r ^ 2 + (1 / 2 : ℂ) * s ^ 6) / (r ^ 4 * (r ^ 2 - 1)) * S ^ 2 * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 0 0 =
      B ^ 2 * (((-2 : ℂ) * s * r ^ 2 + (5 : ℂ) * s * r ^ 4 + (-3 : ℂ) * s * r ^ 6 + (-3 / 2 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (1 : ℂ) * s ^ 2 * r ^ 6 + (-7 / 2 : ℂ) * s ^ 3 + (11 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-3 : ℂ) * s ^ 3 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 4 * r ^ 2 + (1 : ℂ) * s ^ 4 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 5 * r ^ 2) / (r ^ 7 * (r ^ 2 - 1)) * S * Sx * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 0 1 =
      B ^ 2 * (((1 : ℂ) * s * r ^ 4 + (-3 : ℂ) * s * r ^ 6 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (9 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-5 / 2 : ℂ) * s ^ 3 * r ^ 4 + (-7 / 2 : ℂ) * s ^ 4 + (9 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 5) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S * Sx * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 0 2 =
      B ^ 2 * (((-2 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 3 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 1 0 =
      B ^ 2 * (((1 : ℂ) * s * r ^ 4 + (-3 : ℂ) * s * r ^ 6 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (9 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-5 / 2 : ℂ) * s ^ 3 * r ^ 4 + (-7 / 2 : ℂ) * s ^ 4 + (9 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 5) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S * Sx * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 1 1 =
      B ^ 2 * (((-2 : ℂ) * s * r ^ 2 + (7 : ℂ) * s * r ^ 4 + (-9 : ℂ) * s * r ^ 6 + (-3 / 2 : ℂ) * s ^ 2 + (5 / 2 : ℂ) * s ^ 2 * r ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 6 + (-7 / 2 : ℂ) * s ^ 3 + (15 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-5 : ℂ) * s ^ 3 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 4 + (5 / 2 : ℂ) * s ^ 4 * r ^ 2 + (2 : ℂ) * s ^ 4 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 5 * r ^ 2) / (r ^ 7 * (r ^ 2 - 1) ^ 3) * S * Sx * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 1 2 =
      B ^ 2 * (((-3 : ℂ) * s * r ^ 2 + (5 : ℂ) * s * r ^ 4 + (-5 / 2 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (17 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-3 : ℂ) * s ^ 2 * r ^ 6 + (-29 / 4 : ℂ) * s ^ 3 + (23 / 4 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 3 * r ^ 4 + (-15 / 2 : ℂ) * s ^ 4 + (17 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-5 / 2 : ℂ) * s ^ 4 * r ^ 4 + (-13 / 4 : ℂ) * s ^ 5 + (11 / 4 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 2 0 =
      B ^ 2 * (((-2 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 3 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 2 1 =
      B ^ 2 * (((-3 : ℂ) * s * r ^ 2 + (5 : ℂ) * s * r ^ 4 + (-5 / 2 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (17 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-3 : ℂ) * s ^ 2 * r ^ 6 + (-29 / 4 : ℂ) * s ^ 3 + (23 / 4 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 3 * r ^ 4 + (-15 / 2 : ℂ) * s ^ 4 + (17 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-5 / 2 : ℂ) * s ^ 4 * r ^ 4 + (-13 / 4 : ℂ) * s ^ 5 + (11 / 4 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 2 2 =
      B ^ 2 * (((-2 : ℂ) * s * r ^ 2 + (-1 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 2 3 =
      B ^ 2 * (((-2 : ℂ) * s * r ^ 2 + (-1 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 3 2 =
      B ^ 2 * (((-2 : ℂ) * s * r ^ 2 + (-1 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_2_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 3 3 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 2 + (1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (5 / 2 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 4 * r ^ 2 + (1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 0 0 =
      B ^ 2 * (((-2 : ℂ) * s * r ^ 2 + (5 : ℂ) * s * r ^ 4 + (-3 : ℂ) * s * r ^ 6 + (-3 / 2 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 4 + (1 : ℂ) * s ^ 2 * r ^ 6 + (-7 / 2 : ℂ) * s ^ 3 + (11 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-3 : ℂ) * s ^ 3 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 4 + (3 / 2 : ℂ) * s ^ 4 * r ^ 2 + (1 : ℂ) * s ^ 4 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 5 * r ^ 2) / (r ^ 7 * (r ^ 2 - 1)) * S * Sy * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 0 1 =
      B ^ 2 * (((1 : ℂ) * s * r ^ 4 + (-3 : ℂ) * s * r ^ 6 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (9 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-5 / 2 : ℂ) * s ^ 3 * r ^ 4 + (-7 / 2 : ℂ) * s ^ 4 + (9 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 5) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S * Sy * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 0 3 =
      B ^ 2 * (((-2 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 3 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 1 0 =
      B ^ 2 * (((1 : ℂ) * s * r ^ 4 + (-3 : ℂ) * s * r ^ 6 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (9 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (4 : ℂ) * s ^ 3 * r ^ 2 + (-5 / 2 : ℂ) * s ^ 3 * r ^ 4 + (-7 / 2 : ℂ) * s ^ 4 + (9 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-1 : ℂ) * s ^ 5) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S * Sy * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 1 1 =
      B ^ 2 * (((-2 : ℂ) * s * r ^ 2 + (7 : ℂ) * s * r ^ 4 + (-9 : ℂ) * s * r ^ 6 + (-3 / 2 : ℂ) * s ^ 2 + (5 / 2 : ℂ) * s ^ 2 * r ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 6 + (-7 / 2 : ℂ) * s ^ 3 + (15 / 2 : ℂ) * s ^ 3 * r ^ 2 + (-5 : ℂ) * s ^ 3 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 4 + (5 / 2 : ℂ) * s ^ 4 * r ^ 2 + (2 : ℂ) * s ^ 4 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 5 + (-1 / 2 : ℂ) * s ^ 5 * r ^ 2) / (r ^ 7 * (r ^ 2 - 1) ^ 3) * S * Sy * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 1 3 =
      B ^ 2 * (((-3 : ℂ) * s * r ^ 2 + (5 : ℂ) * s * r ^ 4 + (-5 / 2 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (17 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-3 : ℂ) * s ^ 2 * r ^ 6 + (-29 / 4 : ℂ) * s ^ 3 + (23 / 4 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 3 * r ^ 4 + (-15 / 2 : ℂ) * s ^ 4 + (17 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-5 / 2 : ℂ) * s ^ 4 * r ^ 4 + (-13 / 4 : ℂ) * s ^ 5 + (11 / 4 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 2 2 =
      B ^ 2 * (((2 : ℂ) * s * r ^ 2 + (1 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 2 * r ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 4 + (5 / 2 : ℂ) * s ^ 3 + (2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 4 * r ^ 2 + (1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 2 3 =
      B ^ 2 * (((-2 : ℂ) * s * r ^ 2 + (-1 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 3 0 =
      B ^ 2 * (((-2 : ℂ) * s ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 3 + (-3 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 3 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 4 + (-2 : ℂ) * s ^ 5 + (1 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 5 * (r ^ 2 - 1)) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 3 1 =
      B ^ 2 * (((-3 : ℂ) * s * r ^ 2 + (5 : ℂ) * s * r ^ 4 + (-5 / 2 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (17 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-3 : ℂ) * s ^ 2 * r ^ 6 + (-29 / 4 : ℂ) * s ^ 3 + (23 / 4 : ℂ) * s ^ 3 * r ^ 2 + (2 : ℂ) * s ^ 3 * r ^ 4 + (-15 / 2 : ℂ) * s ^ 4 + (17 / 2 : ℂ) * s ^ 4 * r ^ 2 + (-5 / 2 : ℂ) * s ^ 4 * r ^ 4 + (-13 / 4 : ℂ) * s ^ 5 + (11 / 4 : ℂ) * s ^ 5 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 6) / (r ^ 6 * (r ^ 2 - 1) ^ 2) * S ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 3 2 =
      B ^ 2 * (((-2 : ℂ) * s * r ^ 2 + (-1 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_1_3_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 3 3 =
      B ^ 2 * (((-2 : ℂ) * s * r ^ 2 + (-1 : ℂ) * s ^ 2 + (-3 : ℂ) * s ^ 2 * r ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 3 + (-2 : ℂ) * s ^ 4 + (1 : ℂ) * s ^ 4 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 5) / (r ^ 5 * (r ^ 2 - 1)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

end
end RHTower.D4BMScalarLinearEquation
