import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetEntries

/-!
# Christoffel variation table of the fundamental Birmingham–Mokhtari scalar jet: spatial0 part

Closed forms of the spatial derivative `Quadratic.connectionSpatial J K 0 u i j` of the quadratic Christoffel variation (derivative index `0`) for the fundamental scalar metric jet `K` over the
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 0 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (5 / 2 : ℂ) * s ^ (4 : ℕ) + (-11 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (4 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (4 : ℂ) * s ^ (5 : ℕ) + (-4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (3 / 2 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 1 =
      B ^ (2 : ℕ) * (((1 : ℂ) * s ^ (3 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (5 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) * r ^ (6 : ℕ) + (5 / 2 : ℂ) * s ^ (4 : ℕ) + (-13 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (5 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 2 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 3 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 1 0 =
      B ^ (2 : ℕ) * (((1 : ℂ) * s ^ (3 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (5 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) * r ^ (6 : ℕ) + (5 / 2 : ℂ) * s ^ (4 : ℕ) + (-13 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (5 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 1 1 =
      B ^ (2 : ℕ) * (((4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (3 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 2 0 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 2 2 =
      B ^ (2 : ℕ) * (((-4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (5 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 3 0 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_0_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 3 3 =
      B ^ (2 : ℕ) * (((-4 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (5 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 0 =
      B ^ (2 : ℕ) * (((-1 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (5 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) * r ^ (6 : ℕ) + (-5 / 2 : ℂ) * s ^ (4 : ℕ) + (5 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 1 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 1 0 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-3 / 2 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 1 1 =
      B ^ (2 : ℕ) * (((1 : ℂ) * s ^ (3 : ℕ) + (-4 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (5 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (5 / 2 : ℂ) * s ^ (4 : ℕ) + (-13 / 2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (3 : ℂ) * s ^ (4 : ℕ) * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ) + (-4 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ) * r ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ) + (-3 / 2 : ℂ) * s ^ (6 : ℕ) * r ^ (2 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 1 2 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 1 3 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 2 1 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 2 2 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (6 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (5 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (3 : ℕ)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  all_goals simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  all_goals (
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
    ring)

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 3 1 =
      B ^ (2 : ℕ) * (((-1 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_1_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 3 3 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (6 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (1 : ℂ) * s ^ (3 : ℕ) + (-6 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (5 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (5 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (3 : ℕ)) * S ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 0 0 =
      B ^ (2 : ℕ) * (((-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * S * Sx * y ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 0 1 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sx * y ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 0 2 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 1 0 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sx * y ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 1 1 =
      B ^ (2 : ℕ) * (((-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S * Sx * y ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 1 2 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-5 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 2 0 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 2 1 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-5 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 2 2 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 2 3 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 3 2 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_2_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 3 3 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 0 0 =
      B ^ (2 : ℕ) * (((-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ)) * S * Sy * y ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 0 1 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sy * y ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 0 3 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 1 0 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S * Sy * y ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 1 1 =
      B ^ (2 : ℕ) * (((-1 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (3 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ)) / (r ^ (6 : ℕ) * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * S * Sy * y ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 1 3 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-5 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 2 2 =
      B ^ (2 : ℕ) * (((2 : ℂ) * s * r ^ (4 : ℕ) + (2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (1 / 2 : ℂ) * s ^ (3 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (1 : ℂ) * s ^ (4 : ℕ) + (1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 2 3 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 3 0 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (4 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (5 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (4 : ℕ)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 3 1 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ) + (-3 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (2 : ℂ) * s ^ (3 : ℕ) * r ^ (4 : ℕ) + (-5 / 2 : ℂ) * s ^ (4 : ℕ) + (-2 : ℂ) * s ^ (5 : ℕ) + (1 : ℂ) * s ^ (5 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (6 : ℕ)) / (r ^ (5 : ℕ) * (r ^ (2 : ℕ) - 1)) * S ^ (2 : ℕ)) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 3 2 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

@[bmJetTable] theorem scalarJet_quadConnectionSpatial_0_3_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Quadratic.connectionSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 3 3 =
      B ^ (2 : ℕ) * (((-2 : ℂ) * s * r ^ (4 : ℕ) + (-2 : ℂ) * s ^ (2 : ℕ) * r ^ (2 : ℕ) + (-1 / 2 : ℂ) * s ^ (3 : ℕ) + (-2 : ℂ) * s ^ (3 : ℕ) * r ^ (2 : ℕ) + (-1 : ℂ) * s ^ (4 : ℕ) + (-1 / 2 : ℂ) * s ^ (5 : ℕ)) / (r ^ (4 : ℕ)) * S * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.quadratic_connectionSpatial_eq]
  simp only [hd.quadratic_inverseSpatial_apply, hd.linearization_inverseSpatial_apply,
    hd.quadratic_inverse_apply, hd.linearization_inverse_apply]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
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

end
end RHTower.D4BMScalarLinearEquation
