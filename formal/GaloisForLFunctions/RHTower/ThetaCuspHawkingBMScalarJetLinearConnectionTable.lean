import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetEntries

/-!
# Christoffel variation table of the fundamental Birmingham–Mokhtari scalar jet: linear part

Closed forms of the linearized Christoffel variation `Linearization.connection J K u i j` for the fundamental scalar metric jet `K` over the
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

@[bmJetTable] theorem scalarJet_linConnection_0_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 =
      B * (((-1 : ℂ) * s * r ^ 4 + (-1 / 4 : ℂ) * s ^ 2 + (7 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 1 =
      B * (((-1 / 2 : ℂ) * s + (1 : ℂ) * s * r ^ 2 + (-3 / 2 : ℂ) * s * r ^ 4 + (-3 / 4 : ℂ) * s ^ 2 + (7 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 2 =
      B * (((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 3 =
      B * (((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 =
      B * (((-1 / 2 : ℂ) * s + (1 : ℂ) * s * r ^ 2 + (-3 / 2 : ℂ) * s * r ^ 4 + (-3 / 4 : ℂ) * s ^ 2 + (7 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 4 : ℂ) * s ^ 3 + (-1 / 4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 1 =
      B * (((-1 : ℂ) * s * r ^ 2 + (-3 / 4 : ℂ) * s ^ 2 + (9 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 3) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 2 =
      B * (((1 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2) / (r * (r ^ 2 - 1) ^ 2) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 3 =
      B * (((1 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2) / (r * (r ^ 2 - 1) ^ 2) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 0 =
      B * (((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 1 =
      B * (((1 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2) / (r * (r ^ 2 - 1) ^ 2) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 2 =
      B * (((1 / 2 : ℂ) * s * r ^ 2 + (-5 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 3) / ((r ^ 2 - 1)) * S * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_0_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 0 =
      B * (((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 1 =
      B * (((1 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2) / (r * (r ^ 2 - 1) ^ 2) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_0_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_0_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 3 =
      B * (((1 / 2 : ℂ) * s * r ^ 2 + (-5 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 3) / ((r ^ 2 - 1)) * S * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 0 =
      B * (((-1 / 2 : ℂ) * s + (3 / 2 : ℂ) * s * r ^ 4 + (-3 / 4 : ℂ) * s ^ 2 + (3 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-3 / 2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 4 : ℂ) * s ^ 3 + (3 / 4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 3) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 =
      B * (((1 : ℂ) * s * r ^ 4 + (1 / 4 : ℂ) * s ^ 2 + (-7 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 2 =
      B * (((-1 / 2 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2) / (r) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 3 =
      B * (((-1 / 2 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2) / (r) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 0 =
      B * (((1 : ℂ) * s * r ^ 4 + (1 / 4 : ℂ) * s ^ 2 + (-7 / 4 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 =
      B * (((1 / 2 : ℂ) * s + (-1 : ℂ) * s * r ^ 2 + (3 / 2 : ℂ) * s * r ^ 4 + (3 / 4 : ℂ) * s ^ 2 + (-7 / 4 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 4 + (1 / 4 : ℂ) * s ^ 3 + (1 / 4 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 3 * (r ^ 2 - 1) ^ 2) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 2 =
      B * (((1 / 4 : ℂ) * s + (-3 / 4 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 3 =
      B * (((1 / 4 : ℂ) * s + (-3 / 4 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 0 =
      B * (((-1 / 2 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2) / (r) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 1 =
      B * (((1 / 4 : ℂ) * s + (-3 / 4 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 2 =
      B * (((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * s + (-1 : ℂ) * s * r ^ 2 + (3 / 4 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 3) / (r) * S * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_1_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 0 =
      B * (((-1 / 2 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2) / (r) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 1 =
      B * (((1 / 4 : ℂ) * s + (-3 / 4 : ℂ) * s * r ^ 2 + (1 / 4 : ℂ) * s ^ 2 + (1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1)) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_1_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_1_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 3 =
      B * (((-1 : ℂ) * r ^ 2 + (1 : ℂ) * r ^ 4 + (1 / 2 : ℂ) * s + (-1 : ℂ) * s * r ^ 2 + (3 / 4 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 4 : ℂ) * s ^ 3) / (r) * S * y⁻¹ ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 0 =
      B * (((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4) * Sx * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 1 =
      B * (((1 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2) / (r ^ 3 * (r ^ 2 - 1)) * Sx * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 2 =
      B * (((-1 / 2 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 3) / (r ^ 2) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_2_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 0 =
      B * (((1 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2) / (r ^ 3 * (r ^ 2 - 1)) * Sx * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 1 =
      B * (((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1) ^ 2) * Sx * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 2 =
      B * (((-1 / 2 : ℂ) * s + (-3 / 4 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1)) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_2_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 0 =
      B * (((-1 / 2 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 3) / (r ^ 2) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 1 =
      B * (((-1 / 2 : ℂ) * s + (-3 / 4 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1)) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 2 =
      B * (((-1 / 2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * s + (-1 / 4 : ℂ) * s ^ 2) / (r ^ 2) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 3 =
      B * (((-1 / 2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * s + (-1 / 4 : ℂ) * s ^ 2) / (r ^ 2) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_2_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_2_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 2 =
      B * (((-1 / 2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * s + (-1 / 4 : ℂ) * s ^ 2) / (r ^ 2) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_2_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 3 =
      B * (((1 / 2 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * s + (1 / 4 : ℂ) * s ^ 2) / (r ^ 2) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 0 =
      B * (((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4) * Sy * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 1 =
      B * (((1 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2) / (r ^ 3 * (r ^ 2 - 1)) * Sy * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_3_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 3 =
      B * (((-1 / 2 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 3) / (r ^ 2) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 0 =
      B * (((1 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2) / (r ^ 3 * (r ^ 2 - 1)) * Sy * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 1 =
      B * (((-1 / 4 : ℂ) * s + (3 / 4 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 4 * (r ^ 2 - 1) ^ 2) * Sy * y ^ 2) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_3_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 3 =
      B * (((-1 / 2 : ℂ) * s + (-3 / 4 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1)) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_3_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
  simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,

    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg]

@[bmJetTable] theorem scalarJet_linConnection_3_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 2 =
      B * (((1 / 2 : ℂ) * r ^ 2 + (1 / 4 : ℂ) * s + (1 / 4 : ℂ) * s ^ 2) / (r ^ 2) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 3 =
      B * (((-1 / 2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * s + (-1 / 4 : ℂ) * s ^ 2) / (r ^ 2) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 0 =
      B * (((-1 / 2 : ℂ) * s * r ^ 2 + (-1 / 4 : ℂ) * s ^ 2 + (-1 / 4 : ℂ) * s ^ 3) / (r ^ 2) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 1 =
      B * (((-1 / 2 : ℂ) * s + (-3 / 4 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 4 : ℂ) * s ^ 3) / (r ^ 3 * (r ^ 2 - 1)) * S) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 2 =
      B * (((-1 / 2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * s + (-1 / 4 : ℂ) * s ^ 2) / (r ^ 2) * Sx) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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

@[bmJetTable] theorem scalarJet_linConnection_3_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.connection (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 3 =
      B * (((-1 / 2 : ℂ) * r ^ 2 + (-1 / 4 : ℂ) * s + (-1 / 4 : ℂ) * s ^ 2) / (r ^ 2) * Sy) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_connection_eq]
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
