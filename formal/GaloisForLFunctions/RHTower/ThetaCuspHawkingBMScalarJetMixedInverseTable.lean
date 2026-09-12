import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetEntries
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedJetSimpSets
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinDiagonalCollapseMixed

/-!
# Mixed Christoffel variation table of scalar jets at two rates: inversetable part

Closed forms of the mixed (two-rate) quadratic Christoffel variation
`MixedQuadratic.connectionSpatial` of the fundamental jets `K` (rate `s`, amplitude `B`)
and `V` (rate `t`, amplitude `D`) over the Birmingham–Mokhtari background, in every index order
(vanishing entries recorded), by the index-collapsed mixed forms over a diagonal background, the
entry tables and one power-cancellation pass, at the default heartbeat limit. The products of the
two-mode sources of route HB (the `+−` block) are built from these tables.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RHTower.D4BMScalarLinearEquation
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet
noncomputable section
variable {s t r y B D S Sx Sy Sxx Sxy : ℂ}

@[bmMixedTable] theorem scalarJet_linInverse_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 =
      B * ((-1 / 2 : ℂ) * s + (3 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverse_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 =
      B * ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s ^ 2) / (r * (r ^ 2 - 1)) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverse_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverse_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverse_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 =
      B * ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s ^ 2) / (r * (r ^ 2 - 1)) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverse_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 =
      B * ((-1 / 2 : ℂ) * s + (3 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverse_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverse_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverse_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverse_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverse_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 =
      B * ((1 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * s + (1 / 2 : ℂ) * s ^ 2) / (r ^ 4) * S * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverse_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverse_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverse_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverse_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverse_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 =
      B * ((1 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * s + (1 / 2 : ℂ) * s ^ 2) / (r ^ 4) * S * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverse_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 0 =
      B * D * ((-1 / 2 : ℂ) * s * t + (3 : ℂ) * s * t * r ^ 2 + (-9 / 2 : ℂ) * s * t * r ^ 4 + (2 : ℂ) * s * t * r ^ 6 + (-1 / 2 : ℂ) * s * t ^ 2 + (1 : ℂ) * s * t ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s * t ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 2 * t + (1 : ℂ) * s ^ 2 * t * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * t * r ^ 4 + (-1 / 2 : ℂ) * s ^ 2 * t ^ 2 + (1 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * t ^ 2 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1) ^ 3) * S ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverse_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 1 =
      (0 : ℂ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverse_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverse_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverse_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 0 =
      (0 : ℂ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverse_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 1 =
      B * D * ((1 / 2 : ℂ) * s * t + (-3 : ℂ) * s * t * r ^ 2 + (9 / 2 : ℂ) * s * t * r ^ 4 + (-2 : ℂ) * s * t * r ^ 6 + (1 / 2 : ℂ) * s * t ^ 2 + (-1 : ℂ) * s * t ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s * t ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 2 * t + (-1 : ℂ) * s ^ 2 * t * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t * r ^ 4 + (1 / 2 : ℂ) * s ^ 2 * t ^ 2 + (-1 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t ^ 2 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1)) * S ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverse_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverse_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverse_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverse_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverse_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 2 =
      B * D * ((2 : ℂ) * r ^ 4 + (1 : ℂ) * t * r ^ 2 + (1 : ℂ) * t ^ 2 * r ^ 2 + (1 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s * t + (1 / 2 : ℂ) * s * t ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t + (1 / 2 : ℂ) * s ^ 2 * t ^ 2) / (r ^ 6) * S ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverse_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverse_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverse_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverse_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverse_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverse (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 3 =
      B * D * ((2 : ℂ) * r ^ 4 + (1 : ℂ) * t * r ^ 2 + (1 : ℂ) * t ^ 2 * r ^ 2 + (1 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s * t + (1 / 2 : ℂ) * s * t ^ 2 + (1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t + (1 / 2 : ℂ) * s ^ 2 * t ^ 2) / (r ^ 6) * S ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 0 =
      B * ((-1 / 2 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 1 =
      B * ((-1 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3) / (r * (r ^ 2 - 1)) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 0 =
      B * ((-1 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3) / (r * (r ^ 2 - 1)) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 1 =
      B * ((-1 / 2 : ℂ) * s ^ 2 + (3 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 2) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 2 =
      B * ((1 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 3) / (r ^ 4) * S * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_0_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 0 3 3 =
      B * ((1 : ℂ) * s * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 + (1 / 2 : ℂ) * s ^ 3) / (r ^ 4) * S * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 0 =
      B * ((-1 : ℂ) * s + (3 : ℂ) * s * r ^ 2 + (-6 : ℂ) * s * r ^ 4 + (-3 / 2 : ℂ) * s ^ 2 + (9 / 2 : ℂ) * s ^ 2 * r ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 3 * (r ^ 2 - 1) ^ 3) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 1 =
      B * ((1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * r ^ 4 + (1 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1) ^ 2) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 0 =
      B * ((1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * r ^ 4 + (1 : ℂ) * s ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 3) / (r ^ 2 * (r ^ 2 - 1) ^ 2) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 1 =
      B * ((-1 : ℂ) * s + (1 : ℂ) * s * r ^ 2 + (-3 / 2 : ℂ) * s ^ 2 + (5 / 2 : ℂ) * s ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 + (-1 / 2 : ℂ) * s ^ 3 * r ^ 2) / (r ^ 3 * (r ^ 2 - 1)) * S := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 2 =
      B * ((2 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4 + (2 : ℂ) * s + (-1 : ℂ) * s * r ^ 2 + (5 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3) / (r ^ 5 * (r ^ 2 - 1)) * S * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_1_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 1 3 3 =
      B * ((2 : ℂ) * r ^ 2 + (-2 : ℂ) * r ^ 4 + (2 : ℂ) * s + (-1 : ℂ) * s * r ^ 2 + (5 / 2 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3) / (r ^ 5 * (r ^ 2 - 1)) * S * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 0 =
      B * ((-1 / 2 : ℂ) * s + (3 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2) * Sx := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 1 =
      B * ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s ^ 2) / (r * (r ^ 2 - 1)) * Sx := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 0 =
      B * ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s ^ 2) / (r * (r ^ 2 - 1)) * Sx := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 1 =
      B * ((-1 / 2 : ℂ) * s + (3 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2) * Sx := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 2 =
      B * ((1 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * s + (1 / 2 : ℂ) * s ^ 2) / (r ^ 4) * Sx * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_2_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 2 3 3 =
      B * ((1 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * s + (1 / 2 : ℂ) * s ^ 2) / (r ^ 4) * Sx * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 0 =
      B * ((-1 / 2 : ℂ) * s + (3 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2 * (r ^ 2 - 1) ^ 2) * Sy := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 1 =
      B * ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s ^ 2) / (r * (r ^ 2 - 1)) * Sy := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 0 =
      B * ((-1 : ℂ) * s * r ^ 2 + (1 : ℂ) * s ^ 2) / (r * (r ^ 2 - 1)) * Sy := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 1 =
      B * ((-1 / 2 : ℂ) * s + (3 / 2 : ℂ) * s * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * r ^ 2) / (r ^ 2) * Sy := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 2 =
      B * ((2 : ℂ) * r ^ 2 + (1 : ℂ) * s + (1 : ℂ) * s ^ 2) / (r ^ 4) * S * y + B * ((1 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * s + (1 / 2 : ℂ) * s ^ 2) / (r ^ 4) * Sy * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_linInverseSpatial_3_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    Linearization.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) 3 3 3 =
      B * ((2 : ℂ) * r ^ 2 + (1 : ℂ) * s + (1 : ℂ) * s ^ 2) / (r ^ 4) * S * y + B * ((1 : ℂ) * r ^ 2 + (1 / 2 : ℂ) * s + (1 / 2 : ℂ) * s ^ 2) / (r ^ 4) * Sy * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.linearization_inverseSpatial_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 0 0 =
      B * D * ((-1 / 2 : ℂ) * s * t ^ 2 + (3 : ℂ) * s * t ^ 2 * r ^ 2 + (-9 / 2 : ℂ) * s * t ^ 2 * r ^ 4 + (2 : ℂ) * s * t ^ 2 * r ^ 6 + (-1 / 2 : ℂ) * s * t ^ 3 + (1 : ℂ) * s * t ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s * t ^ 3 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 2 * t + (3 : ℂ) * s ^ 2 * t * r ^ 2 + (-9 / 2 : ℂ) * s ^ 2 * t * r ^ 4 + (2 : ℂ) * s ^ 2 * t * r ^ 6 + (-1 : ℂ) * s ^ 2 * t ^ 2 + (2 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 2 * t ^ 2 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 2 * t ^ 3 + (1 : ℂ) * s ^ 2 * t ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * t ^ 3 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 * t + (1 : ℂ) * s ^ 3 * t * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 * t * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 * t ^ 2 + (1 : ℂ) * s ^ 3 * t ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 * t ^ 2 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1) ^ 3) * S ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 0 1 =
      (0 : ℂ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 1 0 =
      (0 : ℂ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 1 1 =
      B * D * ((1 / 2 : ℂ) * s * t ^ 2 + (-3 : ℂ) * s * t ^ 2 * r ^ 2 + (9 / 2 : ℂ) * s * t ^ 2 * r ^ 4 + (-2 : ℂ) * s * t ^ 2 * r ^ 6 + (1 / 2 : ℂ) * s * t ^ 3 + (-1 : ℂ) * s * t ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s * t ^ 3 * r ^ 4 + (1 / 2 : ℂ) * s ^ 2 * t + (-3 : ℂ) * s ^ 2 * t * r ^ 2 + (9 / 2 : ℂ) * s ^ 2 * t * r ^ 4 + (-2 : ℂ) * s ^ 2 * t * r ^ 6 + (1 : ℂ) * s ^ 2 * t ^ 2 + (-2 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * t ^ 2 * r ^ 4 + (1 / 2 : ℂ) * s ^ 2 * t ^ 3 + (-1 : ℂ) * s ^ 2 * t ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t ^ 3 * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 * t + (-1 : ℂ) * s ^ 3 * t * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 * t * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 * t ^ 2 + (-1 : ℂ) * s ^ 3 * t ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 * t ^ 2 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1)) * S ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 2 2 =
      B * D * ((2 : ℂ) * t * r ^ 4 + (1 : ℂ) * t ^ 2 * r ^ 2 + (1 : ℂ) * t ^ 3 * r ^ 2 + (2 : ℂ) * s * r ^ 4 + (2 : ℂ) * s * t * r ^ 2 + (1 / 2 : ℂ) * s * t ^ 2 + (1 : ℂ) * s * t ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s * t ^ 3 + (1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t + (1 : ℂ) * s ^ 2 * t * r ^ 2 + (1 : ℂ) * s ^ 2 * t ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t ^ 3 + (1 : ℂ) * s ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 * t + (1 / 2 : ℂ) * s ^ 3 * t ^ 2) / (r ^ 6) * S ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_0_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 0 3 3 =
      B * D * ((2 : ℂ) * t * r ^ 4 + (1 : ℂ) * t ^ 2 * r ^ 2 + (1 : ℂ) * t ^ 3 * r ^ 2 + (2 : ℂ) * s * r ^ 4 + (2 : ℂ) * s * t * r ^ 2 + (1 / 2 : ℂ) * s * t ^ 2 + (1 : ℂ) * s * t ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s * t ^ 3 + (1 : ℂ) * s ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t + (1 : ℂ) * s ^ 2 * t * r ^ 2 + (1 : ℂ) * s ^ 2 * t ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t ^ 3 + (1 : ℂ) * s ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 * t + (1 / 2 : ℂ) * s ^ 3 * t ^ 2) / (r ^ 6) * S ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 0 0 =
      B * D * ((-2 : ℂ) * s * t + (11 : ℂ) * s * t * r ^ 2 + (-24 : ℂ) * s * t * r ^ 4 + (23 : ℂ) * s * t * r ^ 6 + (-8 : ℂ) * s * t * r ^ 8 + (-5 / 2 : ℂ) * s * t ^ 2 + (10 : ℂ) * s * t ^ 2 * r ^ 2 + (-25 / 2 : ℂ) * s * t ^ 2 * r ^ 4 + (5 : ℂ) * s * t ^ 2 * r ^ 6 + (-1 / 2 : ℂ) * s * t ^ 3 + (1 : ℂ) * s * t ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s * t ^ 3 * r ^ 4 + (-5 / 2 : ℂ) * s ^ 2 * t + (10 : ℂ) * s ^ 2 * t * r ^ 2 + (-25 / 2 : ℂ) * s ^ 2 * t * r ^ 4 + (5 : ℂ) * s ^ 2 * t * r ^ 6 + (-3 : ℂ) * s ^ 2 * t ^ 2 + (9 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (-9 : ℂ) * s ^ 2 * t ^ 2 * r ^ 4 + (3 : ℂ) * s ^ 2 * t ^ 2 * r ^ 6 + (-1 / 2 : ℂ) * s ^ 2 * t ^ 3 + (1 : ℂ) * s ^ 2 * t ^ 3 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 2 * t ^ 3 * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 * t + (1 : ℂ) * s ^ 3 * t * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 * t * r ^ 4 + (-1 / 2 : ℂ) * s ^ 3 * t ^ 2 + (1 : ℂ) * s ^ 3 * t ^ 2 * r ^ 2 + (-1 / 2 : ℂ) * s ^ 3 * t ^ 2 * r ^ 4) / (r ^ 5 * (r ^ 2 - 1) ^ 4) * S ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 0 1 =
      (0 : ℂ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 1 0 =
      (0 : ℂ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 1 1 =
      B * D * ((2 : ℂ) * s * t + (-9 : ℂ) * s * t * r ^ 2 + (12 : ℂ) * s * t * r ^ 4 + (-5 : ℂ) * s * t * r ^ 6 + (5 / 2 : ℂ) * s * t ^ 2 + (-8 : ℂ) * s * t ^ 2 * r ^ 2 + (17 / 2 : ℂ) * s * t ^ 2 * r ^ 4 + (-3 : ℂ) * s * t ^ 2 * r ^ 6 + (1 / 2 : ℂ) * s * t ^ 3 + (-1 : ℂ) * s * t ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s * t ^ 3 * r ^ 4 + (5 / 2 : ℂ) * s ^ 2 * t + (-8 : ℂ) * s ^ 2 * t * r ^ 2 + (17 / 2 : ℂ) * s ^ 2 * t * r ^ 4 + (-3 : ℂ) * s ^ 2 * t * r ^ 6 + (3 : ℂ) * s ^ 2 * t ^ 2 + (-7 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (5 : ℂ) * s ^ 2 * t ^ 2 * r ^ 4 + (-1 : ℂ) * s ^ 2 * t ^ 2 * r ^ 6 + (1 / 2 : ℂ) * s ^ 2 * t ^ 3 + (-1 : ℂ) * s ^ 2 * t ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t ^ 3 * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 * t + (-1 : ℂ) * s ^ 3 * t * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 * t * r ^ 4 + (1 / 2 : ℂ) * s ^ 3 * t ^ 2 + (-1 : ℂ) * s ^ 3 * t ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 * t ^ 2 * r ^ 4) / (r ^ 5 * (r ^ 2 - 1) ^ 2) * S ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 2 2 =
      B * D * ((4 : ℂ) * r ^ 4 + (-4 : ℂ) * r ^ 6 + (4 : ℂ) * t * r ^ 2 + (-2 : ℂ) * t * r ^ 4 + (5 : ℂ) * t ^ 2 * r ^ 2 + (-4 : ℂ) * t ^ 2 * r ^ 4 + (1 : ℂ) * t ^ 3 * r ^ 2 + (4 : ℂ) * s * r ^ 2 + (-2 : ℂ) * s * r ^ 4 + (3 : ℂ) * s * t + (-1 : ℂ) * s * t * r ^ 2 + (7 / 2 : ℂ) * s * t ^ 2 + (-2 : ℂ) * s * t ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s * t ^ 3 + (5 : ℂ) * s ^ 2 * r ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 4 + (7 / 2 : ℂ) * s ^ 2 * t + (-2 : ℂ) * s ^ 2 * t * r ^ 2 + (4 : ℂ) * s ^ 2 * t ^ 2 + (-3 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t ^ 3 + (1 : ℂ) * s ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 * t + (1 / 2 : ℂ) * s ^ 3 * t ^ 2) / (r ^ 7 * (r ^ 2 - 1)) * S ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_1_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 1 3 3 =
      B * D * ((4 : ℂ) * r ^ 4 + (-4 : ℂ) * r ^ 6 + (4 : ℂ) * t * r ^ 2 + (-2 : ℂ) * t * r ^ 4 + (5 : ℂ) * t ^ 2 * r ^ 2 + (-4 : ℂ) * t ^ 2 * r ^ 4 + (1 : ℂ) * t ^ 3 * r ^ 2 + (4 : ℂ) * s * r ^ 2 + (-2 : ℂ) * s * r ^ 4 + (3 : ℂ) * s * t + (-1 : ℂ) * s * t * r ^ 2 + (7 / 2 : ℂ) * s * t ^ 2 + (-2 : ℂ) * s * t ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s * t ^ 3 + (5 : ℂ) * s ^ 2 * r ^ 2 + (-4 : ℂ) * s ^ 2 * r ^ 4 + (7 / 2 : ℂ) * s ^ 2 * t + (-2 : ℂ) * s ^ 2 * t * r ^ 2 + (4 : ℂ) * s ^ 2 * t ^ 2 + (-3 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (1 / 2 : ℂ) * s ^ 2 * t ^ 3 + (1 : ℂ) * s ^ 3 * r ^ 2 + (1 / 2 : ℂ) * s ^ 3 * t + (1 / 2 : ℂ) * s ^ 3 * t ^ 2) / (r ^ 7 * (r ^ 2 - 1)) * S ^ 2 * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 0 0 =
      B * D * ((-1 : ℂ) * s * t + (6 : ℂ) * s * t * r ^ 2 + (-9 : ℂ) * s * t * r ^ 4 + (4 : ℂ) * s * t * r ^ 6 + (-1 : ℂ) * s * t ^ 2 + (2 : ℂ) * s * t ^ 2 * r ^ 2 + (-1 : ℂ) * s * t ^ 2 * r ^ 4 + (-1 : ℂ) * s ^ 2 * t + (2 : ℂ) * s ^ 2 * t * r ^ 2 + (-1 : ℂ) * s ^ 2 * t * r ^ 4 + (-1 : ℂ) * s ^ 2 * t ^ 2 + (2 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 2 * t ^ 2 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1) ^ 3) * S * Sx := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 0 1 =
      (0 : ℂ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 1 0 =
      (0 : ℂ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 1 1 =
      B * D * ((1 : ℂ) * s * t + (-6 : ℂ) * s * t * r ^ 2 + (9 : ℂ) * s * t * r ^ 4 + (-4 : ℂ) * s * t * r ^ 6 + (1 : ℂ) * s * t ^ 2 + (-2 : ℂ) * s * t ^ 2 * r ^ 2 + (1 : ℂ) * s * t ^ 2 * r ^ 4 + (1 : ℂ) * s ^ 2 * t + (-2 : ℂ) * s ^ 2 * t * r ^ 2 + (1 : ℂ) * s ^ 2 * t * r ^ 4 + (1 : ℂ) * s ^ 2 * t ^ 2 + (-2 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * t ^ 2 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1)) * S * Sx := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 2 2 =
      B * D * ((4 : ℂ) * r ^ 4 + (2 : ℂ) * t * r ^ 2 + (2 : ℂ) * t ^ 2 * r ^ 2 + (2 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * t + (1 : ℂ) * s * t ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * t + (1 : ℂ) * s ^ 2 * t ^ 2) / (r ^ 6) * S * Sx * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_2_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 2 3 3 =
      B * D * ((4 : ℂ) * r ^ 4 + (2 : ℂ) * t * r ^ 2 + (2 : ℂ) * t ^ 2 * r ^ 2 + (2 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * t + (1 : ℂ) * s * t ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * t + (1 : ℂ) * s ^ 2 * t ^ 2) / (r ^ 6) * S * Sx * y ^ 2 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_0_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 0 0 =
      B * D * ((-1 : ℂ) * s * t + (6 : ℂ) * s * t * r ^ 2 + (-9 : ℂ) * s * t * r ^ 4 + (4 : ℂ) * s * t * r ^ 6 + (-1 : ℂ) * s * t ^ 2 + (2 : ℂ) * s * t ^ 2 * r ^ 2 + (-1 : ℂ) * s * t ^ 2 * r ^ 4 + (-1 : ℂ) * s ^ 2 * t + (2 : ℂ) * s ^ 2 * t * r ^ 2 + (-1 : ℂ) * s ^ 2 * t * r ^ 4 + (-1 : ℂ) * s ^ 2 * t ^ 2 + (2 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (-1 : ℂ) * s ^ 2 * t ^ 2 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1) ^ 3) * S * Sy := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_0_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 0 1 =
      (0 : ℂ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_0_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 0 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_0_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 0 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 1 0 =
      (0 : ℂ) := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_1_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 1 1 =
      B * D * ((1 : ℂ) * s * t + (-6 : ℂ) * s * t * r ^ 2 + (9 : ℂ) * s * t * r ^ 4 + (-4 : ℂ) * s * t * r ^ 6 + (1 : ℂ) * s * t ^ 2 + (-2 : ℂ) * s * t ^ 2 * r ^ 2 + (1 : ℂ) * s * t ^ 2 * r ^ 4 + (1 : ℂ) * s ^ 2 * t + (-2 : ℂ) * s ^ 2 * t * r ^ 2 + (1 : ℂ) * s ^ 2 * t * r ^ 4 + (1 : ℂ) * s ^ 2 * t ^ 2 + (-2 : ℂ) * s ^ 2 * t ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * t ^ 2 * r ^ 4) / (r ^ 4 * (r ^ 2 - 1)) * S * Sy := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_1_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 1 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_1_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 1 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 2 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 2 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_2_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 2 2 =
      B * D * ((4 : ℂ) * r ^ 4 + (2 : ℂ) * t * r ^ 2 + (2 : ℂ) * t ^ 2 * r ^ 2 + (2 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * t + (1 : ℂ) * s * t ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * t + (1 : ℂ) * s ^ 2 * t ^ 2) / (r ^ 6) * S * Sy * y ^ 2 + B * D * ((4 : ℂ) * r ^ 4 + (2 : ℂ) * t * r ^ 2 + (2 : ℂ) * t ^ 2 * r ^ 2 + (2 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * t + (1 : ℂ) * s * t ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * t + (1 : ℂ) * s ^ 2 * t ^ 2) / (r ^ 6) * S ^ 2 * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_2_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 2 3 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 3 0 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 3 1 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 3 2 = 0 := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  all_goals (try generalize hF : r ^ 2 - 1 = F)
  all_goals (try ring_nf)

@[bmMixedTable] theorem scalarJet_mixedInverseSpatial_3_3_3 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ 2 - 1 ≠ 0) :
    MixedQuadratic.inverseSpatial (D4BMBackground.jet r y) (scalarJet s r y B S Sx Sy Sxx Sxy) (scalarJet t r y D S Sx Sy Sxx Sxy) 3 3 3 =
      B * D * ((4 : ℂ) * r ^ 4 + (2 : ℂ) * t * r ^ 2 + (2 : ℂ) * t ^ 2 * r ^ 2 + (2 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * t + (1 : ℂ) * s * t ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * t + (1 : ℂ) * s ^ 2 * t ^ 2) / (r ^ 6) * S * Sy * y ^ 2 + B * D * ((4 : ℂ) * r ^ 4 + (2 : ℂ) * t * r ^ 2 + (2 : ℂ) * t ^ 2 * r ^ 2 + (2 : ℂ) * s * r ^ 2 + (1 : ℂ) * s * t + (1 : ℂ) * s * t ^ 2 + (2 : ℂ) * s ^ 2 * r ^ 2 + (1 : ℂ) * s ^ 2 * t + (1 : ℂ) * s ^ 2 * t ^ 2) / (r ^ 6) * S ^ 2 * y := by
  have hd := D4BMBackground.jet_isDiagonalJet r y hr hy hf
  rw [hd.mixedQuadratic_inverseSpatial_apply]
  simp only [hd.mixedQuadratic_inverse_apply, hd.linearization_inverse_apply]
  all_goals (try simp only [Fin.sum_univ_four, Fin.isValue, Fin.reduceEq, if_true, if_false])
  all_goals (try simp (disch := assumption) only [bmJetEntry, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, zero_div, div_zero, mul_neg, neg_mul, neg_neg])
  all_goals (try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div])
  generalize hF : r ^ 2 - 1 = F
  have hF0 : F ≠ 0 := hF ▸ hf
  apply mul_left_cancel₀ (show r ^ 9 * r⁻¹ * y ^ 9 * y⁻¹ * F ^ 8 * F⁻¹ ≠ 0 from
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hr)
      (inv_ne_zero hr)) (pow_ne_zero _ hy)) (inv_ne_zero hy)) (pow_ne_zero _ hF0))
      (inv_ne_zero hF0))
  ring_nf
  all_goals (try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow hr, InversePowerCancellation.inv_mul_self hr, InversePowerCancellation.inv_pow_mul hr, InversePowerCancellation.inv_pow_mul_pow hr, InversePowerCancellation.inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_mul_pow hr, InversePowerCancellation.mul_inv_mul_self hr, InversePowerCancellation.mul_inv_pow hr, InversePowerCancellation.mul_inv_pow_mul hr, InversePowerCancellation.mul_inv_pow_mul_pow hr, InversePowerCancellation.mul_inv_pow_mul_pow' hr, InversePowerCancellation.mul_inv_self hr, InversePowerCancellation.mul_mul_inv_pow hr, InversePowerCancellation.mul_mul_inv_self hr, InversePowerCancellation.mul_pow_mul_inv hr, InversePowerCancellation.mul_pow_mul_inv_pow hr, InversePowerCancellation.mul_pow_mul_inv_pow' hr, InversePowerCancellation.pow_mul_inv hr, InversePowerCancellation.pow_mul_inv_pow hr, InversePowerCancellation.pow_mul_inv_pow' hr, InversePowerCancellation.inv_mul_pow hy, InversePowerCancellation.inv_mul_self hy, InversePowerCancellation.inv_pow_mul hy, InversePowerCancellation.inv_pow_mul_pow hy, InversePowerCancellation.inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_mul_pow hy, InversePowerCancellation.mul_inv_mul_self hy, InversePowerCancellation.mul_inv_pow hy, InversePowerCancellation.mul_inv_pow_mul hy, InversePowerCancellation.mul_inv_pow_mul_pow hy, InversePowerCancellation.mul_inv_pow_mul_pow' hy, InversePowerCancellation.mul_inv_self hy, InversePowerCancellation.mul_mul_inv_pow hy, InversePowerCancellation.mul_mul_inv_self hy, InversePowerCancellation.mul_pow_mul_inv hy, InversePowerCancellation.mul_pow_mul_inv_pow hy, InversePowerCancellation.mul_pow_mul_inv_pow' hy, InversePowerCancellation.pow_mul_inv hy, InversePowerCancellation.pow_mul_inv_pow hy, InversePowerCancellation.pow_mul_inv_pow' hy, InversePowerCancellation.inv_mul_pow hF0, InversePowerCancellation.inv_mul_self hF0, InversePowerCancellation.inv_pow_mul hF0, InversePowerCancellation.inv_pow_mul_pow hF0, InversePowerCancellation.inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_mul_pow hF0, InversePowerCancellation.mul_inv_mul_self hF0, InversePowerCancellation.mul_inv_pow hF0, InversePowerCancellation.mul_inv_pow_mul hF0, InversePowerCancellation.mul_inv_pow_mul_pow hF0, InversePowerCancellation.mul_inv_pow_mul_pow' hF0, InversePowerCancellation.mul_inv_self hF0, InversePowerCancellation.mul_mul_inv_pow hF0, InversePowerCancellation.mul_mul_inv_self hF0, InversePowerCancellation.mul_pow_mul_inv hF0, InversePowerCancellation.mul_pow_mul_inv_pow hF0, InversePowerCancellation.mul_pow_mul_inv_pow' hF0, InversePowerCancellation.pow_mul_inv hF0, InversePowerCancellation.pow_mul_inv_pow hF0, InversePowerCancellation.pow_mul_inv_pow' hF0])
  all_goals (try subst hF)
  all_goals (try ring)

end
end RHTower.D4BMScalarLinearEquation
