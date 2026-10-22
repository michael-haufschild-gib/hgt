import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarStreamEinstein

/-!
# Lower-triangle components of the linearized operator on the scalar stream

The six components `(i, j)` with `i > j` of the linearized cosmological Einstein operator on the
harmonic scalar-stream jet, proved by the same evaluation as their transposes, and the resulting
symmetry statements `metricJet_cosmological_symm_i_j`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet
noncomputable section
variable {w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy : ℂ}

theorem metricJet_cosmological_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 1 0 =
      ((-1 / 2 : ℂ)) / (r ^ (2 : ℕ)) * F1 * Pxx * y ^ (2 : ℕ) +
        ((-1 / 2 : ℂ)) / (r ^ (2 : ℕ)) * F1 * Pyy * y ^ (2 : ℕ) +
        ((-1 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r) * F2 * P * w +
        ((2 : ℂ)) / (r * (r ^ (2 : ℕ) - 1)) * H * P * w +
        ((-2 : ℂ)) * H1 * P * w := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_1_0 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem metricJet_cosmological_symm_1_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 1 0 =
      Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 0 1 := by
  rw [metricJet_cosmological_1_0 hr hy hf, metricJet_cosmological_0_1 hr hy hf]

theorem metricJet_cosmological_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 2 0 =
      ((1 : ℂ) * r) * F1 * Px +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ (2 : ℕ)) * F11 * Px +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ (2 : ℕ)) * F2 * Px * w +
        ((-1 : ℂ)) * H * Px * w := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_2_0 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem metricJet_cosmological_symm_2_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 2 0 =
      Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 0 2 := by
  rw [metricJet_cosmological_2_0 hr hy hf, metricJet_cosmological_0_2 hr hy hf]

theorem metricJet_cosmological_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 3 0 =
      ((1 : ℂ) * r) * F1 * Py +
        ((-1 / 2 : ℂ) + (1 / 2 : ℂ) * r ^ (2 : ℕ)) * F11 * Py +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ (2 : ℕ)) * F2 * Py * w +
        ((-1 : ℂ)) * H * Py * w := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_3_0 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem metricJet_cosmological_symm_3_0 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 3 0 =
      Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 0 3 := by
  rw [metricJet_cosmological_3_0 hr hy hf, metricJet_cosmological_0_3 hr hy hf]

theorem metricJet_cosmological_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 2 1 =
      ((1 / 2 : ℂ) + (-1 : ℂ) * r ^ (2 : ℕ)) / (r * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * F0 * Px +
        ((1 / 2 : ℂ)) / ((r ^ (2 : ℕ) - 1)) * F01 * Px +
        ((-1 / 2 : ℂ)) / ((r ^ (2 : ℕ) - 1)) * F1 * Px * w +
        ((-1 / 2 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r) * F2 * Px +
        ((-1 : ℂ)) * H1 * Px := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_2_1 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem metricJet_cosmological_symm_2_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 2 1 =
      Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 1 2 := by
  rw [metricJet_cosmological_2_1 hr hy hf, metricJet_cosmological_1_2 hr hy hf]

theorem metricJet_cosmological_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 3 1 =
      ((1 / 2 : ℂ) + (-1 : ℂ) * r ^ (2 : ℕ)) / (r * (r ^ (2 : ℕ) - 1) ^ (2 : ℕ)) * F0 * Py +
        ((1 / 2 : ℂ)) / ((r ^ (2 : ℕ) - 1)) * F01 * Py +
        ((-1 / 2 : ℂ)) / ((r ^ (2 : ℕ) - 1)) * F1 * Py * w +
        ((-1 / 2 : ℂ) + (1 : ℂ) * r ^ (2 : ℕ)) / (r) * F2 * Py +
        ((-1 : ℂ)) * H1 * Py := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_3_1 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem metricJet_cosmological_symm_3_1 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 3 1 =
      Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 1 3 := by
  rw [metricJet_cosmological_3_1 hr hy hf, metricJet_cosmological_1_3 hr hy hf]

theorem metricJet_cosmological_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 3 2 =
      ((1 / 2 : ℂ)) / ((r ^ (2 : ℕ) - 1)) * F0 * Px * y⁻¹ +
        ((1 / 2 : ℂ)) / ((r ^ (2 : ℕ) - 1)) * F0 * Pxy +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ (2 : ℕ)) * F2 * Px * y⁻¹ +
        ((1 / 2 : ℂ) + (-1 / 2 : ℂ) * r ^ (2 : ℕ)) * F2 * Pxy := by
  simp only [Linearization.cosmological, Linearization.einstein, metricJet_linRicci_3_2 hr hy hf,
    metricJet_linScalar hr hy hf, D4BMBackground.jet_scalar r y hr hy hf]
  simp (disch := assumption) only [bmStreamEntry, bmJetEntry, D4BMBackground.jet, D4BMBackground.metric,
    Matrix.diagonal_apply, Fin.isValue, Fin.reduceEq, if_true, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  field_simp
  ring

theorem metricJet_cosmological_symm_3_2 (hr : r ≠ 0) (hy : y ≠ 0) (hf : r ^ (2 : ℕ) - 1 ≠ 0) :
    Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 3 2 =
      Linearization.cosmological (D4BMBackground.jet r y) (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy) (-3) 2 3 := by
  rw [metricJet_cosmological_3_2 hr hy hf, metricJet_cosmological_2_3 hr hy hf]

end
end RHTower.D4BMScalarStream
