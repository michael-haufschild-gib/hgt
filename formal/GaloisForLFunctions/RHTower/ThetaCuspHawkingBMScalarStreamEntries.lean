import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamJet
import GaloisForLFunctions.HTGeometry.InversePowerCancellation

/-!
# Entry table of the scalar-stream metric jet

Every entry of the Kodama–Ishibashi-gauge scalar-stream metric jet in a fixed normal form
(polynomial in the free radial and angular jet symbols, `r`, `y⁻¹`); off-block entries vanish.
All entries carry the `bmStreamEntry` simp attribute.
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry D4BMScalarLinearEquation
noncomputable section
variable {w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy : ℂ}

@[bmStreamEntry] theorem metricJet_metric_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_metric_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_metric_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_metric_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_metric_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_metric_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_metric_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_metric_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_metric_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_metric_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_0_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_0_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_0_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_0_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_0_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_0_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_0_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_0_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_0_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_0_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_1_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_1_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_1_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_1_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_1_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_1_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_1_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_1_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_1_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_1_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_2_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_2_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_2_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_2_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_2_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_2_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_2_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_2_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_2_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_2_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_3_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_3_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_3_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_3_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_3_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_3_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_3_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_3_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_3_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_first_3_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_0_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_0_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_0_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_0_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_0_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_0_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_0_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_0_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_0_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_0_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_1_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_1_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_1_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_1_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_1_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_1_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_1_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_1_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_1_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_1_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_2_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_2_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_2_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_2_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_2_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_2_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_2_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_2_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_2_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_2_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_3_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_3_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_3_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_3_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_3_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_3_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_3_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_3_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_3_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_0_3_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_0_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_0_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_0_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_0_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_0_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_0_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_0_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_0_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_0_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_0_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_1_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_1_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_1_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_1_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_1_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_1_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_1_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_1_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_1_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_1_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_2_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_2_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_2_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_2_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_2_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_2_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_2_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_2_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_2_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_2_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_3_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_3_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_3_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_3_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_3_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_3_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_3_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_3_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_3_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_1_3_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_0_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_0_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_0_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_0_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_0_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_0_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_0_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_0_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_0_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_0_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_1_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_1_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_1_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_1_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_1_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_1_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_1_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_1_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_1_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_1_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_2_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_2_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_2_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_2_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_2_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_2_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_2_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_2_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_2_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_2_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_3_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_3_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_3_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_3_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_3_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_3_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_3_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_3_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_3_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_2_3_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_0_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_0_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_0_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_0_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_0_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_0_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_0_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_0_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_0_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_0_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_1_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_1_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_1_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_1_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_1_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_1_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_1_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_1_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_1_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_1_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_2_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_2_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_2_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_2_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_2_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_2_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_2_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_2_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_2_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_2_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_3_0_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 0 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_3_0_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 0 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_3_1_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 1 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_3_1_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 1 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_3_2_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 2 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_3_2_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 2 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_3_2_3 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 2 3 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_3_3_0 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 3 0 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_3_3_1 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 3 1 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_second_3_3_3_2 : (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 3 2 = 0 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem metricJet_metric_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 0 0 =
      F0 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_metric_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 0 1 =
      F1 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_metric_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 1 0 =
      F1 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_metric_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 1 1 =
      F2 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_metric_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * P * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_metric_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).metric 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * P * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_0_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 0 0 =
      w * F0 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_0_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 0 1 =
      w * F1 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_0_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 1 0 =
      w * F1 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_0_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 1 1 =
      w * F2 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w * P * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 0 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w * P * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_1_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 0 0 =
      F01 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_1_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 0 1 =
      F11 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_1_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 1 0 =
      F11 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_1_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 1 1 =
      F21 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 2 2 =
      r * y⁻¹ ^ (2 : ℕ) * H * P * 4 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * P * H1 * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 1 3 3 =
      r * y⁻¹ ^ (2 : ℕ) * H * P * 4 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * P * H1 * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_2_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 0 0 =
      F0 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_2_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 0 1 =
      F1 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_2_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 1 0 =
      F1 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_2_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 1 1 =
      F2 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Px * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 2 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Px * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_3_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 0 0 =
      F0 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_3_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 0 1 =
      F1 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_3_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 1 0 =
      F1 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_3_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 1 1 =
      F2 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Py * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * P * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_first_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).first 3 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Py * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * P * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_0_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 0 0 =
      w ^ (2 : ℕ) * F0 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_0_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 0 1 =
      w ^ (2 : ℕ) * F1 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_0_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 1 0 =
      w ^ (2 : ℕ) * F1 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_0_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 1 1 =
      w ^ (2 : ℕ) * F2 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w ^ (2 : ℕ) * P * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 0 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w ^ (2 : ℕ) * P * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_1_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 0 0 =
      w * F01 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_1_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 0 1 =
      w * F11 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_1_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 1 0 =
      w * F11 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_1_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 1 1 =
      w * F21 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 2 2 =
      r * y⁻¹ ^ (2 : ℕ) * H * w * P * 4 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * w * P * H1 * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 1 3 3 =
      r * y⁻¹ ^ (2 : ℕ) * H * w * P * 4 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * w * P * H1 * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_2_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 0 0 =
      w * F0 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_2_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 0 1 =
      w * F1 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_2_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 1 0 =
      w * F1 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_2_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 1 1 =
      w * F2 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w * Px * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 2 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w * Px * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_3_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 0 0 =
      w * F0 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_3_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 0 1 =
      w * F1 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_3_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 1 0 =
      w * F1 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_3_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 1 1 =
      w * F2 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w * Py * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * w * P * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_0_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 0 3 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w * Py * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * w * P * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_0_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 0 0 =
      w * F01 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_0_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 0 1 =
      w * F11 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_0_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 1 0 =
      w * F11 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_0_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 1 1 =
      w * F21 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 2 2 =
      r * y⁻¹ ^ (2 : ℕ) * H * w * P * 4 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * w * P * H1 * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 0 3 3 =
      r * y⁻¹ ^ (2 : ℕ) * H * w * P * 4 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * w * P * H1 * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_1_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 0 0 =
      F02 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_1_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 0 1 =
      F12 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_1_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 1 0 =
      F12 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_1_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 1 1 =
      F22 * P := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 2 2 =
      r * y⁻¹ ^ (2 : ℕ) * H1 * P * 8 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * P * H2 * 2 + y⁻¹ ^ (2 : ℕ) * P * H * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 1 3 3 =
      r * y⁻¹ ^ (2 : ℕ) * H1 * P * 8 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * P * H2 * 2 + y⁻¹ ^ (2 : ℕ) * P * H * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_2_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 0 0 =
      F01 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_2_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 0 1 =
      F11 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_2_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 1 0 =
      F11 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_2_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 1 1 =
      F21 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 2 2 =
      r * y⁻¹ ^ (2 : ℕ) * H * Px * 4 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Px * H1 * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 2 3 3 =
      r * y⁻¹ ^ (2 : ℕ) * H * Px * 4 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Px * H1 * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_3_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 0 0 =
      F01 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_3_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 0 1 =
      F11 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_3_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 1 0 =
      F11 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_3_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 1 1 =
      F21 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 2 2 =
      r * y⁻¹ ^ (2 : ℕ) * H * Py * 4 - r * y⁻¹ ^ (3 : ℕ) * H * P * 8 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Py * H1 * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * P * H1 * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_1_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 1 3 3 3 =
      r * y⁻¹ ^ (2 : ℕ) * H * Py * 4 - r * y⁻¹ ^ (3 : ℕ) * H * P * 8 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Py * H1 * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * P * H1 * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_0_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 0 0 =
      w * F0 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_0_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 0 1 =
      w * F1 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_0_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 1 0 =
      w * F1 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_0_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 1 1 =
      w * F2 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w * Px * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 0 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w * Px * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_1_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 0 0 =
      F01 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_1_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 0 1 =
      F11 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_1_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 1 0 =
      F11 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_1_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 1 1 =
      F21 * Px := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 2 2 =
      r * y⁻¹ ^ (2 : ℕ) * H * Px * 4 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Px * H1 * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 1 3 3 =
      r * y⁻¹ ^ (2 : ℕ) * H * Px * 4 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Px * H1 * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_2_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 0 0 =
      F0 * Pxx := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_2_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 0 1 =
      F1 * Pxx := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_2_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 1 0 =
      F1 * Pxx := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_2_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 1 1 =
      F2 * Pxx := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Pxx * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 2 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Pxx * 2 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_3_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 0 0 =
      F0 * Pxy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_3_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 0 1 =
      F1 * Pxy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_3_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 1 0 =
      F1 * Pxy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_3_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 1 1 =
      F2 * Pxy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Pxy * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * Px * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_2_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 2 3 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Pxy * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * Px * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_0_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 0 0 =
      w * F0 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_0_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 0 1 =
      w * F1 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_0_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 1 0 =
      w * F1 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_0_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 1 1 =
      w * F2 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w * Py * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * w * P * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 0 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * w * Py * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * w * P * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_1_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 0 0 =
      F01 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_1_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 0 1 =
      F11 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_1_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 1 0 =
      F11 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_1_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 1 1 =
      F21 * Py := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 2 2 =
      r * y⁻¹ ^ (2 : ℕ) * H * Py * 4 - r * y⁻¹ ^ (3 : ℕ) * H * P * 8 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Py * H1 * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * P * H1 * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 1 3 3 =
      r * y⁻¹ ^ (2 : ℕ) * H * Py * 4 - r * y⁻¹ ^ (3 : ℕ) * H * P * 8 + r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Py * H1 * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * P * H1 * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_2_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 0 0 =
      F0 * Pxy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_2_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 0 1 =
      F1 * Pxy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_2_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 1 0 =
      F1 * Pxy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_2_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 1 1 =
      F2 * Pxy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Pxy * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * Px * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 2 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Pxy * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * Px * 4 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_3_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 0 0 =
      F0 * Pyy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_3_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 0 1 =
      F1 * Pyy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_3_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 1 0 =
      F1 * Pyy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_3_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 1 1 =
      F2 * Pyy := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 2 2 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Pyy * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * Py * 8 + r ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * H * P * 12 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem metricJet_second_3_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (metricJet w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy).second 3 3 3 3 =
      r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * H * Pyy * 2 - r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * H * Py * 8 + r ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * H * P * 12 := by
  simp only [metricJet, orbitJet, angularJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

end
end RHTower.D4BMScalarStream
