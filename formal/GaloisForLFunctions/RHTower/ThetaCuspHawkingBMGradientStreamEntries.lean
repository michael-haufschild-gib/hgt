import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGradientStreamJet
import GaloisForLFunctions.HTGeometry.InversePowerCancellation

/-!
# Entry table of the gradient-tensor stream jet

Every entry of the gradient-tensor stream metric jet in a fixed normal form (polynomial in the
radial jet `G`, the angular jet of `S`, `s`, `r`, `y⁻¹`); entries outside the angular block vanish.
All entries carry the `bmStreamEntry` simp attribute.
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry D4BMScalarLinearEquation
noncomputable section
variable {w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ}

@[bmStreamEntry] theorem gradientJet_metric_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_0_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_1_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_2_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_first_3_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_0_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_1_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_2_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_0_3_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_0_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_1_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_2_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_1_3_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_0_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_1_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_2_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_2_3_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_0_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_1_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_2_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_0_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 0 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_0_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 0 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_0_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 0 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_0_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 0 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_1_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 1 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_1_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 1 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_1_2 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 1 2 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_1_3 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 1 3 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_2_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 2 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_2_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 2 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_3_0 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 3 0 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_second_3_3_3_1 : (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 3 1 = 0 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]

@[bmStreamEntry] theorem gradientJet_metric_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 2 2 =
      r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) - r ^ (2 : ℕ) * G * Sy ^ (2 : ℕ) := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_metric_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 2 3 =
      r ^ (2 : ℕ) * G * Sx * Sy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_metric_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 3 2 =
      r ^ (2 : ℕ) * G * Sx * Sy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_metric_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).metric 3 3 =
      r ^ (2 : ℕ) * G * Sy ^ (2 : ℕ) - r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 2 2 =
      r ^ (2 : ℕ) * G * w * Sx ^ (2 : ℕ) - r ^ (2 : ℕ) * G * w * Sy ^ (2 : ℕ) := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_0_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 2 3 =
      r ^ (2 : ℕ) * G * w * Sx * Sy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_0_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 3 2 =
      r ^ (2 : ℕ) * G * w * Sx * Sy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 0 3 3 =
      r ^ (2 : ℕ) * G * w * Sy ^ (2 : ℕ) - r ^ (2 : ℕ) * G * w * Sx ^ (2 : ℕ) := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 2 2 =
      r * G * Sx ^ (2 : ℕ) * 2 - r * G * Sy ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * Sx ^ (2 : ℕ) * G1 - r ^ (2 : ℕ) * Sy ^ (2 : ℕ) * G1 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_1_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 2 3 =
      r * G * Sx * Sy * 4 + r ^ (2 : ℕ) * Sx * Sy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_1_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 3 2 =
      r * G * Sx * Sy * 4 + r ^ (2 : ℕ) * Sx * Sy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 1 3 3 =
      r * G * Sy ^ (2 : ℕ) * 2 - r * G * Sx ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * Sy ^ (2 : ℕ) * G1 - r ^ (2 : ℕ) * Sx ^ (2 : ℕ) * G1 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 2 2 =
      r ^ (2 : ℕ) * G * Sx * Sxx * 2 - r ^ (2 : ℕ) * G * Sy * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_2_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 2 3 =
      r ^ (2 : ℕ) * G * Sx * Sxy * 2 + r ^ (2 : ℕ) * G * Sy * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_2_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 3 2 =
      r ^ (2 : ℕ) * G * Sx * Sxy * 2 + r ^ (2 : ℕ) * G * Sy * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 2 3 3 =
      r ^ (2 : ℕ) * G * Sy * Sxy * 2 - r ^ (2 : ℕ) * G * Sx * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 2 2 =
      r ^ (2 : ℕ) * G * Sx * Sxy * 2 - r ^ (2 : ℕ) * G * Sy * s * S * y⁻¹ ^ (2 : ℕ) * 6 - r ^ (2 : ℕ) * G * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * Sy * S * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * Sy * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_3_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 2 3 =
      r ^ (2 : ℕ) * G * Sx * s * S * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sx * S * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * Sx * Sxx * 2 + r ^ (2 : ℕ) * G * Sy * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_3_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 3 2 =
      r ^ (2 : ℕ) * G * Sx * s * S * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sx * S * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * Sx * Sxx * 2 + r ^ (2 : ℕ) * G * Sy * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_first_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).first 3 3 3 =
      r ^ (2 : ℕ) * G * Sy * s * S * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sy * S * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * Sy * Sxx * 2 - r ^ (2 : ℕ) * G * Sx * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 2 2 =
      r ^ (2 : ℕ) * G * w ^ (2 : ℕ) * Sx ^ (2 : ℕ) - r ^ (2 : ℕ) * G * w ^ (2 : ℕ) * Sy ^ (2 : ℕ) := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_0_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 2 3 =
      r ^ (2 : ℕ) * G * w ^ (2 : ℕ) * Sx * Sy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_0_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 3 2 =
      r ^ (2 : ℕ) * G * w ^ (2 : ℕ) * Sx * Sy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 0 3 3 =
      r ^ (2 : ℕ) * G * w ^ (2 : ℕ) * Sy ^ (2 : ℕ) - r ^ (2 : ℕ) * G * w ^ (2 : ℕ) * Sx ^ (2 : ℕ) := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 2 2 =
      r * G * w * Sx ^ (2 : ℕ) * 2 - r * G * w * Sy ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * w * Sx ^ (2 : ℕ) * G1 - r ^ (2 : ℕ) * w * Sy ^ (2 : ℕ) * G1 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_1_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 2 3 =
      r * G * w * Sx * Sy * 4 + r ^ (2 : ℕ) * w * Sx * Sy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_1_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 3 2 =
      r * G * w * Sx * Sy * 4 + r ^ (2 : ℕ) * w * Sx * Sy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 1 3 3 =
      r * G * w * Sy ^ (2 : ℕ) * 2 - r * G * w * Sx ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * w * Sy ^ (2 : ℕ) * G1 - r ^ (2 : ℕ) * w * Sx ^ (2 : ℕ) * G1 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 2 2 =
      r ^ (2 : ℕ) * G * w * Sx * Sxx * 2 - r ^ (2 : ℕ) * G * w * Sy * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_2_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 2 3 =
      r ^ (2 : ℕ) * G * w * Sx * Sxy * 2 + r ^ (2 : ℕ) * G * w * Sy * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_2_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 3 2 =
      r ^ (2 : ℕ) * G * w * Sx * Sxy * 2 + r ^ (2 : ℕ) * G * w * Sy * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 2 3 3 =
      r ^ (2 : ℕ) * G * w * Sy * Sxy * 2 - r ^ (2 : ℕ) * G * w * Sx * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 2 2 =
      r ^ (2 : ℕ) * G * w * Sx * Sxy * 2 - r ^ (2 : ℕ) * G * w * Sy * s * S * y⁻¹ ^ (2 : ℕ) * 6 - r ^ (2 : ℕ) * G * w * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * w * Sy * S * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * w * Sy * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_3_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 2 3 =
      r ^ (2 : ℕ) * G * w * Sx * s * S * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * w * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * w * Sx * S * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * w * Sx * Sxx * 2 + r ^ (2 : ℕ) * G * w * Sy * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_3_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 3 2 =
      r ^ (2 : ℕ) * G * w * Sx * s * S * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * w * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * w * Sx * S * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * w * Sx * Sxx * 2 + r ^ (2 : ℕ) * G * w * Sy * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_0_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 0 3 3 3 =
      r ^ (2 : ℕ) * G * w * Sy * s * S * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * w * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * w * Sy * S * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * w * Sy * Sxx * 2 - r ^ (2 : ℕ) * G * w * Sx * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 2 2 =
      r * G * w * Sx ^ (2 : ℕ) * 2 - r * G * w * Sy ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * w * Sx ^ (2 : ℕ) * G1 - r ^ (2 : ℕ) * w * Sy ^ (2 : ℕ) * G1 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_0_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 2 3 =
      r * G * w * Sx * Sy * 4 + r ^ (2 : ℕ) * w * Sx * Sy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_0_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 3 2 =
      r * G * w * Sx * Sy * 4 + r ^ (2 : ℕ) * w * Sx * Sy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 0 3 3 =
      r * G * w * Sy ^ (2 : ℕ) * 2 - r * G * w * Sx ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * w * Sy ^ (2 : ℕ) * G1 - r ^ (2 : ℕ) * w * Sx ^ (2 : ℕ) * G1 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 2 2 =
      r * G1 * Sx ^ (2 : ℕ) * 4 - r * G1 * Sy ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * Sx ^ (2 : ℕ) * G2 - r ^ (2 : ℕ) * Sy ^ (2 : ℕ) * G2 + Sx ^ (2 : ℕ) * G * 2 - Sy ^ (2 : ℕ) * G * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_1_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 2 3 =
      r * G1 * Sx * Sy * 8 + r ^ (2 : ℕ) * Sx * Sy * G2 * 2 + Sx * Sy * G * 4 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_1_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 3 2 =
      r * G1 * Sx * Sy * 8 + r ^ (2 : ℕ) * Sx * Sy * G2 * 2 + Sx * Sy * G * 4 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 1 3 3 =
      r * G1 * Sy ^ (2 : ℕ) * 4 - r * G1 * Sx ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * Sy ^ (2 : ℕ) * G2 - r ^ (2 : ℕ) * Sx ^ (2 : ℕ) * G2 + Sy ^ (2 : ℕ) * G * 2 - Sx ^ (2 : ℕ) * G * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 2 2 =
      r * G * Sx * Sxx * 4 - r * G * Sy * Sxy * 4 + r ^ (2 : ℕ) * Sx * Sxx * G1 * 2 - r ^ (2 : ℕ) * Sy * Sxy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_2_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 2 3 =
      r * G * Sx * Sxy * 4 + r * G * Sy * Sxx * 4 + r ^ (2 : ℕ) * Sx * Sxy * G1 * 2 + r ^ (2 : ℕ) * Sy * Sxx * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_2_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 3 2 =
      r * G * Sx * Sxy * 4 + r * G * Sy * Sxx * 4 + r ^ (2 : ℕ) * Sx * Sxy * G1 * 2 + r ^ (2 : ℕ) * Sy * Sxx * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 2 3 3 =
      r * G * Sy * Sxy * 4 - r * G * Sx * Sxx * 4 + r ^ (2 : ℕ) * Sy * Sxy * G1 * 2 - r ^ (2 : ℕ) * Sx * Sxx * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 2 2 =
      r * G * Sx * Sxy * 4 - r * G * Sy * s * S * y⁻¹ ^ (2 : ℕ) * 12 - r * G * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 4 - r * G * Sy * S * y⁻¹ ^ (2 : ℕ) * 8 + r * G * Sy * Sxx * 4 + r ^ (2 : ℕ) * Sx * Sxy * G1 * 2 - r ^ (2 : ℕ) * Sy * s * S * y⁻¹ ^ (2 : ℕ) * G1 * 6 - r ^ (2 : ℕ) * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * G1 * 2 - r ^ (2 : ℕ) * Sy * S * y⁻¹ ^ (2 : ℕ) * G1 * 4 + r ^ (2 : ℕ) * Sy * Sxx * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_3_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 2 3 =
      r * G * Sx * s * S * y⁻¹ ^ (2 : ℕ) * 12 + r * G * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 4 + r * G * Sx * S * y⁻¹ ^ (2 : ℕ) * 8 - r * G * Sx * Sxx * 4 + r * G * Sy * Sxy * 4 + r ^ (2 : ℕ) * Sx * s * S * y⁻¹ ^ (2 : ℕ) * G1 * 6 + r ^ (2 : ℕ) * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * G1 * 2 + r ^ (2 : ℕ) * Sx * S * y⁻¹ ^ (2 : ℕ) * G1 * 4 - r ^ (2 : ℕ) * Sx * Sxx * G1 * 2 + r ^ (2 : ℕ) * Sy * Sxy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_3_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 3 2 =
      r * G * Sx * s * S * y⁻¹ ^ (2 : ℕ) * 12 + r * G * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 4 + r * G * Sx * S * y⁻¹ ^ (2 : ℕ) * 8 - r * G * Sx * Sxx * 4 + r * G * Sy * Sxy * 4 + r ^ (2 : ℕ) * Sx * s * S * y⁻¹ ^ (2 : ℕ) * G1 * 6 + r ^ (2 : ℕ) * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * G1 * 2 + r ^ (2 : ℕ) * Sx * S * y⁻¹ ^ (2 : ℕ) * G1 * 4 - r ^ (2 : ℕ) * Sx * Sxx * G1 * 2 + r ^ (2 : ℕ) * Sy * Sxy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_1_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 1 3 3 3 =
      r * G * Sy * s * S * y⁻¹ ^ (2 : ℕ) * 12 + r * G * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 4 + r * G * Sy * S * y⁻¹ ^ (2 : ℕ) * 8 - r * G * Sy * Sxx * 4 - r * G * Sx * Sxy * 4 + r ^ (2 : ℕ) * Sy * s * S * y⁻¹ ^ (2 : ℕ) * G1 * 6 + r ^ (2 : ℕ) * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * G1 * 2 + r ^ (2 : ℕ) * Sy * S * y⁻¹ ^ (2 : ℕ) * G1 * 4 - r ^ (2 : ℕ) * Sy * Sxx * G1 * 2 - r ^ (2 : ℕ) * Sx * Sxy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 2 2 =
      r ^ (2 : ℕ) * G * w * Sx * Sxx * 2 - r ^ (2 : ℕ) * G * w * Sy * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_0_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 2 3 =
      r ^ (2 : ℕ) * G * w * Sx * Sxy * 2 + r ^ (2 : ℕ) * G * w * Sy * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_0_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 3 2 =
      r ^ (2 : ℕ) * G * w * Sx * Sxy * 2 + r ^ (2 : ℕ) * G * w * Sy * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 0 3 3 =
      r ^ (2 : ℕ) * G * w * Sy * Sxy * 2 - r ^ (2 : ℕ) * G * w * Sx * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 2 2 =
      r * G * Sx * Sxx * 4 - r * G * Sy * Sxy * 4 + r ^ (2 : ℕ) * Sx * Sxx * G1 * 2 - r ^ (2 : ℕ) * Sy * Sxy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_1_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 2 3 =
      r * G * Sx * Sxy * 4 + r * G * Sy * Sxx * 4 + r ^ (2 : ℕ) * Sx * Sxy * G1 * 2 + r ^ (2 : ℕ) * Sy * Sxx * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_1_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 3 2 =
      r * G * Sx * Sxy * 4 + r * G * Sy * Sxx * 4 + r ^ (2 : ℕ) * Sx * Sxy * G1 * 2 + r ^ (2 : ℕ) * Sy * Sxx * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 1 3 3 =
      r * G * Sy * Sxy * 4 - r * G * Sx * Sxx * 4 + r ^ (2 : ℕ) * Sy * Sxy * G1 * 2 - r ^ (2 : ℕ) * Sx * Sxx * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 2 2 =
      r ^ (2 : ℕ) * G * Sx * Sxxx * 2 - r ^ (2 : ℕ) * G * Sy * Sxxy * 2 + r ^ (2 : ℕ) * G * Sxx ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * Sxy ^ (2 : ℕ) * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_2_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 2 3 =
      r ^ (2 : ℕ) * G * Sx * Sxxy * 2 + r ^ (2 : ℕ) * G * Sy * Sxxx * 2 + r ^ (2 : ℕ) * G * Sxx * Sxy * 4 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_2_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 3 2 =
      r ^ (2 : ℕ) * G * Sx * Sxxy * 2 + r ^ (2 : ℕ) * G * Sy * Sxxx * 2 + r ^ (2 : ℕ) * G * Sxx * Sxy * 4 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 2 3 3 =
      r ^ (2 : ℕ) * G * Sy * Sxxy * 2 - r ^ (2 : ℕ) * G * Sx * Sxxx * 2 + r ^ (2 : ℕ) * G * Sxy ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * Sxx ^ (2 : ℕ) * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 2 2 =
      -(r ^ (2 : ℕ) * G * Sx * Sy * s * y⁻¹ ^ (2 : ℕ) * 6) - r ^ (2 : ℕ) * G * Sx * Sy * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * Sx * Sy * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * Sx * Sxxy * 2 + r ^ (2 : ℕ) * G * Sy * Sxxx * 2 - r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * Sxy * S * 6 - r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxy * S * 2 - r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * Sxy * S * 4 + r ^ (2 : ℕ) * G * Sxx * Sxy * 4 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_3_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 2 3 =
      -(r ^ (2 : ℕ) * G * Sx * Sxxx * 2) + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * s * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * Sxx * S * 6 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxx * S * 2 + r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * Sxx * S * 4 + r ^ (2 : ℕ) * G * Sy * Sxxy * 2 - r ^ (2 : ℕ) * G * Sxx ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sxy ^ (2 : ℕ) * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_3_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 3 2 =
      -(r ^ (2 : ℕ) * G * Sx * Sxxx * 2) + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * s * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * Sxx * S * 6 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxx * S * 2 + r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * Sxx * S * 4 + r ^ (2 : ℕ) * G * Sy * Sxxy * 2 - r ^ (2 : ℕ) * G * Sxx ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sxy ^ (2 : ℕ) * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_2_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 2 3 3 3 =
      r ^ (2 : ℕ) * G * Sy * Sx * s * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sy * Sx * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sy * Sx * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * Sy * Sxxx * 2 - r ^ (2 : ℕ) * G * Sx * Sxxy * 2 + r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * Sxy * S * 6 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxy * S * 2 + r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * Sxy * S * 4 - r ^ (2 : ℕ) * G * Sxy * Sxx * 4 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 2 2 =
      r ^ (2 : ℕ) * G * w * Sx * Sxy * 2 - r ^ (2 : ℕ) * G * w * Sy * s * S * y⁻¹ ^ (2 : ℕ) * 6 - r ^ (2 : ℕ) * G * w * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * w * Sy * S * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * w * Sy * Sxx * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_0_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 2 3 =
      r ^ (2 : ℕ) * G * w * Sx * s * S * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * w * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * w * Sx * S * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * w * Sx * Sxx * 2 + r ^ (2 : ℕ) * G * w * Sy * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_0_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 3 2 =
      r ^ (2 : ℕ) * G * w * Sx * s * S * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * w * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * w * Sx * S * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * w * Sx * Sxx * 2 + r ^ (2 : ℕ) * G * w * Sy * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 0 3 3 =
      r ^ (2 : ℕ) * G * w * Sy * s * S * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * w * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * w * Sy * S * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * w * Sy * Sxx * 2 - r ^ (2 : ℕ) * G * w * Sx * Sxy * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 2 2 =
      r * G * Sx * Sxy * 4 - r * G * Sy * s * S * y⁻¹ ^ (2 : ℕ) * 12 - r * G * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 4 - r * G * Sy * S * y⁻¹ ^ (2 : ℕ) * 8 + r * G * Sy * Sxx * 4 + r ^ (2 : ℕ) * Sx * Sxy * G1 * 2 - r ^ (2 : ℕ) * Sy * s * S * y⁻¹ ^ (2 : ℕ) * G1 * 6 - r ^ (2 : ℕ) * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * G1 * 2 - r ^ (2 : ℕ) * Sy * S * y⁻¹ ^ (2 : ℕ) * G1 * 4 + r ^ (2 : ℕ) * Sy * Sxx * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_1_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 2 3 =
      r * G * Sx * s * S * y⁻¹ ^ (2 : ℕ) * 12 + r * G * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 4 + r * G * Sx * S * y⁻¹ ^ (2 : ℕ) * 8 - r * G * Sx * Sxx * 4 + r * G * Sy * Sxy * 4 + r ^ (2 : ℕ) * Sx * s * S * y⁻¹ ^ (2 : ℕ) * G1 * 6 + r ^ (2 : ℕ) * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * G1 * 2 + r ^ (2 : ℕ) * Sx * S * y⁻¹ ^ (2 : ℕ) * G1 * 4 - r ^ (2 : ℕ) * Sx * Sxx * G1 * 2 + r ^ (2 : ℕ) * Sy * Sxy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_1_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 3 2 =
      r * G * Sx * s * S * y⁻¹ ^ (2 : ℕ) * 12 + r * G * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 4 + r * G * Sx * S * y⁻¹ ^ (2 : ℕ) * 8 - r * G * Sx * Sxx * 4 + r * G * Sy * Sxy * 4 + r ^ (2 : ℕ) * Sx * s * S * y⁻¹ ^ (2 : ℕ) * G1 * 6 + r ^ (2 : ℕ) * Sx * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * G1 * 2 + r ^ (2 : ℕ) * Sx * S * y⁻¹ ^ (2 : ℕ) * G1 * 4 - r ^ (2 : ℕ) * Sx * Sxx * G1 * 2 + r ^ (2 : ℕ) * Sy * Sxy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 1 3 3 =
      r * G * Sy * s * S * y⁻¹ ^ (2 : ℕ) * 12 + r * G * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 4 + r * G * Sy * S * y⁻¹ ^ (2 : ℕ) * 8 - r * G * Sy * Sxx * 4 - r * G * Sx * Sxy * 4 + r ^ (2 : ℕ) * Sy * s * S * y⁻¹ ^ (2 : ℕ) * G1 * 6 + r ^ (2 : ℕ) * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * G1 * 2 + r ^ (2 : ℕ) * Sy * S * y⁻¹ ^ (2 : ℕ) * G1 * 4 - r ^ (2 : ℕ) * Sy * Sxx * G1 * 2 - r ^ (2 : ℕ) * Sx * Sxy * G1 * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 2 2 =
      -(r ^ (2 : ℕ) * G * Sx * Sy * s * y⁻¹ ^ (2 : ℕ) * 6) - r ^ (2 : ℕ) * G * Sx * Sy * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * Sx * Sy * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * Sx * Sxxy * 2 + r ^ (2 : ℕ) * G * Sy * Sxxx * 2 - r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * Sxy * S * 6 - r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxy * S * 2 - r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * Sxy * S * 4 + r ^ (2 : ℕ) * G * Sxy * Sxx * 4 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_2_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 2 3 =
      -(r ^ (2 : ℕ) * G * Sx * Sxxx * 2) + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * s * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * S * Sxx * 6 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * S * Sxx * 2 + r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * S * Sxx * 4 + r ^ (2 : ℕ) * G * Sy * Sxxy * 2 + r ^ (2 : ℕ) * G * Sxy ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * Sxx ^ (2 : ℕ) * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_2_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 3 2 =
      -(r ^ (2 : ℕ) * G * Sx * Sxxx * 2) + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * s * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * S * Sxx * 6 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * S * Sxx * 2 + r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * S * Sxx * 4 + r ^ (2 : ℕ) * G * Sy * Sxxy * 2 + r ^ (2 : ℕ) * G * Sxy ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * Sxx ^ (2 : ℕ) * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 2 3 3 =
      r ^ (2 : ℕ) * G * Sy * Sx * s * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sy * Sx * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sy * Sx * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * Sy * Sxxx * 2 - r ^ (2 : ℕ) * G * Sx * Sxxy * 2 + r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * S * Sxy * 6 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * S * Sxy * 2 + r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * S * Sxy * 4 - r ^ (2 : ℕ) * G * Sxy * Sxx * 4 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 2 2 =
      -(r ^ (2 : ℕ) * G * Sx * Sxxx * 2) + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * s * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sx ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * Sy ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * S * Sxx * 12 + r ^ (2 : ℕ) * G * s * y⁻¹ ^ (3 : ℕ) * Sy * S * 12 - r ^ (2 : ℕ) * G * s * y⁻¹ ^ (4 : ℕ) * S ^ (2 : ℕ) * 24 - r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sy ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * S * Sxx * 4 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * Sy * S * 4 - r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * S ^ (2 : ℕ) * 26 - r ^ (2 : ℕ) * G * s ^ (3 : ℕ) * y⁻¹ ^ (4 : ℕ) * S ^ (2 : ℕ) * 12 - r ^ (2 : ℕ) * G * s ^ (4 : ℕ) * y⁻¹ ^ (4 : ℕ) * S ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * Sy ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * S * Sxx * 8 + r ^ (2 : ℕ) * G * y⁻¹ ^ (3 : ℕ) * Sy * S * 8 - r ^ (2 : ℕ) * G * y⁻¹ ^ (4 : ℕ) * S ^ (2 : ℕ) * 8 + r ^ (2 : ℕ) * G * Sy * Sxxy * 2 + r ^ (2 : ℕ) * G * Sxy ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * Sxx ^ (2 : ℕ) * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_3_2_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 2 3 =
      r ^ (2 : ℕ) * G * Sx * Sy * s * y⁻¹ ^ (2 : ℕ) * 12 + r ^ (2 : ℕ) * G * Sx * Sy * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * Sx * Sy * y⁻¹ ^ (2 : ℕ) * 8 - r ^ (2 : ℕ) * G * Sx * s * y⁻¹ ^ (3 : ℕ) * S * 12 - r ^ (2 : ℕ) * G * Sx * s ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * S * 4 - r ^ (2 : ℕ) * G * Sx * y⁻¹ ^ (3 : ℕ) * S * 8 - r ^ (2 : ℕ) * G * Sx * Sxxy * 2 - r ^ (2 : ℕ) * G * Sy * Sxxx * 2 + r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * S * Sxy * 12 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * S * Sxy * 4 + r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * S * Sxy * 8 - r ^ (2 : ℕ) * G * Sxy * Sxx * 4 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_3_3_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 3 2 =
      r ^ (2 : ℕ) * G * Sx * Sy * s * y⁻¹ ^ (2 : ℕ) * 12 + r ^ (2 : ℕ) * G * Sx * Sy * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * Sx * Sy * y⁻¹ ^ (2 : ℕ) * 8 - r ^ (2 : ℕ) * G * Sx * s * y⁻¹ ^ (3 : ℕ) * S * 12 - r ^ (2 : ℕ) * G * Sx * s ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * S * 4 - r ^ (2 : ℕ) * G * Sx * y⁻¹ ^ (3 : ℕ) * S * 8 - r ^ (2 : ℕ) * G * Sx * Sxxy * 2 - r ^ (2 : ℕ) * G * Sy * Sxxx * 2 + r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * S * Sxy * 12 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * S * Sxy * 4 + r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * S * Sxy * 8 - r ^ (2 : ℕ) * G * Sxy * Sxx * 4 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

@[bmStreamEntry] theorem gradientJet_second_3_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (gradientJet w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy).second 3 3 3 3 =
      -(r ^ (2 : ℕ) * G * Sy * s * S * y⁻¹ ^ (3 : ℕ) * 12) - r ^ (2 : ℕ) * G * Sy * s ^ (2 : ℕ) * S * y⁻¹ ^ (3 : ℕ) * 4 - r ^ (2 : ℕ) * G * Sy * S * y⁻¹ ^ (3 : ℕ) * 8 - r ^ (2 : ℕ) * G * Sy * Sxxy * 2 + r ^ (2 : ℕ) * G * Sy ^ (2 : ℕ) * s * y⁻¹ ^ (2 : ℕ) * 6 + r ^ (2 : ℕ) * G * Sy ^ (2 : ℕ) * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * Sy ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * 4 - r ^ (2 : ℕ) * G * s * S * y⁻¹ ^ (2 : ℕ) * Sxx * 12 + r ^ (2 : ℕ) * G * s * S ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * 24 - r ^ (2 : ℕ) * G * s * y⁻¹ ^ (2 : ℕ) * Sx ^ (2 : ℕ) * 6 - r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * Sxx * 4 + r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * S ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * 26 - r ^ (2 : ℕ) * G * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sx ^ (2 : ℕ) * 2 + r ^ (2 : ℕ) * G * s ^ (3 : ℕ) * S ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * 12 + r ^ (2 : ℕ) * G * s ^ (4 : ℕ) * S ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * 2 - r ^ (2 : ℕ) * G * S * y⁻¹ ^ (2 : ℕ) * Sxx * 8 + r ^ (2 : ℕ) * G * S ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * 8 - r ^ (2 : ℕ) * G * y⁻¹ ^ (2 : ℕ) * Sx ^ (2 : ℕ) * 4 + r ^ (2 : ℕ) * G * Sx * Sxxx * 2 + r ^ (2 : ℕ) * G * Sxx ^ (2 : ℕ) * 2 - r ^ (2 : ℕ) * G * Sxy ^ (2 : ℕ) * 2 := by
  simp only [gradientJet, gradXJet, gradYJet, orbitJet, coord, ScalarTwoJet.mul, ScalarTwoJet.add,
    ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_mul_self _hy]
  try ring_nf

end
end RHTower.D4BMScalarStream
