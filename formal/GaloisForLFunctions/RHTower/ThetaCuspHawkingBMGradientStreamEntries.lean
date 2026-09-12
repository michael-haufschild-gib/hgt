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
      r ^ 2 * G * Sx ^ 2 - r ^ 2 * G * Sy ^ 2 := by
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
      r ^ 2 * G * Sx * Sy * 2 := by
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
      r ^ 2 * G * Sx * Sy * 2 := by
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
      r ^ 2 * G * Sy ^ 2 - r ^ 2 * G * Sx ^ 2 := by
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
      r ^ 2 * G * w * Sx ^ 2 - r ^ 2 * G * w * Sy ^ 2 := by
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
      r ^ 2 * G * w * Sx * Sy * 2 := by
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
      r ^ 2 * G * w * Sx * Sy * 2 := by
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
      r ^ 2 * G * w * Sy ^ 2 - r ^ 2 * G * w * Sx ^ 2 := by
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
      r * G * Sx ^ 2 * 2 - r * G * Sy ^ 2 * 2 + r ^ 2 * Sx ^ 2 * G1 - r ^ 2 * Sy ^ 2 * G1 := by
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
      r * G * Sx * Sy * 4 + r ^ 2 * Sx * Sy * G1 * 2 := by
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
      r * G * Sx * Sy * 4 + r ^ 2 * Sx * Sy * G1 * 2 := by
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
      r * G * Sy ^ 2 * 2 - r * G * Sx ^ 2 * 2 + r ^ 2 * Sy ^ 2 * G1 - r ^ 2 * Sx ^ 2 * G1 := by
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
      r ^ 2 * G * Sx * Sxx * 2 - r ^ 2 * G * Sy * Sxy * 2 := by
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
      r ^ 2 * G * Sx * Sxy * 2 + r ^ 2 * G * Sy * Sxx * 2 := by
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
      r ^ 2 * G * Sx * Sxy * 2 + r ^ 2 * G * Sy * Sxx * 2 := by
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
      r ^ 2 * G * Sy * Sxy * 2 - r ^ 2 * G * Sx * Sxx * 2 := by
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
      r ^ 2 * G * Sx * Sxy * 2 - r ^ 2 * G * Sy * s * S * y⁻¹ ^ 2 * 6 - r ^ 2 * G * Sy * s ^ 2 * S * y⁻¹ ^ 2 * 2 - r ^ 2 * G * Sy * S * y⁻¹ ^ 2 * 4 + r ^ 2 * G * Sy * Sxx * 2 := by
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
      r ^ 2 * G * Sx * s * S * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sx * s ^ 2 * S * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sx * S * y⁻¹ ^ 2 * 4 - r ^ 2 * G * Sx * Sxx * 2 + r ^ 2 * G * Sy * Sxy * 2 := by
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
      r ^ 2 * G * Sx * s * S * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sx * s ^ 2 * S * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sx * S * y⁻¹ ^ 2 * 4 - r ^ 2 * G * Sx * Sxx * 2 + r ^ 2 * G * Sy * Sxy * 2 := by
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
      r ^ 2 * G * Sy * s * S * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sy * s ^ 2 * S * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sy * S * y⁻¹ ^ 2 * 4 - r ^ 2 * G * Sy * Sxx * 2 - r ^ 2 * G * Sx * Sxy * 2 := by
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
      r ^ 2 * G * w ^ 2 * Sx ^ 2 - r ^ 2 * G * w ^ 2 * Sy ^ 2 := by
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
      r ^ 2 * G * w ^ 2 * Sx * Sy * 2 := by
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
      r ^ 2 * G * w ^ 2 * Sx * Sy * 2 := by
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
      r ^ 2 * G * w ^ 2 * Sy ^ 2 - r ^ 2 * G * w ^ 2 * Sx ^ 2 := by
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
      r * G * w * Sx ^ 2 * 2 - r * G * w * Sy ^ 2 * 2 + r ^ 2 * w * Sx ^ 2 * G1 - r ^ 2 * w * Sy ^ 2 * G1 := by
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
      r * G * w * Sx * Sy * 4 + r ^ 2 * w * Sx * Sy * G1 * 2 := by
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
      r * G * w * Sx * Sy * 4 + r ^ 2 * w * Sx * Sy * G1 * 2 := by
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
      r * G * w * Sy ^ 2 * 2 - r * G * w * Sx ^ 2 * 2 + r ^ 2 * w * Sy ^ 2 * G1 - r ^ 2 * w * Sx ^ 2 * G1 := by
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
      r ^ 2 * G * w * Sx * Sxx * 2 - r ^ 2 * G * w * Sy * Sxy * 2 := by
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
      r ^ 2 * G * w * Sx * Sxy * 2 + r ^ 2 * G * w * Sy * Sxx * 2 := by
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
      r ^ 2 * G * w * Sx * Sxy * 2 + r ^ 2 * G * w * Sy * Sxx * 2 := by
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
      r ^ 2 * G * w * Sy * Sxy * 2 - r ^ 2 * G * w * Sx * Sxx * 2 := by
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
      r ^ 2 * G * w * Sx * Sxy * 2 - r ^ 2 * G * w * Sy * s * S * y⁻¹ ^ 2 * 6 - r ^ 2 * G * w * Sy * s ^ 2 * S * y⁻¹ ^ 2 * 2 - r ^ 2 * G * w * Sy * S * y⁻¹ ^ 2 * 4 + r ^ 2 * G * w * Sy * Sxx * 2 := by
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
      r ^ 2 * G * w * Sx * s * S * y⁻¹ ^ 2 * 6 + r ^ 2 * G * w * Sx * s ^ 2 * S * y⁻¹ ^ 2 * 2 + r ^ 2 * G * w * Sx * S * y⁻¹ ^ 2 * 4 - r ^ 2 * G * w * Sx * Sxx * 2 + r ^ 2 * G * w * Sy * Sxy * 2 := by
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
      r ^ 2 * G * w * Sx * s * S * y⁻¹ ^ 2 * 6 + r ^ 2 * G * w * Sx * s ^ 2 * S * y⁻¹ ^ 2 * 2 + r ^ 2 * G * w * Sx * S * y⁻¹ ^ 2 * 4 - r ^ 2 * G * w * Sx * Sxx * 2 + r ^ 2 * G * w * Sy * Sxy * 2 := by
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
      r ^ 2 * G * w * Sy * s * S * y⁻¹ ^ 2 * 6 + r ^ 2 * G * w * Sy * s ^ 2 * S * y⁻¹ ^ 2 * 2 + r ^ 2 * G * w * Sy * S * y⁻¹ ^ 2 * 4 - r ^ 2 * G * w * Sy * Sxx * 2 - r ^ 2 * G * w * Sx * Sxy * 2 := by
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
      r * G * w * Sx ^ 2 * 2 - r * G * w * Sy ^ 2 * 2 + r ^ 2 * w * Sx ^ 2 * G1 - r ^ 2 * w * Sy ^ 2 * G1 := by
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
      r * G * w * Sx * Sy * 4 + r ^ 2 * w * Sx * Sy * G1 * 2 := by
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
      r * G * w * Sx * Sy * 4 + r ^ 2 * w * Sx * Sy * G1 * 2 := by
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
      r * G * w * Sy ^ 2 * 2 - r * G * w * Sx ^ 2 * 2 + r ^ 2 * w * Sy ^ 2 * G1 - r ^ 2 * w * Sx ^ 2 * G1 := by
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
      r * G1 * Sx ^ 2 * 4 - r * G1 * Sy ^ 2 * 4 + r ^ 2 * Sx ^ 2 * G2 - r ^ 2 * Sy ^ 2 * G2 + Sx ^ 2 * G * 2 - Sy ^ 2 * G * 2 := by
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
      r * G1 * Sx * Sy * 8 + r ^ 2 * Sx * Sy * G2 * 2 + Sx * Sy * G * 4 := by
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
      r * G1 * Sx * Sy * 8 + r ^ 2 * Sx * Sy * G2 * 2 + Sx * Sy * G * 4 := by
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
      r * G1 * Sy ^ 2 * 4 - r * G1 * Sx ^ 2 * 4 + r ^ 2 * Sy ^ 2 * G2 - r ^ 2 * Sx ^ 2 * G2 + Sy ^ 2 * G * 2 - Sx ^ 2 * G * 2 := by
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
      r * G * Sx * Sxx * 4 - r * G * Sy * Sxy * 4 + r ^ 2 * Sx * Sxx * G1 * 2 - r ^ 2 * Sy * Sxy * G1 * 2 := by
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
      r * G * Sx * Sxy * 4 + r * G * Sy * Sxx * 4 + r ^ 2 * Sx * Sxy * G1 * 2 + r ^ 2 * Sy * Sxx * G1 * 2 := by
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
      r * G * Sx * Sxy * 4 + r * G * Sy * Sxx * 4 + r ^ 2 * Sx * Sxy * G1 * 2 + r ^ 2 * Sy * Sxx * G1 * 2 := by
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
      r * G * Sy * Sxy * 4 - r * G * Sx * Sxx * 4 + r ^ 2 * Sy * Sxy * G1 * 2 - r ^ 2 * Sx * Sxx * G1 * 2 := by
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
      r * G * Sx * Sxy * 4 - r * G * Sy * s * S * y⁻¹ ^ 2 * 12 - r * G * Sy * s ^ 2 * S * y⁻¹ ^ 2 * 4 - r * G * Sy * S * y⁻¹ ^ 2 * 8 + r * G * Sy * Sxx * 4 + r ^ 2 * Sx * Sxy * G1 * 2 - r ^ 2 * Sy * s * S * y⁻¹ ^ 2 * G1 * 6 - r ^ 2 * Sy * s ^ 2 * S * y⁻¹ ^ 2 * G1 * 2 - r ^ 2 * Sy * S * y⁻¹ ^ 2 * G1 * 4 + r ^ 2 * Sy * Sxx * G1 * 2 := by
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
      r * G * Sx * s * S * y⁻¹ ^ 2 * 12 + r * G * Sx * s ^ 2 * S * y⁻¹ ^ 2 * 4 + r * G * Sx * S * y⁻¹ ^ 2 * 8 - r * G * Sx * Sxx * 4 + r * G * Sy * Sxy * 4 + r ^ 2 * Sx * s * S * y⁻¹ ^ 2 * G1 * 6 + r ^ 2 * Sx * s ^ 2 * S * y⁻¹ ^ 2 * G1 * 2 + r ^ 2 * Sx * S * y⁻¹ ^ 2 * G1 * 4 - r ^ 2 * Sx * Sxx * G1 * 2 + r ^ 2 * Sy * Sxy * G1 * 2 := by
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
      r * G * Sx * s * S * y⁻¹ ^ 2 * 12 + r * G * Sx * s ^ 2 * S * y⁻¹ ^ 2 * 4 + r * G * Sx * S * y⁻¹ ^ 2 * 8 - r * G * Sx * Sxx * 4 + r * G * Sy * Sxy * 4 + r ^ 2 * Sx * s * S * y⁻¹ ^ 2 * G1 * 6 + r ^ 2 * Sx * s ^ 2 * S * y⁻¹ ^ 2 * G1 * 2 + r ^ 2 * Sx * S * y⁻¹ ^ 2 * G1 * 4 - r ^ 2 * Sx * Sxx * G1 * 2 + r ^ 2 * Sy * Sxy * G1 * 2 := by
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
      r * G * Sy * s * S * y⁻¹ ^ 2 * 12 + r * G * Sy * s ^ 2 * S * y⁻¹ ^ 2 * 4 + r * G * Sy * S * y⁻¹ ^ 2 * 8 - r * G * Sy * Sxx * 4 - r * G * Sx * Sxy * 4 + r ^ 2 * Sy * s * S * y⁻¹ ^ 2 * G1 * 6 + r ^ 2 * Sy * s ^ 2 * S * y⁻¹ ^ 2 * G1 * 2 + r ^ 2 * Sy * S * y⁻¹ ^ 2 * G1 * 4 - r ^ 2 * Sy * Sxx * G1 * 2 - r ^ 2 * Sx * Sxy * G1 * 2 := by
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
      r ^ 2 * G * w * Sx * Sxx * 2 - r ^ 2 * G * w * Sy * Sxy * 2 := by
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
      r ^ 2 * G * w * Sx * Sxy * 2 + r ^ 2 * G * w * Sy * Sxx * 2 := by
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
      r ^ 2 * G * w * Sx * Sxy * 2 + r ^ 2 * G * w * Sy * Sxx * 2 := by
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
      r ^ 2 * G * w * Sy * Sxy * 2 - r ^ 2 * G * w * Sx * Sxx * 2 := by
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
      r * G * Sx * Sxx * 4 - r * G * Sy * Sxy * 4 + r ^ 2 * Sx * Sxx * G1 * 2 - r ^ 2 * Sy * Sxy * G1 * 2 := by
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
      r * G * Sx * Sxy * 4 + r * G * Sy * Sxx * 4 + r ^ 2 * Sx * Sxy * G1 * 2 + r ^ 2 * Sy * Sxx * G1 * 2 := by
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
      r * G * Sx * Sxy * 4 + r * G * Sy * Sxx * 4 + r ^ 2 * Sx * Sxy * G1 * 2 + r ^ 2 * Sy * Sxx * G1 * 2 := by
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
      r * G * Sy * Sxy * 4 - r * G * Sx * Sxx * 4 + r ^ 2 * Sy * Sxy * G1 * 2 - r ^ 2 * Sx * Sxx * G1 * 2 := by
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
      r ^ 2 * G * Sx * Sxxx * 2 - r ^ 2 * G * Sy * Sxxy * 2 + r ^ 2 * G * Sxx ^ 2 * 2 - r ^ 2 * G * Sxy ^ 2 * 2 := by
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
      r ^ 2 * G * Sx * Sxxy * 2 + r ^ 2 * G * Sy * Sxxx * 2 + r ^ 2 * G * Sxx * Sxy * 4 := by
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
      r ^ 2 * G * Sx * Sxxy * 2 + r ^ 2 * G * Sy * Sxxx * 2 + r ^ 2 * G * Sxx * Sxy * 4 := by
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
      r ^ 2 * G * Sy * Sxxy * 2 - r ^ 2 * G * Sx * Sxxx * 2 + r ^ 2 * G * Sxy ^ 2 * 2 - r ^ 2 * G * Sxx ^ 2 * 2 := by
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
      -(r ^ 2 * G * Sx * Sy * s * y⁻¹ ^ 2 * 6) - r ^ 2 * G * Sx * Sy * s ^ 2 * y⁻¹ ^ 2 * 2 - r ^ 2 * G * Sx * Sy * y⁻¹ ^ 2 * 4 + r ^ 2 * G * Sx * Sxxy * 2 + r ^ 2 * G * Sy * Sxxx * 2 - r ^ 2 * G * s * y⁻¹ ^ 2 * Sxy * S * 6 - r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * Sxy * S * 2 - r ^ 2 * G * y⁻¹ ^ 2 * Sxy * S * 4 + r ^ 2 * G * Sxx * Sxy * 4 := by
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
      -(r ^ 2 * G * Sx * Sxxx * 2) + r ^ 2 * G * Sx ^ 2 * s * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sx ^ 2 * s ^ 2 * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sx ^ 2 * y⁻¹ ^ 2 * 4 + r ^ 2 * G * s * y⁻¹ ^ 2 * Sxx * S * 6 + r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * Sxx * S * 2 + r ^ 2 * G * y⁻¹ ^ 2 * Sxx * S * 4 + r ^ 2 * G * Sy * Sxxy * 2 - r ^ 2 * G * Sxx ^ 2 * 2 + r ^ 2 * G * Sxy ^ 2 * 2 := by
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
      -(r ^ 2 * G * Sx * Sxxx * 2) + r ^ 2 * G * Sx ^ 2 * s * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sx ^ 2 * s ^ 2 * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sx ^ 2 * y⁻¹ ^ 2 * 4 + r ^ 2 * G * s * y⁻¹ ^ 2 * Sxx * S * 6 + r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * Sxx * S * 2 + r ^ 2 * G * y⁻¹ ^ 2 * Sxx * S * 4 + r ^ 2 * G * Sy * Sxxy * 2 - r ^ 2 * G * Sxx ^ 2 * 2 + r ^ 2 * G * Sxy ^ 2 * 2 := by
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
      r ^ 2 * G * Sy * Sx * s * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sy * Sx * s ^ 2 * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sy * Sx * y⁻¹ ^ 2 * 4 - r ^ 2 * G * Sy * Sxxx * 2 - r ^ 2 * G * Sx * Sxxy * 2 + r ^ 2 * G * s * y⁻¹ ^ 2 * Sxy * S * 6 + r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * Sxy * S * 2 + r ^ 2 * G * y⁻¹ ^ 2 * Sxy * S * 4 - r ^ 2 * G * Sxy * Sxx * 4 := by
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
      r ^ 2 * G * w * Sx * Sxy * 2 - r ^ 2 * G * w * Sy * s * S * y⁻¹ ^ 2 * 6 - r ^ 2 * G * w * Sy * s ^ 2 * S * y⁻¹ ^ 2 * 2 - r ^ 2 * G * w * Sy * S * y⁻¹ ^ 2 * 4 + r ^ 2 * G * w * Sy * Sxx * 2 := by
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
      r ^ 2 * G * w * Sx * s * S * y⁻¹ ^ 2 * 6 + r ^ 2 * G * w * Sx * s ^ 2 * S * y⁻¹ ^ 2 * 2 + r ^ 2 * G * w * Sx * S * y⁻¹ ^ 2 * 4 - r ^ 2 * G * w * Sx * Sxx * 2 + r ^ 2 * G * w * Sy * Sxy * 2 := by
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
      r ^ 2 * G * w * Sx * s * S * y⁻¹ ^ 2 * 6 + r ^ 2 * G * w * Sx * s ^ 2 * S * y⁻¹ ^ 2 * 2 + r ^ 2 * G * w * Sx * S * y⁻¹ ^ 2 * 4 - r ^ 2 * G * w * Sx * Sxx * 2 + r ^ 2 * G * w * Sy * Sxy * 2 := by
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
      r ^ 2 * G * w * Sy * s * S * y⁻¹ ^ 2 * 6 + r ^ 2 * G * w * Sy * s ^ 2 * S * y⁻¹ ^ 2 * 2 + r ^ 2 * G * w * Sy * S * y⁻¹ ^ 2 * 4 - r ^ 2 * G * w * Sy * Sxx * 2 - r ^ 2 * G * w * Sx * Sxy * 2 := by
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
      r * G * Sx * Sxy * 4 - r * G * Sy * s * S * y⁻¹ ^ 2 * 12 - r * G * Sy * s ^ 2 * S * y⁻¹ ^ 2 * 4 - r * G * Sy * S * y⁻¹ ^ 2 * 8 + r * G * Sy * Sxx * 4 + r ^ 2 * Sx * Sxy * G1 * 2 - r ^ 2 * Sy * s * S * y⁻¹ ^ 2 * G1 * 6 - r ^ 2 * Sy * s ^ 2 * S * y⁻¹ ^ 2 * G1 * 2 - r ^ 2 * Sy * S * y⁻¹ ^ 2 * G1 * 4 + r ^ 2 * Sy * Sxx * G1 * 2 := by
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
      r * G * Sx * s * S * y⁻¹ ^ 2 * 12 + r * G * Sx * s ^ 2 * S * y⁻¹ ^ 2 * 4 + r * G * Sx * S * y⁻¹ ^ 2 * 8 - r * G * Sx * Sxx * 4 + r * G * Sy * Sxy * 4 + r ^ 2 * Sx * s * S * y⁻¹ ^ 2 * G1 * 6 + r ^ 2 * Sx * s ^ 2 * S * y⁻¹ ^ 2 * G1 * 2 + r ^ 2 * Sx * S * y⁻¹ ^ 2 * G1 * 4 - r ^ 2 * Sx * Sxx * G1 * 2 + r ^ 2 * Sy * Sxy * G1 * 2 := by
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
      r * G * Sx * s * S * y⁻¹ ^ 2 * 12 + r * G * Sx * s ^ 2 * S * y⁻¹ ^ 2 * 4 + r * G * Sx * S * y⁻¹ ^ 2 * 8 - r * G * Sx * Sxx * 4 + r * G * Sy * Sxy * 4 + r ^ 2 * Sx * s * S * y⁻¹ ^ 2 * G1 * 6 + r ^ 2 * Sx * s ^ 2 * S * y⁻¹ ^ 2 * G1 * 2 + r ^ 2 * Sx * S * y⁻¹ ^ 2 * G1 * 4 - r ^ 2 * Sx * Sxx * G1 * 2 + r ^ 2 * Sy * Sxy * G1 * 2 := by
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
      r * G * Sy * s * S * y⁻¹ ^ 2 * 12 + r * G * Sy * s ^ 2 * S * y⁻¹ ^ 2 * 4 + r * G * Sy * S * y⁻¹ ^ 2 * 8 - r * G * Sy * Sxx * 4 - r * G * Sx * Sxy * 4 + r ^ 2 * Sy * s * S * y⁻¹ ^ 2 * G1 * 6 + r ^ 2 * Sy * s ^ 2 * S * y⁻¹ ^ 2 * G1 * 2 + r ^ 2 * Sy * S * y⁻¹ ^ 2 * G1 * 4 - r ^ 2 * Sy * Sxx * G1 * 2 - r ^ 2 * Sx * Sxy * G1 * 2 := by
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
      -(r ^ 2 * G * Sx * Sy * s * y⁻¹ ^ 2 * 6) - r ^ 2 * G * Sx * Sy * s ^ 2 * y⁻¹ ^ 2 * 2 - r ^ 2 * G * Sx * Sy * y⁻¹ ^ 2 * 4 + r ^ 2 * G * Sx * Sxxy * 2 + r ^ 2 * G * Sy * Sxxx * 2 - r ^ 2 * G * s * y⁻¹ ^ 2 * Sxy * S * 6 - r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * Sxy * S * 2 - r ^ 2 * G * y⁻¹ ^ 2 * Sxy * S * 4 + r ^ 2 * G * Sxy * Sxx * 4 := by
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
      -(r ^ 2 * G * Sx * Sxxx * 2) + r ^ 2 * G * Sx ^ 2 * s * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sx ^ 2 * s ^ 2 * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sx ^ 2 * y⁻¹ ^ 2 * 4 + r ^ 2 * G * s * y⁻¹ ^ 2 * S * Sxx * 6 + r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * S * Sxx * 2 + r ^ 2 * G * y⁻¹ ^ 2 * S * Sxx * 4 + r ^ 2 * G * Sy * Sxxy * 2 + r ^ 2 * G * Sxy ^ 2 * 2 - r ^ 2 * G * Sxx ^ 2 * 2 := by
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
      -(r ^ 2 * G * Sx * Sxxx * 2) + r ^ 2 * G * Sx ^ 2 * s * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sx ^ 2 * s ^ 2 * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sx ^ 2 * y⁻¹ ^ 2 * 4 + r ^ 2 * G * s * y⁻¹ ^ 2 * S * Sxx * 6 + r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * S * Sxx * 2 + r ^ 2 * G * y⁻¹ ^ 2 * S * Sxx * 4 + r ^ 2 * G * Sy * Sxxy * 2 + r ^ 2 * G * Sxy ^ 2 * 2 - r ^ 2 * G * Sxx ^ 2 * 2 := by
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
      r ^ 2 * G * Sy * Sx * s * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sy * Sx * s ^ 2 * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sy * Sx * y⁻¹ ^ 2 * 4 - r ^ 2 * G * Sy * Sxxx * 2 - r ^ 2 * G * Sx * Sxxy * 2 + r ^ 2 * G * s * y⁻¹ ^ 2 * S * Sxy * 6 + r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * S * Sxy * 2 + r ^ 2 * G * y⁻¹ ^ 2 * S * Sxy * 4 - r ^ 2 * G * Sxy * Sxx * 4 := by
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
      -(r ^ 2 * G * Sx * Sxxx * 2) + r ^ 2 * G * Sx ^ 2 * s * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sx ^ 2 * s ^ 2 * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sx ^ 2 * y⁻¹ ^ 2 * 4 - r ^ 2 * G * s * y⁻¹ ^ 2 * Sy ^ 2 * 6 + r ^ 2 * G * s * y⁻¹ ^ 2 * S * Sxx * 12 + r ^ 2 * G * s * y⁻¹ ^ 3 * Sy * S * 12 - r ^ 2 * G * s * y⁻¹ ^ 4 * S ^ 2 * 24 - r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * Sy ^ 2 * 2 + r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * S * Sxx * 4 + r ^ 2 * G * s ^ 2 * y⁻¹ ^ 3 * Sy * S * 4 - r ^ 2 * G * s ^ 2 * y⁻¹ ^ 4 * S ^ 2 * 26 - r ^ 2 * G * s ^ 3 * y⁻¹ ^ 4 * S ^ 2 * 12 - r ^ 2 * G * s ^ 4 * y⁻¹ ^ 4 * S ^ 2 * 2 - r ^ 2 * G * y⁻¹ ^ 2 * Sy ^ 2 * 4 + r ^ 2 * G * y⁻¹ ^ 2 * S * Sxx * 8 + r ^ 2 * G * y⁻¹ ^ 3 * Sy * S * 8 - r ^ 2 * G * y⁻¹ ^ 4 * S ^ 2 * 8 + r ^ 2 * G * Sy * Sxxy * 2 + r ^ 2 * G * Sxy ^ 2 * 2 - r ^ 2 * G * Sxx ^ 2 * 2 := by
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
      r ^ 2 * G * Sx * Sy * s * y⁻¹ ^ 2 * 12 + r ^ 2 * G * Sx * Sy * s ^ 2 * y⁻¹ ^ 2 * 4 + r ^ 2 * G * Sx * Sy * y⁻¹ ^ 2 * 8 - r ^ 2 * G * Sx * s * y⁻¹ ^ 3 * S * 12 - r ^ 2 * G * Sx * s ^ 2 * y⁻¹ ^ 3 * S * 4 - r ^ 2 * G * Sx * y⁻¹ ^ 3 * S * 8 - r ^ 2 * G * Sx * Sxxy * 2 - r ^ 2 * G * Sy * Sxxx * 2 + r ^ 2 * G * s * y⁻¹ ^ 2 * S * Sxy * 12 + r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * S * Sxy * 4 + r ^ 2 * G * y⁻¹ ^ 2 * S * Sxy * 8 - r ^ 2 * G * Sxy * Sxx * 4 := by
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
      r ^ 2 * G * Sx * Sy * s * y⁻¹ ^ 2 * 12 + r ^ 2 * G * Sx * Sy * s ^ 2 * y⁻¹ ^ 2 * 4 + r ^ 2 * G * Sx * Sy * y⁻¹ ^ 2 * 8 - r ^ 2 * G * Sx * s * y⁻¹ ^ 3 * S * 12 - r ^ 2 * G * Sx * s ^ 2 * y⁻¹ ^ 3 * S * 4 - r ^ 2 * G * Sx * y⁻¹ ^ 3 * S * 8 - r ^ 2 * G * Sx * Sxxy * 2 - r ^ 2 * G * Sy * Sxxx * 2 + r ^ 2 * G * s * y⁻¹ ^ 2 * S * Sxy * 12 + r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * S * Sxy * 4 + r ^ 2 * G * y⁻¹ ^ 2 * S * Sxy * 8 - r ^ 2 * G * Sxy * Sxx * 4 := by
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
      -(r ^ 2 * G * Sy * s * S * y⁻¹ ^ 3 * 12) - r ^ 2 * G * Sy * s ^ 2 * S * y⁻¹ ^ 3 * 4 - r ^ 2 * G * Sy * S * y⁻¹ ^ 3 * 8 - r ^ 2 * G * Sy * Sxxy * 2 + r ^ 2 * G * Sy ^ 2 * s * y⁻¹ ^ 2 * 6 + r ^ 2 * G * Sy ^ 2 * s ^ 2 * y⁻¹ ^ 2 * 2 + r ^ 2 * G * Sy ^ 2 * y⁻¹ ^ 2 * 4 - r ^ 2 * G * s * S * y⁻¹ ^ 2 * Sxx * 12 + r ^ 2 * G * s * S ^ 2 * y⁻¹ ^ 4 * 24 - r ^ 2 * G * s * y⁻¹ ^ 2 * Sx ^ 2 * 6 - r ^ 2 * G * s ^ 2 * S * y⁻¹ ^ 2 * Sxx * 4 + r ^ 2 * G * s ^ 2 * S ^ 2 * y⁻¹ ^ 4 * 26 - r ^ 2 * G * s ^ 2 * y⁻¹ ^ 2 * Sx ^ 2 * 2 + r ^ 2 * G * s ^ 3 * S ^ 2 * y⁻¹ ^ 4 * 12 + r ^ 2 * G * s ^ 4 * S ^ 2 * y⁻¹ ^ 4 * 2 - r ^ 2 * G * S * y⁻¹ ^ 2 * Sxx * 8 + r ^ 2 * G * S ^ 2 * y⁻¹ ^ 4 * 8 - r ^ 2 * G * y⁻¹ ^ 2 * Sx ^ 2 * 4 + r ^ 2 * G * Sx * Sxxx * 2 + r ^ 2 * G * Sxx ^ 2 * 2 - r ^ 2 * G * Sxy ^ 2 * 2 := by
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
