import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetQuadraticEinstein

/-!
# Entry tables for the Birmingham–Mokhtari background jet and the fundamental scalar jet

Every diagonal entry of the background jet and every entry of the fundamental scalar metric jet
is recorded in a fixed normal form whose only inverses are `r⁻¹`, `y⁻¹` and `(-1 + r ^ 2)⁻¹`.
Off-block entries of the scalar jet vanish. These tables let the index-collapsed Einstein
coefficients over the background be evaluated by flat rewriting instead of by unfolding the jet
algebra inside every summand; they are the heartbeat-efficient replacement for the brute-force
expansions of the quadratic source modules.
-/

set_option linter.unusedSimpArgs false

namespace RHTower.D4BMBackground
open GaloisForLFunctions.HTGeometry
noncomputable section
variable (r y : ℂ)

theorem jet_metric_0_0 : (jet r y).metric 0 0 = -(r ^ 2 - 1) := rfl
theorem jet_metric_1_1 : (jet r y).metric 1 1 = (r ^ 2 - 1)⁻¹ := rfl
theorem jet_metric_2_2 : (jet r y).metric 2 2 = r ^ 2 * y⁻¹ ^ 2 := rfl
theorem jet_metric_3_3 : (jet r y).metric 3 3 = r ^ 2 * y⁻¹ ^ 2 := rfl
theorem jet_first_0_0_0 : (jet r y).first 0 0 0 = 0 := rfl
theorem jet_first_0_1_1 : (jet r y).first 0 1 1 = 0 := rfl
theorem jet_first_0_2_2 : (jet r y).first 0 2 2 = 0 := rfl
theorem jet_first_0_3_3 : (jet r y).first 0 3 3 = 0 := rfl
theorem jet_first_1_0_0 : (jet r y).first 1 0 0 = -2 * r := rfl
theorem jet_first_1_1_1 : (jet r y).first 1 1 1 = -2 * r * (r ^ 2 - 1)⁻¹ ^ 2 := rfl
theorem jet_first_1_2_2 : (jet r y).first 1 2 2 = 2 * r * y⁻¹ ^ 2 := rfl
theorem jet_first_1_3_3 : (jet r y).first 1 3 3 = 2 * r * y⁻¹ ^ 2 := rfl
theorem jet_first_2_0_0 : (jet r y).first 2 0 0 = 0 := rfl
theorem jet_first_2_1_1 : (jet r y).first 2 1 1 = 0 := rfl
theorem jet_first_2_2_2 : (jet r y).first 2 2 2 = 0 := rfl
theorem jet_first_2_3_3 : (jet r y).first 2 3 3 = 0 := rfl
theorem jet_first_3_0_0 : (jet r y).first 3 0 0 = 0 := rfl
theorem jet_first_3_1_1 : (jet r y).first 3 1 1 = 0 := rfl
theorem jet_first_3_2_2 : (jet r y).first 3 2 2 = -2 * r ^ 2 * y⁻¹ ^ 3 := rfl
theorem jet_first_3_3_3 : (jet r y).first 3 3 3 = -2 * r ^ 2 * y⁻¹ ^ 3 := rfl
theorem jet_second_0_0_0_0 : (jet r y).second 0 0 0 0 = 0 := rfl
theorem jet_second_0_0_1_1 : (jet r y).second 0 0 1 1 = 0 := rfl
theorem jet_second_0_0_2_2 : (jet r y).second 0 0 2 2 = 0 := rfl
theorem jet_second_0_0_3_3 : (jet r y).second 0 0 3 3 = 0 := rfl
theorem jet_second_0_1_0_0 : (jet r y).second 0 1 0 0 = 0 := rfl
theorem jet_second_0_1_1_1 : (jet r y).second 0 1 1 1 = 0 := rfl
theorem jet_second_0_1_2_2 : (jet r y).second 0 1 2 2 = 0 := rfl
theorem jet_second_0_1_3_3 : (jet r y).second 0 1 3 3 = 0 := rfl
theorem jet_second_0_2_0_0 : (jet r y).second 0 2 0 0 = 0 := rfl
theorem jet_second_0_2_1_1 : (jet r y).second 0 2 1 1 = 0 := rfl
theorem jet_second_0_2_2_2 : (jet r y).second 0 2 2 2 = 0 := rfl
theorem jet_second_0_2_3_3 : (jet r y).second 0 2 3 3 = 0 := rfl
theorem jet_second_0_3_0_0 : (jet r y).second 0 3 0 0 = 0 := rfl
theorem jet_second_0_3_1_1 : (jet r y).second 0 3 1 1 = 0 := rfl
theorem jet_second_0_3_2_2 : (jet r y).second 0 3 2 2 = 0 := rfl
theorem jet_second_0_3_3_3 : (jet r y).second 0 3 3 3 = 0 := rfl
theorem jet_second_1_0_0_0 : (jet r y).second 1 0 0 0 = 0 := rfl
theorem jet_second_1_0_1_1 : (jet r y).second 1 0 1 1 = 0 := rfl
theorem jet_second_1_0_2_2 : (jet r y).second 1 0 2 2 = 0 := rfl
theorem jet_second_1_0_3_3 : (jet r y).second 1 0 3 3 = 0 := rfl
theorem jet_second_1_1_0_0 : (jet r y).second 1 1 0 0 = -2 := rfl
theorem jet_second_1_1_1_1 : (jet r y).second 1 1 1 1 = -2 * (r ^ 2 - 1)⁻¹ ^ 2 + 8 * r ^ 2 * (r ^ 2 - 1)⁻¹ ^ 3 := rfl
theorem jet_second_1_1_2_2 : (jet r y).second 1 1 2 2 = 2 * y⁻¹ ^ 2 := rfl
theorem jet_second_1_1_3_3 : (jet r y).second 1 1 3 3 = 2 * y⁻¹ ^ 2 := rfl
theorem jet_second_1_2_0_0 : (jet r y).second 1 2 0 0 = 0 := rfl
theorem jet_second_1_2_1_1 : (jet r y).second 1 2 1 1 = 0 := rfl
theorem jet_second_1_2_2_2 : (jet r y).second 1 2 2 2 = 0 := rfl
theorem jet_second_1_2_3_3 : (jet r y).second 1 2 3 3 = 0 := rfl
theorem jet_second_1_3_0_0 : (jet r y).second 1 3 0 0 = 0 := rfl
theorem jet_second_1_3_1_1 : (jet r y).second 1 3 1 1 = 0 := rfl
theorem jet_second_1_3_2_2 : (jet r y).second 1 3 2 2 = -4 * r * y⁻¹ ^ 3 := rfl
theorem jet_second_1_3_3_3 : (jet r y).second 1 3 3 3 = -4 * r * y⁻¹ ^ 3 := rfl
theorem jet_second_2_0_0_0 : (jet r y).second 2 0 0 0 = 0 := rfl
theorem jet_second_2_0_1_1 : (jet r y).second 2 0 1 1 = 0 := rfl
theorem jet_second_2_0_2_2 : (jet r y).second 2 0 2 2 = 0 := rfl
theorem jet_second_2_0_3_3 : (jet r y).second 2 0 3 3 = 0 := rfl
theorem jet_second_2_1_0_0 : (jet r y).second 2 1 0 0 = 0 := rfl
theorem jet_second_2_1_1_1 : (jet r y).second 2 1 1 1 = 0 := rfl
theorem jet_second_2_1_2_2 : (jet r y).second 2 1 2 2 = 0 := rfl
theorem jet_second_2_1_3_3 : (jet r y).second 2 1 3 3 = 0 := rfl
theorem jet_second_2_2_0_0 : (jet r y).second 2 2 0 0 = 0 := rfl
theorem jet_second_2_2_1_1 : (jet r y).second 2 2 1 1 = 0 := rfl
theorem jet_second_2_2_2_2 : (jet r y).second 2 2 2 2 = 0 := rfl
theorem jet_second_2_2_3_3 : (jet r y).second 2 2 3 3 = 0 := rfl
theorem jet_second_2_3_0_0 : (jet r y).second 2 3 0 0 = 0 := rfl
theorem jet_second_2_3_1_1 : (jet r y).second 2 3 1 1 = 0 := rfl
theorem jet_second_2_3_2_2 : (jet r y).second 2 3 2 2 = 0 := rfl
theorem jet_second_2_3_3_3 : (jet r y).second 2 3 3 3 = 0 := rfl
theorem jet_second_3_0_0_0 : (jet r y).second 3 0 0 0 = 0 := rfl
theorem jet_second_3_0_1_1 : (jet r y).second 3 0 1 1 = 0 := rfl
theorem jet_second_3_0_2_2 : (jet r y).second 3 0 2 2 = 0 := rfl
theorem jet_second_3_0_3_3 : (jet r y).second 3 0 3 3 = 0 := rfl
theorem jet_second_3_1_0_0 : (jet r y).second 3 1 0 0 = 0 := rfl
theorem jet_second_3_1_1_1 : (jet r y).second 3 1 1 1 = 0 := rfl
theorem jet_second_3_1_2_2 : (jet r y).second 3 1 2 2 = -4 * r * y⁻¹ ^ 3 := rfl
theorem jet_second_3_1_3_3 : (jet r y).second 3 1 3 3 = -4 * r * y⁻¹ ^ 3 := rfl
theorem jet_second_3_2_0_0 : (jet r y).second 3 2 0 0 = 0 := rfl
theorem jet_second_3_2_1_1 : (jet r y).second 3 2 1 1 = 0 := rfl
theorem jet_second_3_2_2_2 : (jet r y).second 3 2 2 2 = 0 := rfl
theorem jet_second_3_2_3_3 : (jet r y).second 3 2 3 3 = 0 := rfl
theorem jet_second_3_3_0_0 : (jet r y).second 3 3 0 0 = 0 := rfl
theorem jet_second_3_3_1_1 : (jet r y).second 3 3 1 1 = 0 := rfl
theorem jet_second_3_3_2_2 : (jet r y).second 3 3 2 2 = 6 * r ^ 2 * y⁻¹ ^ 4 := rfl
theorem jet_second_3_3_3_3 : (jet r y).second 3 3 3 3 = 6 * r ^ 2 * y⁻¹ ^ 4 := rfl

end
end RHTower.D4BMBackground

namespace RHTower.D4BMScalarLinearEquation
open GaloisForLFunctions.HTGeometry
noncomputable section
variable (s r y B S Sx Sy Sxx Sxy : ℂ)

theorem scalarJet_metric_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_metric_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_metric_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_metric_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_metric_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_metric_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_metric_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_metric_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_metric_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_metric_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_0_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_0_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_0_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_0_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_0_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_0_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_0_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_0_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_0_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_0_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_1_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_1_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_1_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_1_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_1_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_1_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_1_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_1_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_1_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_1_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_2_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_2_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_2_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_2_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_2_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_2_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_2_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_2_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_2_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_2_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_3_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_3_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_3_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_3_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_3_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_3_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_3_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_3_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_3_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_first_3_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_0_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_0_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_0_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_0_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_0_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_0_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_0_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_0_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_0_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_0_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_1_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_1_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_1_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_1_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_1_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_1_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_1_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_1_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_1_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_1_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_2_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_2_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_2_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_2_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_2_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_2_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_2_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_2_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_2_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_2_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_3_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_3_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_3_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_3_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_3_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_3_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_3_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_3_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_3_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_0_3_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_0_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_0_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_0_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_0_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_0_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_0_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_0_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_0_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_0_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_0_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_1_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_1_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_1_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_1_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_1_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_1_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_1_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_1_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_1_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_1_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_2_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_2_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_2_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_2_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_2_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_2_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_2_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_2_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_2_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_2_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_3_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_3_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_3_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_3_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_3_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_3_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_3_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_3_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_3_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_1_3_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_0_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_0_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_0_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_0_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_0_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_0_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_0_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_0_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_0_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_0_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_1_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_1_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_1_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_1_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_1_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_1_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_1_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_1_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_1_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_1_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_2_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_2_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_2_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_2_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_2_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_2_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_2_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_2_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_2_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_2_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_3_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_3_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_3_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_3_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_3_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_3_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_3_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_3_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_3_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_2_3_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_0_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_0_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_0_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_0_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_0_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_0_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_0_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_0_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_0_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_0_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_1_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_1_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_1_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_1_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_1_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_1_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_1_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_1_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_1_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_1_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_2_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_2_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_2_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_2_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_2_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_2_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_2_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_2_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_2_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_2_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_3_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_3_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_3_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_3_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_3_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_3_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_3_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_3_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_3_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_second_3_3_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

theorem scalarJet_metric_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 0 =
      B * S * s * (-3 / 2) + B * S * s * r⁻¹ ^ 2 * (1 / 2) + B * S * s ^ 2 * (1 / 2) + B * S * s ^ 2 * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_metric_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 1 =
      -(B * S * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * S * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_metric_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 0 =
      -(B * S * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * S * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_metric_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 1 =
      B * S * s * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * S * s * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + B * S * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * S * s ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_metric_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 2 =
      -(B * S * r ^ 2 * y⁻¹ ^ 2) + B * S * s * y⁻¹ ^ 2 * (-1 / 2) + B * S * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_metric_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 3 =
      -(B * S * r ^ 2 * y⁻¹ ^ 2) + B * S * s * y⁻¹ ^ 2 * (-1 / 2) + B * S * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_0_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 0 0 =
      s ^ 2 * B * S * (-3 / 2) + s ^ 2 * B * S * r⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * S * (1 / 2) + s ^ 3 * B * S * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_0_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 0 1 =
      -(s ^ 2 * B * S * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 3 * B * S * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_0_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 1 0 =
      -(s ^ 2 * B * S * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 3 * B * S * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_0_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 1 1 =
      s ^ 2 * B * S * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 2 * B * S * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + s ^ 3 * B * S * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * S * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_0_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 2 2 =
      -(s * B * S * r ^ 2 * y⁻¹ ^ 2) + s ^ 2 * B * S * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * S * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_0_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 3 3 =
      -(s * B * S * r ^ 2 * y⁻¹ ^ 2) + s ^ 2 * B * S * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * S * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_1_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 0 0 =
      -(s * B * r⁻¹ ^ 3 * S) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * (-3 / 2) + s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * S * (1 / 2) - s ^ 2 * B * r⁻¹ ^ 3 * S + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * (1 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_1_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 0 1 =
      -(s * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * 2) - s * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 3 - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 4 + s ^ 2 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_1_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 1 0 =
      -(s * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * 2) - s * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 3 - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 4 + s ^ 2 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_1_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 1 1 =
      -(s * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2) + s * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * S * 6 - s * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * S - s ^ 2 * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 - s ^ 2 * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * S * (-3 / 2) - s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * (1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * S * (1 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_1_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 2 2 =
      -(s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) - B * r * S * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_1_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 3 3 =
      -(s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) - B * r * S * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_2_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 0 0 =
      B * Sx * s * (-3 / 2) + B * Sx * s * r⁻¹ ^ 2 * (1 / 2) + B * Sx * s ^ 2 * (1 / 2) + B * Sx * s ^ 2 * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_2_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 0 1 =
      -(B * Sx * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * Sx * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_2_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 1 0 =
      -(B * Sx * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * Sx * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_2_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 1 1 =
      B * Sx * s * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * Sx * s * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + B * Sx * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * Sx * s ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_2_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 2 2 =
      -(B * Sx * r ^ 2 * y⁻¹ ^ 2) + B * Sx * s * y⁻¹ ^ 2 * (-1 / 2) + B * Sx * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_2_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 3 3 =
      -(B * Sx * r ^ 2 * y⁻¹ ^ 2) + B * Sx * s * y⁻¹ ^ 2 * (-1 / 2) + B * Sx * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_3_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 0 0 =
      B * Sy * s * (-3 / 2) + B * Sy * s * r⁻¹ ^ 2 * (1 / 2) + B * Sy * s ^ 2 * (1 / 2) + B * Sy * s ^ 2 * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_3_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 0 1 =
      -(B * Sy * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * Sy * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_3_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 1 0 =
      -(B * Sy * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * Sy * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_3_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 1 1 =
      B * Sy * s * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * Sy * s * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + B * Sy * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * Sy * s ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_3_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 2 2 =
      S * B * r ^ 2 * y⁻¹ ^ 3 * 2 + S * B * s * y⁻¹ ^ 3 + S * B * s ^ 2 * y⁻¹ ^ 3 - B * Sy * r ^ 2 * y⁻¹ ^ 2 + B * Sy * s * y⁻¹ ^ 2 * (-1 / 2) + B * Sy * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_first_3_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 3 3 =
      S * B * r ^ 2 * y⁻¹ ^ 3 * 2 + S * B * s * y⁻¹ ^ 3 + S * B * s ^ 2 * y⁻¹ ^ 3 - B * Sy * r ^ 2 * y⁻¹ ^ 2 + B * Sy * s * y⁻¹ ^ 2 * (-1 / 2) + B * Sy * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_0_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 0 0 =
      s ^ 3 * B * S * (-3 / 2) + s ^ 3 * B * S * r⁻¹ ^ 2 * (1 / 2) + s ^ 4 * B * S * (1 / 2) + s ^ 4 * B * S * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_0_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 0 1 =
      -(s ^ 3 * B * S * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 4 * B * S * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_0_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 1 0 =
      -(s ^ 3 * B * S * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 4 * B * S * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_0_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 1 1 =
      s ^ 3 * B * S * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * S * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + s ^ 4 * B * S * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 4 * B * S * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_0_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 2 2 =
      -(s ^ 2 * B * S * r ^ 2 * y⁻¹ ^ 2) + s ^ 3 * B * S * y⁻¹ ^ 2 * (-1 / 2) + s ^ 4 * B * S * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_0_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 3 3 =
      -(s ^ 2 * B * S * r ^ 2 * y⁻¹ ^ 2) + s ^ 3 * B * S * y⁻¹ ^ 2 * (-1 / 2) + s ^ 4 * B * S * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_1_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 0 0 =
      -(s ^ 2 * B * r⁻¹ ^ 3 * S) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * (-3 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * S * (1 / 2) - s ^ 3 * B * r⁻¹ ^ 3 * S + s ^ 4 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * (1 / 2) + s ^ 4 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_1_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 0 1 =
      -(s ^ 2 * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * 2) - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 2 * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 3 - s ^ 3 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 4 + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 4 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_1_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 1 0 =
      -(s ^ 2 * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * 2) - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 2 * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 3 - s ^ 3 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 4 + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 4 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_1_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 1 1 =
      -(s ^ 2 * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2) + s ^ 2 * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * S * 6 - s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * S - s ^ 3 * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 - s ^ 3 * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * S * (-3 / 2) - s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * (1 / 2) + s ^ 4 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * S * (1 / 2) + s ^ 4 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_1_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 2 2 =
      -(s * B * r * S * y⁻¹ ^ 2 * 2) - s ^ 2 * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) + s ^ 4 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_1_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 3 3 =
      -(s * B * r * S * y⁻¹ ^ 2 * 2) - s ^ 2 * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) + s ^ 4 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_2_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 0 0 =
      s ^ 2 * B * Sx * (-3 / 2) + s ^ 2 * B * Sx * r⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * Sx * (1 / 2) + s ^ 3 * B * Sx * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_2_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 0 1 =
      -(s ^ 2 * B * Sx * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 3 * B * Sx * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_2_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 1 0 =
      -(s ^ 2 * B * Sx * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 3 * B * Sx * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_2_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 1 1 =
      s ^ 2 * B * Sx * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 2 * B * Sx * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + s ^ 3 * B * Sx * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * Sx * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_2_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 2 2 =
      -(s * B * Sx * r ^ 2 * y⁻¹ ^ 2) + s ^ 2 * B * Sx * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * Sx * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_2_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 3 3 =
      -(s * B * Sx * r ^ 2 * y⁻¹ ^ 2) + s ^ 2 * B * Sx * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * Sx * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_3_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 0 0 =
      s ^ 2 * B * Sy * (-3 / 2) + s ^ 2 * B * Sy * r⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * Sy * (1 / 2) + s ^ 3 * B * Sy * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_3_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 0 1 =
      -(s ^ 2 * B * Sy * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 3 * B * Sy * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_3_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 1 0 =
      -(s ^ 2 * B * Sy * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 3 * B * Sy * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_3_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 1 1 =
      s ^ 2 * B * Sy * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 2 * B * Sy * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + s ^ 3 * B * Sy * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * Sy * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_3_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 2 2 =
      S * s * B * r ^ 2 * y⁻¹ ^ 3 * 2 + S * s ^ 2 * B * y⁻¹ ^ 3 + S * s ^ 3 * B * y⁻¹ ^ 3 - s * B * Sy * r ^ 2 * y⁻¹ ^ 2 + s ^ 2 * B * Sy * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * Sy * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_0_3_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 3 3 =
      S * s * B * r ^ 2 * y⁻¹ ^ 3 * 2 + S * s ^ 2 * B * y⁻¹ ^ 3 + S * s ^ 3 * B * y⁻¹ ^ 3 - s * B * Sy * r ^ 2 * y⁻¹ ^ 2 + s ^ 2 * B * Sy * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * Sy * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_0_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 0 0 =
      -(s ^ 2 * B * r⁻¹ ^ 3 * S) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * (-3 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * S * (1 / 2) - s ^ 3 * B * r⁻¹ ^ 3 * S + s ^ 4 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * (1 / 2) + s ^ 4 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_0_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 0 1 =
      -(s ^ 2 * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * 2) - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 2 * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 3 - s ^ 3 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 4 + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 4 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_0_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 1 0 =
      -(s ^ 2 * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * 2) - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 2 * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 3 - s ^ 3 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 4 + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 4 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_0_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 1 1 =
      -(s ^ 2 * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2) + s ^ 2 * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * S * 6 - s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * S - s ^ 3 * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 - s ^ 3 * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * S * (-3 / 2) - s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * S + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * (1 / 2) + s ^ 4 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * S * (1 / 2) + s ^ 4 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_0_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 2 2 =
      -(s * B * r * S * y⁻¹ ^ 2 * 2) - s ^ 2 * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) + s ^ 4 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_0_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 3 3 =
      -(s * B * r * S * y⁻¹ ^ 2 * 2) - s ^ 2 * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) + s ^ 4 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_1_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 0 0 =
      B * s * r⁻¹ ^ 4 * S * 3 + B * s ^ 2 * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * (9 / 2) + B * s ^ 2 * r ^ 2 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 2 * S * (-3 / 2) + B * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * (-3 / 2) - B * s ^ 2 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ * S * 2 + B * s ^ 2 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 2 * S * (1 / 2) + B * s ^ 2 * r⁻¹ ^ 4 * S * 3 + B * s ^ 3 * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * (-3 / 2) + B * s ^ 3 * r ^ 2 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 2 * S * (-3 / 2) - B * s ^ 3 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S - B * s ^ 3 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ * S * 2 + B * s ^ 3 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 2 * S + B * s ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * (1 / 2) + B * s ^ 4 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 2 * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_1_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 0 1 =
      -(B * s * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 4) - B * s * r ^ 2 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 + B * s * r ^ 3 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 18 + B * s * r ^ 4 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 12 - B * s * r ^ 6 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 18 - B * s * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * 2 - B * s ^ 2 * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 10 - B * s ^ 2 * r ^ 2 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 15 + B * s ^ 2 * r ^ 4 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 27 + B * s ^ 2 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 - B * s ^ 3 * r ^ 2 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 10 + B * s ^ 3 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 3 + B * s ^ 4 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_1_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 1 0 =
      -(B * s * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 4) - B * s * r ^ 2 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 + B * s * r ^ 3 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 18 + B * s * r ^ 4 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 12 - B * s * r ^ 6 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 18 - B * s * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * 2 - B * s ^ 2 * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 10 - B * s ^ 2 * r ^ 2 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 15 + B * s ^ 2 * r ^ 4 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 27 + B * s ^ 2 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 - B * s ^ 3 * r ^ 2 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 10 + B * s ^ 3 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 3 + B * s ^ 4 * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_1_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 1 1 =
      B * s * r * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 8 + B * s * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 4 * S * 12 - B * s * r ^ 2 * (-1 + r ^ 2)⁻¹ ^ 4 * S * 36 - B * s * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 + B * s * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 3 + B * s * (-1 + r ^ 2)⁻¹ ^ 3 * S * 6 + B * s ^ 2 * r * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 4 * S * 12 + B * s ^ 2 * r * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 8 - B * s ^ 2 * r * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 4 * S * 4 + B * s ^ 2 * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 4 * S * (33 / 2) + B * s ^ 2 * r ^ 2 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 4 * S * (-3 / 2) + B * s ^ 2 * r ^ 2 * (-1 + r ^ 2)⁻¹ ^ 4 * S * 12 - B * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 + B * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 4 * S * (-3 / 2) + B * s ^ 2 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 2 * S * 3 - B * s ^ 2 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 + B * s ^ 2 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 4 * S * (1 / 2) - B * s ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 - B * s ^ 3 * r * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 4 * S * 4 - B * s ^ 3 * r * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 4 * S * 4 + B * s ^ 3 * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 4 * S * (-3 / 2) + B * s ^ 3 * r ^ 2 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 4 * S * (-3 / 2) - B * s ^ 3 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 4 * S - B * s ^ 3 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 3 * S * 2 + B * s ^ 3 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 4 * S + B * s ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 4 * S * (1 / 2) + B * s ^ 4 * r⁻¹ ^ 4 * (-1 + r ^ 2)⁻¹ ^ 4 * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_1_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 2 2 =
      -(B * s * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * 4) - B * s * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 + B * s * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 * 3 + B * s ^ 2 * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 * (1 / 2) + B * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 * (-1 / 2) + B * s ^ 3 * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 * (3 / 2) - B * s ^ 3 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 + B * s ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 * (-1 / 2) - B * S * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_1_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 3 3 =
      -(B * s * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * S * y⁻¹ ^ 2 * 4) - B * s * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 + B * s * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 * 3 + B * s ^ 2 * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 * (1 / 2) + B * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 * (-1 / 2) + B * s ^ 3 * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 * (3 / 2) - B * s ^ 3 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 + B * s ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * S * y⁻¹ ^ 2 * (-1 / 2) - B * S * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_2_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 0 0 =
      -(s * B * r⁻¹ ^ 3 * Sx) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * (-3 / 2) + s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * Sx * (1 / 2) - s ^ 2 * B * r⁻¹ ^ 3 * Sx + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * (1 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * Sx * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_2_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 0 1 =
      -(s * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * 2) - s * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx + s * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx * 3 - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx * 4 + s ^ 2 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_2_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 1 0 =
      -(s * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * 2) - s * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx + s * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx * 3 - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx * 4 + s ^ 2 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_2_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 1 1 =
      -(s * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * 2) + s * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * 6 - s * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx - s ^ 2 * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * 2 - s ^ 2 * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * 2 + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * (-3 / 2) - s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx + s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * (1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * (1 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_2_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 2 2 =
      -(s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2 * (-1 / 2) - B * r * Sx * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_2_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 3 3 =
      -(s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2 * (-1 / 2) - B * r * Sx * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_3_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 0 0 =
      -(s * B * r⁻¹ ^ 3 * Sy) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * (-3 / 2) + s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * Sy * (1 / 2) - s ^ 2 * B * r⁻¹ ^ 3 * Sy + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * (1 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * Sy * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_3_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 0 1 =
      -(s * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * 2) - s * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy + s * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy * 3 - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy * 4 + s ^ 2 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_3_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 1 0 =
      -(s * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * 2) - s * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy + s * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy * 3 - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy * 4 + s ^ 2 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_3_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 1 1 =
      -(s * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * 2) + s * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * 6 - s * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy - s ^ 2 * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * 2 - s ^ 2 * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * 2 + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * (-3 / 2) - s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy + s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * (1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * (1 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_3_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 2 2 =
      S * s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 * 2 + S * s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 + S * s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 + S * B * r * y⁻¹ ^ 3 * 4 - s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 * (-1 / 2) - B * r * Sy * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_1_3_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 3 3 =
      S * s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 * 2 + S * s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 + S * s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 + S * B * r * y⁻¹ ^ 3 * 4 - s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 * (-1 / 2) - B * r * Sy * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_0_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 0 0 =
      s ^ 2 * B * Sx * (-3 / 2) + s ^ 2 * B * Sx * r⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * Sx * (1 / 2) + s ^ 3 * B * Sx * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_0_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 0 1 =
      -(s ^ 2 * B * Sx * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 3 * B * Sx * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_0_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 1 0 =
      -(s ^ 2 * B * Sx * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 3 * B * Sx * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_0_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 1 1 =
      s ^ 2 * B * Sx * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 2 * B * Sx * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + s ^ 3 * B * Sx * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * Sx * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_0_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 2 2 =
      -(s * B * Sx * r ^ 2 * y⁻¹ ^ 2) + s ^ 2 * B * Sx * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * Sx * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_0_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 3 3 =
      -(s * B * Sx * r ^ 2 * y⁻¹ ^ 2) + s ^ 2 * B * Sx * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * Sx * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_1_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 0 0 =
      -(s * B * r⁻¹ ^ 3 * Sx) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * (-3 / 2) + s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * Sx * (1 / 2) - s ^ 2 * B * r⁻¹ ^ 3 * Sx + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * (1 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * Sx * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_1_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 0 1 =
      -(s * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * 2) - s * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx + s * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx * 3 - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx * 4 + s ^ 2 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_1_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 1 0 =
      -(s * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * 2) - s * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx + s * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx * 3 - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx * 4 + s ^ 2 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_1_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 1 1 =
      -(s * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * 2) + s * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * 6 - s * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx - s ^ 2 * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * 2 - s ^ 2 * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * 2 + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * (-3 / 2) - s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * Sx + s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * (1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * (1 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * Sx * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_1_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 2 2 =
      -(s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2 * (-1 / 2) - B * r * Sx * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_1_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 3 3 =
      -(s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sx * y⁻¹ ^ 2 * (-1 / 2) - B * r * Sx * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_2_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 0 0 =
      B * Sxx * s * (-3 / 2) + B * Sxx * s * r⁻¹ ^ 2 * (1 / 2) + B * Sxx * s ^ 2 * (1 / 2) + B * Sxx * s ^ 2 * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_2_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 0 1 =
      -(B * Sxx * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * Sxx * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_2_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 1 0 =
      -(B * Sxx * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * Sxx * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_2_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 1 1 =
      B * Sxx * s * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * Sxx * s * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + B * Sxx * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * Sxx * s ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_2_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 2 2 =
      -(B * Sxx * r ^ 2 * y⁻¹ ^ 2) + B * Sxx * s * y⁻¹ ^ 2 * (-1 / 2) + B * Sxx * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_2_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 3 3 =
      -(B * Sxx * r ^ 2 * y⁻¹ ^ 2) + B * Sxx * s * y⁻¹ ^ 2 * (-1 / 2) + B * Sxx * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_3_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 0 0 =
      B * Sxy * s * (-3 / 2) + B * Sxy * s * r⁻¹ ^ 2 * (1 / 2) + B * Sxy * s ^ 2 * (1 / 2) + B * Sxy * s ^ 2 * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_3_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 0 1 =
      -(B * Sxy * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * Sxy * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_3_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 1 0 =
      -(B * Sxy * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * Sxy * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_3_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 1 1 =
      B * Sxy * s * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * Sxy * s * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + B * Sxy * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * Sxy * s ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_3_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 2 2 =
      Sx * B * r ^ 2 * y⁻¹ ^ 3 * 2 + Sx * B * s * y⁻¹ ^ 3 + Sx * B * s ^ 2 * y⁻¹ ^ 3 - B * Sxy * r ^ 2 * y⁻¹ ^ 2 + B * Sxy * s * y⁻¹ ^ 2 * (-1 / 2) + B * Sxy * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_2_3_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 3 3 =
      Sx * B * r ^ 2 * y⁻¹ ^ 3 * 2 + Sx * B * s * y⁻¹ ^ 3 + Sx * B * s ^ 2 * y⁻¹ ^ 3 - B * Sxy * r ^ 2 * y⁻¹ ^ 2 + B * Sxy * s * y⁻¹ ^ 2 * (-1 / 2) + B * Sxy * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_0_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 0 0 =
      s ^ 2 * B * Sy * (-3 / 2) + s ^ 2 * B * Sy * r⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * Sy * (1 / 2) + s ^ 3 * B * Sy * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_0_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 0 1 =
      -(s ^ 2 * B * Sy * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 3 * B * Sy * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_0_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 1 0 =
      -(s ^ 2 * B * Sy * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + s ^ 3 * B * Sy * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_0_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 1 1 =
      s ^ 2 * B * Sy * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 2 * B * Sy * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + s ^ 3 * B * Sy * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + s ^ 3 * B * Sy * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_0_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 2 2 =
      S * s * B * r ^ 2 * y⁻¹ ^ 3 * 2 + S * s ^ 2 * B * y⁻¹ ^ 3 + S * s ^ 3 * B * y⁻¹ ^ 3 - s * B * Sy * r ^ 2 * y⁻¹ ^ 2 + s ^ 2 * B * Sy * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * Sy * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_0_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 3 3 =
      S * s * B * r ^ 2 * y⁻¹ ^ 3 * 2 + S * s ^ 2 * B * y⁻¹ ^ 3 + S * s ^ 3 * B * y⁻¹ ^ 3 - s * B * Sy * r ^ 2 * y⁻¹ ^ 2 + s ^ 2 * B * Sy * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * Sy * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_1_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 0 0 =
      -(s * B * r⁻¹ ^ 3 * Sy) + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * (-3 / 2) + s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * Sy * (1 / 2) - s ^ 2 * B * r⁻¹ ^ 3 * Sy + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * (1 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ * Sy * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_1_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 0 1 =
      -(s * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * 2) - s * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy + s * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy * 3 - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy * 4 + s ^ 2 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_1_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 1 0 =
      -(s * B * r * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * 2) - s * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy + s * B * r ^ 4 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy * 3 - s ^ 2 * B * r ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy * 4 + s ^ 2 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy + s ^ 3 * B * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_1_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 1 1 =
      -(s * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * 2) + s * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * 6 - s * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy - s ^ 2 * B * r * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * 2 - s ^ 2 * B * r * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * 2 + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * (-3 / 2) - s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 2 * Sy + s ^ 2 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * (1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * (1 / 2) + s ^ 3 * B * r⁻¹ ^ 3 * (-1 + r ^ 2)⁻¹ ^ 3 * Sy * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_1_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 2 2 =
      S * s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 * 2 + S * s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 + S * s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 + S * B * r * y⁻¹ ^ 3 * 4 - s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 * (-1 / 2) - B * r * Sy * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_1_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 3 3 =
      S * s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 * 2 + S * s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 + S * s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * y⁻¹ ^ 3 + S * B * r * y⁻¹ ^ 3 * 4 - s * B * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 + s ^ 2 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 * (-1 / 2) + s ^ 3 * B * r⁻¹ * (-1 + r ^ 2)⁻¹ * Sy * y⁻¹ ^ 2 * (-1 / 2) - B * r * Sy * y⁻¹ ^ 2 * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_2_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 0 0 =
      B * Sxy * s * (-3 / 2) + B * Sxy * s * r⁻¹ ^ 2 * (1 / 2) + B * Sxy * s ^ 2 * (1 / 2) + B * Sxy * s ^ 2 * r⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_2_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 0 1 =
      -(B * Sxy * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * Sxy * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_2_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 1 0 =
      -(B * Sxy * s * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹) + B * Sxy * s ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_2_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 1 1 =
      B * Sxy * s * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * Sxy * s * (-1 + r ^ 2)⁻¹ ^ 2 * (-3 / 2) + B * Sxy * s ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * Sxy * s ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_2_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 2 2 =
      Sx * B * r ^ 2 * y⁻¹ ^ 3 * 2 + Sx * B * s * y⁻¹ ^ 3 + Sx * B * s ^ 2 * y⁻¹ ^ 3 - B * Sxy * r ^ 2 * y⁻¹ ^ 2 + B * Sxy * s * y⁻¹ ^ 2 * (-1 / 2) + B * Sxy * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_2_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 3 3 =
      Sx * B * r ^ 2 * y⁻¹ ^ 3 * 2 + Sx * B * s * y⁻¹ ^ 3 + Sx * B * s ^ 2 * y⁻¹ ^ 3 - B * Sxy * r ^ 2 * y⁻¹ ^ 2 + B * Sxy * s * y⁻¹ ^ 2 * (-1 / 2) + B * Sxy * s ^ 2 * y⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_3_0_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 0 0 =
      -(S * B * s * y⁻¹ ^ 2 * 3) + S * B * s * y⁻¹ ^ 2 * r⁻¹ ^ 2 + S * B * s ^ 2 * y⁻¹ ^ 2 * (-7 / 2) + S * B * s ^ 2 * y⁻¹ ^ 2 * r⁻¹ ^ 2 * (5 / 2) + S * B * s ^ 3 * y⁻¹ ^ 2 * r⁻¹ ^ 2 * 2 + S * B * s ^ 4 * y⁻¹ ^ 2 * (1 / 2) + S * B * s ^ 4 * y⁻¹ ^ 2 * r⁻¹ ^ 2 * (1 / 2) + B * s * Sxx * (3 / 2) + B * s * Sxx * r⁻¹ ^ 2 * (-1 / 2) + B * s ^ 2 * Sxx * (-1 / 2) + B * s ^ 2 * Sxx * r⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_3_0_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 0 1 =
      -(S * B * s * y⁻¹ ^ 2 * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * 2) - S * B * s ^ 2 * y⁻¹ ^ 2 * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * 3 + S * B * s ^ 2 * y⁻¹ ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * 2 - S * B * s ^ 3 * y⁻¹ ^ 2 * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ + S * B * s ^ 3 * y⁻¹ ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * 3 + S * B * s ^ 4 * y⁻¹ ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ + B * s * Sxx * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ - B * s ^ 2 * Sxx * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_3_1_0 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 1 0 =
      -(S * B * s * y⁻¹ ^ 2 * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * 2) - S * B * s ^ 2 * y⁻¹ ^ 2 * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * 3 + S * B * s ^ 2 * y⁻¹ ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * 2 - S * B * s ^ 3 * y⁻¹ ^ 2 * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ + S * B * s ^ 3 * y⁻¹ ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ * 3 + S * B * s ^ 4 * y⁻¹ ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ + B * s * Sxx * r ^ 2 * r⁻¹ * (-1 + r ^ 2)⁻¹ - B * s ^ 2 * Sxx * r⁻¹ * (-1 + r ^ 2)⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_3_1_1 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 1 1 =
      S * B * s * y⁻¹ ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 - S * B * s * y⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * 3 + S * B * s ^ 2 * y⁻¹ ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (5 / 2) + S * B * s ^ 2 * y⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (-7 / 2) + S * B * s ^ 3 * y⁻¹ ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * 2 + S * B * s ^ 4 * y⁻¹ ^ 2 * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + S * B * s ^ 4 * y⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (1 / 2) + B * s * Sxx * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (-1 / 2) + B * s * Sxx * (-1 + r ^ 2)⁻¹ ^ 2 * (3 / 2) + B * s ^ 2 * Sxx * r⁻¹ ^ 2 * (-1 + r ^ 2)⁻¹ ^ 2 * (-1 / 2) + B * s ^ 2 * Sxx * (-1 + r ^ 2)⁻¹ ^ 2 * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_3_2_2 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 2 2 =
      -(S * B * s * y⁻¹ ^ 4 * 4) - S * B * s * y⁻¹ ^ 4 * r ^ 2 * 3 + S * B * s ^ 2 * y⁻¹ ^ 4 * (-11 / 2) - S * B * s ^ 2 * y⁻¹ ^ 4 * r ^ 2 - S * B * s ^ 3 * y⁻¹ ^ 4 * 2 + S * B * s ^ 4 * y⁻¹ ^ 4 * (-1 / 2) - S * B * y⁻¹ ^ 4 * r ^ 2 * 8 + Sy * B * s * y⁻¹ ^ 3 * 2 + Sy * B * s ^ 2 * y⁻¹ ^ 3 * 2 + Sy * B * y⁻¹ ^ 3 * r ^ 2 * 4 + B * s * y⁻¹ ^ 2 * Sxx * (1 / 2) + B * s ^ 2 * y⁻¹ ^ 2 * Sxx * (1 / 2) + B * y⁻¹ ^ 2 * Sxx * r ^ 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

theorem scalarJet_second_3_3_3_3 :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 3 3 =
      -(S * B * s * y⁻¹ ^ 4 * 4) - S * B * s * y⁻¹ ^ 4 * r ^ 2 * 3 + S * B * s ^ 2 * y⁻¹ ^ 4 * (-11 / 2) - S * B * s ^ 2 * y⁻¹ ^ 4 * r ^ 2 - S * B * s ^ 3 * y⁻¹ ^ 4 * 2 + S * B * s ^ 4 * y⁻¹ ^ 4 * (-1 / 2) - S * B * y⁻¹ ^ 4 * r ^ 2 * 8 + Sy * B * s * y⁻¹ ^ 3 * 2 + Sy * B * s ^ 2 * y⁻¹ ^ 3 * 2 + Sy * B * y⁻¹ ^ 3 * r ^ 2 * 4 + B * s * y⁻¹ ^ 2 * Sxx * (1 / 2) + B * s ^ 2 * y⁻¹ ^ 2 * Sxx * (1 / 2) + B * y⁻¹ ^ 2 * Sxx * r ^ 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf

end
end RHTower.D4BMScalarLinearEquation
