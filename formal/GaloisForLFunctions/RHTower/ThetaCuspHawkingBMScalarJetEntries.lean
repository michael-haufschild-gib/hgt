import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetQuadraticEinstein
import GaloisForLFunctions.HTGeometry.InversePowerCancellation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetSimpSets

/-!
# Entry tables for the Birmingham–Mokhtari background jet and the fundamental scalar jet

Every diagonal entry of the background jet and every entry of the fundamental scalar metric jet
is recorded in a fixed normal form whose only inverses are `r⁻¹`, `y⁻¹` and `(r ^ (2 : ℕ) - 1)⁻¹`, with
no monomial carrying both a power and an inverse power of `r` or of `y`.
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

@[bmJetEntry] theorem jet_metric_0_0 : (jet r y).metric 0 0 = -(r ^ (2 : ℕ) - 1) := rfl
@[bmJetEntry] theorem jet_metric_1_1 : (jet r y).metric 1 1 = (r ^ (2 : ℕ) - 1)⁻¹ := rfl
@[bmJetEntry] theorem jet_metric_2_2 : (jet r y).metric 2 2 = r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) := rfl
@[bmJetEntry] theorem jet_metric_3_3 : (jet r y).metric 3 3 = r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) := rfl
@[bmJetEntry] theorem jet_first_0_0_0 : (jet r y).first 0 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_first_0_1_1 : (jet r y).first 0 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_first_0_2_2 : (jet r y).first 0 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_first_0_3_3 : (jet r y).first 0 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_first_1_0_0 : (jet r y).first 1 0 0 = -2 * r := rfl
@[bmJetEntry] theorem jet_first_1_1_1 : (jet r y).first 1 1 1 = -2 * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) := rfl
@[bmJetEntry] theorem jet_first_1_2_2 : (jet r y).first 1 2 2 = 2 * r * y⁻¹ ^ (2 : ℕ) := rfl
@[bmJetEntry] theorem jet_first_1_3_3 : (jet r y).first 1 3 3 = 2 * r * y⁻¹ ^ (2 : ℕ) := rfl
@[bmJetEntry] theorem jet_first_2_0_0 : (jet r y).first 2 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_first_2_1_1 : (jet r y).first 2 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_first_2_2_2 : (jet r y).first 2 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_first_2_3_3 : (jet r y).first 2 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_first_3_0_0 : (jet r y).first 3 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_first_3_1_1 : (jet r y).first 3 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_first_3_2_2 : (jet r y).first 3 2 2 = -2 * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) := rfl
@[bmJetEntry] theorem jet_first_3_3_3 : (jet r y).first 3 3 3 = -2 * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) := rfl
@[bmJetEntry] theorem jet_second_0_0_0_0 : (jet r y).second 0 0 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_0_1_1 : (jet r y).second 0 0 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_0_2_2 : (jet r y).second 0 0 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_0_3_3 : (jet r y).second 0 0 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_1_0_0 : (jet r y).second 0 1 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_1_1_1 : (jet r y).second 0 1 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_1_2_2 : (jet r y).second 0 1 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_1_3_3 : (jet r y).second 0 1 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_2_0_0 : (jet r y).second 0 2 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_2_1_1 : (jet r y).second 0 2 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_2_2_2 : (jet r y).second 0 2 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_2_3_3 : (jet r y).second 0 2 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_3_0_0 : (jet r y).second 0 3 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_3_1_1 : (jet r y).second 0 3 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_3_2_2 : (jet r y).second 0 3 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_0_3_3_3 : (jet r y).second 0 3 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_0_0_0 : (jet r y).second 1 0 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_0_1_1 : (jet r y).second 1 0 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_0_2_2 : (jet r y).second 1 0 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_0_3_3 : (jet r y).second 1 0 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_1_0_0 : (jet r y).second 1 1 0 0 = -2 := rfl
@[bmJetEntry] theorem jet_second_1_1_1_1 : (jet r y).second 1 1 1 1 = -2 * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) + 8 * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) := rfl
@[bmJetEntry] theorem jet_second_1_1_2_2 : (jet r y).second 1 1 2 2 = 2 * y⁻¹ ^ (2 : ℕ) := rfl
@[bmJetEntry] theorem jet_second_1_1_3_3 : (jet r y).second 1 1 3 3 = 2 * y⁻¹ ^ (2 : ℕ) := rfl
@[bmJetEntry] theorem jet_second_1_2_0_0 : (jet r y).second 1 2 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_2_1_1 : (jet r y).second 1 2 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_2_2_2 : (jet r y).second 1 2 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_2_3_3 : (jet r y).second 1 2 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_3_0_0 : (jet r y).second 1 3 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_3_1_1 : (jet r y).second 1 3 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_1_3_2_2 : (jet r y).second 1 3 2 2 = -4 * r * y⁻¹ ^ (3 : ℕ) := rfl
@[bmJetEntry] theorem jet_second_1_3_3_3 : (jet r y).second 1 3 3 3 = -4 * r * y⁻¹ ^ (3 : ℕ) := rfl
@[bmJetEntry] theorem jet_second_2_0_0_0 : (jet r y).second 2 0 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_0_1_1 : (jet r y).second 2 0 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_0_2_2 : (jet r y).second 2 0 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_0_3_3 : (jet r y).second 2 0 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_1_0_0 : (jet r y).second 2 1 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_1_1_1 : (jet r y).second 2 1 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_1_2_2 : (jet r y).second 2 1 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_1_3_3 : (jet r y).second 2 1 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_2_0_0 : (jet r y).second 2 2 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_2_1_1 : (jet r y).second 2 2 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_2_2_2 : (jet r y).second 2 2 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_2_3_3 : (jet r y).second 2 2 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_3_0_0 : (jet r y).second 2 3 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_3_1_1 : (jet r y).second 2 3 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_3_2_2 : (jet r y).second 2 3 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_2_3_3_3 : (jet r y).second 2 3 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_0_0_0 : (jet r y).second 3 0 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_0_1_1 : (jet r y).second 3 0 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_0_2_2 : (jet r y).second 3 0 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_0_3_3 : (jet r y).second 3 0 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_1_0_0 : (jet r y).second 3 1 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_1_1_1 : (jet r y).second 3 1 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_1_2_2 : (jet r y).second 3 1 2 2 = -4 * r * y⁻¹ ^ (3 : ℕ) := rfl
@[bmJetEntry] theorem jet_second_3_1_3_3 : (jet r y).second 3 1 3 3 = -4 * r * y⁻¹ ^ (3 : ℕ) := rfl
@[bmJetEntry] theorem jet_second_3_2_0_0 : (jet r y).second 3 2 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_2_1_1 : (jet r y).second 3 2 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_2_2_2 : (jet r y).second 3 2 2 2 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_2_3_3 : (jet r y).second 3 2 3 3 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_3_0_0 : (jet r y).second 3 3 0 0 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_3_1_1 : (jet r y).second 3 3 1 1 = 0 := rfl
@[bmJetEntry] theorem jet_second_3_3_2_2 : (jet r y).second 3 3 2 2 = 6 * r ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) := rfl
@[bmJetEntry] theorem jet_second_3_3_3_3 : (jet r y).second 3 3 3 3 = 6 * r ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) := rfl

end
end RHTower.D4BMBackground

namespace RHTower.D4BMScalarLinearEquation
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {s r y B S Sx Sy Sxx Sxy : ℂ}

@[bmJetEntry] theorem scalarJet_metric_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_metric_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_metric_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_metric_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_metric_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_metric_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_metric_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_metric_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_metric_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_metric_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_0_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_0_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_0_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_0_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_0_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_0_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_0_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_0_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_0_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_0_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_1_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_1_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_1_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_1_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_1_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_1_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_1_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_1_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_1_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_1_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_2_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_2_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_2_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_2_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_2_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_2_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_2_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_2_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_2_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_2_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_3_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_3_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_3_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_3_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_3_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_3_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_3_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_3_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_3_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_first_3_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_0_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_0_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_0_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_0_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_0_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_0_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_0_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_0_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_0_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_0_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_1_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_1_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_1_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_1_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_1_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_1_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_1_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_1_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_1_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_1_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_2_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_2_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_2_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_2_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_2_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_2_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_2_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_2_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_2_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_2_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_3_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_3_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_3_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_3_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_3_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_3_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_3_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_3_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_3_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_0_3_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_0_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_0_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_0_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_0_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_0_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_0_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_0_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_0_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_0_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_0_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_1_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_1_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_1_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_1_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_1_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_1_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_1_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_1_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_1_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_1_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_2_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_2_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_2_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_2_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_2_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_2_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_2_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_2_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_2_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_2_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_3_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_3_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_3_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_3_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_3_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_3_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_3_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_3_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_3_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_1_3_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_0_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_0_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_0_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_0_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_0_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_0_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_0_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_0_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_0_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_0_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_1_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_1_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_1_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_1_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_1_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_1_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_1_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_1_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_1_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_1_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_2_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_2_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_2_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_2_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_2_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_2_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_2_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_2_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_2_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_2_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_3_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_3_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_3_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_3_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_3_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_3_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_3_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_3_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_3_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_2_3_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_0_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_0_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_0_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_0_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_0_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_0_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_0_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_0_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_0_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_0_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_1_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_1_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_1_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_1_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_1_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_1_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_1_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_1_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_1_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_1_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_2_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_2_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_2_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_2_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_2_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_2_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_2_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_2_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_2_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_2_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_3_0_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 0 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_3_0_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 0 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_3_1_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 1 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_3_1_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 1 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_3_2_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 2 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_3_2_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 2 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_3_2_3 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 2 3 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_3_3_0 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 3 0 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_3_3_1 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 3 1 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_second_3_3_3_2 : (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 3 2 = 0 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp

@[bmJetEntry] theorem scalarJet_metric_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 0 =
      B * S * s * (-3 / 2) + B * S * s * r⁻¹ ^ (2 : ℕ) * (1 / 2) + B * S * s ^ (2 : ℕ) * (1 / 2) + B * S * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_metric_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 0 1 =
      -(B * S * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * S * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_metric_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 0 =
      -(B * S * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * S * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_metric_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 1 1 =
      B * S * s * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * S * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + B * S * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * S * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_metric_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 2 2 =
      -(B * S * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + B * S * y⁻¹ ^ (2 : ℕ) * s * (-1 / 2) + B * S * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_metric_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).metric 3 3 =
      -(B * S * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + B * S * y⁻¹ ^ (2 : ℕ) * s * (-1 / 2) + B * S * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_0_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 0 0 =
      s ^ (2 : ℕ) * B * S * (-3 / 2) + s ^ (2 : ℕ) * B * S * r⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * S * (1 / 2) + s ^ (3 : ℕ) * B * S * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_0_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 0 1 =
      -(s ^ (2 : ℕ) * B * S * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (3 : ℕ) * B * S * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_0_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 1 0 =
      -(s ^ (2 : ℕ) * B * S * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (3 : ℕ) * B * S * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_0_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 1 1 =
      s ^ (2 : ℕ) * B * S * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (2 : ℕ) * B * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + s ^ (3 : ℕ) * B * S * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 2 2 =
      -(s * B * S * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (-1 / 2) + s ^ (3 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 0 3 3 =
      -(s * B * S * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (-1 / 2) + s ^ (3 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_1_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 0 0 =
      -(s * B * r⁻¹ ^ (3 : ℕ) * S) + s ^ (2 : ℕ) * B * r⁻¹ * S * (r ^ (2 : ℕ) - 1)⁻¹ * (-3 / 2) - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S + s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ * S * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_1_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 0 1 =
      s * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 3 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ * S * 2 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 4 + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_1_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 1 0 =
      s * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 3 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ * S * 2 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 4 + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_1_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 1 1 =
      s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 6 - s * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 - s * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S - s ^ (2 : ℕ) * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 + s ^ (2 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (-7 / 2) - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S + s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 2 2 =
      -(s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * S * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * S * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * S * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) - B * r * S * y⁻¹ ^ (2 : ℕ) * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 1 3 3 =
      -(s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * S * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * S * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * S * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) - B * r * S * y⁻¹ ^ (2 : ℕ) * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_2_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 0 0 =
      B * Sx * s * (-3 / 2) + B * Sx * s * r⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sx * s ^ (2 : ℕ) * (1 / 2) + B * Sx * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_2_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 0 1 =
      -(B * Sx * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * Sx * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_2_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 1 0 =
      -(B * Sx * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * Sx * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_2_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 1 1 =
      B * Sx * s * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sx * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + B * Sx * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sx * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 2 2 =
      -(B * Sx * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + B * Sx * y⁻¹ ^ (2 : ℕ) * s * (-1 / 2) + B * Sx * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 2 3 3 =
      -(B * Sx * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + B * Sx * y⁻¹ ^ (2 : ℕ) * s * (-1 / 2) + B * Sx * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_3_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 0 0 =
      B * Sy * s * (-3 / 2) + B * Sy * s * r⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sy * s ^ (2 : ℕ) * (1 / 2) + B * Sy * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_3_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 0 1 =
      -(B * Sy * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * Sy * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_3_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 1 0 =
      -(B * Sy * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * Sy * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_3_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 1 1 =
      B * Sy * s * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sy * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + B * Sy * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sy * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 2 2 =
      S * B * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * 2 + S * B * y⁻¹ ^ (3 : ℕ) * s + S * B * y⁻¹ ^ (3 : ℕ) * s ^ (2 : ℕ) - B * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sy + B * y⁻¹ ^ (2 : ℕ) * s * Sy * (-1 / 2) + B * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * Sy * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_first_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).first 3 3 3 =
      S * B * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * 2 + S * B * y⁻¹ ^ (3 : ℕ) * s + S * B * y⁻¹ ^ (3 : ℕ) * s ^ (2 : ℕ) - B * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sy + B * y⁻¹ ^ (2 : ℕ) * s * Sy * (-1 / 2) + B * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * Sy * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_0_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 0 0 =
      s ^ (3 : ℕ) * B * S * (-3 / 2) + s ^ (3 : ℕ) * B * S * r⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (4 : ℕ) * B * S * (1 / 2) + s ^ (4 : ℕ) * B * S * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_0_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 0 1 =
      -(s ^ (3 : ℕ) * B * S * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (4 : ℕ) * B * S * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_0_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 1 0 =
      -(s ^ (3 : ℕ) * B * S * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (4 : ℕ) * B * S * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_0_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 1 1 =
      s ^ (3 : ℕ) * B * S * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + s ^ (4 : ℕ) * B * S * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (4 : ℕ) * B * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 2 2 =
      -(s ^ (2 : ℕ) * B * S * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + s ^ (3 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (-1 / 2) + s ^ (4 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 0 3 3 =
      -(s ^ (2 : ℕ) * B * S * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + s ^ (3 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (-1 / 2) + s ^ (4 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_1_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 0 0 =
      -(s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S) + s ^ (3 : ℕ) * B * r⁻¹ * S * (r ^ (2 : ℕ) - 1)⁻¹ * (-3 / 2) - s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (4 : ℕ) * B * r⁻¹ * S * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (4 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_1_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 0 1 =
      s ^ (2 : ℕ) * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 3 - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * S * 2 - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S - s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 4 + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) + s ^ (4 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_1_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 1 0 =
      s ^ (2 : ℕ) * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 3 - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * S * 2 - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S - s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 4 + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) + s ^ (4 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_1_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 1 1 =
      s ^ (2 : ℕ) * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 6 - s ^ (2 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S - s ^ (3 : ℕ) * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 + s ^ (3 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (-7 / 2) - s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (1 / 2) + s ^ (4 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (1 / 2) + s ^ (4 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 2 2 =
      -(s * B * r * S * y⁻¹ ^ (2 : ℕ) * 2) - s ^ (2 : ℕ) * B * r * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ + s ^ (3 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * (-1 / 2) + s ^ (4 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 1 3 3 =
      -(s * B * r * S * y⁻¹ ^ (2 : ℕ) * 2) - s ^ (2 : ℕ) * B * r * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ + s ^ (3 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * (-1 / 2) + s ^ (4 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_2_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 0 0 =
      s ^ (2 : ℕ) * B * Sx * (-3 / 2) + s ^ (2 : ℕ) * B * Sx * r⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * Sx * (1 / 2) + s ^ (3 : ℕ) * B * Sx * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_2_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 0 1 =
      -(s ^ (2 : ℕ) * B * Sx * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (3 : ℕ) * B * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_2_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 1 0 =
      -(s ^ (2 : ℕ) * B * Sx * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (3 : ℕ) * B * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_2_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 1 1 =
      s ^ (2 : ℕ) * B * Sx * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (2 : ℕ) * B * Sx * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + s ^ (3 : ℕ) * B * Sx * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * Sx * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 2 2 =
      -(s * B * Sx * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * Sx * y⁻¹ ^ (2 : ℕ) * (-1 / 2) + s ^ (3 : ℕ) * B * Sx * y⁻¹ ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 2 3 3 =
      -(s * B * Sx * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * Sx * y⁻¹ ^ (2 : ℕ) * (-1 / 2) + s ^ (3 : ℕ) * B * Sx * y⁻¹ ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_3_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 0 0 =
      s ^ (2 : ℕ) * B * Sy * (-3 / 2) + s ^ (2 : ℕ) * B * Sy * r⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * Sy * (1 / 2) + s ^ (3 : ℕ) * B * Sy * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_3_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 0 1 =
      -(s ^ (2 : ℕ) * B * Sy * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (3 : ℕ) * B * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_3_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 1 0 =
      -(s ^ (2 : ℕ) * B * Sy * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (3 : ℕ) * B * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_3_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 1 1 =
      s ^ (2 : ℕ) * B * Sy * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (2 : ℕ) * B * Sy * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + s ^ (3 : ℕ) * B * Sy * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * Sy * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 2 2 =
      S * s * B * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * 2 + S * s ^ (2 : ℕ) * B * y⁻¹ ^ (3 : ℕ) + S * s ^ (3 : ℕ) * B * y⁻¹ ^ (3 : ℕ) - s * B * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sy + s ^ (2 : ℕ) * B * y⁻¹ ^ (2 : ℕ) * Sy * (-1 / 2) + s ^ (3 : ℕ) * B * y⁻¹ ^ (2 : ℕ) * Sy * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_0_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 0 3 3 3 =
      S * s * B * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * 2 + S * s ^ (2 : ℕ) * B * y⁻¹ ^ (3 : ℕ) + S * s ^ (3 : ℕ) * B * y⁻¹ ^ (3 : ℕ) - s * B * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sy + s ^ (2 : ℕ) * B * y⁻¹ ^ (2 : ℕ) * Sy * (-1 / 2) + s ^ (3 : ℕ) * B * y⁻¹ ^ (2 : ℕ) * Sy * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_0_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 0 0 =
      -(s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S) + s ^ (3 : ℕ) * B * r⁻¹ * S * (r ^ (2 : ℕ) - 1)⁻¹ * (-3 / 2) - s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (4 : ℕ) * B * r⁻¹ * S * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (4 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_0_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 0 1 =
      s ^ (2 : ℕ) * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 3 - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * S * 2 - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S - s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 4 + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) + s ^ (4 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_0_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 1 0 =
      s ^ (2 : ℕ) * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 3 - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * S * 2 - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S - s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 4 + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) + s ^ (4 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_0_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 1 1 =
      s ^ (2 : ℕ) * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 6 - s ^ (2 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S - s ^ (3 : ℕ) * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 + s ^ (3 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (-7 / 2) - s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (1 / 2) + s ^ (4 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (1 / 2) + s ^ (4 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 2 2 =
      -(s * B * r * S * y⁻¹ ^ (2 : ℕ) * 2) - s ^ (2 : ℕ) * B * r * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ + s ^ (3 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * (-1 / 2) + s ^ (4 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 0 3 3 =
      -(s * B * r * S * y⁻¹ ^ (2 : ℕ) * 2) - s ^ (2 : ℕ) * B * r * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ + s ^ (3 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * (-1 / 2) + s ^ (4 : ℕ) * B * S * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_1_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 0 0 =
      B * s * r⁻¹ ^ (4 : ℕ) * S * 3 - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * 3 + B * s ^ (2 : ℕ) * r⁻¹ ^ (4 : ℕ) * S * 3 - B * s ^ (2 : ℕ) * r⁻¹ ^ (4 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ * 2 + B * s ^ (2 : ℕ) * r⁻¹ ^ (4 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * s ^ (2 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (9 / 2) + B * s ^ (3 : ℕ) * r⁻¹ ^ (2 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-5 / 2) - B * s ^ (3 : ℕ) * r⁻¹ ^ (4 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ * 2 + B * s ^ (3 : ℕ) * r⁻¹ ^ (4 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) + B * s ^ (3 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + B * s ^ (4 : ℕ) * r⁻¹ ^ (2 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * s ^ (4 : ℕ) * r⁻¹ ^ (4 : ℕ) * S * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_1_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 0 1 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 18 + B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 12 - B * s * r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 18 - B * s * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ * S * 2 - B * s * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 4 - B * s * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 + B * s ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 27 - B * s ^ (2 : ℕ) * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 10 - B * s ^ (2 : ℕ) * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 15 + B * s ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 - B * s ^ (3 : ℕ) * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 10 + B * s ^ (3 : ℕ) * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 3 + B * s ^ (4 : ℕ) * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_1_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 1 0 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 18 + B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 12 - B * s * r ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 18 - B * s * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ * S * 2 - B * s * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 4 - B * s * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 + B * s ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 27 - B * s ^ (2 : ℕ) * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 10 - B * s ^ (2 : ℕ) * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 15 + B * s ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 - B * s ^ (3 : ℕ) * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 10 + B * s ^ (3 : ℕ) * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 3 + B * s ^ (4 : ℕ) * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_1_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 1 1 =
      -(B * s * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S * 36) + B * s * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 6 + B * s * r⁻¹ ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 3 + B * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 6 + B * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S * 12 + B * s ^ (2 : ℕ) * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S * 12 + B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 6 - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S * 7 + B * s ^ (2 : ℕ) * r⁻¹ ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * 3 - B * s ^ (2 : ℕ) * r⁻¹ ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 + B * s ^ (2 : ℕ) * r⁻¹ ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S * (1 / 2) - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S * (57 / 2) + B * s ^ (3 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S * (-13 / 2) - B * s ^ (3 : ℕ) * r⁻¹ ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * S * 2 + B * s ^ (3 : ℕ) * r⁻¹ ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S + B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S * (-11 / 2) + B * s ^ (4 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S * (1 / 2) + B * s ^ (4 : ℕ) * r⁻¹ ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (4 : ℕ) * S * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 2 2 =
      B * s * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 3 - B * s * (r ^ (2 : ℕ) - 1)⁻¹ * S * y⁻¹ ^ (2 : ℕ) * 4 - B * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * (1 / 2) + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (-1 / 2) + B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * (3 / 2) - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) + B * s ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (-1 / 2) - B * S * y⁻¹ ^ (2 : ℕ) * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 1 3 3 =
      B * s * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * 3 - B * s * (r ^ (2 : ℕ) - 1)⁻¹ * S * y⁻¹ ^ (2 : ℕ) * 4 - B * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * (1 / 2) + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (-1 / 2) + B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * (3 / 2) - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) + B * s ^ (4 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * S * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (-1 / 2) - B * S * y⁻¹ ^ (2 : ℕ) * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_2_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 0 0 =
      -(s * B * r⁻¹ ^ (3 : ℕ) * Sx) + s ^ (2 : ℕ) * B * r⁻¹ * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * (-3 / 2) - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sx + s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_2_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 0 1 =
      s * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * 3 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * 2 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * 4 + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * r⁻¹ ^ (2 : ℕ) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_2_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 1 0 =
      s * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * 3 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * 2 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * 4 + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * r⁻¹ ^ (2 : ℕ) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_2_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 1 1 =
      s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * 6 - s * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * 2 - s * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx - s ^ (2 : ℕ) * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * 2 + s ^ (2 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * (-7 / 2) - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx + s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 2 2 =
      -(s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) - B * r * Sx * y⁻¹ ^ (2 : ℕ) * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 2 3 3 =
      -(s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) - B * r * Sx * y⁻¹ ^ (2 : ℕ) * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_3_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 0 0 =
      -(s * B * r⁻¹ ^ (3 : ℕ) * Sy) + s ^ (2 : ℕ) * B * r⁻¹ * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * (-3 / 2) - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sy + s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_3_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 0 1 =
      s * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * 3 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sy * 2 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * 4 + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * r⁻¹ ^ (2 : ℕ) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_3_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 1 0 =
      s * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * 3 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sy * 2 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * 4 + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * r⁻¹ ^ (2 : ℕ) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_3_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 1 1 =
      s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * 6 - s * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * 2 - s * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy - s ^ (2 : ℕ) * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * 2 + s ^ (2 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * (-7 / 2) - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy + s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 2 2 =
      S * s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * 2 + S * s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * r⁻¹ + S * s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * r⁻¹ + S * B * r * y⁻¹ ^ (3 : ℕ) * 4 - s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * Sy + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * r⁻¹ * Sy * (-1 / 2) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * r⁻¹ * Sy * (-1 / 2) - B * r * y⁻¹ ^ (2 : ℕ) * Sy * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_1_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 1 3 3 3 =
      S * s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * 2 + S * s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * r⁻¹ + S * s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * r⁻¹ + S * B * r * y⁻¹ ^ (3 : ℕ) * 4 - s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * Sy + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * r⁻¹ * Sy * (-1 / 2) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * r⁻¹ * Sy * (-1 / 2) - B * r * y⁻¹ ^ (2 : ℕ) * Sy * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_0_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 0 0 =
      s ^ (2 : ℕ) * B * Sx * (-3 / 2) + s ^ (2 : ℕ) * B * Sx * r⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * Sx * (1 / 2) + s ^ (3 : ℕ) * B * Sx * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_0_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 0 1 =
      -(s ^ (2 : ℕ) * B * Sx * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (3 : ℕ) * B * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_0_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 1 0 =
      -(s ^ (2 : ℕ) * B * Sx * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (3 : ℕ) * B * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_0_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 1 1 =
      s ^ (2 : ℕ) * B * Sx * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (2 : ℕ) * B * Sx * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + s ^ (3 : ℕ) * B * Sx * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * Sx * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 2 2 =
      -(s * B * Sx * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * Sx * y⁻¹ ^ (2 : ℕ) * (-1 / 2) + s ^ (3 : ℕ) * B * Sx * y⁻¹ ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 0 3 3 =
      -(s * B * Sx * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * Sx * y⁻¹ ^ (2 : ℕ) * (-1 / 2) + s ^ (3 : ℕ) * B * Sx * y⁻¹ ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_1_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 0 0 =
      -(s * B * r⁻¹ ^ (3 : ℕ) * Sx) + s ^ (2 : ℕ) * B * r⁻¹ * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * (-3 / 2) - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sx + s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sx * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_1_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 0 1 =
      s * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * 3 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * 2 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * 4 + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * r⁻¹ ^ (2 : ℕ) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_1_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 1 0 =
      s * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * 3 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * 2 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * 4 + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * r⁻¹ ^ (2 : ℕ) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_1_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 1 1 =
      s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * 6 - s * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * 2 - s * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx - s ^ (2 : ℕ) * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * 2 + s ^ (2 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * (-7 / 2) - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sx + s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sx * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 2 2 =
      -(s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) - B * r * Sx * y⁻¹ ^ (2 : ℕ) * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 1 3 3 =
      -(s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ)) + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sx * y⁻¹ ^ (2 : ℕ) * r⁻¹ * (-1 / 2) - B * r * Sx * y⁻¹ ^ (2 : ℕ) * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_2_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 0 0 =
      B * Sxx * s * (-3 / 2) + B * Sxx * s * r⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sxx * s ^ (2 : ℕ) * (1 / 2) + B * Sxx * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_2_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 0 1 =
      -(B * Sxx * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * Sxx * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_2_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 1 0 =
      -(B * Sxx * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * Sxx * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_2_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 1 1 =
      B * Sxx * s * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sxx * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + B * Sxx * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sxx * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 2 2 =
      -(B * Sxx * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + B * Sxx * y⁻¹ ^ (2 : ℕ) * s * (-1 / 2) + B * Sxx * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 2 3 3 =
      -(B * Sxx * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ)) + B * Sxx * y⁻¹ ^ (2 : ℕ) * s * (-1 / 2) + B * Sxx * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_3_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 0 0 =
      B * Sxy * s * (-3 / 2) + B * Sxy * s * r⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sxy * s ^ (2 : ℕ) * (1 / 2) + B * Sxy * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_3_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 0 1 =
      -(B * Sxy * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * Sxy * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_3_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 1 0 =
      -(B * Sxy * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * Sxy * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_3_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 1 1 =
      B * Sxy * s * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sxy * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + B * Sxy * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sxy * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 2 2 =
      Sx * B * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * 2 + Sx * B * y⁻¹ ^ (3 : ℕ) * s + Sx * B * y⁻¹ ^ (3 : ℕ) * s ^ (2 : ℕ) - B * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxy + B * y⁻¹ ^ (2 : ℕ) * s * Sxy * (-1 / 2) + B * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * Sxy * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_2_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 2 3 3 3 =
      Sx * B * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * 2 + Sx * B * y⁻¹ ^ (3 : ℕ) * s + Sx * B * y⁻¹ ^ (3 : ℕ) * s ^ (2 : ℕ) - B * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxy + B * y⁻¹ ^ (2 : ℕ) * s * Sxy * (-1 / 2) + B * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * Sxy * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_0_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 0 0 =
      s ^ (2 : ℕ) * B * Sy * (-3 / 2) + s ^ (2 : ℕ) * B * Sy * r⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * Sy * (1 / 2) + s ^ (3 : ℕ) * B * Sy * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_0_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 0 1 =
      -(s ^ (2 : ℕ) * B * Sy * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (3 : ℕ) * B * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_0_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 1 0 =
      -(s ^ (2 : ℕ) * B * Sy * r * (r ^ (2 : ℕ) - 1)⁻¹) + s ^ (3 : ℕ) * B * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_0_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 1 1 =
      s ^ (2 : ℕ) * B * Sy * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (2 : ℕ) * B * Sy * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + s ^ (3 : ℕ) * B * Sy * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + s ^ (3 : ℕ) * B * Sy * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_0_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 2 2 =
      S * s * B * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * 2 + S * s ^ (2 : ℕ) * B * y⁻¹ ^ (3 : ℕ) + S * s ^ (3 : ℕ) * B * y⁻¹ ^ (3 : ℕ) - s * B * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sy + s ^ (2 : ℕ) * B * y⁻¹ ^ (2 : ℕ) * Sy * (-1 / 2) + s ^ (3 : ℕ) * B * y⁻¹ ^ (2 : ℕ) * Sy * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_0_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 0 3 3 =
      S * s * B * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * 2 + S * s ^ (2 : ℕ) * B * y⁻¹ ^ (3 : ℕ) + S * s ^ (3 : ℕ) * B * y⁻¹ ^ (3 : ℕ) - s * B * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sy + s ^ (2 : ℕ) * B * y⁻¹ ^ (2 : ℕ) * Sy * (-1 / 2) + s ^ (3 : ℕ) * B * y⁻¹ ^ (2 : ℕ) * Sy * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_1_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 0 0 =
      -(s * B * r⁻¹ ^ (3 : ℕ) * Sy) + s ^ (2 : ℕ) * B * r⁻¹ * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * (-3 / 2) - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sy + s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * Sy * (r ^ (2 : ℕ) - 1)⁻¹ * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_1_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 0 1 =
      s * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * 3 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sy * 2 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * 4 + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * r⁻¹ ^ (2 : ℕ) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_1_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 1 0 =
      s * B * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * 3 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ * Sy * 2 - s * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy - s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * 4 + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * r⁻¹ ^ (2 : ℕ) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy * r⁻¹ ^ (2 : ℕ) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_1_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 1 1 =
      s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * 6 - s * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * 2 - s * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy - s ^ (2 : ℕ) * B * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * 2 + s ^ (2 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * (-7 / 2) - s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sy + s ^ (2 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * (1 / 2) + s ^ (3 : ℕ) * B * r⁻¹ ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * Sy * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_1_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 2 2 =
      S * s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * 2 + S * s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * r⁻¹ + S * s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * r⁻¹ + S * B * r * y⁻¹ ^ (3 : ℕ) * 4 - s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * Sy + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * r⁻¹ * Sy * (-1 / 2) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * r⁻¹ * Sy * (-1 / 2) - B * r * y⁻¹ ^ (2 : ℕ) * Sy * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_1_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 1 3 3 =
      S * s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * 2 + S * s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * r⁻¹ + S * s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (3 : ℕ) * r⁻¹ + S * B * r * y⁻¹ ^ (3 : ℕ) * 4 - s * B * r * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * Sy + s ^ (2 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * r⁻¹ * Sy * (-1 / 2) + s ^ (3 : ℕ) * B * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ ^ (2 : ℕ) * r⁻¹ * Sy * (-1 / 2) - B * r * y⁻¹ ^ (2 : ℕ) * Sy * 2 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_2_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 0 0 =
      B * Sxy * s * (-3 / 2) + B * Sxy * s * r⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sxy * s ^ (2 : ℕ) * (1 / 2) + B * Sxy * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_2_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 0 1 =
      -(B * Sxy * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * Sxy * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_2_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 1 0 =
      -(B * Sxy * s * r * (r ^ (2 : ℕ) - 1)⁻¹) + B * Sxy * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_2_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 1 1 =
      B * Sxy * s * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sxy * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-3 / 2) + B * Sxy * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * Sxy * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_2_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 2 2 =
      Sx * B * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * 2 + Sx * B * y⁻¹ ^ (3 : ℕ) * s + Sx * B * y⁻¹ ^ (3 : ℕ) * s ^ (2 : ℕ) - B * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxy + B * y⁻¹ ^ (2 : ℕ) * s * Sxy * (-1 / 2) + B * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * Sxy * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_2_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 2 3 3 =
      Sx * B * r ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * 2 + Sx * B * y⁻¹ ^ (3 : ℕ) * s + Sx * B * y⁻¹ ^ (3 : ℕ) * s ^ (2 : ℕ) - B * r ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxy + B * y⁻¹ ^ (2 : ℕ) * s * Sxy * (-1 / 2) + B * y⁻¹ ^ (2 : ℕ) * s ^ (2 : ℕ) * Sxy * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_3_0_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 0 0 =
      -(S * B * s * y⁻¹ ^ (2 : ℕ) * 3) + S * B * s * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) + S * B * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * (-7 / 2) + S * B * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (5 / 2) + S * B * s ^ (3 : ℕ) * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * 2 + S * B * s ^ (4 : ℕ) * y⁻¹ ^ (2 : ℕ) * (1 / 2) + S * B * s ^ (4 : ℕ) * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (1 / 2) + B * s * r⁻¹ ^ (2 : ℕ) * Sxx * (-1 / 2) + B * s * Sxx * (3 / 2) + B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * Sxx * (-1 / 2) + B * s ^ (2 : ℕ) * Sxx * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_3_0_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 0 1 =
      -(S * B * s * y⁻¹ ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ * 2) - S * B * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ * 3 + S * B * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * 2 - S * B * s ^ (3 : ℕ) * y⁻¹ ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ + S * B * s ^ (3 : ℕ) * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * 3 + S * B * s ^ (4 : ℕ) * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ + B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ * Sxx - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * Sxx := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_3_1_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 1 0 =
      -(S * B * s * y⁻¹ ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ * 2) - S * B * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ * 3 + S * B * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * 2 - S * B * s ^ (3 : ℕ) * y⁻¹ ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ + S * B * s ^ (3 : ℕ) * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * 3 + S * B * s ^ (4 : ℕ) * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ + B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ * Sxx - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * r⁻¹ * Sxx := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_3_1_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 1 1 =
      S * B * s * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) - S * B * s * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * 3 + S * B * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (5 / 2) + S * B * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (-7 / 2) + S * B * s ^ (3 : ℕ) * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * 2 + S * B * s ^ (4 : ℕ) * y⁻¹ ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + S * B * s ^ (4 : ℕ) * y⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * (1 / 2) + B * s * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sxx * (-1 / 2) + B * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sxx * (3 / 2) + B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sxx * (-1 / 2) + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Sxx * (-1 / 2) := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_3_2_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 2 2 =
      -(S * B * s * y⁻¹ ^ (4 : ℕ) * 4) - S * B * s * y⁻¹ ^ (4 : ℕ) * r ^ (2 : ℕ) * 3 + S * B * s ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * (-11 / 2) - S * B * s ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * r ^ (2 : ℕ) - S * B * s ^ (3 : ℕ) * y⁻¹ ^ (4 : ℕ) * 2 + S * B * s ^ (4 : ℕ) * y⁻¹ ^ (4 : ℕ) * (-1 / 2) - S * B * y⁻¹ ^ (4 : ℕ) * r ^ (2 : ℕ) * 8 + B * s * y⁻¹ ^ (2 : ℕ) * Sxx * (1 / 2) + B * s * y⁻¹ ^ (3 : ℕ) * Sy * 2 + B * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxx * (1 / 2) + B * s ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * Sy * 2 + B * y⁻¹ ^ (2 : ℕ) * r ^ (2 : ℕ) * Sxx + B * y⁻¹ ^ (3 : ℕ) * r ^ (2 : ℕ) * Sy * 4 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

@[bmJetEntry] theorem scalarJet_second_3_3_3_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (scalarJet s r y B S Sx Sy Sxx Sxy).second 3 3 3 3 =
      -(S * B * s * y⁻¹ ^ (4 : ℕ) * 4) - S * B * s * y⁻¹ ^ (4 : ℕ) * r ^ (2 : ℕ) * 3 + S * B * s ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * (-11 / 2) - S * B * s ^ (2 : ℕ) * y⁻¹ ^ (4 : ℕ) * r ^ (2 : ℕ) - S * B * s ^ (3 : ℕ) * y⁻¹ ^ (4 : ℕ) * 2 + S * B * s ^ (4 : ℕ) * y⁻¹ ^ (4 : ℕ) * (-1 / 2) - S * B * y⁻¹ ^ (4 : ℕ) * r ^ (2 : ℕ) * 8 + B * s * y⁻¹ ^ (2 : ℕ) * Sxx * (1 / 2) + B * s * y⁻¹ ^ (3 : ℕ) * Sy * 2 + B * s ^ (2 : ℕ) * y⁻¹ ^ (2 : ℕ) * Sxx * (1 / 2) + B * s ^ (2 : ℕ) * y⁻¹ ^ (3 : ℕ) * Sy * 2 + B * y⁻¹ ^ (2 : ℕ) * r ^ (2 : ℕ) * Sxx + B * y⁻¹ ^ (3 : ℕ) * r ^ (2 : ℕ) * Sy * 4 := by
  simp only [scalarJet, radialEntries, temporalRadial, angular, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  ring_nf
  try simp (disch := decide) only [InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy]
  try ring_nf

end
end RHTower.D4BMScalarLinearEquation
