import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorLinearizedRicciJet
import GaloisForLFunctions.HTGeometry.InversePowerCancellation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMVectorJetSimpSets

/-!
# Entry tables for the fundamental vector (coexact) metric jet

Every entry of the fundamental vector metric jet `vectorJet` (mixed orbit–angular block only) is
recorded in the fixed normal form whose only inverses are `r⁻¹`, `y⁻¹` and `(r ^ (2 : ℕ) - 1)⁻¹`; the
orbit and angular blocks vanish. These tables let the index-collapsed quadratic Einstein source of
the vector–vector and scalar–vector channels be evaluated by flat rewriting.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RHTower.D4BMVectorLinearEquation
open GaloisForLFunctions.HTGeometry D4BMScalarLinearEquation
noncomputable section
variable {s r y B A C P Q R U W : ℂ}

@[bmVectorEntry] theorem vectorJet_metric_0_0 : (vectorJet s r y B A C P Q R U W).metric 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_0_0_0 : (vectorJet s r y B A C P Q R U W).first 0 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_1_0_0 : (vectorJet s r y B A C P Q R U W).first 1 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_2_0_0 : (vectorJet s r y B A C P Q R U W).first 2 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_3_0_0 : (vectorJet s r y B A C P Q R U W).first 3 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_0_0_0 : (vectorJet s r y B A C P Q R U W).second 0 0 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_1_0_0 : (vectorJet s r y B A C P Q R U W).second 0 1 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_2_0_0 : (vectorJet s r y B A C P Q R U W).second 0 2 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_3_0_0 : (vectorJet s r y B A C P Q R U W).second 0 3 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_0_0_0 : (vectorJet s r y B A C P Q R U W).second 1 0 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_1_0_0 : (vectorJet s r y B A C P Q R U W).second 1 1 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_2_0_0 : (vectorJet s r y B A C P Q R U W).second 1 2 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_3_0_0 : (vectorJet s r y B A C P Q R U W).second 1 3 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_0_0_0 : (vectorJet s r y B A C P Q R U W).second 2 0 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_1_0_0 : (vectorJet s r y B A C P Q R U W).second 2 1 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_2_0_0 : (vectorJet s r y B A C P Q R U W).second 2 2 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_3_0_0 : (vectorJet s r y B A C P Q R U W).second 2 3 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_0_0_0 : (vectorJet s r y B A C P Q R U W).second 3 0 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_1_0_0 : (vectorJet s r y B A C P Q R U W).second 3 1 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_2_0_0 : (vectorJet s r y B A C P Q R U W).second 3 2 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_3_0_0 : (vectorJet s r y B A C P Q R U W).second 3 3 0 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_metric_0_1 : (vectorJet s r y B A C P Q R U W).metric 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_0_0_1 : (vectorJet s r y B A C P Q R U W).first 0 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_1_0_1 : (vectorJet s r y B A C P Q R U W).first 1 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_2_0_1 : (vectorJet s r y B A C P Q R U W).first 2 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_3_0_1 : (vectorJet s r y B A C P Q R U W).first 3 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_0_0_1 : (vectorJet s r y B A C P Q R U W).second 0 0 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_1_0_1 : (vectorJet s r y B A C P Q R U W).second 0 1 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_2_0_1 : (vectorJet s r y B A C P Q R U W).second 0 2 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_3_0_1 : (vectorJet s r y B A C P Q R U W).second 0 3 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_0_0_1 : (vectorJet s r y B A C P Q R U W).second 1 0 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_1_0_1 : (vectorJet s r y B A C P Q R U W).second 1 1 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_2_0_1 : (vectorJet s r y B A C P Q R U W).second 1 2 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_3_0_1 : (vectorJet s r y B A C P Q R U W).second 1 3 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_0_0_1 : (vectorJet s r y B A C P Q R U W).second 2 0 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_1_0_1 : (vectorJet s r y B A C P Q R U W).second 2 1 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_2_0_1 : (vectorJet s r y B A C P Q R U W).second 2 2 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_3_0_1 : (vectorJet s r y B A C P Q R U W).second 2 3 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_0_0_1 : (vectorJet s r y B A C P Q R U W).second 3 0 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_1_0_1 : (vectorJet s r y B A C P Q R U W).second 3 1 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_2_0_1 : (vectorJet s r y B A C P Q R U W).second 3 2 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_3_0_1 : (vectorJet s r y B A C P Q R U W).second 3 3 0 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_metric_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).metric 0 2 =
      -(s * B * r⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_0_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 0 0 2 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_1_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 1 0 2 =
      B * s * r⁻¹ ^ (2 : ℕ) * A - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_2_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 2 0 2 =
      -(B * s * r⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_3_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 3 0 2 =
      -(B * s * r⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_0_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 0 0 2 =
      -(B * s ^ (3 : ℕ) * r⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_1_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 1 0 2 =
      B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * A - B * s ^ (3 : ℕ) * r⁻¹ ^ (2 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_2_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 2 0 2 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_3_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 3 0 2 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_0_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 0 0 2 =
      B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * A - B * s ^ (3 : ℕ) * r⁻¹ ^ (2 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_1_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 1 0 2 =
      -(B * s * r⁻¹ ^ (3 : ℕ) * A * 2) + B * s ^ (2 : ℕ) * r⁻¹ * A * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * 3 + B * s ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ * 2 - B * s ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) - B * s ^ (3 : ℕ) * r⁻¹ ^ (3 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_2_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 2 0 2 =
      B * s * r⁻¹ ^ (2 : ℕ) * P - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * P * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_3_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 3 0 2 =
      B * s * r⁻¹ ^ (2 : ℕ) * Q - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * Q * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_0_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 0 0 2 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_1_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 1 0 2 =
      B * s * r⁻¹ ^ (2 : ℕ) * P - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * P * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_2_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 2 0 2 =
      -(B * s * r⁻¹ * U) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_3_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 3 0 2 =
      -(B * s * r⁻¹ * W) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_0_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 0 0 2 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_1_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 1 0 2 =
      B * s * r⁻¹ ^ (2 : ℕ) * Q - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * Q * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_2_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 2 0 2 =
      -(B * s * r⁻¹ * W) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_3_0_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 3 0 2 =
      -(B * s * r⁻¹ * A * y⁻¹ ^ (2 : ℕ) * 2) - B * s * r⁻¹ * y * y⁻¹ ^ (2 : ℕ) * R * 2 + B * s * r⁻¹ * y⁻¹ * Q * 2 + B * s * r⁻¹ * U - B * s ^ (2 : ℕ) * r⁻¹ * A * y⁻¹ ^ (2 : ℕ) * 3 - B * s ^ (3 : ℕ) * r⁻¹ * A * y⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_metric_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).metric 0 3 =
      -(s * B * r⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_0_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 0 0 3 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_1_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 1 0 3 =
      B * s * r⁻¹ ^ (2 : ℕ) * C - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_2_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 2 0 3 =
      -(B * s * r⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_3_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 3 0 3 =
      B * s * r⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_0_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 0 0 3 =
      -(B * s ^ (3 : ℕ) * r⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_1_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 1 0 3 =
      B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * C - B * s ^ (3 : ℕ) * r⁻¹ ^ (2 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_2_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 2 0 3 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_3_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 3 0 3 =
      B * s ^ (2 : ℕ) * r⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_0_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 0 0 3 =
      B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * C - B * s ^ (3 : ℕ) * r⁻¹ ^ (2 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_1_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 1 0 3 =
      -(B * s * r⁻¹ ^ (3 : ℕ) * C * 2) + B * s ^ (2 : ℕ) * r⁻¹ * C * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * 3 + B * s ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ * 2 - B * s ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) - B * s ^ (3 : ℕ) * r⁻¹ ^ (3 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_2_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 2 0 3 =
      B * s * r⁻¹ ^ (2 : ℕ) * R - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * R * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_3_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 3 0 3 =
      -(B * s * r⁻¹ ^ (2 : ℕ) * P) + B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * P * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_0_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 0 0 3 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_1_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 1 0 3 =
      B * s * r⁻¹ ^ (2 : ℕ) * R - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * R * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_2_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 2 0 3 =
      -(B * s * r⁻¹ * C * y⁻¹ ^ (2 : ℕ) * 2) - B * s * r⁻¹ * W - B * s ^ (2 : ℕ) * r⁻¹ * C * y⁻¹ ^ (2 : ℕ) * 3 - B * s ^ (3 : ℕ) * r⁻¹ * C * y⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_3_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 3 0 3 =
      B * s * r⁻¹ * U := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_0_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 0 0 3 =
      B * s ^ (2 : ℕ) * r⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_1_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 1 0 3 =
      -(B * s * r⁻¹ ^ (2 : ℕ) * P) + B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * P * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_2_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 2 0 3 =
      B * s * r⁻¹ * U := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_3_0_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 3 0 3 =
      B * s * r⁻¹ * W := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_metric_1_0 : (vectorJet s r y B A C P Q R U W).metric 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_0_1_0 : (vectorJet s r y B A C P Q R U W).first 0 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_1_1_0 : (vectorJet s r y B A C P Q R U W).first 1 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_2_1_0 : (vectorJet s r y B A C P Q R U W).first 2 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_3_1_0 : (vectorJet s r y B A C P Q R U W).first 3 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_0_1_0 : (vectorJet s r y B A C P Q R U W).second 0 0 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_1_1_0 : (vectorJet s r y B A C P Q R U W).second 0 1 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_2_1_0 : (vectorJet s r y B A C P Q R U W).second 0 2 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_3_1_0 : (vectorJet s r y B A C P Q R U W).second 0 3 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_0_1_0 : (vectorJet s r y B A C P Q R U W).second 1 0 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_1_1_0 : (vectorJet s r y B A C P Q R U W).second 1 1 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_2_1_0 : (vectorJet s r y B A C P Q R U W).second 1 2 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_3_1_0 : (vectorJet s r y B A C P Q R U W).second 1 3 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_0_1_0 : (vectorJet s r y B A C P Q R U W).second 2 0 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_1_1_0 : (vectorJet s r y B A C P Q R U W).second 2 1 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_2_1_0 : (vectorJet s r y B A C P Q R U W).second 2 2 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_3_1_0 : (vectorJet s r y B A C P Q R U W).second 2 3 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_0_1_0 : (vectorJet s r y B A C P Q R U W).second 3 0 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_1_1_0 : (vectorJet s r y B A C P Q R U W).second 3 1 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_2_1_0 : (vectorJet s r y B A C P Q R U W).second 3 2 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_3_1_0 : (vectorJet s r y B A C P Q R U W).second 3 3 1 0 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_metric_1_1 : (vectorJet s r y B A C P Q R U W).metric 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_0_1_1 : (vectorJet s r y B A C P Q R U W).first 0 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_1_1_1 : (vectorJet s r y B A C P Q R U W).first 1 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_2_1_1 : (vectorJet s r y B A C P Q R U W).first 2 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_3_1_1 : (vectorJet s r y B A C P Q R U W).first 3 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_0_1_1 : (vectorJet s r y B A C P Q R U W).second 0 0 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_1_1_1 : (vectorJet s r y B A C P Q R U W).second 0 1 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_2_1_1 : (vectorJet s r y B A C P Q R U W).second 0 2 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_3_1_1 : (vectorJet s r y B A C P Q R U W).second 0 3 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_0_1_1 : (vectorJet s r y B A C P Q R U W).second 1 0 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_1_1_1 : (vectorJet s r y B A C P Q R U W).second 1 1 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_2_1_1 : (vectorJet s r y B A C P Q R U W).second 1 2 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_3_1_1 : (vectorJet s r y B A C P Q R U W).second 1 3 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_0_1_1 : (vectorJet s r y B A C P Q R U W).second 2 0 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_1_1_1 : (vectorJet s r y B A C P Q R U W).second 2 1 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_2_1_1 : (vectorJet s r y B A C P Q R U W).second 2 2 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_3_1_1 : (vectorJet s r y B A C P Q R U W).second 2 3 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_0_1_1 : (vectorJet s r y B A C P Q R U W).second 3 0 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_1_1_1 : (vectorJet s r y B A C P Q R U W).second 3 1 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_2_1_1 : (vectorJet s r y B A C P Q R U W).second 3 2 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_3_1_1 : (vectorJet s r y B A C P Q R U W).second 3 3 1 1 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_metric_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).metric 1 2 =
      -(s * B * (r ^ (2 : ℕ) - 1)⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_0_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 0 1 2 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_1_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 1 1 2 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_2_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 2 1 2 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_3_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 3 1 2 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_0_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 0 1 2 =
      -(B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_1_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 1 1 2 =
      B * s ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * 2 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_2_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 2 1 2 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_3_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 3 1 2 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_0_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 0 1 2 =
      B * s ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * 2 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_1_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 1 1 2 =
      -(B * s * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * A * 8) + B * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * 2 + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * A * 7 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * A * r⁻¹ ^ (2 : ℕ) - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * A * r⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_2_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 2 1 2 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_3_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 3 1 2 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Q * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Q * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_0_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 0 1 2 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_1_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 1 1 2 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_2_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 2 1 2 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * U) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_3_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 3 1 2 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * W) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_0_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 0 1 2 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_1_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 1 1 2 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Q * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Q * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_2_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 2 1 2 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * W) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_3_1_2 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 3 1 2 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * A * y⁻¹ ^ (2 : ℕ) * 2) - B * s * (r ^ (2 : ℕ) - 1)⁻¹ * y * y⁻¹ ^ (2 : ℕ) * R * 2 + B * s * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ * Q * 2 + B * s * (r ^ (2 : ℕ) - 1)⁻¹ * U - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * A * y⁻¹ ^ (2 : ℕ) * 3 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * A * y⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_metric_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).metric 1 3 =
      -(s * B * (r ^ (2 : ℕ) - 1)⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_0_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 0 1 3 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_1_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 1 1 3 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_2_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 2 1 3 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_3_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 3 1 3 =
      B * s * (r ^ (2 : ℕ) - 1)⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_0_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 0 1 3 =
      -(B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_1_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 1 1 3 =
      B * s ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * 2 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_2_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 2 1 3 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_3_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 3 1 3 =
      B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_0_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 0 1 3 =
      B * s ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * 2 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_1_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 1 1 3 =
      -(B * s * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * C * 8) + B * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * 2 + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * C * 7 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * C * r⁻¹ ^ (2 : ℕ) - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * C * r⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_2_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 2 1 3 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * R * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * R * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_3_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 3 1 3 =
      -(B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * 2) + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_0_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 0 1 3 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_1_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 1 1 3 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * R * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * R * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_2_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 2 1 3 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * C * y⁻¹ ^ (2 : ℕ) * 2) - B * s * (r ^ (2 : ℕ) - 1)⁻¹ * W - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * C * y⁻¹ ^ (2 : ℕ) * 3 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * C * y⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_3_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 3 1 3 =
      B * s * (r ^ (2 : ℕ) - 1)⁻¹ * U := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_0_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 0 1 3 =
      B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_1_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 1 1 3 =
      -(B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * 2) + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_2_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 2 1 3 =
      B * s * (r ^ (2 : ℕ) - 1)⁻¹ * U := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_3_1_3 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 3 1 3 =
      B * s * (r ^ (2 : ℕ) - 1)⁻¹ * W := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_metric_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).metric 2 0 =
      -(s * B * r⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_0_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 0 2 0 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_1_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 1 2 0 =
      B * s * r⁻¹ ^ (2 : ℕ) * A - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_2_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 2 2 0 =
      -(B * s * r⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_3_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 3 2 0 =
      -(B * s * r⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_0_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 0 2 0 =
      -(B * s ^ (3 : ℕ) * r⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_1_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 1 2 0 =
      B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * A - B * s ^ (3 : ℕ) * r⁻¹ ^ (2 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_2_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 2 2 0 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_3_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 3 2 0 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_0_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 0 2 0 =
      B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * A - B * s ^ (3 : ℕ) * r⁻¹ ^ (2 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_1_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 1 2 0 =
      -(B * s * r⁻¹ ^ (3 : ℕ) * A * 2) + B * s ^ (2 : ℕ) * r⁻¹ * A * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * 3 + B * s ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ * 2 - B * s ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) - B * s ^ (3 : ℕ) * r⁻¹ ^ (3 : ℕ) * A * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_2_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 2 2 0 =
      B * s * r⁻¹ ^ (2 : ℕ) * P - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * P * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_3_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 3 2 0 =
      B * s * r⁻¹ ^ (2 : ℕ) * Q - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * Q * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_0_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 0 2 0 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_1_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 1 2 0 =
      B * s * r⁻¹ ^ (2 : ℕ) * P - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * P * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_2_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 2 2 0 =
      -(B * s * r⁻¹ * U) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_3_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 3 2 0 =
      -(B * s * r⁻¹ * W) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_0_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 0 2 0 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_1_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 1 2 0 =
      B * s * r⁻¹ ^ (2 : ℕ) * Q - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * Q * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_2_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 2 2 0 =
      -(B * s * r⁻¹ * W) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_3_2_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 3 2 0 =
      -(B * s * r⁻¹ * A * y⁻¹ ^ (2 : ℕ) * 2) - B * s * r⁻¹ * y * y⁻¹ ^ (2 : ℕ) * R * 2 + B * s * r⁻¹ * y⁻¹ * Q * 2 + B * s * r⁻¹ * U - B * s ^ (2 : ℕ) * r⁻¹ * A * y⁻¹ ^ (2 : ℕ) * 3 - B * s ^ (3 : ℕ) * r⁻¹ * A * y⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_metric_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).metric 2 1 =
      -(s * B * (r ^ (2 : ℕ) - 1)⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_0_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 0 2 1 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_1_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 1 2 1 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_2_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 2 2 1 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_3_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 3 2 1 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_0_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 0 2 1 =
      -(B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * A) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_1_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 1 2 1 =
      B * s ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * 2 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_2_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 2 2 1 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_3_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 3 2 1 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_0_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 0 2 1 =
      B * s ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * 2 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_1_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 1 2 1 =
      -(B * s * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * A * 8) + B * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * A * 2 + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * A * 7 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * A * r⁻¹ ^ (2 : ℕ) - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * A * r⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_2_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 2 2 1 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_3_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 3 2 1 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Q * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Q * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_0_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 0 2 1 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * P) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_1_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 1 2 1 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_2_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 2 2 1 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * U) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_3_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 3 2 1 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * W) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_0_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 0 2 1 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * Q) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_1_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 1 2 1 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Q * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * Q * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_2_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 2 2 1 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * W) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_3_2_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 3 2 1 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * A * y⁻¹ ^ (2 : ℕ) * 2) - B * s * (r ^ (2 : ℕ) - 1)⁻¹ * y * y⁻¹ ^ (2 : ℕ) * R * 2 + B * s * (r ^ (2 : ℕ) - 1)⁻¹ * y⁻¹ * Q * 2 + B * s * (r ^ (2 : ℕ) - 1)⁻¹ * U - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * A * y⁻¹ ^ (2 : ℕ) * 3 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * A * y⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_metric_2_2 : (vectorJet s r y B A C P Q R U W).metric 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_0_2_2 : (vectorJet s r y B A C P Q R U W).first 0 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_1_2_2 : (vectorJet s r y B A C P Q R U W).first 1 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_2_2_2 : (vectorJet s r y B A C P Q R U W).first 2 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_3_2_2 : (vectorJet s r y B A C P Q R U W).first 3 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_0_2_2 : (vectorJet s r y B A C P Q R U W).second 0 0 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_1_2_2 : (vectorJet s r y B A C P Q R U W).second 0 1 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_2_2_2 : (vectorJet s r y B A C P Q R U W).second 0 2 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_3_2_2 : (vectorJet s r y B A C P Q R U W).second 0 3 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_0_2_2 : (vectorJet s r y B A C P Q R U W).second 1 0 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_1_2_2 : (vectorJet s r y B A C P Q R U W).second 1 1 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_2_2_2 : (vectorJet s r y B A C P Q R U W).second 1 2 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_3_2_2 : (vectorJet s r y B A C P Q R U W).second 1 3 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_0_2_2 : (vectorJet s r y B A C P Q R U W).second 2 0 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_1_2_2 : (vectorJet s r y B A C P Q R U W).second 2 1 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_2_2_2 : (vectorJet s r y B A C P Q R U W).second 2 2 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_3_2_2 : (vectorJet s r y B A C P Q R U W).second 2 3 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_0_2_2 : (vectorJet s r y B A C P Q R U W).second 3 0 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_1_2_2 : (vectorJet s r y B A C P Q R U W).second 3 1 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_2_2_2 : (vectorJet s r y B A C P Q R U W).second 3 2 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_3_2_2 : (vectorJet s r y B A C P Q R U W).second 3 3 2 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_metric_2_3 : (vectorJet s r y B A C P Q R U W).metric 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_0_2_3 : (vectorJet s r y B A C P Q R U W).first 0 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_1_2_3 : (vectorJet s r y B A C P Q R U W).first 1 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_2_2_3 : (vectorJet s r y B A C P Q R U W).first 2 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_3_2_3 : (vectorJet s r y B A C P Q R U W).first 3 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_0_2_3 : (vectorJet s r y B A C P Q R U W).second 0 0 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_1_2_3 : (vectorJet s r y B A C P Q R U W).second 0 1 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_2_2_3 : (vectorJet s r y B A C P Q R U W).second 0 2 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_3_2_3 : (vectorJet s r y B A C P Q R U W).second 0 3 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_0_2_3 : (vectorJet s r y B A C P Q R U W).second 1 0 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_1_2_3 : (vectorJet s r y B A C P Q R U W).second 1 1 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_2_2_3 : (vectorJet s r y B A C P Q R U W).second 1 2 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_3_2_3 : (vectorJet s r y B A C P Q R U W).second 1 3 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_0_2_3 : (vectorJet s r y B A C P Q R U W).second 2 0 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_1_2_3 : (vectorJet s r y B A C P Q R U W).second 2 1 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_2_2_3 : (vectorJet s r y B A C P Q R U W).second 2 2 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_3_2_3 : (vectorJet s r y B A C P Q R U W).second 2 3 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_0_2_3 : (vectorJet s r y B A C P Q R U W).second 3 0 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_1_2_3 : (vectorJet s r y B A C P Q R U W).second 3 1 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_2_2_3 : (vectorJet s r y B A C P Q R U W).second 3 2 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_3_2_3 : (vectorJet s r y B A C P Q R U W).second 3 3 2 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_metric_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).metric 3 0 =
      -(s * B * r⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_0_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 0 3 0 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_1_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 1 3 0 =
      B * s * r⁻¹ ^ (2 : ℕ) * C - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_2_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 2 3 0 =
      -(B * s * r⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_3_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 3 3 0 =
      B * s * r⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_0_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 0 3 0 =
      -(B * s ^ (3 : ℕ) * r⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_1_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 1 3 0 =
      B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * C - B * s ^ (3 : ℕ) * r⁻¹ ^ (2 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_2_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 2 3 0 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_3_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 3 3 0 =
      B * s ^ (2 : ℕ) * r⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_0_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 0 3 0 =
      B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * C - B * s ^ (3 : ℕ) * r⁻¹ ^ (2 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_1_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 1 3 0 =
      -(B * s * r⁻¹ ^ (3 : ℕ) * C * 2) + B * s ^ (2 : ℕ) * r⁻¹ * C * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * 3 + B * s ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ * 2 - B * s ^ (2 : ℕ) * r⁻¹ ^ (3 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) - B * s ^ (3 : ℕ) * r⁻¹ ^ (3 : ℕ) * C * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_2_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 2 3 0 =
      B * s * r⁻¹ ^ (2 : ℕ) * R - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * R * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_3_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 3 3 0 =
      -(B * s * r⁻¹ ^ (2 : ℕ) * P) + B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * P * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_0_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 0 3 0 =
      -(B * s ^ (2 : ℕ) * r⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_1_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 1 3 0 =
      B * s * r⁻¹ ^ (2 : ℕ) * R - B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * R * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_2_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 2 3 0 =
      -(B * s * r⁻¹ * C * y⁻¹ ^ (2 : ℕ) * 2) - B * s * r⁻¹ * W - B * s ^ (2 : ℕ) * r⁻¹ * C * y⁻¹ ^ (2 : ℕ) * 3 - B * s ^ (3 : ℕ) * r⁻¹ * C * y⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_3_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 3 3 0 =
      B * s * r⁻¹ * U := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_0_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 0 3 0 =
      B * s ^ (2 : ℕ) * r⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_1_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 1 3 0 =
      -(B * s * r⁻¹ ^ (2 : ℕ) * P) + B * s ^ (2 : ℕ) * r⁻¹ ^ (2 : ℕ) * P * (r ^ (2 : ℕ) - 1)⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_2_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 2 3 0 =
      B * s * r⁻¹ * U := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_3_3_0 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 3 3 0 =
      B * s * r⁻¹ * W := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_metric_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).metric 3 1 =
      -(s * B * (r ^ (2 : ℕ) - 1)⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_0_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 0 3 1 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_1_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 1 3 1 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_2_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 2 3 1 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_first_3_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).first 3 3 1 =
      B * s * (r ^ (2 : ℕ) - 1)⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_0_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 0 3 1 =
      -(B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * C) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_1_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 1 3 1 =
      B * s ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * 2 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_2_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 2 3 1 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_0_3_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 0 3 3 1 =
      B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_0_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 0 3 1 =
      B * s ^ (2 : ℕ) * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * 2 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_1_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 1 3 1 =
      -(B * s * r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * C * 8) + B * s * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * C * 2 + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * C * 7 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * C * r⁻¹ ^ (2 : ℕ) - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (3 : ℕ) * C * r⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_2_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 2 3 1 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * R * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * R * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_1_3_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 1 3 3 1 =
      -(B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * 2) + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_0_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 0 3 1 =
      -(B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * R) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_1_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 1 3 1 =
      B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * R * 2 - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * R * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_2_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 2 3 1 =
      -(B * s * (r ^ (2 : ℕ) - 1)⁻¹ * C * y⁻¹ ^ (2 : ℕ) * 2) - B * s * (r ^ (2 : ℕ) - 1)⁻¹ * W - B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * C * y⁻¹ ^ (2 : ℕ) * 3 - B * s ^ (3 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * C * y⁻¹ ^ (2 : ℕ) := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_2_3_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 2 3 3 1 =
      B * s * (r ^ (2 : ℕ) - 1)⁻¹ * U := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_0_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 0 3 1 =
      B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ * P := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_1_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 1 3 1 =
      -(B * s * r * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * 2) + B * s ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1)⁻¹ ^ (2 : ℕ) * P * r⁻¹ := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_2_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 2 3 1 =
      B * s * (r ^ (2 : ℕ) - 1)⁻¹ * U := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_second_3_3_3_1 (_hr : r ≠ 0) (_hy : y ≠ 0) :
    (vectorJet s r y B A C P Q R U W).second 3 3 3 1 =
      B * s * (r ^ (2 : ℕ) - 1)⁻¹ * W := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp only [div_eq_mul_inv, mul_inv, inv_neg, ← inv_pow, inv_inv, one_div]
  try ring_nf
  try simp (disch := decide) only [InversePowerCancellation.inv_mul_pow _hr, InversePowerCancellation.inv_mul_self _hr, InversePowerCancellation.inv_pow_mul _hr, InversePowerCancellation.inv_pow_mul_pow _hr, InversePowerCancellation.inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_mul_pow _hr, InversePowerCancellation.mul_inv_mul_self _hr, InversePowerCancellation.mul_inv_pow _hr, InversePowerCancellation.mul_inv_pow_mul _hr, InversePowerCancellation.mul_inv_pow_mul_pow _hr, InversePowerCancellation.mul_inv_pow_mul_pow' _hr, InversePowerCancellation.mul_inv_self _hr, InversePowerCancellation.mul_mul_inv_pow _hr, InversePowerCancellation.mul_mul_inv_self _hr, InversePowerCancellation.mul_pow_mul_inv _hr, InversePowerCancellation.mul_pow_mul_inv_pow _hr, InversePowerCancellation.mul_pow_mul_inv_pow' _hr, InversePowerCancellation.pow_mul_inv _hr, InversePowerCancellation.pow_mul_inv_pow _hr, InversePowerCancellation.pow_mul_inv_pow' _hr, InversePowerCancellation.inv_mul_pow _hy, InversePowerCancellation.inv_mul_self _hy, InversePowerCancellation.inv_pow_mul _hy, InversePowerCancellation.inv_pow_mul_pow _hy, InversePowerCancellation.inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_mul_pow _hy, InversePowerCancellation.mul_inv_mul_self _hy, InversePowerCancellation.mul_inv_pow _hy, InversePowerCancellation.mul_inv_pow_mul _hy, InversePowerCancellation.mul_inv_pow_mul_pow _hy, InversePowerCancellation.mul_inv_pow_mul_pow' _hy, InversePowerCancellation.mul_inv_self _hy, InversePowerCancellation.mul_mul_inv_pow _hy, InversePowerCancellation.mul_mul_inv_self _hy, InversePowerCancellation.mul_pow_mul_inv _hy, InversePowerCancellation.mul_pow_mul_inv_pow _hy, InversePowerCancellation.mul_pow_mul_inv_pow' _hy, InversePowerCancellation.pow_mul_inv _hy, InversePowerCancellation.pow_mul_inv_pow _hy, InversePowerCancellation.pow_mul_inv_pow' _hy]
  try ring_nf

@[bmVectorEntry] theorem vectorJet_metric_3_2 : (vectorJet s r y B A C P Q R U W).metric 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_0_3_2 : (vectorJet s r y B A C P Q R U W).first 0 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_1_3_2 : (vectorJet s r y B A C P Q R U W).first 1 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_2_3_2 : (vectorJet s r y B A C P Q R U W).first 2 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_3_3_2 : (vectorJet s r y B A C P Q R U W).first 3 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_0_3_2 : (vectorJet s r y B A C P Q R U W).second 0 0 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_1_3_2 : (vectorJet s r y B A C P Q R U W).second 0 1 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_2_3_2 : (vectorJet s r y B A C P Q R U W).second 0 2 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_3_3_2 : (vectorJet s r y B A C P Q R U W).second 0 3 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_0_3_2 : (vectorJet s r y B A C P Q R U W).second 1 0 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_1_3_2 : (vectorJet s r y B A C P Q R U W).second 1 1 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_2_3_2 : (vectorJet s r y B A C P Q R U W).second 1 2 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_3_3_2 : (vectorJet s r y B A C P Q R U W).second 1 3 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_0_3_2 : (vectorJet s r y B A C P Q R U W).second 2 0 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_1_3_2 : (vectorJet s r y B A C P Q R U W).second 2 1 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_2_3_2 : (vectorJet s r y B A C P Q R U W).second 2 2 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_3_3_2 : (vectorJet s r y B A C P Q R U W).second 2 3 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_0_3_2 : (vectorJet s r y B A C P Q R U W).second 3 0 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_1_3_2 : (vectorJet s r y B A C P Q R U W).second 3 1 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_2_3_2 : (vectorJet s r y B A C P Q R U W).second 3 2 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_3_3_2 : (vectorJet s r y B A C P Q R U W).second 3 3 3 2 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_metric_3_3 : (vectorJet s r y B A C P Q R U W).metric 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_0_3_3 : (vectorJet s r y B A C P Q R U W).first 0 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_1_3_3 : (vectorJet s r y B A C P Q R U W).first 1 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_2_3_3 : (vectorJet s r y B A C P Q R U W).first 2 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_first_3_3_3 : (vectorJet s r y B A C P Q R U W).first 3 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_0_3_3 : (vectorJet s r y B A C P Q R U W).second 0 0 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_1_3_3 : (vectorJet s r y B A C P Q R U W).second 0 1 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_2_3_3 : (vectorJet s r y B A C P Q R U W).second 0 2 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_0_3_3_3 : (vectorJet s r y B A C P Q R U W).second 0 3 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_0_3_3 : (vectorJet s r y B A C P Q R U W).second 1 0 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_1_3_3 : (vectorJet s r y B A C P Q R U W).second 1 1 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_2_3_3 : (vectorJet s r y B A C P Q R U W).second 1 2 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_1_3_3_3 : (vectorJet s r y B A C P Q R U W).second 1 3 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_0_3_3 : (vectorJet s r y B A C P Q R U W).second 2 0 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_1_3_3 : (vectorJet s r y B A C P Q R U W).second 2 1 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_2_3_3 : (vectorJet s r y B A C P Q R U W).second 2 2 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_2_3_3_3 : (vectorJet s r y B A C P Q R U W).second 2 3 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_0_3_3 : (vectorJet s r y B A C P Q R U W).second 3 0 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_1_3_3 : (vectorJet s r y B A C P Q R U W).second 3 1 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_2_3_3 : (vectorJet s r y B A C P Q R U W).second 3 2 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

@[bmVectorEntry] theorem vectorJet_second_3_3_3_3 : (vectorJet s r y B A C P Q R U W).second 3 3 3 3 = 0 := by
  simp only [vectorJet, angular0, angular1, temporalRadial, coord, ScalarTwoJet.mul,
    ScalarTwoJet.add, ScalarTwoJet.neg, ScalarTwoJet.inv, ScalarTwoJet.constant, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true, if_false]
  try simp

end
end RHTower.D4BMVectorLinearEquation
