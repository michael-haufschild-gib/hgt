import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Comparison
import GaloisForLFunctions.HTGeometry.ThreeSlotExchangeabilityInformation

/-! # Exact information of the reflected logistic proof-exchange law

The native logistic phase gives a strictly positive two-atom law. Reflection exchanges
the atoms, and its log likelihood ratio is exactly the signed grade. The paper's finite
relative entropy and total variation therefore measure the native phase contrast exactly.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open FourierLLogL

/-- The actual logistic completion phase, with its complementary atom. -/
def paperLogisticLaw (a : ℝ) : Law Bool :=
  ⟨fun b => if b then Real.exp a / (1 + Real.exp a) else 1 / (1 + Real.exp a),
    (fun b => by dsimp; split_ifs <;> positivity), by
      simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
      field_simp
      ring⟩

theorem paperLogisticLaw_true (a : ℝ) :
    paperLogisticLaw a true = (logisticPhase a : ℝ) := rfl

theorem paperLogisticLaw_false (a : ℝ) :
    paperLogisticLaw a false = (logisticPhase (-a) : ℝ) := by
  change 1 / (1 + Real.exp a) = Real.exp (-a) / (1 + Real.exp (-a))
  rw [Real.exp_neg]
  have he := (Real.exp_pos a).ne'
  have hd : 1 + Real.exp a ≠ 0 := by positivity
  field_simp
  ring

theorem paperLogisticLaw_pos (a : ℝ) (b : Bool) : 0 < paperLogisticLaw a b := by
  change 0 < if b then Real.exp a / (1 + Real.exp a) else 1 / (1 + Real.exp a)
  split_ifs <;> positivity

theorem paperLogisticLaw_dominated (a b : ℝ) :
    (paperLogisticLaw a).dominated (paperLogisticLaw b) :=
  fun x _ => paperLogisticLaw_pos b x

theorem paperLogisticLaw_reflect (a : ℝ) (b : Bool) :
    paperLogisticLaw (-a) b = paperLogisticLaw a (!b) := by
  cases b <;> simp only [Bool.not_false, Bool.not_true, paperLogisticLaw_true,
    paperLogisticLaw_false, neg_neg]

private theorem log_normalizer_reflect (a : ℝ) :
    Real.log (1 + Real.exp (-a)) = Real.log (1 + Real.exp a) - a := by
  have he := (Real.exp_pos a).ne'
  have hd : 1 + Real.exp a ≠ 0 := by positivity
  rw [show 1 + Real.exp (-a) = (1 + Real.exp a) / Real.exp a by
    rw [Real.exp_neg]; field_simp; ring]
  rw [Real.log_div hd he, Real.log_exp]

/-- Reflection has the signed grade as its exact atomwise log likelihood ratio. -/
theorem paperLogisticLaw_log_ratio (a : ℝ) (b : Bool) :
    Real.log (paperLogisticLaw a b) - Real.log (paperLogisticLaw (-a) b) =
      if b then a else -a := by
  have he := (Real.exp_pos a).ne'
  have hen := (Real.exp_pos (-a)).ne'
  have hd : 1 + Real.exp a ≠ 0 := by positivity
  have hdn : 1 + Real.exp (-a) ≠ 0 := by positivity
  cases b
  · change Real.log (1 / (1 + Real.exp a)) - Real.log (1 / (1 + Real.exp (-a))) = -a
    simp only [Real.log_div one_ne_zero hd,
      Real.log_div one_ne_zero hdn, Real.log_one, log_normalizer_reflect]
    ring
  · change Real.log (Real.exp a / (1 + Real.exp a)) -
      Real.log (Real.exp (-a) / (1 + Real.exp (-a))) = a
    simp only [Real.log_div he hd, Real.log_div hen hdn,
      Real.log_exp, log_normalizer_reflect]
    ring

theorem paperLogisticLaw_kl_reflect (a : ℝ) :
    (paperLogisticLaw a).kl (paperLogisticLaw (-a)) =
      a * ((logisticPhase a : ℝ) - (logisticPhase (-a) : ℝ)) := by
  rw [Law.kl_ex]
  simp only [paperLogisticLaw_log_ratio, Law.Ex, Fintype.sum_bool,
    Bool.false_eq_true, ↓reduceIte, paperLogisticLaw_true, paperLogisticLaw_false]
  ring

theorem paperLogisticLaw_tv_reflect (a : ℝ) :
    (paperLogisticLaw a).tv (paperLogisticLaw (-a)) =
      |(logisticPhase a : ℝ) - (logisticPhase (-a) : ℝ)| := by
  simp only [Law.tv, Fintype.sum_bool, paperLogisticLaw_true, paperLogisticLaw_false,
    neg_neg, abs_sub_comm (logisticPhase (-a) : ℝ)]
  ring

/-- The proven paper Pinsker inequality controls the native phase imbalance. -/
theorem paperLogisticLaw_contrast_sq_le_kl (a : ℝ) :
    ((logisticPhase a : ℝ) - (logisticPhase (-a) : ℝ)) ^ 2 ≤
      (paperLogisticLaw a).kl (paperLogisticLaw (-a)) := by
  simpa only [paperLogisticLaw_tv_reflect, sq_abs] using
    Law.tv_sq_le_kl (paperLogisticLaw_dominated a (-a))

end
end GaloisForLFunctions.HTGeometry
