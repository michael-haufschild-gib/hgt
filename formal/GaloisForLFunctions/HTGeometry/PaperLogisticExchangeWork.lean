import GaloisForLFunctions.HTGeometry.PaperAtomicLawInformation
import GaloisForLFunctions.HTGeometry.PaperLogisticExchangeLaw

/-! # Exact information work of repeated logistic exchanges

The paper's two directional relative entropies recover the native three-slot divergence.
Independent repetitions multiply this real work by the depth. At fixed grade the work
vanishes exactly at neutrality; the statements quantify over every real grade and depth.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory InformationTheory FourierLLogL
open scoped ENNReal

/-- Symmetric relative entropy of the actual reflected logistic laws. -/
def paperLogisticExchangeInformation (a : ℝ) : ℝ :=
  (paperLogisticLaw a).kl (paperLogisticLaw (-a)) +
    (paperLogisticLaw (-a)).kl (paperLogisticLaw a)

theorem paperLogisticExchangeInformation_eq (a : ℝ) :
    paperLogisticExchangeInformation a =
      2 * a * ((logisticPhase a : ℝ) - (logisticPhase (-a) : ℝ)) := by
  unfold paperLogisticExchangeInformation
  rw [paperLogisticLaw_kl_reflect,
    show (paperLogisticLaw (-a)).kl (paperLogisticLaw a) =
      (-a) * ((logisticPhase (-a) : ℝ) - (logisticPhase a : ℝ)) by
        simpa only [neg_neg] using paperLogisticLaw_kl_reflect (-a)]
  ring

theorem paperLogisticExchangeInformation_nonneg (a : ℝ) :
    0 ≤ paperLogisticExchangeInformation a :=
  add_nonneg (Law.kl_nonneg (paperLogisticLaw_dominated _ _))
    (Law.kl_nonneg (paperLogisticLaw_dominated _ _))

theorem paperLogisticExchangeInformation_neg (a : ℝ) :
    paperLogisticExchangeInformation (-a) = paperLogisticExchangeInformation a := by
  simp only [paperLogisticExchangeInformation, neg_neg, add_comm]

theorem paperLogisticExchangeInformation_contrast_bound (a : ℝ) :
    2 * ((logisticPhase a : ℝ) - (logisticPhase (-a) : ℝ)) ^ 2 ≤
      paperLogisticExchangeInformation a := by
  have hp := paperLogisticLaw_contrast_sq_le_kl a
  have hm := paperLogisticLaw_contrast_sq_le_kl (-a)
  simp only [neg_neg, sub_sq_comm (logisticPhase (-a) : ℝ)] at hm
  exact by unfold paperLogisticExchangeInformation; linarith

theorem paperLogisticExchangeInformation_eq_zero_iff (a : ℝ) :
    paperLogisticExchangeInformation a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hb := paperLogisticExchangeInformation_contrast_bound a
    rw [h] at hb
    have he : (logisticPhase a : ℝ) = (logisticPhase (-a) : ℝ) := by nlinarith
    exact (logisticPhase_eq_iff a).mp (Subtype.ext he)
  · rintro rfl
    simp [paperLogisticExchangeInformation_eq]

theorem paperLogisticLaw_native_kl (a b : ℝ) :
    klDiv (paperLogisticLaw a |>.atomicProbability id : Measure Bool)
      (paperLogisticLaw b |>.atomicProbability id : Measure Bool) =
      ENNReal.ofReal ((paperLogisticLaw a).kl (paperLogisticLaw b)) := by
  rw [paperAtomicLaw_klDiv, if_pos (paperLogisticLaw_dominated a b)]

/-- The native repeated three-slot experiment has exactly the paper information budget. -/
theorem paperLogisticLaw_slotWork (a : ℝ) (m : ℕ) :
    slotWork (paperLogisticLaw a |>.atomicProbability id : Measure Bool)
      (paperLogisticLaw (-a) |>.atomicProbability id : Measure Bool) m =
      ENNReal.ofReal ((m : ℝ) * paperLogisticExchangeInformation a) := by
  rw [slotWork_eq, paperLogisticLaw_native_kl, paperLogisticLaw_native_kl,
    ← ENNReal.ofReal_add (Law.kl_nonneg (paperLogisticLaw_dominated _ _))
      (Law.kl_nonneg (paperLogisticLaw_dominated _ _))]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
  rfl

theorem paperLogisticLaw_slotWork_toReal (a : ℝ) (m : ℕ) :
    (slotWork (paperLogisticLaw a |>.atomicProbability id : Measure Bool)
      (paperLogisticLaw (-a) |>.atomicProbability id : Measure Bool) m).toReal =
      (m : ℝ) * paperLogisticExchangeInformation a := by
  rw [paperLogisticLaw_slotWork, ENNReal.toReal_ofReal
    (mul_nonneg (Nat.cast_nonneg m) (paperLogisticExchangeInformation_nonneg a))]

end
end GaloisForLFunctions.HTGeometry
