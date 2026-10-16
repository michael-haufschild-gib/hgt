import GaloisForLFunctions.RHTower.PaperThetaConfluentCut
import GaloisForLFunctions.RHTower.PaperThetaBranchAbsoluteContinuity

/-! # Absolute-continuity admission through the singular theta quantile

Every differentiated compact branch is controlled by an already admitted
imaginary-parameter branch. This pays its actual L1 derivative, not merely
pointwise or scalar-charge analyticity.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

def parameterControlPoint (z : ℂ) : ℂ := -I*((|z.im|+1 : ℝ) : ℂ)

def parameterJetComparisonCost (n : ℕ) (z : ℂ) : ℝ :=
  (n.factorial : ℝ)*((‖z‖+1)/(|z.im|+1))

def closedParameterJet (n : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  iteratedDeriv n (fun w => closedQuantileMode w t) z

def leftClosedParameterJet (n : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (-1 : ℂ)^n * closedParameterJet n (-z) (1-t)

def cutQuantileParameterJet (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) (t : ℝ) : ℂ :=
  iteratedDeriv n (fun w => cutQuantileMode w c t) z

theorem flatParameterJet_comparison (n : ℕ) (z : ℂ) (x y : ℝ) :
    ‖flatParameterJet n z x-flatParameterJet n z y‖ ≤
      parameterJetComparisonCost n z *
        ‖flatQuotient (parameterControlPoint z) x-flatQuotient (parameterControlPoint z) y‖ := by
  let C := (‖z‖+1)/(|z.im|+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : |parameterVariationBudget z x-parameterVariationBudget z y| ≤
      C*‖flatQuotient (parameterControlPoint z) x-flatQuotient (parameterControlPoint z) y‖ := by
    rw [parameterVariationBudget_eq, parameterVariationBudget_eq, ← mul_sub, abs_mul,
      abs_of_nonneg hC]
    apply mul_le_mul_of_nonneg_left _ hC
    have h := abs_norm_sub_norm_le
      (flatQuotient (parameterControlPoint z) x+1) (flatQuotient (parameterControlPoint z) y+1)
    simpa only [parameterControlPoint, add_sub_add_right_eq_sub] using h
  exact (flatParameterJet_increment_abs n z y x).trans (by
    simpa only [parameterJetComparisonCost, C, mul_assoc] using
      mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ n.factorial by positivity))

theorem flatParameterJet_trace_comparison (n : ℕ) (z : ℂ) (x : ℝ) :
    ‖flatParameterJet n z x-parameterEndpointTrace n‖ ≤
      parameterJetComparisonCost n z * ‖flatQuotient (parameterControlPoint z) x+1‖ := by
  have h := norm_flatParameterJet_sub_trace_le n z x
  rw [parameterVariationBudget_eq] at h
  simpa only [parameterEndpointTrace, parameterJetComparisonCost, parameterControlPoint, mul_assoc] using h

theorem closedParameterJet_interior (n : ℕ) (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    closedParameterJet n z t.val = flatParameterJet n z (thetaSource.quantileFun t.val) := by
  unfold closedParameterJet flatParameterJet
  congr 1
  funext w
  rw [closedQuantileMode_interior, flatModePullback_eq_flatQuotient]

theorem closedParameterJet_endpoints (n : ℕ) (z : ℂ) :
    closedParameterJet n z 0 = parameterEndpointTrace n ∧
      closedParameterJet n z 1 = parameterEndpointTrace n := by
  have h0 : (fun w => closedQuantileMode w 0) = fun _ : ℂ => (-1 : ℂ) :=
    funext fun w => (closedQuantileMode_endpoints w).1
  have h1 : (fun w => closedQuantileMode w 1) = fun _ : ℂ => (-1 : ℂ) :=
    funext fun w => (closedQuantileMode_endpoints w).2
  simp only [closedParameterJet, h0, h1, iteratedDeriv_const, parameterEndpointTrace, and_self]

theorem leftClosedParameterJet_eq (n : ℕ) (z : ℂ) (t : ℝ) :
    leftClosedParameterJet n z t = iteratedDeriv n (fun w => leftClosedQuantileMode w t) z :=
  (iteratedDeriv_comp_neg n (fun w => closedQuantileMode w (1-t)) z).symm

theorem closedParameterJet_right_comparison (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1)
    (s t : Icc c.val 1) :
    ‖closedParameterJet n z s.val-closedParameterJet n z t.val‖ ≤
      parameterJetComparisonCost n z *
        ‖closedQuantileMode (parameterControlPoint z) s.val-
          closedQuantileMode (parameterControlPoint z) t.val‖ := by
  by_cases hs : s.val = 1
  · by_cases ht : t.val = 1
    · simp only [hs, ht, sub_self, norm_zero, mul_zero, le_refl]
    · have hti : t.val ∈ Ioo (0 : ℝ) 1 :=
        ⟨c.property.1.trans_le t.property.1, lt_of_le_of_ne t.property.2 ht⟩
      rw [hs, (closedParameterJet_endpoints n z).2, closedParameterJet_interior n z ⟨_, hti⟩,
        (closedQuantileMode_endpoints _).2, closedQuantileMode_interior _ ⟨_, hti⟩,
        flatModePullback_eq_flatQuotient]
      rw [norm_sub_rev (-1 : ℂ), sub_neg_eq_add,
        norm_sub_rev (parameterEndpointTrace n)]
      exact flatParameterJet_trace_comparison n z (thetaSource.quantileFun t.val)
  · have hsi : s.val ∈ Ioo (0 : ℝ) 1 :=
      ⟨c.property.1.trans_le s.property.1, lt_of_le_of_ne s.property.2 hs⟩
    by_cases ht : t.val = 1
    · rw [ht, (closedParameterJet_endpoints n z).2, closedParameterJet_interior n z ⟨_, hsi⟩,
        (closedQuantileMode_endpoints _).2, closedQuantileMode_interior _ ⟨_, hsi⟩,
        flatModePullback_eq_flatQuotient]
      simpa only [sub_neg_eq_add] using
        flatParameterJet_trace_comparison n z (thetaSource.quantileFun s.val)
    · have hti : t.val ∈ Ioo (0 : ℝ) 1 :=
        ⟨c.property.1.trans_le t.property.1, lt_of_le_of_ne t.property.2 ht⟩
      rw [closedParameterJet_interior n z ⟨_, hsi⟩, closedParameterJet_interior n z ⟨_, hti⟩,
        closedQuantileMode_interior _ ⟨_, hsi⟩, closedQuantileMode_interior _ ⟨_, hti⟩,
        flatModePullback_eq_flatQuotient, flatModePullback_eq_flatQuotient]
      exact flatParameterJet_comparison n z _ _

/-- Every order has an actual AC right branch through the singular endpoint. -/
theorem absolutelyContinuousOnInterval_closedParameterJet_right
    (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval (closedParameterJet n z) c.val 1 := by
  apply absolutelyContinuous_of_increment_comparison
    (absolutelyContinuousOnInterval_closedQuantileMode_right (parameterControlPoint z) c)
  intro s hs t ht
  rw [uIcc_of_le c.property.2.le] at hs ht
  exact closedParameterJet_right_comparison n z c ⟨s, hs⟩ ⟨t, ht⟩

/-- Reflection admits every AC left branch, with the correct parameter-jet sign. -/
theorem absolutelyContinuousOnInterval_leftClosedParameterJet
    (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval (leftClosedParameterJet n z) 0 c.val := by
  let d : Ioo (0 : ℝ) 1 :=
    ⟨1-c.val, by constructor <;> linarith [c.property.1, c.property.2]⟩
  apply absolutelyContinuous_of_increment_comparison
    (K := parameterJetComparisonCost n (-z))
    (absolutelyContinuousOnInterval_leftClosedQuantileMode (-parameterControlPoint (-z)) c)
  intro s hs t ht
  rw [uIcc_of_le c.property.1.le] at hs ht
  have hs' : 1-s ∈ Icc d.val 1 := ⟨by dsimp [d]; linarith [hs.2], by linarith [hs.1]⟩
  have ht' : 1-t ∈ Icc d.val 1 := ⟨by dsimp [d]; linarith [ht.2], by linarith [ht.1]⟩
  rw [leftClosedParameterJet, leftClosedParameterJet, ← mul_sub, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul]
  simpa only [leftClosedQuantileMode, neg_neg] using
    closedParameterJet_right_comparison n (-z) d ⟨1-s, hs'⟩ ⟨1-t, ht'⟩

theorem intervalIntegrable_deriv_closedParameterJet_right (n : ℕ) (z : ℂ)
    (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (deriv (closedParameterJet n z)) volume c.val 1 :=
  (absolutelyContinuousOnInterval_closedParameterJet_right n z c).intervalIntegrable_deriv_vector

theorem intervalIntegrable_deriv_leftClosedParameterJet (n : ℕ) (z : ℂ)
    (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (deriv (leftClosedParameterJet n z)) volume 0 c.val :=
  (absolutelyContinuousOnInterval_leftClosedParameterJet n z c).intervalIntegrable_deriv_vector

end RHTower.PaperThetaEndpoint
