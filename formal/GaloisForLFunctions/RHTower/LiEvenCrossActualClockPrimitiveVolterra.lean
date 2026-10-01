import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitive
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelFlattening
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact

open MeasureTheory Filter Topology Set
namespace RHTower
noncomputable section
local notation "P" => liEvenCrossActualClockPrimitive
local notation "F" => liEvenCrossActualClockResponse
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "K" => deriv liEvenCrossActualClockBorelKernel

private theorem pv_borel_hasDerivAt (t : ℝ) : HasDerivAt B (K t) t :=
  (hasDerivAt_liEvenCrossActualClockBorelKernel t).differentiableAt.hasDerivAt

private theorem pv_primitive_continuous : Continuous P :=
  contDiff_liEvenCrossActualClockPrimitive.continuous

private theorem pv_integral_kernel (hK : Continuous K) (t : ℝ) :
    (∫ s in 0..t, K s) = B t - 1 := by
  simpa only [liEvenCrossActualClockBorelKernel_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => pv_borel_hasDerivAt s) (hK.intervalIntegrable 0 t)

private theorem pv_integral_shift_kernel (hK : Continuous K) (t : ℝ) :
    (∫ s in 0..t, K (t-s)) = B t - 1 := by
  rw [intervalIntegral.integral_comp_sub_left]
  simpa only [sub_self, sub_zero] using pv_integral_kernel hK t

private theorem pv_volterra (hK : Continuous K) {t : ℝ} (ht : 0 ≤ t) :
    P t + (∫ s in 0..t, P s * K (t-s)) = t * K t := by
  have hBshift : Continuous (fun s : ℝ => B (t-s)) :=
    continuous_liEvenCrossActualClockBorelKernel.comp (continuous_const.sub continuous_id)
  have hKshift : Continuous (fun s : ℝ => K (t-s)) :=
    hK.comp (continuous_const.sub continuous_id)
  have hv (s : ℝ) : HasDerivAt (fun s : ℝ => B (t-s)) (-K (t-s)) s := by
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using
      (pv_borel_hasDerivAt (t-s)).comp s ((hasDerivAt_id s).const_sub t)
  have hip := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    pv_primitive_continuous.continuousOn hBshift.continuousOn
    (fun s _ => hasDerivAt_liEvenCrossActualClockPrimitive s)
    (fun s _ => hv s)
    (continuous_liEvenCrossActualClockResponse.intervalIntegrable 0 t)
    (hKshift.neg.intervalIntegrable 0 t)
  have hi : (∫ s in 0..t, F s * B (t-s) + P s * (-K (t-s))) =
      (∫ s in 0..t, F s * B (t-s)) - (∫ s in 0..t, P s * K (t-s)) := by
    simp only [mul_neg, ← sub_eq_add_neg]
    exact intervalIntegral.integral_sub
      ((continuous_liEvenCrossActualClockResponse.mul hBshift).intervalIntegrable 0 t)
      ((pv_primitive_continuous.mul hKshift).intervalIntegrable 0 t)
  rw [hi, liEvenCrossActualClockPrimitive_origin_even.1] at hip
  simp only [sub_self, liEvenCrossActualClockBorelKernel_zero, mul_one, zero_mul, sub_zero] at hip
  rw [liEvenCrossActualClockResponse_volterra_eq_mul_deriv ht] at hip
  linarith

private theorem pv_kernel_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ K t := by
  rcases lt_or_eq_of_le ht with h | h
  · exact (liEvenCrossActualClockBorel_deriv_pos h).le
  · rw [← h, liEvenCrossActualClockBorelCorrection_origin.1]

private theorem pv_degree_le (hK : Continuous K) {C : ℝ}
    (hC : ∀ t : ℝ, 0 ≤ t → P t ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    t * K t / B t ≤ C := by
  have hKshift : Continuous (fun s : ℝ => K (t-s)) :=
    hK.comp (continuous_const.sub continuous_id)
  have hi := intervalIntegral.integral_mono_on (μ := volume) ht
    ((pv_primitive_continuous.mul hKshift).intervalIntegrable 0 t)
    ((continuous_const.mul hKshift).intervalIntegrable 0 t)
    (fun s hs => mul_le_mul_of_nonneg_right (hC s hs.1)
      (pv_kernel_nonneg (sub_nonneg.mpr hs.2)))
  change (∫ s in 0..t, P s * K (t-s)) ≤ (∫ s in 0..t, C * K (t-s)) at hi
  rw [intervalIntegral.integral_const_mul, pv_integral_shift_kernel hK t] at hi
  apply (div_le_iff₀ (liEvenCrossActualClockBorelKernel_pos t)).2
  calc
    t * K t = P t + ∫ s in 0..t, P s * K (t-s) := (pv_volterra hK ht).symm
    _ ≤ C + C * (B t - 1) := add_le_add (hC t ht) hi
    _ = C * B t := by ring

private theorem pv_no_upper (hK : Continuous K) (C : ℝ) :
    ¬ ∀ t : ℝ, 0 ≤ t → P t ≤ C := by
  intro hC
  have hd := liEvenCrossActualClockBorel_logarithmicDegree_tendsto_atTop.eventually_gt_atTop C
  obtain ⟨t, ht, hdegree⟩ := ((eventually_ge_atTop (0 : ℝ)).and hd).exists
  exact (not_lt_of_ge (pv_degree_le hK hC ht)) hdegree

private theorem pv_unbounded (hK : Continuous K) (M T : ℝ) :
    ∃ t : ℝ, max T 0 < t ∧ M < P t := by
  by_contra h
  have htail (t : ℝ) (ht : max T 0 < t) : P t ≤ M :=
    le_of_not_gt (fun hp => h ⟨t, ht, hp⟩)
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max T 0))).bddAbove_image
    pv_primitive_continuous.continuousOn
  apply pv_no_upper hK (max C₀ M)
  intro t ht
  by_cases hta : t ≤ max T 0
  · exact (hC₀ ⟨t, ⟨ht, hta⟩, rfl⟩).trans (le_max_left _ _)
  · exact (htail t (lt_of_not_ge hta)).trans (le_max_right _ _)

private theorem pv_kernel_continuous : Continuous K :=
  contDiff_liEvenCrossActualClockBorelKernel.continuous_deriv (by simp)

/-- The literal primitive satisfies the integrated Volterra identity with
the actual Borel derivative kernel and factor one. -/
theorem liEvenCrossActualClockPrimitive_volterra {t : ℝ} (ht : 0 ≤ t) :
    liEvenCrossActualClockPrimitive t +
      (∫ s in 0..t, liEvenCrossActualClockPrimitive s *
        deriv liEvenCrossActualClockBorelKernel (t-s)) =
      t * deriv liEvenCrossActualClockBorelKernel t :=
  pv_volterra pv_kernel_continuous ht

/-- Unconditionally, primitive values exceed every real bound on every tail. -/
theorem liEvenCrossActualClockPrimitive_unboundedAbove_tail (M T : ℝ) :
    ∃ t : ℝ, max T 0 < t ∧ M < liEvenCrossActualClockPrimitive t :=
  pv_unbounded pv_kernel_continuous M T

end
end RHTower
