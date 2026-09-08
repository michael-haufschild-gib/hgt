import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeDecay
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! A uniform analytic majorant for the differentiated causal onset. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
noncomputable section

private theorem continuous_transition_second : Continuous (deriv (deriv Real.smoothTransition)) := by
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
    ContDiff.continuous_iteratedDeriv' 2 (Real.smoothTransition.contDiff (n := 2))

private theorem transition_second_zero {x : ℝ} (hx : x ∉ Icc (0:ℝ) 1) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    exact deriv_smoothTransition_eq_zero_of_notMem hy
  rw [h.deriv_eq,deriv_const]

private theorem transition_second_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, |deriv (deriv Real.smoothTransition) u| ≤ B := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_transition_second.continuousOn (s := Icc (0:ℝ) 1))
  refine ⟨max B 0,le_max_right _ _,fun u => ?_⟩
  by_cases hu : u ∈ Icc (0:ℝ) 1
  · simpa only [Real.norm_eq_abs] using (hB u hu).trans (le_max_left B 0)
  · rw [transition_second_zero hu,abs_zero]
    exact le_max_right _ _

/-- The second onset derivative is continuous across both ends of the transition. -/
theorem timeOnsetSecond_continuous (v : ℂ) : Continuous (timeOnsetSecond v) := by
  have h₀ := Real.smoothTransition.continuous
  have h₁ := continuous_deriv_smoothTransition
  have h₂ := continuous_transition_second
  unfold timeOnsetSecond
  fun_prop

/-- Differentiating the actual onset preserves its vanishing before arrival. -/
theorem timeOnsetSecond_zero_of_neg (v : ℂ) {u : ℝ} (hu : u < 0) :
    timeOnsetSecond v u = 0 := by
  rw [timeOnsetSecond,Real.smoothTransition.zero_of_nonpos hu.le,
    deriv_smoothTransition_eq_zero_of_notMem (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.1),
    transition_second_zero (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.1)]
  simp

/-- Both terms required by the time derivative admit one global bound at a decaying rate. -/
theorem timeOnset_derivative_pair_bound (v : ℂ) (hv : v.re ≤ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, ‖timeOnsetFirst v u‖+‖timeOnsetSecond v u‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := timeOnset_pair_bound v 0 (by simpa using hv)
  obtain ⟨Λ,hΛ,hLam⟩ := exists_bound_deriv_smoothTransition
  obtain ⟨K,hK,hk⟩ := transition_second_bound
  refine ⟨B+K+2*‖v‖*Λ+‖v‖^2,by positivity,fun u => ?_⟩
  by_cases hu : u < 0
  · rw [timeOnsetFirst_zero_of_neg v hu,timeOnsetSecond_zero_of_neg v hu]
    simp only [norm_zero,zero_add]
    positivity
  have hχ : ‖(Real.smoothTransition u:ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg u)]
      using Real.smoothTransition.le_one u
  have hχ' : ‖((deriv Real.smoothTransition u:ℝ):ℂ)‖ ≤ Λ := by
    simpa [Complex.norm_real,Real.norm_eq_abs] using hLam u
  have hχ'' : ‖((deriv (deriv Real.smoothTransition) u:ℝ):ℂ)‖ ≤ K := by
    simpa [Complex.norm_real,Real.norm_eq_abs] using hk u
  have hE : ‖Complex.exp (v*(u:ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp,← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    simpa using mul_nonpos_of_nonpos_of_nonneg hv (le_of_not_gt hu)
  have hD : ‖timeOnsetSecond v u‖ ≤ K+2*‖v‖*Λ+‖v‖^2 := by
    unfold timeOnsetSecond
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left hE (norm_nonneg _)).trans
    rw [mul_one]
    calc
      _ ≤ ‖((deriv (deriv Real.smoothTransition) u:ℝ):ℂ)‖+
          ‖2*v*((deriv Real.smoothTransition u:ℝ):ℂ)‖+‖v^2*(Real.smoothTransition u:ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ K+2*‖v‖*Λ+‖v‖^2 := by
        simp only [norm_mul,norm_pow,Complex.norm_ofNat]
        nlinarith [mul_le_mul_of_nonneg_left hχ' (by positivity : 0 ≤ 2*‖v‖),
          mul_le_mul_of_nonneg_left hχ (sq_nonneg ‖v‖)]
  have hFirst : ‖timeOnset v u‖+‖timeOnsetFirst v u‖ ≤ B := by simpa using hb u
  linarith [norm_nonneg (timeOnset v u)]

end
end RHTower.D4BMJointSource
