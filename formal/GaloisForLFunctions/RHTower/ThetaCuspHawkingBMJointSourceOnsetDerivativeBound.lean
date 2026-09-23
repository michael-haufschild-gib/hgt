import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeDecay
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! A uniform analytic majorant for the differentiated causal onset. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
noncomputable section

private theorem continuous_transition_second : Continuous (deriv (deriv Real.smoothTransition)) := by
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
    ContDiff.continuous_iteratedDeriv' 2 (Real.smoothTransition.contDiff (n := 2))

private theorem continuous_transition_third : Continuous (deriv (deriv (deriv Real.smoothTransition))) := by
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
    ContDiff.continuous_iteratedDeriv' 3 (Real.smoothTransition.contDiff (n := 3))

private theorem transition_second_zero {x : ℝ} (hx : x ∉ Icc (0:ℝ) 1) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    exact deriv_smoothTransition_eq_zero_of_notMem hy
  rw [h.deriv_eq,deriv_const]

private theorem transition_third_zero {x : ℝ} (hx : x ∉ Icc (0:ℝ) 1) :
    deriv (deriv (deriv Real.smoothTransition)) x = 0 := by
  have h : deriv (deriv Real.smoothTransition) =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    exact transition_second_zero hy
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

private theorem transition_third_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, |deriv (deriv (deriv Real.smoothTransition)) u| ≤ B := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_transition_third.continuousOn (s := Icc (0:ℝ) 1))
  refine ⟨max B 0,le_max_right _ _,fun u => ?_⟩
  by_cases hu : u ∈ Icc (0:ℝ) 1
  · simpa only [Real.norm_eq_abs] using (hB u hu).trans (le_max_left B 0)
  · rw [transition_third_zero hu,abs_zero]
    exact le_max_right _ _

/-- The second onset derivative is continuous across both ends of the transition. -/
theorem timeOnsetSecond_continuous (v : ℂ) : Continuous (timeOnsetSecond v) := by
  have h₀ := Real.smoothTransition.continuous
  have h₁ := continuous_deriv_smoothTransition
  have h₂ := continuous_transition_second
  unfold timeOnsetSecond
  fun_prop

/-- The third onset jet remains continuous through both smooth-transition endpoints. -/
theorem timeOnsetThird_continuous (v : ℂ) : Continuous (timeOnsetThird v) := by
  have h₀ := Real.smoothTransition.continuous
  have h₁ := continuous_deriv_smoothTransition
  have h₂ := continuous_transition_second
  have h₃ := continuous_transition_third
  unfold timeOnsetThird
  fun_prop

/-- Differentiating the actual onset preserves its vanishing before arrival. -/
theorem timeOnsetSecond_zero_of_neg (v : ℂ) {u : ℝ} (hu : u < 0) :
    timeOnsetSecond v u = 0 := by
  rw [timeOnsetSecond,Real.smoothTransition.zero_of_nonpos hu.le,
    deriv_smoothTransition_eq_zero_of_notMem (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.1),
    transition_second_zero (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.1)]
  simp

/-- The third onset derivative also vanishes strictly before causal arrival. -/
theorem timeOnsetThird_zero_of_neg (v : ℂ) {u : ℝ} (hu : u < 0) :
    timeOnsetThird v u = 0 := by
  rw [timeOnsetThird,Real.smoothTransition.zero_of_nonpos hu.le,
    deriv_smoothTransition_eq_zero_of_notMem (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.1),
    transition_second_zero (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.1),
    transition_third_zero (show u ∉ Icc (0:ℝ) 1 from fun h => not_le_of_gt hu h.1)]
  simp

/-- Both terms required by the time derivative admit one global bound at a decaying rate. -/
theorem timeOnset_derivative_pair_bound (v : ℂ) (hv : v.re ≤ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, ‖timeOnsetFirst v u‖+‖timeOnsetSecond v u‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := timeOnset_pair_bound v 0 (by simpa using hv)
  obtain ⟨Λ,hΛ,hLam⟩ := exists_bound_deriv_smoothTransition
  obtain ⟨K,hK,hk⟩ := transition_second_bound
  refine ⟨B+K+2*‖v‖*Λ+‖v‖^(2 : ℕ),by positivity,fun u => ?_⟩
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
  have hD : ‖timeOnsetSecond v u‖ ≤ K+2*‖v‖*Λ+‖v‖^(2 : ℕ) := by
    unfold timeOnsetSecond
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left hE (norm_nonneg _)).trans
    rw [mul_one]
    calc
      _ ≤ ‖((deriv (deriv Real.smoothTransition) u:ℝ):ℂ)‖+
          ‖2*v*((deriv Real.smoothTransition u:ℝ):ℂ)‖+‖v^(2 : ℕ)*(Real.smoothTransition u:ℂ)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ K+2*‖v‖*Λ+‖v‖^(2 : ℕ) := by
        simp only [norm_mul,norm_pow,Complex.norm_ofNat]
        exact add_le_add (add_le_add hχ''
          (mul_le_mul_of_nonneg_left hχ' (by positivity)))
          ((mul_le_mul_of_nonneg_left hχ (sq_nonneg ‖v‖)).trans_eq (mul_one _))
  have hFirst : ‖timeOnset v u‖+‖timeOnsetFirst v u‖ ≤ B := by simpa using hb u
  linarith [norm_nonneg (timeOnset v u)]

/- The second onset jet obeys the same shifted-exponential identity as the
first one.  Keeping it here makes the source-time majorant reusable outside
the cap calculation. -/
private theorem timeOnsetSecond_shift (v : ℂ) (c u : ℝ) :
    timeOnsetSecond v u = Complex.exp (-(c:ℂ)*(u:ℂ))*
      (timeOnsetSecond (v+c) u-2*c*timeOnsetFirst (v+c) u+
        (c:ℂ)^(2 : ℕ)*timeOnset (v+c) u) := by
  unfold timeOnsetSecond timeOnsetFirst timeOnset
  have he : Complex.exp (-(c:ℂ)*(u:ℂ))*Complex.exp ((v+c)*(u:ℂ)) =
      Complex.exp (v*(u:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = Complex.exp (v*(u:ℂ))*
        (((deriv (deriv Real.smoothTransition) u:ℝ):ℂ)+
          2*v*((deriv Real.smoothTransition u:ℝ):ℂ)+v^(2 : ℕ)*(Real.smoothTransition u:ℂ)) := by ring
    _ = _ := by rw [← he]; ring

/-- The first two literal onset derivatives retain every nonnegative decay
exponent below the real decay of the source rate. -/
theorem timeOnset_derivative_pair_decay (v : ℂ) (c : ℝ)
    (hv : v.re ≤ -c) (hc : 0 ≤ c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖timeOnsetFirst v u‖+‖timeOnsetSecond v u‖ ≤ B*Real.exp (-c*u) := by
  have hvc : (v+c).re ≤ 0 := by
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith
  obtain ⟨B,hB,hb⟩ := timeOnset_pair_bound v c hv
  obtain ⟨D,hD,hd⟩ := timeOnset_derivative_pair_bound (v+c) hvc
  obtain ⟨A,hA,ha⟩ := timeOnset_pair_bound (v+c) 0 (by simpa using hvc)
  refine ⟨B+D+2*c*D+c^(2 : ℕ)*A,by positivity,fun u => ?_⟩
  have h0 : ‖timeOnset (v+c) u‖ ≤ A := by
    have h := ha u
    simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at h
    linarith [norm_nonneg (timeOnsetFirst (v+c) u)]
  have h1 : ‖timeOnsetFirst (v+c) u‖ ≤ D := by
    linarith [hd u,norm_nonneg (timeOnsetSecond (v+c) u)]
  have h2 : ‖timeOnsetSecond (v+c) u‖ ≤ D := by
    linarith [hd u,norm_nonneg (timeOnsetFirst (v+c) u)]
  have hSecond : ‖timeOnsetSecond v u‖ ≤
      Real.exp (-c*u)*(D+2*c*D+c^(2 : ℕ)*A) := by
    rw [timeOnsetSecond_shift v c u,norm_mul,Complex.norm_exp]
    have he : (-(c:ℂ)*(u:ℂ)).re = -c*u := by simp
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    calc
      _ ≤ ‖timeOnsetSecond (v+c) u‖+‖2*(c:ℂ)*timeOnsetFirst (v+c) u‖+
          ‖(c:ℂ)^(2 : ℕ)*timeOnset (v+c) u‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ D+2*c*D+c^(2 : ℕ)*A := by
        simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg hc]
        gcongr
  have hFirst : ‖timeOnsetFirst v u‖ ≤ B*Real.exp (-c*u) := by
    linarith [hb u,norm_nonneg (timeOnset v u)]
  nlinarith

/-- The second and third onset jets have a common global majorant whenever the
source rate is non-growing. -/
theorem timeOnset_second_derivative_pair_bound (v : ℂ) (hv : v.re ≤ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, ‖timeOnsetSecond v u‖+‖timeOnsetThird v u‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := timeOnset_derivative_pair_bound v hv
  obtain ⟨Λ,hΛ,hLam⟩ := exists_bound_deriv_smoothTransition
  obtain ⟨K,hK,hk⟩ := transition_second_bound
  obtain ⟨L,hL,hℓ⟩ := transition_third_bound
  refine ⟨B+L+3*‖v‖*K+3*‖v‖^(2 : ℕ)*Λ+‖v‖^(3 : ℕ),by positivity,fun u => ?_⟩
  by_cases hu : u < 0
  · rw [timeOnsetSecond_zero_of_neg v hu,timeOnsetThird_zero_of_neg v hu]
    simp only [norm_zero,zero_add]
    positivity
  have hχ : ‖(Real.smoothTransition u:ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg u)]
      using Real.smoothTransition.le_one u
  have hχ' : ‖((deriv Real.smoothTransition u:ℝ):ℂ)‖ ≤ Λ := by
    simpa [Complex.norm_real,Real.norm_eq_abs] using hLam u
  have hχ'' : ‖((deriv (deriv Real.smoothTransition) u:ℝ):ℂ)‖ ≤ K := by
    simpa [Complex.norm_real,Real.norm_eq_abs] using hk u
  have hχ''' : ‖((deriv (deriv (deriv Real.smoothTransition)) u:ℝ):ℂ)‖ ≤ L := by
    simpa [Complex.norm_real,Real.norm_eq_abs] using hℓ u
  have hE : ‖Complex.exp (v*(u:ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp,← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    simpa using mul_nonpos_of_nonpos_of_nonneg hv (le_of_not_gt hu)
  have hThird : ‖timeOnsetThird v u‖ ≤ L+3*‖v‖*K+3*‖v‖^(2 : ℕ)*Λ+‖v‖^(3 : ℕ) := by
    unfold timeOnsetThird
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left hE (norm_nonneg _)).trans
    rw [mul_one]
    calc
      _ ≤ (‖((deriv (deriv (deriv Real.smoothTransition)) u:ℝ):ℂ)‖+
          ‖3*v*((deriv (deriv Real.smoothTransition) u:ℝ):ℂ)‖+
          ‖3*v^(2 : ℕ)*((deriv Real.smoothTransition u:ℝ):ℂ)‖)+
          ‖v^(3 : ℕ)*(Real.smoothTransition u:ℂ)‖ := by
        exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
          (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl))
      _ ≤ L+3*‖v‖*K+3*‖v‖^(2 : ℕ)*Λ+‖v‖^(3 : ℕ) := by
        simp only [norm_mul,norm_pow,Complex.norm_ofNat]
        gcongr
        exact mul_le_of_le_one_right (by positivity) hχ
  have hSecond : ‖timeOnsetSecond v u‖ ≤ B := by
    linarith [hb u,norm_nonneg (timeOnsetFirst v u)]
  linarith

end
end RHTower.D4BMJointSource
