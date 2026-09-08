import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceHorizonFactor

/-! Quantitative decay of the actual delayed radial source, including the onset derivative. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMLaplaceRadial D4BMModularCore
noncomputable section

/-- The fixed onset and its first derivative share every exponential majorant below their decay rate. -/
theorem timeOnset_pair_bound (v : ℂ) (c : ℝ) (hc : v.re ≤ -c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖timeOnset v u‖ + ‖timeOnsetFirst v u‖ ≤ B*Real.exp (-c*u) := by
  obtain ⟨Λ,hΛ,hb⟩ := exists_bound_deriv_smoothTransition
  refine ⟨1+Λ+‖v‖,by positivity,?_⟩
  intro u
  by_cases hu : u < 0
  · rw [timeOnset_zero_of_nonpos v hu.le,timeOnsetFirst_zero_of_neg v hu]
    simp only [norm_zero,zero_add]
    positivity
  have hχ : ‖(Real.smoothTransition u:ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg u)]
      using Real.smoothTransition.le_one u
  have hχ' : ‖((deriv Real.smoothTransition u:ℝ):ℂ)‖ ≤ Λ := by
    simpa [Complex.norm_real,Real.norm_eq_abs] using hb u
  have hE : ‖Complex.exp (v*(u:ℂ))‖ ≤ Real.exp (-c*u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using mul_le_mul_of_nonneg_right hc (le_of_not_gt hu)
  have hH : ‖timeOnset v u‖ ≤ Real.exp (-c*u) := by
    unfold timeOnset
    rw [norm_mul]
    exact (mul_le_mul hχ hE (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hD : ‖timeOnsetFirst v u‖ ≤ (Λ+‖v‖)*Real.exp (-c*u) := by
    unfold timeOnsetFirst
    rw [norm_mul]
    apply mul_le_mul _ hE (norm_nonneg _) (by positivity)
    calc
      ‖((deriv Real.smoothTransition u:ℝ):ℂ)+v*(Real.smoothTransition u:ℂ)‖ ≤
          ‖((deriv Real.smoothTransition u:ℝ):ℂ)‖+‖v*(Real.smoothTransition u:ℂ)‖ := norm_add_le _ _
      _ ≤ Λ+‖v‖ := by rw [norm_mul]; nlinarith [norm_nonneg v]
  nlinarith

/-- Actual radial source bound retains two powers of horizon decay and any time exponent below two. -/
theorem timeReducedCoefficient_bound (s a : ℂ) (c : ℝ) (hc : (2*s).re ≤ -c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ t : ℝ, t < 0 →
      ‖timeReducedCoefficient s a τ t‖ ≤ C*Real.exp (-c*τ)*Real.exp ((2-c)*t) := by
  obtain ⟨C₀,h₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (sourceHorizonProfile_continuousOn s a 0)
  obtain ⟨C₁,h₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (sourceHorizonProfile_continuousOn s a 1)
  obtain ⟨B,hB,hb⟩ := timeOnset_pair_bound (2*s) c hc
  let D := max (max C₀ C₁) 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨D*B,mul_nonneg hD hB,?_⟩
  intro τ t ht
  have hu : radialUnit t ∈ Icc (0:ℝ) 1 :=
    ⟨(radialUnit_bounds t ht).1.le,(radialUnit_bounds t ht).2.le⟩
  have hb₀ : ‖sourceHorizonProfile s a 0 (radialUnit t)‖ ≤ D :=
    (h₀ _ hu).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hb₁ : ‖sourceHorizonProfile s a 1 (radialUnit t)‖ ≤ D :=
    (h₁ _ hu).trans ((le_max_right _ _).trans (le_max_left _ _))
  have he : Real.exp (2*t)*Real.exp (-c*(τ+t)) = Real.exp (-c*τ)*Real.exp ((2-c)*t) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  unfold timeReducedCoefficient
  rw [reducedCoefficient_horizon,radialLiftFirst_horizon]
  calc
    _ ≤ ‖(Real.exp (2*t):ℂ)*sourceHorizonProfile s a 0 (radialUnit t)*timeOnset (2*s) (τ+t)‖+
        ‖(Real.exp (2*t):ℂ)*sourceHorizonProfile s a 1 (radialUnit t)*timeOnsetFirst (2*s) (τ+t)‖ := norm_add_le _ _
    _ = Real.exp (2*t)*(‖sourceHorizonProfile s a 0 (radialUnit t)‖*‖timeOnset (2*s) (τ+t)‖+
        ‖sourceHorizonProfile s a 1 (radialUnit t)‖*‖timeOnsetFirst (2*s) (τ+t)‖) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ Real.exp (2*t)*(D*(‖timeOnset (2*s) (τ+t)‖+‖timeOnsetFirst (2*s) (τ+t)‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      nlinarith [norm_nonneg (timeOnset (2*s) (τ+t)),norm_nonneg (timeOnsetFirst (2*s) (τ+t))]
    _ ≤ Real.exp (2*t)*(D*(B*Real.exp (-c*(τ+t)))) := by gcongr; exact hb (τ+t)
    _ = D*B*Real.exp (-c*τ)*Real.exp ((2-c)*t) := by calc
      _ = D*B*(Real.exp (2*t)*Real.exp (-c*(τ+t))) := by ring
      _ = _ := by rw [he]; ring

/-- The physical source rate proves the bound throughout the chamber needed for left-half-plane source transforms. -/
theorem timeReducedCoefficient_physical_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (c : ℝ) (hc : c < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ t : ℝ, t < 0 →
      ‖timeReducedCoefficient (physicalRate q branch) a τ t‖ ≤
        C*Real.exp (-c*τ)*Real.exp ((2-c)*t) := by
  apply timeReducedCoefficient_bound
  have h := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at h
  linarith

end
end RHTower.D4BMJointSource
