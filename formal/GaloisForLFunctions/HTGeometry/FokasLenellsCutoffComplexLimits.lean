import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffComplexExponential
import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffPhaseNormGap

/-!
# Complete cutoff norm-limit classification at complex time

Every positive derivative order diverges in norm. Zeroth order diverges
exactly away from real time. Norm boundedness survives precisely for the
zeroth real-time family; an actual operator-norm limit exists only at time zero.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Complex time never reduces the exact real-time generator-power norm. -/
theorem cutoffPhaseBudget_pow_le_norm_cutoffComplexOperator (a : ℝ) (n : ℕ) (τ : ℂ) :
    cutoffPhaseBudget a ^ n ≤ ‖cutoffComplexOperator a n τ‖ := by
  rw [norm_cutoffComplexOperator]
  have he : 1 ≤ Real.exp (|τ.im| * cutoffPhaseBudget a) :=
    Real.one_le_exp (mul_nonneg (abs_nonneg _) (cutoffPhaseBudget_pos a).le)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (pow_nonneg (cutoffPhaseBudget_pos a).le n)

/-- Exact classification of norm divergence across every derivative order and complex time. -/
theorem cutoffComplexOperator_norm_tendsto_atBot_iff (n : ℕ) (τ : ℂ) :
    Tendsto (fun a => ‖cutoffComplexOperator a n τ‖) atBot atTop ↔ n ≠ 0 ∨ τ.im ≠ 0 := by
  cases n with
  | zero =>
    simp only [ne_eq,not_true_eq_false,false_or]
    by_cases hi : τ.im = 0
    · simp only [hi,not_true_eq_false,iff_false,norm_cutoffComplexOperator,pow_zero,one_mul,
        abs_zero,zero_mul,Real.exp_zero]
      exact not_tendsto_atTop_of_tendsto_nhds (tendsto_const_nhds (x := (1:ℝ)))
    · constructor
      · intro _; exact hi
      · intro _
        simp only [norm_cutoffComplexOperator,pow_zero,one_mul]
        exact Real.tendsto_exp_atTop.comp
          ((tendsto_const_mul_atTop_of_pos (abs_pos.mpr hi)).2 cutoffPhaseBudget_tendsto_atBot)
  | succ n =>
    constructor
    · intro _; exact Or.inl (Nat.succ_ne_zero n)
    · intro _
      exact tendsto_atTop_mono (fun a => cutoffPhaseBudget_pow_le_norm_cutoffComplexOperator a (n+1) τ)
        ((tendsto_pow_atTop (Nat.succ_ne_zero n)).comp cutoffPhaseBudget_tendsto_atBot)

/-- A uniform norm bound survives cutoff removal exactly at order zero and real time. -/
theorem cutoffComplexOperator_uniform_norm_bound_iff (n : ℕ) (τ : ℂ) :
    (∃ C : ℝ, ∀ a : ℝ, ‖cutoffComplexOperator a n τ‖ ≤ C) ↔ n = 0 ∧ τ.im = 0 := by
  constructor
  · rintro ⟨C,hC⟩
    by_contra hn
    have ho : n ≠ 0 ∨ τ.im ≠ 0 := by simpa only [not_and_or] using hn
    have ht := (cutoffComplexOperator_norm_tendsto_atBot_iff n τ).2 ho
    obtain ⟨a,ha⟩ := (tendsto_atTop.1 ht (C+1)).exists
    linarith [hC a]
  · rintro ⟨rfl,hτ⟩
    refine ⟨1,fun a => ?_⟩
    simp [norm_cutoffComplexOperator,hτ]

/-- An operator-norm cutoff limit exists only for the zeroth derivative at literal time zero. -/
theorem cutoffComplexOperator_exists_norm_limit_iff (n : ℕ) (τ : ℂ) :
    (∃ A : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (fun a => cutoffComplexOperator a n τ) atBot (𝓝 A)) ↔ n = 0 ∧ τ = 0 := by
  constructor
  · rintro ⟨A,hA⟩
    have hp : n = 0 ∧ τ.im = 0 := by
      by_contra hn
      have ho : n ≠ 0 ∨ τ.im ≠ 0 := by simpa only [not_and_or] using hn
      exact not_tendsto_atTop_of_tendsto_nhds hA.norm
        ((cutoffComplexOperator_norm_tendsto_atBot_iff n τ).2 ho)
    rcases hp with ⟨rfl,hi⟩
    have he : τ = (τ.re : ℂ) := by apply Complex.ext <;> simp [hi]
    have hreal : ∃ A : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
        Tendsto (fun a => cutoffEvolution a τ.re) atBot (𝓝 A) := by
      refine ⟨A,?_⟩
      have hA' := hA
      rw [he] at hA'
      simpa only [cutoffComplexOperator_zero_ofReal,Complex.ofReal_re] using hA'
    have hr := (cutoffEvolution_exists_operator_limit_iff τ.re).1 hreal
    exact ⟨rfl,by apply Complex.ext <;> simp [hr,hi]⟩
  · rintro ⟨rfl,rfl⟩
    refine ⟨ContinuousLinearMap.id ℂ _,?_⟩
    have he (a : ℝ) : cutoffComplexOperator a 0 0 = ContinuousLinearMap.id ℂ _ := by
      simpa only [Complex.ofReal_zero,cutoffEvolution_zero] using cutoffComplexOperator_zero_ofReal a 0
    simpa only [he] using (tendsto_const_nhds (x := ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
      Tendsto (fun _ : ℝ => ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure ℝ))) atBot _)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
