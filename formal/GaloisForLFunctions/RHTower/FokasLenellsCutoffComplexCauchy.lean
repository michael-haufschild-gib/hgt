import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffComplexLimits
import GaloisForLFunctions.RHTower.FokasLenellsCutoffCauchyAllOrder
import GaloisForLFunctions.RHTower.FokasLenellsCutoffCauchyNormGap

/-!
# Entire complex-time growth and cutoff limits after actual Cauchy compression

The paper's signed Cauchy operator preserves all complex derivative norms
and all cross-order distances. It preserves the exact norm-divergence and
boundedness classifications, with an operator-norm cutoff limit only at
zeroth order and literal time zero.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual Cauchy compression of the complex cutoff derivative multiplier. -/
def cutoffComplexCauchyOperator (a : ℝ) (n : ℕ) (τ : ℂ) : SoninL2 →L[ℂ] SoninL2 :=
  negativeCauchy.comp (cutoffComplexOperator a n τ)

/-- The compressed operator retains the literal complex-time symbol representation. -/
theorem cutoffComplexCauchyOperator_eq_cauchyLinfty (a : ℝ) (n : ℕ) (τ : ℂ) :
    cutoffComplexCauchyOperator a n τ = cauchyLinftyMultiplier (cutoffComplexLinfty a n τ) := rfl

/-- Exact vertical growth and every derivative factor survive actual Cauchy compression. -/
theorem norm_cutoffComplexCauchyOperator (a : ℝ) (n : ℕ) (τ : ℂ) :
    ‖cutoffComplexCauchyOperator a n τ‖ =
      cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a) := by
  rw [cutoffComplexCauchyOperator_eq_cauchyLinfty,norm_cauchyLinftyMultiplier,norm_cutoffComplexLinfty]

/-- Cauchy compression preserves distances across all complex times, orders, and widths. -/
theorem norm_cutoffComplexCauchyOperator_sub_eq_uncompressed (a b : ℝ) (m n : ℕ) (τ σ : ℂ) :
    ‖cutoffComplexCauchyOperator a m τ - cutoffComplexCauchyOperator b n σ‖ =
      ‖cutoffComplexOperator a m τ - cutoffComplexOperator b n σ‖ := by
  rw [cutoffComplexCauchyOperator_eq_cauchyLinfty,cutoffComplexCauchyOperator_eq_cauchyLinfty,
    cutoffComplexOperator,cutoffComplexOperator,← map_sub,← map_sub,
    norm_cauchyLinftyMultiplier,norm_lineLinftyMultiplier]

/-- Every complex Cauchy derivative differentiates to the next actual compressed operator. -/
theorem cutoffComplexCauchyOperator_hasDerivAt (a : ℝ) (n : ℕ) (τ : ℂ) :
    HasDerivAt (cutoffComplexCauchyOperator a n) (cutoffComplexCauchyOperator a (n+1) τ) τ :=
  (ContinuousLinearMap.compL ℂ SoninL2 SoninL2 SoninL2 negativeCauchy).hasFDerivAt.comp_hasDerivAt τ
    (cutoffComplexOperator_hasDerivAt a n τ)

/-- The actual Cauchy family is entire in operator norm at every derivative order. -/
theorem cutoffComplexCauchyOperator_analyticAt (a : ℝ) (n : ℕ) (τ : ℂ) :
    AnalyticAt ℂ (cutoffComplexCauchyOperator a n) τ :=
  ((ContinuousLinearMap.compL ℂ SoninL2 SoninL2 SoninL2 negativeCauchy).analyticAt _).comp
    (cutoffComplexOperator_analyticAt a n τ)

/-- Every iterated complex Cauchy derivative is its actual compressed multiplier. -/
theorem iteratedDeriv_cutoffComplexCauchyOperator (a : ℝ) (n : ℕ) :
    iteratedDeriv n (cutoffComplexCauchyOperator a 0) = cutoffComplexCauchyOperator a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun τ => (cutoffComplexCauchyOperator_hasDerivAt a n τ).deriv

/-- Restriction to real time recovers every previously verified actual Cauchy derivative. -/
theorem cutoffComplexCauchyOperator_ofReal (a t : ℝ) (n : ℕ) :
    cutoffComplexCauchyOperator a n (t : ℂ) = cutoffCauchyDerivative a n t := by
  rw [cutoffComplexCauchyOperator,cutoffComplexOperator_ofReal]
  rfl

/-- The entire family is the literal Cauchy compression of the actual generator exponential. -/
theorem cutoffComplexCauchyOperator_eq_pow_exp (a : ℝ) (n : ℕ) (τ : ℂ) :
    cutoffComplexCauchyOperator a n τ = negativeCauchy.comp
      (cutoffEvolutionTimeOperator a 0 ^ n * NormedSpace.exp (τ • cutoffEvolutionTimeOperator a 0)) := by
  rw [cutoffComplexCauchyOperator,cutoffComplexOperator_eq_pow_exp]

/-- Cauchy compression preserves the complete complex norm-divergence classification. -/
theorem cutoffComplexCauchyOperator_norm_tendsto_atBot_iff (n : ℕ) (τ : ℂ) :
    Tendsto (fun a => ‖cutoffComplexCauchyOperator a n τ‖) atBot atTop ↔ n ≠ 0 ∨ τ.im ≠ 0 := by
  simpa only [norm_cutoffComplexCauchyOperator,norm_cutoffComplexOperator] using
    cutoffComplexOperator_norm_tendsto_atBot_iff n τ

/-- Uniform norm boundedness survives precisely at zeroth order and real time, also after projection. -/
theorem cutoffComplexCauchyOperator_uniform_norm_bound_iff (n : ℕ) (τ : ℂ) :
    (∃ C : ℝ, ∀ a : ℝ, ‖cutoffComplexCauchyOperator a n τ‖ ≤ C) ↔ n = 0 ∧ τ.im = 0 := by
  simpa only [norm_cutoffComplexCauchyOperator,norm_cutoffComplexOperator] using
    cutoffComplexOperator_uniform_norm_bound_iff n τ

/-- Actual Cauchy operator-norm limits exist only at zeroth order and literal time zero. -/
theorem cutoffComplexCauchyOperator_exists_norm_limit_iff (n : ℕ) (τ : ℂ) :
    (∃ A : SoninL2 →L[ℂ] SoninL2,
      Tendsto (fun a => cutoffComplexCauchyOperator a n τ) atBot (𝓝 A)) ↔ n = 0 ∧ τ = 0 := by
  constructor
  · rintro ⟨A,hA⟩
    have hp : n = 0 ∧ τ.im = 0 := by
      by_contra hn
      have ho : n ≠ 0 ∨ τ.im ≠ 0 := by simpa only [not_and_or] using hn
      exact not_tendsto_atTop_of_tendsto_nhds hA.norm
        ((cutoffComplexCauchyOperator_norm_tendsto_atBot_iff n τ).2 ho)
    rcases hp with ⟨rfl,hi⟩
    have he : τ = (τ.re : ℂ) := by apply Complex.ext <;> simp [hi]
    have hreal : ∃ A : SoninL2 →L[ℂ] SoninL2,
        Tendsto (fun a => cutoffCauchyEvolution a τ.re) atBot (𝓝 A) := by
      refine ⟨A,?_⟩
      have hA' := hA
      rw [he] at hA'
      simpa only [cutoffComplexCauchyOperator_ofReal,cutoffCauchyDerivative_zero,Complex.ofReal_re] using hA'
    have hr := (cutoffCauchyEvolution_exists_operator_limit_iff τ.re).1 hreal
    exact ⟨rfl,by apply Complex.ext <;> simp [hr,hi]⟩
  · rintro ⟨rfl,rfl⟩
    refine ⟨negativeCauchy,?_⟩
    have he (a : ℝ) : cutoffComplexCauchyOperator a 0 0 = negativeCauchy := by
      change negativeCauchy.comp (cutoffComplexOperator a 0 (0 : ℝ)) = negativeCauchy
      rw [cutoffComplexOperator_zero_ofReal,cutoffEvolution_zero,ContinuousLinearMap.comp_id]
    simpa only [he] using (tendsto_const_nhds (x := negativeCauchy) :
      Tendsto (fun _ : ℝ => negativeCauchy) atBot _)

end
end RHTower.FokasLenells
