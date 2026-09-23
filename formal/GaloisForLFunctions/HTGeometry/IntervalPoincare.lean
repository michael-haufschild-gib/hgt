import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The interval Poincaré estimate

On an interval of length `h` a differentiable function differs from its value at the left endpoint
by at most the total variation of its derivative, and Cauchy–Schwarz turns that into

`∫_α^β (g(x) − g(α))² dx ≤ h²·∫_α^β g'(x)² dx`.

This is the elementary quantitative input behind finite-dimensional approximation in `L²`: a grid of
mesh `h` approximates a function with square-integrable derivative to accuracy `h·‖g'‖₂`.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem integrableOn_one_Ioc (α β : ℝ) :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc α β) volume :=
  (integrableOn_const_iff (by simp)).2 (Or.inr measure_Ioc_lt_top)

theorem integral_one_Ioc {α β : ℝ} (h : α ≤ β) : (∫ _y in Set.Ioc α β, (1 : ℝ)) = β - α := by
  simp [h]

/-- Cauchy–Schwarz against the constant one on a bounded interval. -/
theorem sq_integral_le_length_mul {f : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hf : IntegrableOn f (Set.Ioc α β) volume)
    (hf2 : IntegrableOn (fun y => f y ^ (2 : ℕ)) (Set.Ioc α β) volume) :
    (∫ y in Set.Ioc α β, f y) ^ (2 : ℕ) ≤ (β - α) * ∫ y in Set.Ioc α β, f y ^ (2 : ℕ) := by
  have hone : Integrable (fun _ : ℝ => (1 : ℝ) ^ (2 : ℕ))
      ((volume : Measure ℝ).restrict (Set.Ioc α β)) := by
    simp
  have hbase := sq_integral_mul_le
    (μ := (volume : Measure ℝ).restrict (Set.Ioc α β))
    (f := fun _ : ℝ => (1 : ℝ)) (g := f)
    aestronglyMeasurable_const hf.aestronglyMeasurable hone hf2
  simp only [one_mul, one_pow] at hbase
  rwa [integral_one_Ioc hαβ] at hbase

/-- The increment of a differentiable function is controlled by the `L²` norm of its derivative. -/
theorem sq_sub_left_le_of_hasDerivAt {g g' : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hderiv : ∀ y : ℝ, HasDerivAt g (g' y) y)
    (hg' : IntervalIntegrable g' volume α β)
    (hg'2 : IntervalIntegrable (fun y => g' y ^ (2 : ℕ)) volume α β)
    {x : ℝ} (hx : x ∈ Set.Icc α β) :
    (g x - g α) ^ (2 : ℕ) ≤ (β - α) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ) := by
  obtain ⟨hxα, hxβ⟩ := hx
  have hsub : Set.uIcc α x ⊆ Set.uIcc α β := by
    rw [Set.uIcc_of_le hxα, Set.uIcc_of_le hαβ]
    exact Set.Icc_subset_Icc le_rfl hxβ
  have hftc : (∫ y in α..x, g' y) = g x - g α :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) (hg'.mono_set hsub)
  have habsInt : IntegrableOn (fun y => |g' y|) (Set.Ioc α β) volume := hg'.abs.1
  have habs : |∫ y in α..x, g' y| ≤ ∫ y in Set.Ioc α β, |g' y| := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hxα) ?_
    rw [intervalIntegral.integral_of_le hxα]
    refine MeasureTheory.setIntegral_mono_set habsInt ?_ ?_
    · filter_upwards with y
      exact abs_nonneg _
    · exact Filter.Eventually.of_forall (Set.Ioc_subset_Ioc_right hxβ)
  have habsSq : IntegrableOn (fun y => |g' y| ^ (2 : ℕ)) (Set.Ioc α β) volume := by
    refine hg'2.1.congr ?_
    filter_upwards with y
    rw [sq_abs]
  have hcs : (∫ y in Set.Ioc α β, |g' y|) ^ (2 : ℕ)
      ≤ (β - α) * ∫ y in Set.Ioc α β, |g' y| ^ (2 : ℕ) :=
    sq_integral_le_length_mul hαβ habsInt habsSq
  have hsame : (∫ y in Set.Ioc α β, |g' y| ^ (2 : ℕ)) = ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with y
    rw [sq_abs]
  rw [hsame] at hcs
  have hnn : (0 : ℝ) ≤ ∫ y in Set.Ioc α β, |g' y| :=
    MeasureTheory.integral_nonneg fun y => abs_nonneg _
  have hsq : (g x - g α) ^ (2 : ℕ) = |∫ y in α..x, g' y| ^ (2 : ℕ) := by
    rw [hftc, sq_abs]
  rw [hsq]
  have h0 : (0 : ℝ) ≤ |∫ y in α..x, g' y| := abs_nonneg _
  nlinarith

/-- **The interval Poincaré estimate.** -/
theorem integral_sub_left_sq_le_of_hasDerivAt {g g' : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hderiv : ∀ y : ℝ, HasDerivAt g (g' y) y)
    (hg' : IntervalIntegrable g' volume α β)
    (hg'2 : IntervalIntegrable (fun y => g' y ^ (2 : ℕ)) volume α β)
    (hgint : IntegrableOn (fun x => (g x - g α) ^ (2 : ℕ)) (Set.Ioc α β) volume) :
    (∫ x in Set.Ioc α β, (g x - g α) ^ (2 : ℕ))
      ≤ (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ) := by
  have hconst : IntegrableOn (fun _ : ℝ => (β - α) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ))
      (Set.Ioc α β) volume := integrableOn_const (measure_Ioc_lt_top).ne
  have hmono := MeasureTheory.setIntegral_mono_on hgint hconst measurableSet_Ioc
    (fun x hx => sq_sub_left_le_of_hasDerivAt hαβ hderiv hg' hg'2
      (Set.Ioc_subset_Icc_self hx))
  have hval : (∫ _x in Set.Ioc α β, (β - α) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ))
      = (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ) := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hαβ, smul_eq_mul]
    ring
  rw [hval] at hmono
  exact hmono

/-- The pointwise interval Poincaré estimate needs derivatives only on the closed interval. -/
theorem sq_sub_left_le_of_hasDerivAt_on_Icc {g g' : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hderiv : ∀ y ∈ Set.Icc α β, HasDerivAt g (g' y) y)
    (hg' : IntervalIntegrable g' volume α β)
    (hg'2 : IntervalIntegrable (fun y => g' y ^ (2 : ℕ)) volume α β)
    {x : ℝ} (hx : x ∈ Set.Icc α β) :
    (g x - g α) ^ (2 : ℕ) ≤ (β - α) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ) := by
  obtain ⟨hxα, hxβ⟩ := hx
  have hsubU : Set.uIcc α x ⊆ Set.uIcc α β := by
    rw [Set.uIcc_of_le hxα, Set.uIcc_of_le hαβ]
    exact Set.Icc_subset_Icc le_rfl hxβ
  have hsub : Set.uIcc α x ⊆ Set.Icc α β := by
    rw [Set.uIcc_of_le hxα]
    exact Set.Icc_subset_Icc le_rfl hxβ
  have hftc : (∫ y in α..x, g' y) = g x - g α :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hderiv y (hsub hy))
      (hg'.mono_set hsubU)
  have habsInt : IntegrableOn (fun y => |g' y|) (Set.Ioc α β) volume := hg'.abs.1
  have habs : |∫ y in α..x, g' y| ≤ ∫ y in Set.Ioc α β, |g' y| := by
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hxα) ?_
    rw [intervalIntegral.integral_of_le hxα]
    refine MeasureTheory.setIntegral_mono_set habsInt ?_ ?_
    · filter_upwards with y
      exact abs_nonneg _
    · exact Filter.Eventually.of_forall (Set.Ioc_subset_Ioc_right hxβ)
  have habsSq : IntegrableOn (fun y => |g' y| ^ (2 : ℕ)) (Set.Ioc α β) volume := by
    refine hg'2.1.congr ?_
    filter_upwards with y
    rw [sq_abs]
  have hcs : (∫ y in Set.Ioc α β, |g' y|) ^ (2 : ℕ)
      ≤ (β - α) * ∫ y in Set.Ioc α β, |g' y| ^ (2 : ℕ) :=
    sq_integral_le_length_mul hαβ habsInt habsSq
  have hsame : (∫ y in Set.Ioc α β, |g' y| ^ (2 : ℕ)) = ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with y
    rw [sq_abs]
  rw [hsame] at hcs
  have hnn : (0 : ℝ) ≤ ∫ y in Set.Ioc α β, |g' y| :=
    MeasureTheory.integral_nonneg fun y => abs_nonneg _
  have hsq : (g x - g α) ^ (2 : ℕ) = |∫ y in α..x, g' y| ^ (2 : ℕ) := by
    rw [hftc, sq_abs]
  rw [hsq]
  have h0 : (0 : ℝ) ≤ |∫ y in α..x, g' y| := abs_nonneg _
  nlinarith

/-- The integral interval Poincaré estimate needs derivatives only on the closed interval. -/
theorem integral_sub_left_sq_le_of_hasDerivAt_on_Icc {g g' : ℝ → ℝ} {α β : ℝ}
    (hαβ : α ≤ β) (hderiv : ∀ y ∈ Set.Icc α β, HasDerivAt g (g' y) y)
    (hg' : IntervalIntegrable g' volume α β)
    (hg'2 : IntervalIntegrable (fun y => g' y ^ (2 : ℕ)) volume α β)
    (hgint : IntegrableOn (fun x => (g x - g α) ^ (2 : ℕ)) (Set.Ioc α β) volume) :
    (∫ x in Set.Ioc α β, (g x - g α) ^ (2 : ℕ))
      ≤ (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ) := by
  have hconst : IntegrableOn (fun _ : ℝ => (β - α) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ))
      (Set.Ioc α β) volume := integrableOn_const (measure_Ioc_lt_top).ne
  have hmono := MeasureTheory.setIntegral_mono_on hgint hconst measurableSet_Ioc
    (fun x hx => sq_sub_left_le_of_hasDerivAt_on_Icc hαβ hderiv hg' hg'2
      (Set.Ioc_subset_Icc_self hx))
  have hval : (∫ _x in Set.Ioc α β, (β - α) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ))
      = (β - α) ^ (2 : ℕ) * ∫ y in Set.Ioc α β, g' y ^ (2 : ℕ) := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hαβ, smul_eq_mul]
    ring
  rw [hval] at hmono
  exact hmono

end GaloisForLFunctions.HTGeometry
