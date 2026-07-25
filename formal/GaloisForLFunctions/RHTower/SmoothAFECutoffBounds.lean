import GaloisForLFunctions.RHTower.SmoothAFEZetaDualContourLimit

/-!
# Power localization of the Gaussian cutoff

Contour invariance on positive lines and the unit-residue crossing at zero
give arbitrary power decay at infinity and arbitrary positive-power approach
to one at zero.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory

theorem norm_smoothAFECutoffAt_le
    {x σ : ℝ} (hx : 0 < x) (hσ : σ ≠ 0) :
    ‖smoothAFECutoffAt σ x‖ ≤
      ((1 / (2 * Real.pi)) * (Real.exp (σ ^ 2) / |σ|) *
        (∫ t : ℝ, Real.exp (-(t ^ 2)))) * x ^ (-σ) := by
  let f : ℝ → ℂ := fun t =>
    smoothAFEMellinIntegrand x ((σ : ℂ) + (t : ℂ) * I)
  let D : ℝ := x ^ (-σ) * (Real.exp (σ ^ 2) / |σ|)
  have hf : Integrable f :=
    smoothAFEMellinIntegrand_verticalIntegrable_of_ne hx hσ
  have hmajor : Integrable (fun t : ℝ =>
      D * Real.exp (-(t ^ 2))) := by
    simpa [one_mul] using
      (integrable_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 1)).const_mul D
  have hpoint : ∀ t : ℝ, ‖f t‖ ≤
      D * Real.exp (-(t ^ 2)) := by
    intro t
    simpa [f, D] using
      norm_smoothAFEMellinIntegrand_vertical_le_of_ne hx hσ t
  unfold smoothAFECutoffAt mellinInv
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) * ‖∫ t : ℝ, f t‖
      ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖f t‖ := by
        exact mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm f) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
          ∫ t : ℝ, D * Real.exp (-(t ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply integral_mono_ae hf.norm hmajor
        exact Filter.Eventually.of_forall hpoint
    _ = ((1 / (2 * Real.pi)) * (Real.exp (σ ^ 2) / |σ|) *
          (∫ t : ℝ, Real.exp (-(t ^ 2)))) * x ^ (-σ) := by
      rw [integral_const_mul]
      dsimp only [D]
      ring

theorem exists_norm_smoothAFECutoff_le_neg_rpow
    {A : ℝ} (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {x : ℝ}, 0 < x →
      ‖smoothAFECutoff x‖ ≤ K * x ^ (-A) := by
  let K : ℝ :=
    (1 / (2 * Real.pi)) * (Real.exp (A ^ 2) / A) *
      (∫ t : ℝ, Real.exp (-(t ^ 2)))
  have hG : 0 ≤ ∫ t : ℝ, Real.exp (-(t ^ 2)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, fun {x} hx => ?_⟩
  rw [← smoothAFECutoffAt_eq_smoothAFECutoff hx hA]
  have h := norm_smoothAFECutoffAt_le hx hA.ne'
  simpa [K, abs_of_pos hA] using h

theorem exists_norm_smoothAFECutoff_sub_one_le_rpow
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {x : ℝ}, 0 < x →
      ‖smoothAFECutoff x - 1‖ ≤ K * x ^ δ := by
  let K : ℝ :=
    (1 / (2 * Real.pi)) * (Real.exp (δ ^ 2) / δ) *
      (∫ t : ℝ, Real.exp (-(t ^ 2)))
  have hG : 0 ≤ ∫ t : ℝ, Real.exp (-(t ^ 2)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, fun {x} hx => ?_⟩
  rw [← smoothAFECutoffAt_eq_smoothAFECutoff_sub_one
    hx (neg_lt_zero.mpr hδ)]
  have h := norm_smoothAFECutoffAt_le hx (neg_ne_zero.mpr hδ.ne')
  simpa [K, neg_sq, abs_neg, abs_of_pos hδ] using h

end RHTower
