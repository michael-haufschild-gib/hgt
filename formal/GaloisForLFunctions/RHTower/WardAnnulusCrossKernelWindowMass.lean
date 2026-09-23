import GaloisForLFunctions.RHTower.WardAnnulusCrossKernelMassRigidity

/-!
# Exact window mass of a finite Lorentzian cross kernel

The mass of `K_A` on a symmetric window `[-ρ, ρ]` is an exact arctangent sum.  Letting `ρ → ∞`
recovers the total mass law.  Nonnegativity of the cross kernel on the window is therefore an
exact arctangent inequality, and for a two-width annulus the sign locus factors completely: the
kernel is nonnegative exactly on `D ^ 2 ≤ (A + b₀) (A + b₁)`.
-/

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace RHTower

noncomputable section

theorem hasDerivAt_two_arctan_div {β : ℝ} (hβ : 0 < β) (D : ℝ) :
    HasDerivAt (fun D : ℝ => 2 * Real.arctan (D / β))
      (2 * β / (β ^ (2 : ℕ) + D ^ (2 : ℕ))) D := by
  have hβ' : β ≠ 0 := ne_of_gt hβ
  have h1 : HasDerivAt (fun D : ℝ => D / β) (1 / β) D := (hasDerivAt_id D).div_const β
  have h2 := ((Real.hasDerivAt_arctan (D / β)).comp D h1).const_mul (2 : ℝ)
  refine h2.congr_deriv ?_
  field_simp

/-- Exact mass of one Lorentzian on a symmetric window. -/
theorem integral_lorentzian_window {β : ℝ} (hβ : 0 < β) (ρ : ℝ) :
    (∫ D in (-ρ)..ρ, 2 * β / (β ^ (2 : ℕ) + D ^ (2 : ℕ))) = 4 * Real.arctan (ρ / β) := by
  have hderiv : ∀ D ∈ Set.uIcc (-ρ) ρ,
      HasDerivAt (fun D : ℝ => 2 * Real.arctan (D / β))
        (2 * β / (β ^ (2 : ℕ) + D ^ (2 : ℕ))) D := fun D _ => hasDerivAt_two_arctan_div hβ D
  have hint : IntervalIntegrable
      (fun D : ℝ => 2 * β / (β ^ (2 : ℕ) + D ^ (2 : ℕ))) MeasureTheory.volume (-ρ) ρ := by
    apply Continuous.intervalIntegrable
    have : Continuous fun D : ℝ => β ^ (2 : ℕ) + D ^ (2 : ℕ) := by continuity
    exact continuous_const.div this fun D => by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [neg_div, Real.arctan_neg]
  ring

/-- **Exact window-mass law.**  The cross-kernel mass on `[-ρ, ρ]` is an arctangent sum; the total
mass law is its limit as `ρ → ∞`. -/
theorem intervalIntegral_annulusCrossKernel {ι : Type*} (S : Finset ι) (c b : ι → ℝ) {A : ℝ}
    (hb : ∀ i ∈ S, 0 < A + b i) (ρ : ℝ) :
    (∫ D in (-ρ)..ρ, annulusCrossKernel S c b A D) =
      4 * ∑ i ∈ S, c i * Real.arctan (ρ / (A + b i)) := by
  have hsplit : ∀ i ∈ S, IntervalIntegrable
      (fun D : ℝ => 2 * c i * (A + b i) / ((A + b i) ^ (2 : ℕ) + D ^ (2 : ℕ)))
      MeasureTheory.volume (-ρ) ρ := by
    intro i hi
    apply Continuous.intervalIntegrable
    have hβ := hb i hi
    have : Continuous fun D : ℝ => (A + b i) ^ (2 : ℕ) + D ^ (2 : ℕ) := by continuity
    exact continuous_const.div this fun D => by positivity
  unfold annulusCrossKernel
  rw [intervalIntegral.integral_finsetSum hsplit, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hβ := hb i hi
  have hrw : (fun D : ℝ => 2 * c i * (A + b i) / ((A + b i) ^ (2 : ℕ) + D ^ (2 : ℕ))) =
      fun D : ℝ => c i * (2 * (A + b i) / ((A + b i) ^ (2 : ℕ) + D ^ (2 : ℕ))) := by
    funext D
    ring
  rw [hrw, intervalIntegral.integral_const_mul, integral_lorentzian_window hβ]
  ring

/-- Nonnegativity of the cross kernel on a symmetric window is an arctangent inequality. -/
theorem sum_arctan_nonneg_of_annulusCrossKernel_nonneg {ι : Type*} (S : Finset ι) (c b : ι → ℝ)
    {A ρ : ℝ} (hb : ∀ i ∈ S, 0 < A + b i) (hρ : 0 ≤ ρ)
    (hnn : ∀ D ∈ Set.Icc (-ρ) ρ, 0 ≤ annulusCrossKernel S c b A D) :
    0 ≤ ∑ i ∈ S, c i * Real.arctan (ρ / (A + b i)) := by
  have hle : (0 : ℝ) ≤ ∫ D in (-ρ)..ρ, annulusCrossKernel S c b A D := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro D hD
    exact hnn D (by simpa using hD)
  rw [intervalIntegral_annulusCrossKernel S c b hb ρ] at hle
  linarith

/-- **Exact two-width sign locus.**  With coefficients `1, -1` the cross kernel factors, so it is
nonnegative exactly on the disc `D ^ 2 ≤ (A + b₀) (A + b₁)`. -/
theorem annulusCrossKernel_two_eq {A b₀ b₁ D : ℝ} (h₀ : 0 < A + b₀) (h₁ : 0 < A + b₁) :
    annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![b₀, b₁] A D =
      2 * ((A + b₁) - (A + b₀)) * ((A + b₀) * (A + b₁) - D ^ (2 : ℕ)) /
        (((A + b₀) ^ (2 : ℕ) + D ^ (2 : ℕ)) * ((A + b₁) ^ (2 : ℕ) + D ^ (2 : ℕ))) := by
  simp only [annulusCrossKernel, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hd₀ : ((A + b₀) ^ (2 : ℕ) + D ^ (2 : ℕ)) ≠ 0 := by positivity
  have hd₁ : ((A + b₁) ^ (2 : ℕ) + D ^ (2 : ℕ)) ≠ 0 := by positivity
  field_simp
  ring

theorem annulusCrossKernel_two_nonneg_iff {A b₀ b₁ D : ℝ} (h₀ : 0 < A + b₀) (h₁ : 0 < A + b₁)
    (hlt : A + b₀ < A + b₁) :
    0 ≤ annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![b₀, b₁] A D ↔
      D ^ (2 : ℕ) ≤ (A + b₀) * (A + b₁) := by
  rw [annulusCrossKernel_two_eq h₀ h₁]
  have hd : (0 : ℝ) < ((A + b₀) ^ (2 : ℕ) + D ^ (2 : ℕ)) * ((A + b₁) ^ (2 : ℕ) + D ^ (2 : ℕ)) := by
    positivity
  rw [le_div_iff₀ hd]
  constructor
  · intro h
    nlinarith [h]
  · intro h
    nlinarith [h]

/-- **Local diagonal domination.**  Inside the positivity radius the cross channel costs nothing:
if every pairwise ordinate separation of a finite nonnegative family lies in `[-ρ, ρ]` and the
cross kernel is nonnegative there, the full quadratic form dominates its diagonal. -/
theorem sum_annulusCrossKernel_ge_diagonal {ι J : Type*} (S : Finset ι) (c b : ι → ℝ) {A ρ : ℝ}
    (F : Finset J) (m γ : J → ℝ) (hm : ∀ j ∈ F, 0 ≤ m j)
    (hnn : ∀ D ∈ Set.Icc (-ρ) ρ, 0 ≤ annulusCrossKernel S c b A D)
    (hclose : ∀ j ∈ F, ∀ k ∈ F, |γ j - γ k| ≤ ρ) :
    (∑ j ∈ F, m j ^ (2 : ℕ) * annulusCrossKernel S c b A 0) ≤
      ∑ j ∈ F, ∑ k ∈ F, m j * m k * annulusCrossKernel S c b A (γ j - γ k) := by
  refine Finset.sum_le_sum fun j hj => ?_
  have hterm : ∀ k ∈ F, 0 ≤ m j * m k * annulusCrossKernel S c b A (γ j - γ k) := by
    intro k hk
    have habs := hclose j hj k hk
    have hmem : γ j - γ k ∈ Set.Icc (-ρ) ρ := abs_le.mp habs |> fun h => ⟨h.1, h.2⟩
    exact mul_nonneg (mul_nonneg (hm j hj) (hm k hk)) (hnn _ hmem)
  have hdiag : m j ^ (2 : ℕ) * annulusCrossKernel S c b A 0 =
      m j * m j * annulusCrossKernel S c b A (γ j - γ j) := by
    rw [sub_self]
    ring
  rw [hdiag]
  exact Finset.single_le_sum hterm hj

end

end RHTower
