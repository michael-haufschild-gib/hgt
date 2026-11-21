import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.Contact

/-! # Uniform error from the contact order and total generator norm -/
open NormedSpace Metric Set
namespace GaloisForLFunctions.HTGeometry.ProductFormula
noncomputable section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

private theorem norm_flow_le (x : A) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  rw [Real.exp_eq_exp_ℝ]
  apply (exp_series_hasSum_exp' (𝕂 := ℂ) x).norm_le_of_bounded (expSeries_div_hasSum_exp ‖x‖)
  intro n
  rw [norm_smul,norm_inv,Complex.norm_natCast,div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)

theorem norm_word_le (w : List A) (z : ℂ) : ‖word w z‖ ≤ Real.exp (‖z‖*mass w) := by
  induction w with
  | nil => simp [word,mass]
  | cons x w ih =>
    change ‖exp (z • x)*word w z‖ ≤ _
    calc
      _ ≤ ‖exp (z • x)‖ * ‖word w z‖ := norm_mul_le _ _
      _ ≤ Real.exp ‖z • x‖ * Real.exp (‖z‖*mass w) :=
        mul_le_mul (norm_flow_le _) ih (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add,norm_smul]; congr 1; change _ = ‖z‖*(‖x‖+mass w); ring

/-- On a complex-time disk of radius 1/K, the quotient by time to the
contact order is bounded everywhere by its boundary maximum. -/
theorem contact_error {p : ℕ} {w : List A} {x : A} (h : Contact p w x)
    {K : ℝ} (hK : 0 < K) (hw : mass w ≤ K) (hx : ‖x‖ ≤ K)
    {z : ℂ} (hz : ‖z‖*K ≤ 1) :
    ‖word w z - exp (z • x)‖ ≤ 6*(‖z‖*K)^p := by
  obtain ⟨E,hE,he⟩ := h
  let R := 1/K
  have hR : 0 < R := by dsimp [R]; positivity
  have hball (u : ℂ) (hu : ‖u‖=R) : ‖word w u-exp (u • x)‖ ≤ 6 := by
    have hRK : R*K=1 := by dsimp [R]; field_simp
    have h₁ := mul_le_mul_of_nonneg_left hw hR.le
    have h₂ := mul_le_mul_of_nonneg_left hx hR.le
    rw [hRK] at h₁ h₂
    have h₃ := norm_word_le w u
    have h₄ := norm_flow_le (u • x)
    rw [hu] at h₃
    rw [norm_smul,hu] at h₄
    have h₅ := h₃.trans ((Real.exp_le_exp.mpr h₁).trans Real.exp_one_lt_three.le)
    have h₆ := h₄.trans ((Real.exp_le_exp.mpr h₂).trans Real.exp_one_lt_three.le)
    exact (norm_sub_le _ _).trans (by linarith only [h₅,h₆])
  have hbd (u : ℂ) (hu : u ∈ frontier (ball (0:ℂ) R)) : ‖E u‖ ≤ 6/R^p := by
    rw [frontier_ball _ hR.ne',mem_sphere_zero_iff_norm] at hu
    have hb := hball u hu
    rwa [he,norm_smul,norm_pow,hu,mul_comm,← le_div_iff₀ (pow_pos hR _)] at hb
  have hzm : z ∈ closure (ball (0:ℂ) R) := by
    rw [closure_ball _ hR.ne',mem_closedBall_zero_iff]
    exact (le_div_iff₀ hK).mpr hz
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hE.diffContOnCl hbd hzm
  rw [he,norm_smul,norm_pow]
  calc
    _ ≤ ‖z‖^p*(6/R^p) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by dsimp [R]; rw [div_pow,mul_pow,one_pow]; field_simp

#print axioms contact_error
end
end GaloisForLFunctions.HTGeometry.ProductFormula
