import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCuspJointSmooth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Uniform height decay of the complete signed Fourier–Bessel family. Every complex-power-weighted tail is bounded on each positive-height half-strip, uniformly in horizontal position.
-/

open Complex Real Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMAngularSeries
noncomputable section

private theorem besselBound_antitone (nu : ℂ) {l y : ℝ} (hl : 0 < l) (hy : l ≤ y) :
    besselBound nu y ≤ besselBound nu l := by
  unfold besselBound
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  · apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left (by positivity) hl hy
  · positivity
  · positivity

/-- The complete Bessel carrier retains exponential decay in the actual height. -/
theorem bessel_height_decay (nu : ℂ) (l : ℝ) (hl : 0 < l) (N : ℕ) (y : ℝ) (hy : l ≤ y) :
    ‖modifiedBesselKOrder (2*Real.pi*((N:ℝ)+1)*y) nu‖ ≤
      besselBound nu l * Real.exp (-(((N:ℝ)+1)*l/2)) * Real.exp (-y/2) := by
  have hy0 := hl.trans_le hy
  have hN : (1 : ℝ) ≤ (N:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hsplit : -(((N:ℝ)+1)*y) ≤ -(((N:ℝ)+1)*l/2) + (-y/2) := by
    nlinarith [mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ (N:ℝ)+1),
      mul_le_mul_of_nonneg_right hN hy0.le]
  calc
    _ ≤ besselBound nu y * Real.exp (-(((N:ℝ)+1)*y)) :=
      bessel_local_bound nu y hy0 N y le_rfl
    _ ≤ besselBound nu l * Real.exp (-(((N:ℝ)+1)*y)) := by
      gcongr
      exact besselBound_antitone nu hl hy
    _ ≤ besselBound nu l * Real.exp (-(((N:ℝ)+1)*l/2)+(-y/2)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsplit) (by unfold besselBound; positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- Finite coefficient mass controlling every horizontal position in the infinite tail. -/
def heightDecayConstant (u nu : ℂ) (d : ℕ) (l : ℝ) : ℝ :=
  besselBound nu l * ∑' N : ℕ, ‖coefficient u d N‖ * Real.exp (-(((N:ℝ)+1)*l/2))

/-- Uniform exponential bound for the full infinite Fourier--Bessel family. -/
theorem value_height_decay (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (l : ℝ) (hl : 0 < l) (z : Fin 2 → ℝ) (hz : l ≤ z 1) :
    ‖value u nu a d negative z‖ ≤ heightDecayConstant u nu d l *
      (z 1)^a * Real.exp (-(z 1)/2) := by
  have hy := hl.trans_le hz
  let M := fun N : ℕ => ‖coefficient u d N‖ * Real.exp (-(((N:ℝ)+1)*l/2))
  have hM : Summable M := by
    simpa only [M, mul_div_assoc] using coefficient_weighted_summable u d (l/2) (by positivity)
  have hD : 0 ≤ besselBound nu l := by unfold besselBound; positivity
  have hterm (N : ℕ) : ‖term u nu a d negative N z‖ ≤
      (besselBound nu l * (z 1)^a * Real.exp (-(z 1)/2)) * M N := by
    rw [term, norm_mul, norm_mul, norm_mul, d4BM_norm_completedEisensteinFourierPhase,
      mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.rpow_eq_pow, abs_of_nonneg (Real.rpow_nonneg hy.le a)]
    calc
      _ ≤ ‖coefficient u d N‖ * (z 1)^a *
          (besselBound nu l * Real.exp (-(((N:ℝ)+1)*l/2)) * Real.exp (-(z 1)/2)) := by
        gcongr
        exact bessel_height_decay nu l hl N (z 1) hz
      _ = _ := by dsimp [M]; ring
  have hsum := Summable.tsum_le_tsum hterm
    (term_summable u nu a d negative z hy).norm (hM.mul_left _)
  calc
    _ ≤ ∑' N, ‖term u nu a d negative N z‖ := norm_tsum_le_tsum_norm
      (term_summable u nu a d negative z hy).norm
    _ ≤ _ := hsum
    _ = _ := by rw [tsum_mul_left]; dsimp [heightDecayConstant, M]; ring

private theorem rpow_exp_bounded (a l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, l ≤ y → y^a * Real.exp (-y/2) ≤ C := by
  have ht : Tendsto (fun y : ℝ => y^a * Real.exp (-y/2)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a (1/2) (by norm_num) using 1
    ext y
    congr 2
    ring
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 1 (by norm_num))
  have hc : ContinuousOn (fun y : ℝ => y^a * Real.exp (-y/2)) (Icc l M) := by
    intro y hy
    exact ((Real.contDiffAt_rpow_const_of_ne (ne_of_gt (hl.trans_le hy.1)) (n := 0)).continuousAt.mul
      (by fun_prop)).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, (by exact le_trans (by norm_num) (le_max_right C 1)), ?_⟩
  intro y hy
  by_cases h : M ≤ y
  · exact (hM y h).le.trans (le_max_right C 1)
  · exact (le_abs_self _).trans ((hC y ⟨hy,le_of_not_ge h⟩).trans (le_max_left C 1))

/-- Any complex height power times the complete tail is bounded uniformly in horizontal position. -/
theorem weighted_value_bounded (u nu w : ℂ) (a : ℝ) (d : ℕ) (negative : Bool)
    (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, l ≤ z 1 →
      ‖(z 1 : ℂ)^w * value u nu a d negative z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := rpow_exp_bounded (w.re+a) l hl
  have hD : 0 ≤ heightDecayConstant u nu d l := by
    unfold heightDecayConstant besselBound
    exact mul_nonneg (by positivity) (tsum_nonneg fun N => by positivity)
  refine ⟨heightDecayConstant u nu d l*C, mul_nonneg hD hC, ?_⟩
  intro z hz
  have hy := hl.trans_le hz
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  calc
    _ ≤ (z 1)^w.re * (heightDecayConstant u nu d l * (z 1)^a * Real.exp (-(z 1)/2)) := by
      gcongr
      exact value_height_decay u nu a d negative l hl z hz
    _ = heightDecayConstant u nu d l * ((z 1)^(w.re+a) * Real.exp (-(z 1)/2)) := by
      rw [Real.rpow_add hy]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (z 1) hz) hD

end
end RHTower.D4BMAngularSeries
