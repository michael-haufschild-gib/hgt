import GaloisForLFunctions.SelbergClass.SubcriticalEulerRigidity
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.HTGeometry.StencilJetExpansion
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Logarithmic derivatives of Selberg Gamma factors

Every positive-order derivative of the logarithmic Gamma slope decays on
upper vertical lines in the right half-plane. Positive scales and shifts
with nonnegative real part keep all polygamma arguments in that half-plane.
-/

noncomputable section
open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

open RHTower

theorem gammaArgument_re_pos (D : SelbergGammaData) {s : ℂ} (hs : 0 < s.re)
    (j : Fin D.rank) : 0 < ((D.lambda j : ℂ) * s + D.mu j).re := by
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact add_pos_of_pos_of_nonneg (mul_pos (D.lambda_pos j) hs) (D.mu_re_nonneg j)

private theorem ne_gamma_pole_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ∀ n : ℕ, s ≠ -(n : ℂ) := by
  intro n heq
  rw [heq] at hs
  simp only [neg_re, natCast_re] at hs
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The logarithmic derivative of the completed Gamma factor. -/
def gammaLogSlope (D : SelbergGammaData) (s : ℂ) : ℂ :=
  (Real.log D.Q : ℂ) + ∑ j, (D.lambda j : ℂ) * digamma ((D.lambda j : ℂ) * s + D.mu j)

theorem gammaLogSlope_contDiffAt (D : SelbergGammaData) {s : ℂ}
    (hs : 0 < s.re) (m : ℕ) : ContDiffAt ℂ m (gammaLogSlope D) s := by
  apply contDiffAt_const.add
  apply ContDiffAt.sum
  intro j _
  exact contDiffAt_const.mul ((contDiffAt_digamma_n _
    (ne_gamma_pole_of_re_pos (gammaArgument_re_pos D hs j)) m).comp s (by fun_prop))

theorem logDeriv_gammaFactor (D : SelbergGammaData) {s : ℂ} (hs : 0 < s.re) :
    logDeriv D.gammaFactor s = gammaLogSlope D s := by
  have harg (j : Fin D.rank) := ne_gamma_pole_of_re_pos (gammaArgument_re_pos D hs j)
  have hd (j : Fin D.rank) :
      DifferentiableAt ℂ (fun z : ℂ => Gamma ((D.lambda j : ℂ) * z + D.mu j)) s :=
    ((analyticAt_Gamma _ (harg j)).comp
      (f := fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j) (x := s)
      (show AnalyticAt ℂ (fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j) s by fun_prop)).differentiableAt
  have heq : D.gammaFactor = fun z => exp ((Real.log D.Q : ℂ) * z) *
      ∏ j, Gamma ((D.lambda j : ℂ) * z + D.mu j) :=
    funext (gammaFactor_eq_exp_mul_archGammaFactor D)
  rw [heq, logDeriv_mul (f := fun z : ℂ => exp ((Real.log D.Q : ℂ) * z))
    (g := fun z : ℂ => ∏ j, Gamma ((D.lambda j : ℂ) * z + D.mu j))
    s (exp_ne_zero _) (Finset.prod_ne_zero_iff.mpr
    fun j _ => Gamma_ne_zero (harg j)) (by fun_prop) (.fun_finsetProd fun j _ => hd j)]
  have hExp : logDeriv (fun z : ℂ => exp ((Real.log D.Q : ℂ) * z)) s =
      (Real.log D.Q : ℂ) := by
    have hExp' : HasDerivAt (fun z : ℂ => exp ((Real.log D.Q : ℂ) * z))
        (exp ((Real.log D.Q : ℂ) * s) * (Real.log D.Q : ℂ)) s := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id s).const_mul (Real.log D.Q : ℂ)).cexp)
    rw [logDeriv_apply, hExp'.deriv]
    exact mul_div_cancel_left₀ _ (exp_ne_zero _)
  rw [hExp, logDeriv_prod (f := fun j z => Gamma ((D.lambda j : ℂ) * z + D.mu j))
    (s := Finset.univ) (x := s) (fun j _ => Gamma_ne_zero (harg j)) (fun j _ => hd j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hc := logDeriv_comp (g := fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j) (x := s)
    (analyticAt_Gamma _ (harg j)).differentiableAt
    (show DifferentiableAt ℂ (fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j) s by fun_prop)
  change logDeriv (fun z : ℂ => Gamma ((D.lambda j : ℂ) * z + D.mu j)) s = _ at hc
  have hlin : HasDerivAt (fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j) (D.lambda j) s := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id s).const_mul (D.lambda j : ℂ)).add_const (D.mu j))
  rw [hc, ← digamma_def, hlin.deriv]
  ring

private theorem digamma_analytic_right : AnalyticOnNhd ℂ digamma {s : ℂ | 0 < s.re} := by
  intro s hs
  rw [digamma_def]
  change AnalyticAt ℂ (fun z => deriv Gamma z / Gamma z) s
  simpa only [iteratedDeriv_zero] using
    analyticAt_iteratedDeriv_logDeriv 0 s (ne_gamma_pole_of_re_pos hs)

theorem iteratedDeriv_gammaLogSlope (D : SelbergGammaData) (m : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    iteratedDeriv (m + 1) (gammaLogSlope D) s =
      ∑ j, (D.lambda j : ℂ) ^ (m + 2) *
        iteratedDeriv (m + 1) digamma ((D.lambda j : ℂ) * s + D.mu j) := by
  unfold gammaLogSlope
  rw [iteratedDeriv_const_add (by omega)]
  have hsum : (fun z : ℂ => ∑ j, (D.lambda j : ℂ) * digamma ((D.lambda j : ℂ) * z + D.mu j)) =
      ∑ j, fun z : ℂ => (D.lambda j : ℂ) * digamma ((D.lambda j : ℂ) * z + D.mu j) := by
    ext z
    simp only [Finset.sum_apply]
  have hterm (j : Fin D.rank) : ContDiffAt ℂ (m + 1 : ℕ)
      (fun z : ℂ => (D.lambda j : ℂ) * digamma ((D.lambda j : ℂ) * z + D.mu j)) s :=
    contDiffAt_const.mul
      ((contDiffAt_digamma_n _ (ne_gamma_pole_of_re_pos (gammaArgument_re_pos D hs j))
        (m + 1)).comp s
          (show ContDiffAt ℂ (m + 1 : ℕ) (fun z : ℂ => (D.lambda j : ℂ) * z + D.mu j) s by fun_prop))
  rw [hsum, iteratedDeriv_sum (fun j _ => hterm j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDeriv_const_mul_field]
  have hcomp := HTGeometry.iteratedDeriv_comp_affine_on
    (isOpen_lt continuous_const continuous_re) digamma_analytic_right
    (D.mu j) (D.lambda j) (m + 1) (h := s)
    (show 0 < (D.mu j + (D.lambda j : ℂ) * s).re by
      simpa only [add_comm] using gammaArgument_re_pos D hs j)
  simp only [add_comm (D.mu j)] at hcomp
  dsimp only
  rw [hcomp, pow_succ]
  ring

/-- Positive-order derivatives of every Selberg Gamma slope vanish vertically. -/
theorem iteratedDeriv_gammaLogSlope_vertical_tendsto_zero (D : SelbergGammaData)
    (m : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => iteratedDeriv (m + 1) (gammaLogSlope D)
      ((σ : ℂ) + (t : ℂ) * I)) atTop (𝓝 0) := by
  have heq : (fun t : ℝ => iteratedDeriv (m + 1) (gammaLogSlope D)
      ((σ : ℂ) + (t : ℂ) * I)) = fun t : ℝ =>
      ∑ j, (D.lambda j : ℂ) ^ (m + 2) * iteratedDeriv (m + 1) digamma
        ((D.lambda j : ℂ) * ((σ : ℂ) + (t : ℂ) * I) + D.mu j) := by
    funext t
    exact iteratedDeriv_gammaLogSlope D m (by simpa using hσ)
  rw [heq]
  have hterm (j : Fin D.rank) : Tendsto (fun t : ℝ =>
      (D.lambda j : ℂ) ^ (m + 2) * iteratedDeriv (m + 1) digamma
        ((D.lambda j : ℂ) * ((σ : ℂ) + (t : ℂ) * I) + D.mu j)) atTop (𝓝 0) := by
    have hpos : 0 < D.lambda j * σ + (D.mu j).re :=
      add_pos_of_pos_of_nonneg (mul_pos (D.lambda_pos j) hσ) (D.mu_re_nonneg j)
    have ht : Tendsto (fun t : ℝ => D.lambda j * t + (D.mu j).im) atTop atTop :=
      tendsto_atTop.mpr fun b => by
        filter_upwards [eventually_ge_atTop ((b - (D.mu j).im) / D.lambda j)] with t ht
        have hmul := (div_le_iff₀ (D.lambda_pos j)).mp ht
        linarith
    have hl := (iteratedDeriv_digamma_vertical_tendsto_zero m hpos).comp ht
    have harg (t : ℝ) :
        ((D.lambda j * σ + (D.mu j).re : ℝ) : ℂ) +
          ((D.lambda j * t + (D.mu j).im : ℝ) : ℂ) * I =
        (D.lambda j : ℂ) * ((σ : ℂ) + (t : ℂ) * I) + D.mu j := by
      rw [ofReal_add, ofReal_add, ofReal_mul, ofReal_mul]
      conv_rhs => rw [← re_add_im (D.mu j)]
      ring
    simpa only [Function.comp_def, harg, mul_zero] using hl.const_mul ((D.lambda j : ℂ) ^ (m + 2))
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hterm j)

end GaloisForLFunctions.SelbergClass
