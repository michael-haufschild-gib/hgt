import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoissonBoundary
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorLogMoments
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorFiniteBoundary

/-! # The actual logarithmic boundary coefficient at every polynomial order -/

noncomputable section

open MeasureTheory Set Complex Filter Topology Polynomial

namespace RHTower.WeilHigherDenominator

private lemma polynomial_boundary_weight_lipschitz (ρ : ℂ) (P : ℂ[X])
    (hP : P.eval 0 = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Icc (1 / 2 : ℝ) (3 / 2),
      ‖P.eval (Real.log t : ℂ) * (t : ℂ) ^ (-ρ)‖ ≤ L * |t - 1| := by
  let W : ℝ → ℂ := fun t => P.eval (Real.log t : ℂ) * exp (-ρ * (Real.log t : ℂ))
  have hreg : ContDiffOn ℝ 1 W (Ioi 0) := by
    have he : W = finitePoleBoundary ({()} : Finset Unit) (fun _ => ρ) (fun _ => P) := by
      funext t
      simp only [W, finitePoleBoundary, Finset.sum_singleton]
    rw [he]
    exact finitePoleBoundary_contDiffOn ({()} : Finset Unit) (fun _ => ρ) (fun _ => P)
  have hsub : Icc (1 / 2 : ℝ) (3 / 2) ⊆ Ioi 0 := by
    intro t ht
    change 0 < t
    linarith [ht.1]
  have hc := hreg.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono hsub)
  have hdiff : ∀ t ∈ Icc (1 / 2 : ℝ) (3 / 2), DifferentiableAt ℝ W t := by
    intro t ht
    exact ((hreg t (hsub ht)).contDiffAt
      (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt (by decide)
  refine ⟨max D 0, le_max_right _ _, fun t ht => ?_⟩
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le hdiff
    (fun t ht => (hD t ht).trans (le_max_left D 0)) (convex_Icc _ _)
    (show (1 : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2) by constructor <;> norm_num) ht
  have hW1 : W 1 = 0 := by simp [W, hP]
  have ht0 : 0 < t := hsub ht
  have hp : (t : ℂ) ^ (-ρ) = exp (-ρ * (Real.log t : ℂ)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht0.ne'), ← ofReal_log ht0.le, mul_comm]
  simpa only [hW1, sub_zero, Real.norm_eq_abs, W, hp] using hb

/-- A logarithmic polynomial vanishing at zero has no logarithmic boundary singularity. -/
theorem polynomial_polarKernel_boundary_zero_bounded {ρ : ℂ}
    (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) (P : ℂ[X]) (hP : P.eval 0 = 0) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y →
      ‖∫ t : ℝ, P.eval (Real.log |t| : ℂ) * polarKernel ρ (1 + (y : ℂ) * I) t‖ ≤ C := by
  obtain ⟨L, hL0, hL⟩ := polynomial_boundary_weight_lipschitz ρ P hP
  let M : ℝ → ℝ := fun t => (Icc (1 / 2 : ℝ) (3 / 2)).indicator (fun _ => L) t +
    (1 + 2 * ‖I - 1‖) * ‖P.eval (Real.log |t| : ℂ) * polarKernel ρ I t‖
  have hM : Integrable M :=
    (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc).add
      ((integrable_polynomial_polarKernel hρ₀ hρ₁ (by simp) P).norm.const_mul _)
  refine ⟨∫ t : ℝ, M t, fun y hy => ?_⟩
  have hz : 0 < (1 + (y : ℂ) * I).im := by simpa using hy
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (integrable_polynomial_polarKernel hρ₀ hρ₁ hz P).norm hM
  apply Eventually.of_forall
  intro t
  dsimp only [M]
  by_cases ht : t ∈ Icc (1 / 2 : ℝ) (3 / 2)
  · rw [indicator_of_mem ht]
    have ht0 : 0 < t := by linarith [ht.1]
    have hd : 0 < ‖1 + (y : ℂ) * I - (t : ℂ)‖ := by
      apply lt_of_lt_of_le hy
      simpa [abs_of_pos hy] using abs_im_le_norm (1 + (y : ℂ) * I - (t : ℂ))
    have hdist : |t - 1| ≤ ‖1 + (y : ℂ) * I - (t : ℂ)‖ := by
      simpa [abs_sub_comm] using abs_re_le_norm (1 + (y : ℂ) * I - (t : ℂ))
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    rw [polarKernel, abs_of_pos ht0, ← mul_div_assoc, norm_div, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (div_le_iff₀ hd).mpr ((hL t ht).trans (mul_le_mul_of_nonneg_left hdist hL0))
  · rw [indicator_of_notMem ht, zero_add, norm_mul, norm_mul]
    calc
      _ ≤ ‖P.eval (Real.log |t| : ℂ)‖ *
          ((1 + 2 * ‖I - 1‖) * ‖polarKernel ρ I t‖) :=
        mul_le_mul_of_nonneg_left (norm_polarKernel_boundary_tail ρ hy ht) (norm_nonneg _)
      _ = _ := by ring

/-- The complete polynomial-weight singularity has the exact coefficient `-2 P(0)`. -/
theorem polynomial_polarKernel_boundary_remainder_bounded {ρ : ℂ}
    (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) (P : ℂ[X]) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖(∫ t : ℝ, P.eval (Real.log |t| : ℂ) * polarKernel ρ (1 + (y : ℂ) * I) t) +
        P.eval 0 * (2 * Real.log y : ℝ)‖ ≤ C := by
  let Q : ℂ[X] := P - Polynomial.C (P.eval 0)
  have hQ : Q.eval 0 = 0 := by simp [Q]
  obtain ⟨C, hC⟩ := polynomial_polarKernel_boundary_zero_bounded hρ₀ hρ₁ Q hQ
  obtain ⟨D, hD⟩ := polarKernel_boundary_remainder_bounded hρ₀ hρ₁
  refine ⟨C + ‖P.eval 0‖ * D, fun y hy hy1 => ?_⟩
  have hz : 0 < (1 + (y : ℂ) * I).im := by simpa using hy
  have he : (∫ t : ℝ, P.eval (Real.log |t| : ℂ) * polarKernel ρ (1 + (y : ℂ) * I) t) +
      P.eval 0 * (2 * Real.log y : ℝ) =
      (∫ t : ℝ, Q.eval (Real.log |t| : ℂ) * polarKernel ρ (1 + (y : ℂ) * I) t) +
        P.eval 0 * ((∫ t : ℝ, polarKernel ρ (1 + (y : ℂ) * I) t) + (2 * Real.log y : ℝ)) := by
    simp only [Q, eval_sub, eval_C, sub_mul]
    rw [integral_sub (integrable_polynomial_polarKernel hρ₀ hρ₁ hz P)
      ((integrable_polarKernel hρ₀ hρ₁ hz).const_mul _), integral_const_mul]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  exact add_le_add (hC y hy) (mul_le_mul_of_nonneg_left (hD y hy hy1) (norm_nonneg _))

/-- Boundary limit of the actual integral, with no restriction on logarithmic order. -/
theorem polynomial_polarKernel_boundary_one {ρ : ℂ}
    (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) (P : ℂ[X]) :
    Tendsto (fun y : ℝ =>
      (∫ t : ℝ, P.eval (Real.log |t| : ℂ) * polarKernel ρ (1 + (y : ℂ) * I) t) /
        (Real.log y : ℂ)) (𝓝[>] 0) (𝓝 (-2 * P.eval 0)) := by
  obtain ⟨C, hC⟩ := polynomial_polarKernel_boundary_remainder_bounded hρ₀ hρ₁ P
  let F : ℝ → ℂ := fun y => ∫ t : ℝ,
    P.eval (Real.log |t| : ℂ) * polarKernel ρ (1 + (y : ℂ) * I) t
  have hypos : ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < y := self_mem_nhdsWithin
  have hyone : ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
  have hinv : Tendsto (fun y : ℝ => |(Real.log y)⁻¹|) (𝓝[>] 0) (𝓝 0) := by
    simpa only [abs_zero, Function.comp_def] using
      (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero).abs
  have hzero : Tendsto (fun y : ℝ => (F y + P.eval 0 * (2 * Real.log y : ℝ)) /
      (Real.log y : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun y => |C| * |(Real.log y)⁻¹|)
    · filter_upwards [hypos, hyone] with y hy hy1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, abs_inv]
      exact mul_le_mul_of_nonneg_right ((hC y hy hy1.le).trans (le_abs_self C))
        (inv_nonneg.mpr (abs_nonneg _))
    · simpa only [mul_zero] using tendsto_const_nhds.mul hinv
  have he : (fun y : ℝ => (F y + P.eval 0 * (2 * Real.log y : ℝ)) /
      (Real.log y : ℂ) - 2 * P.eval 0) =ᶠ[𝓝[>] 0]
        (fun y : ℝ => F y / (Real.log y : ℂ)) := by
    filter_upwards [hypos, hyone] with y hy hy1
    have hlog : (Real.log y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.log_neg hy hy1).ne
    push_cast
    field_simp
    ring
  simpa only [zero_sub, neg_mul] using (hzero.sub_const (2 * P.eval 0)).congr' he

/-- The boundary coefficient of the actual polynomial Poisson mode. -/
theorem polynomialPolarMode_boundary_one {ρ : ℂ}
    (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) (P : ℂ[X]) :
    Tendsto (fun y : ℝ => polynomialPolarMode ρ P (1 + (y : ℂ) * I) /
      ((Real.sqrt y : ℂ) * (Real.log y : ℂ))) (𝓝[>] 0) (𝓝 (-2 * P.eval 0)) := by
  apply (polynomial_polarKernel_boundary_one hρ₀ hρ₁ P).congr'
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  have hs : (Real.sqrt y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [polynomialPolarMode, add_im, one_im, mul_im, ofReal_re, I_im, mul_one,
    ofReal_im, I_re, mul_zero, add_zero, zero_add]
  field_simp

end RHTower.WeilHigherDenominator
