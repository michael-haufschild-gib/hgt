import GaloisForLFunctions.RHTower.RiemannKernelStripLPMaximality

/-!
# The first-order multiplier on the strip

For `a > 0` put `m(z) = 1/(1 − iz/a)`, the Fourier multiplier of the inverse of `1 − D/a`. Its pole
`−ia` lies below the real axis, so on the closed strip `0 ≤ Im z ≤ c` it is holomorphic with
`|m| ≤ 1` (`lorentzOne_hm`, `lorentzOne_hmb`), and on `|Re z| ≤ R` it is bounded below
(`norm_lorentzOne_line_ge`). With the flat theta lower bound for Riemann's kernel this gives
`∫|Φ(u+ic)m(u+ic)|²du ≥ L(cos 2c)^{-9/2}` once `cos 2c` is small
(`exists_integral_norm_sq_shiftedProfile_lorentzOne_ge`), the lower half of the degree-one
argument.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RHTower.KernelStrip

/-- `m(z) = 1/(1 − iz/a)`. -/
def lorentzOne (a : ℝ) (z : ℂ) : ℂ := 1 / (1 - I * z / a)

variable {a : ℝ}

theorem lorentzOne_hm (ha : 0 < a) (c : ℝ) :
    ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → DifferentiableAt ℂ (lorentzOne a) z := by
  intro z hz _
  unfold lorentzOne
  exact (differentiableAt_const _).div (by fun_prop) (lorentzPair_ne ha hz)

theorem lorentzOne_hmb (ha : 0 < a) (c : ℝ) :
    ∀ z : ℂ, 0 ≤ z.im → z.im ≤ c → ‖lorentzOne a z‖ ≤ 1 := by
  intro z hz _
  rw [lorentzOne, norm_div, norm_one]
  have := (norm_one_sub_I_mul_div_ge ha hz).1
  rw [div_le_one (by linarith)]
  exact this

theorem norm_lorentzOne_line_ge (ha : 0 < a) {c u R : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu : |u| ≤ R) :
    1 / (1 + (R + 1) / a) ≤ ‖lorentzOne a ((u : ℂ) + c * I)‖ := by
  have hz : 0 ≤ ((u : ℂ) + c * I).im := by simp [hc0]
  have hn : ‖1 - I * ((u : ℂ) + c * I) / a‖ ≤ 1 + (R + 1) / a := by
    calc ‖1 - I * ((u : ℂ) + c * I) / a‖ ≤ ‖(1 : ℂ)‖ + ‖I * ((u : ℂ) + c * I) / a‖ :=
          norm_sub_le _ _
      _ = 1 + ‖(u : ℂ) + c * I‖ / a := by
          rw [norm_one, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ 1 + (R + 1) / a := by
          gcongr
          calc ‖(u : ℂ) + c * I‖ ≤ ‖(u : ℂ)‖ + ‖(c : ℂ) * I‖ := norm_add_le _ _
            _ = |u| + c := by
                rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
                  Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0]
            _ ≤ R + 1 := by linarith
  have p := (norm_one_sub_I_mul_div_ge ha hz).1
  rw [lorentzOne, norm_div, norm_one]
  exact one_div_le_one_div_of_le (by linarith) hn

/-- **Lower bound for the first-order profile.** -/
theorem exists_integral_norm_sq_shiftedProfile_lorentzOne_ge (ha : 0 < a) :
    ∃ L : ℝ, 0 < L ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ c : ℝ, 0 ≤ c → c < π / 4 →
      1 / 2 ≤ Real.sin (2 * c) → Real.cos (2 * c) ≤ κ₀ →
      L * (Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c))) ≤
        ∫ u : ℝ, ‖shiftedProfile (lorentzOne a) c u‖ ^ 2 := by
  obtain ⟨U₀, hU₀, c₀, hc₀, κ₀, hκ₀, H⟩ := exists_integral_norm_sq_kernelC_line_ge
  set μ : ℝ := 1 / (1 + (U₀ + 1 + 1) / a) with hμ_def
  have hμ : 0 < μ := by rw [hμ_def]; positivity
  refine ⟨μ ^ 2 * c₀, by positivity, κ₀, hκ₀, fun c hc0 hc hs hκ => ?_⟩
  have hc1 : c ≤ 1 := by have := Real.pi_lt_four; linarith
  obtain ⟨-, h2, -, -⟩ := shiftedProfile_integrability hc0 hc (lorentzOne_hm ha c)
    (lorentzOne_hmb ha c)
  have hint := h2.integrable_norm_pow (p := 2) (by norm_num)
  have hUU : U₀ ≤ U₀ + 1 := by linarith
  have hPhic : Continuous fun u : ℝ => ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 :=
    (continuous_kernelC_line hc0 hc).norm.pow 2
  have hset : ∫ u in U₀..U₀ + 1, ‖shiftedProfile (lorentzOne a) c u‖ ^ 2 ≤
      ∫ u : ℝ, ‖shiftedProfile (lorentzOne a) c u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hUU]
    exact setIntegral_le_integral hint (Eventually.of_forall fun _ => by positivity)
  have hpt : ∀ u ∈ Icc U₀ (U₀ + 1), μ ^ 2 * ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      ‖shiftedProfile (lorentzOne a) c u‖ ^ 2 := by
    intro u hu
    have hu' : |u| ≤ U₀ + 1 := by rw [abs_of_nonneg (by linarith [hu.1])]; exact hu.2
    have hm := norm_lorentzOne_line_ge ha hc0 hc1 hu'
    rw [← hμ_def] at hm
    simp only [shiftedProfile, norm_mul, mul_pow]
    have hK := sq_nonneg ‖kernelC ((u : ℂ) + c * I)‖
    have : μ ^ 2 ≤ ‖lorentzOne a ((u : ℂ) + c * I)‖ ^ 2 := pow_le_pow_left₀ hμ.le hm 2
    nlinarith
  have hGc := continuous_shiftedProfile hc0 hc (lorentzOne_hm ha c)
  have hwin : μ ^ 2 * ∫ u in U₀..U₀ + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 ≤
      ∫ u in U₀..U₀ + 1, ‖shiftedProfile (lorentzOne a) c u‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hUU ((hPhic.const_mul _).intervalIntegrable _ _)
      ((hGc.norm.pow 2).intervalIntegrable _ _) hpt
  have hH := H c hc0 hc hs hκ
  calc μ ^ 2 * c₀ * (Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c)))
      = μ ^ 2 * (c₀ * (Real.cos (2 * c))⁻¹ ^ 4 * (1 / Real.sqrt (Real.cos (2 * c)))) := by ring
    _ ≤ μ ^ 2 * ∫ u in U₀..U₀ + 1, ‖kernelC ((u : ℂ) + c * I)‖ ^ 2 := by gcongr
    _ ≤ _ := hwin
    _ ≤ _ := hset

end RHTower.KernelStrip
