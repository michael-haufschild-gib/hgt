import GaloisForLFunctions.RHTower.ThmEUniformCross
import GaloisForLFunctions.RHTower.FamilyTaperBridge

/-!
# The archimedean–prime cross term at any bandwidth

`abs_Mform_PXc_le` needs only the `Φ` facts, which hold at every bandwidth; with the modulus shift
`μ_q = μ_1 + (log q)/2π` this gives `|𝓜[μ_q, P_c]| ≤ C (1 + log q) l √X` for every bandwidth ratio `λ > 0`
(`prop_cross_uniform_wide`), uniformly in the modulus and the coefficients.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

variable (cϱ : ℝ) in
/-- **[prop:cross] for `L(s, χ)` at any bandwidth, uniformly in the modulus and the coefficients.** -/
theorem prop_cross_uniform_wide {lam : ℝ} (hlam : 0 < lam) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ κ q : ℕ, κ ≤ 1 → 1 ≤ q → ∀ c : ℕ → ℂ, CoeffOK q c →
      ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHypsCoreW cϱ p F →
        |Mform F.Phi p.T (muq κ q) (PXc c p.X)|
          ≤ C * (1 + Real.log q) * (Zeta23.l p.T * Real.sqrt p.X) := by
  obtain ⟨Cμ₀, T₀₀, hCμ₀, hT₀₀⟩ := Zeta23.ThmE.muq_abs_le 0 1
    (GammaChi.gammaFactsChi (by norm_num) le_rfl) le_rfl
  obtain ⟨Cμ₁, T₀₁, hCμ₁, hT₀₁⟩ := Zeta23.ThmE.muq_abs_le 1 1
    (GammaChi.gammaFactsChi le_rfl le_rfl) le_rfl
  obtain ⟨Cd₀, hCd₀⟩ := (GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) le_rfl).deriv_bound
  obtain ⟨Cd₁, hCd₁⟩ := (GammaChi.gammaFactsChi (κ := 1) (q := 1) le_rfl le_rfl).deriv_bound
  obtain ⟨Cc, hCc⟩ := Cheb.chebyshevMertens.cheb1c
  set Cμ := Cμ₀ + Cμ₁ with hCμ
  set Cd := |Cd₀| + |Cd₁| with hCd
  refine ⟨4 * (4 * (Cμ + 1) + Cd) * |Cc|,
    max (max T₀₀ T₀₁) (2 * π * Real.exp (|(2:ℝ)| / lam)), by positivity,
    fun κ q hκ hq c hc p F hp hT hF => ?_⟩
  have hT2 : 2 * π * Real.exp (|(2:ℝ)| / p.lam) ≤ p.T := by
    rw [hp]; exact (le_max_right _ _).trans hT
  have hlam0 : 0 < p.lam := hp ▸ hlam
  have hT1 : 1 ≤ p.T := Setting.one_le_T (div_nonneg (abs_nonneg _) hlam0.le) hT2
  have hT0 : 0 ≤ p.T := by linarith
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hL := hF.L_pos
  have hX2 : 2 ≤ p.X := Setting.le_X_of_T hlam0 hT2
  have hlogX : Real.log p.X = p.L := by simp [Setting.X]
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hΓ := GammaChi.gammaFactsChi hκ hq
  have hμ : ContDiff ℝ 1 (muq κ q) := hΓ.smooth.of_le (by exact_mod_cast le_top)
  -- the modulus-one bounds, shifted
  have hB1 : ∀ τ ∈ Set.Icc p.T (2 * p.T), |muq κ 1 τ| ≤ Cμ * p.l := by
    intro τ hτ
    interval_cases κ
    · exact (hT₀₀ p ((le_max_left _ _).trans ((le_max_left _ _).trans hT)) τ hτ).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
    · exact (hT₀₁ p ((le_max_right _ _).trans ((le_max_left _ _).trans hT)) τ hτ).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hB : ∀ τ ∈ Set.Icc p.T (2 * p.T), |muq κ q τ| ≤ (Cμ + Real.log q) * p.l := by
    intro τ hτ
    rw [muq_eq_muq_one_add κ q hq]
    have hc2 : 0 ≤ Real.log q / (2 * π) := div_nonneg hlq (by positivity)
    have hc3 : Real.log q / (2 * π) ≤ Real.log q * p.l := by
      calc Real.log q / (2 * π) ≤ Real.log q := div_le_self hlq (by nlinarith [Real.pi_gt_three])
        _ ≤ Real.log q * p.l := le_mul_of_one_le_right hlq hl1
    calc |muq κ 1 τ + Real.log q / (2 * π)| ≤ |muq κ 1 τ| + |Real.log q / (2 * π)| := abs_add_le _ _
      _ ≤ Cμ * p.l + Real.log q * p.l := by rw [abs_of_nonneg hc2]; linarith [hB1 τ hτ]
      _ = (Cμ + Real.log q) * p.l := by ring
  have hD : ∀ τ ∈ Set.Icc p.T (2 * p.T), |deriv (muq κ q) τ| ≤ Cd / p.T := by
    intro τ hτ
    have hderiv : deriv (muq κ q) τ = deriv (muq κ 1) τ := by
      have e : muq κ q = fun x => muq κ 1 x + Real.log q / (2 * π) :=
        funext (muq_eq_muq_one_add κ q hq)
      rw [e, deriv_add_const]
    rw [hderiv]
    have hτ1 : 1 ≤ |τ| := by rw [abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.1]
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have h1 : |deriv (muq κ 1) τ| ≤ Cd / |τ| := by
      interval_cases κ
      · exact (hCd₀ τ hτ1).trans (div_le_div_of_nonneg_right
          (by linarith [le_abs_self Cd₀, abs_nonneg Cd₁]) (abs_nonneg _))
      · exact (hCd₁ τ hτ1).trans (div_le_div_of_nonneg_right
          (by linarith [le_abs_self Cd₁, abs_nonneg Cd₀]) (abs_nonneg _))
    refine h1.trans ?_
    rw [abs_of_pos hτ0]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) hτ.1
  have hBq0 : 0 ≤ (Cμ + Real.log q) * p.l := by
    have : 0 ≤ Cμ := by positivity
    positivity
  have h := abs_Mform_PXc_le hT0 hF.Phi_contDiff hF.Phi_sq_integrable hF.integral_Phi_sq_le hL hμ
    hBq0 (by positivity) hB hD hc.norm_le hX2 hlogX (hCc p.X hX2)
  refine h.trans ?_
  have hTne : p.T ≠ 0 := by linarith
  have e : 4 * (4 * ((Cμ + Real.log q) * p.l) + Cd / p.T * p.T) * |Cc| * Real.sqrt p.X
      = 4 * (4 * (Cμ + Real.log q) * p.l + Cd) * |Cc| * Real.sqrt p.X := by
    rw [div_mul_cancel₀ _ hTne]; ring
  rw [e]
  have hCμ0 : 0 ≤ Cμ := by positivity
  have hCd0 : 0 ≤ Cd := by positivity
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have key : 4 * (Cμ + Real.log q) * p.l + Cd ≤ (4 * (Cμ + 1) + Cd) * (1 + Real.log q) * p.l := by
    have h1 : Cd ≤ Cd * (1 + Real.log q) * p.l := by
      have : 1 ≤ (1 + Real.log q) * p.l := by nlinarith
      nlinarith
    nlinarith [mul_nonneg hCμ0 hlq, mul_nonneg (mul_nonneg hCμ0 hlq) (by linarith : (0:ℝ) ≤ p.l)]
  calc 4 * (4 * (Cμ + Real.log q) * p.l + Cd) * |Cc| * Real.sqrt p.X
      ≤ 4 * ((4 * (Cμ + 1) + Cd) * (1 + Real.log q) * p.l) * |Cc| * Real.sqrt p.X := by
        gcongr
    _ = 4 * (4 * (Cμ + 1) + Cd) * |Cc| * (1 + Real.log q) * (Zeta23.l p.T * Real.sqrt p.X) := by
        ring

end RHTower
