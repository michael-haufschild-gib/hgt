import GaloisForLFunctions.HTGeometry.UniformTubeLimit
import GaloisForLFunctions.HTGeometry.GammaShapeInteger

/-!
# Uniform bounds for the factors of the boundary shape

Each factor of `Γ^k·s^a·(log s)^b` obeys an abscissa-free estimate on a vertical tube: the argument
has modulus between the ordinate and `(1+M)` times it, the vertical logarithm does not see the
abscissa at all, and `Γ` decays faster than every power uniformly.  Negative exponents are harmless
because both moduli are eventually at least one.

These are the ingredients the dominance limits of eq. (26) need in tube form.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A quantity dominated on the tube by an abscissa-free null sequence has tube limit zero. -/
theorem tubeLimit_of_squeeze {M : ℝ} {f : ℝ → ℝ → ℂ} {g : ℝ → ℝ} {T₀ : ℝ}
    (hle : ∀ σ t : ℝ, 0 < σ → σ ≤ M → T₀ ≤ t → ‖f σ t‖ ≤ g t)
    (hg : Tendsto g atTop (nhds 0)) : TubeLimit M f 0 := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := Metric.tendsto_atTop.mp hg ε hε
  refine ⟨max T₀ T₁, fun σ t hσ hσM ht => ?_⟩
  have h1 := hle σ t hσ hσM (le_trans (le_max_left _ _) ht)
  have h2 := hT₁ t (le_trans (le_max_right _ _) ht)
  rw [Real.dist_eq, sub_zero] at h2
  have h3 : g t < ε := lt_of_le_of_lt (le_abs_self _) h2
  rw [sub_zero]
  linarith

/-- **The argument power, uniformly on a tube.**  Positive exponents grow at most like `((1+M)t)^a`
and negative ones are bounded by `t^a`. -/
theorem norm_zpow_vertical_le {M : ℝ} {σ t : ℝ} (hσ : 0 < σ) (hσM : σ ≤ M) (ht : 1 ≤ t) (a : ℤ) :
    ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a‖ ≤ (1 + M) ^ a.toNat * t ^ a := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hM1 : (1 : ℝ) ≤ 1 + M := by linarith [lt_of_lt_of_le hσ hσM]
  have hge : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := norm_vertical_ge_im σ t
  have hle : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ (1 + M) * t := norm_vertical_le_of_le hσ hσM ht
  have hone : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := le_trans ht hge
  rw [norm_zpow]
  by_cases hsign : 0 ≤ a
  · have htoNat : a = (a.toNat : ℤ) := (Int.toNat_of_nonneg hsign).symm
    rw [htoNat, zpow_natCast, zpow_natCast]
    calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ a.toNat ≤ ((1 + M) * t) ^ a.toNat :=
          pow_le_pow_left₀ (norm_nonneg _) hle _
      _ = (1 + M) ^ a.toNat * t ^ a.toNat := by rw [mul_pow]
  · have hneg : a < 0 := by omega
    have htoNat : a.toNat = 0 := by omega
    rw [htoNat, pow_zero, one_mul]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, a = -((n : ℤ) + 1) := ⟨(-a - 1).toNat, by omega⟩
    have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hn, zpow_neg, zpow_neg, hcast, zpow_natCast, zpow_natCast]
    have hpow : t ^ (n + 1) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (n + 1) :=
      pow_le_pow_left₀ (by linarith) hge _
    have htn : (0 : ℝ) < t ^ (n + 1) := by positivity
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le htn hpow

/-- **The logarithm power, uniformly in the abscissa** — it does not depend on it at all. -/
theorem norm_vertLog_zpow_le {t : ℝ} (ht : 3 ≤ t) (b : ℤ) :
    ‖vertLog t ^ b‖ ≤ (Real.log t + Real.pi / 2) ^ b.toNat := by
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log t := by
    have hexp : Real.exp 1 ≤ t := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hre : (vertLog t).re = Real.log t := by
    rw [vertLog]
    simp
  have hlow : (1 : ℝ) ≤ ‖vertLog t‖ := by
    calc (1 : ℝ) ≤ Real.log t := hlog1
      _ = (vertLog t).re := hre.symm
      _ ≤ ‖vertLog t‖ := Complex.re_le_norm _
  have hhigh : ‖vertLog t‖ ≤ Real.log t + Real.pi / 2 := norm_vertLog_le ht1
  rw [norm_zpow]
  by_cases hsign : 0 ≤ b
  · have htoNat : b = (b.toNat : ℤ) := (Int.toNat_of_nonneg hsign).symm
    rw [htoNat, zpow_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) hhigh _
  · have hneg : b < 0 := by omega
    have htoNat : b.toNat = 0 := by omega
    rw [htoNat, pow_zero]
    calc ‖vertLog t‖ ^ b ≤ ‖vertLog t‖ ^ (0 : ℤ) :=
          zpow_le_zpow_right₀ hlow (le_of_lt hneg)
      _ = 1 := zpow_zero _

end

end GaloisForLFunctions.HTGeometry
