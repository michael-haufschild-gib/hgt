import GaloisForLFunctions.HTGeometry.DigammaJetLeadingConstants
import GaloisForLFunctions.HTGeometry.DigammaFieldLexRatio

/-!
# Dominance of jet normalization data

A jet monomial with data `(a, b)` — log degree `a`, argument degree `b` — is normalized by
`(log s)^a / s^b`.  Comparing two such factors, the argument degree decides first and the log degree
only at equality: a power of the leading logarithm is negligible against any positive power of the
argument.

So the normalization factor of a dominated datum, divided by that of the dominant one, vanishes on
every vertical line, and only the monomials sharing the dominant datum survive the normalization.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- A power of the leading logarithm is negligible against a positive power of the argument. -/
theorem tendsto_vertLog_pow_div_vertical_pow (_hσ : 0 < σ) (a : ℕ) {p : ℕ} (hp : 0 < p) :
    Tendsto (fun t : ℝ => (vertLog t) ^ a / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => (1 + Real.pi / 2) ^ a * (Real.log t ^ a / t)) atTop (nhds 0) := by
    have := (tendsto_pow_log_div_self a).const_mul ((1 + Real.pi / 2) ^ a)
    simpa using this
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) le_rfl) ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hlog1 : (1 : ℝ) ≤ Real.log t := by
    have := Real.log_le_log (Real.exp_pos 1) ht
    rwa [Real.log_exp] at this
  have hLnorm : ‖vertLog t‖ ≤ (1 + Real.pi / 2) * Real.log t := by
    have h := norm_vertLog_le ht1
    have hpi : Real.pi / 2 ≤ Real.pi / 2 * Real.log t := by
      have hpi0 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
      exact le_mul_of_one_le_right hpi0 hlog1
    calc ‖vertLog t‖ ≤ Real.log t + Real.pi / 2 := h
      _ ≤ Real.log t + Real.pi / 2 * Real.log t := by linarith
      _ = (1 + Real.pi / 2) * Real.log t := by ring
  have hsnorm : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    have him : ‖((σ : ℂ) + (t : ℂ) * Complex.I).im‖ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      Complex.abs_im_le_norm _
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [hval, Real.norm_eq_abs, abs_of_nonneg htpos.le] at him
    exact him
  have hspos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := lt_of_lt_of_le htpos hsnorm
  have hpow : t ^ p ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ p := pow_le_pow_left₀ htpos.le hsnorm _
  have htp : t ≤ t ^ p := by
    calc t = t ^ (1 : ℕ) := (pow_one t).symm
      _ ≤ t ^ p := pow_le_pow_right₀ ht1 hp
  rw [norm_div, norm_pow, norm_pow]
  have hnum : ‖vertLog t‖ ^ a ≤ ((1 + Real.pi / 2) * Real.log t) ^ a :=
    pow_le_pow_left₀ (norm_nonneg _) hLnorm _
  have hden : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ p := le_trans htp hpow
  calc ‖vertLog t‖ ^ a / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ p
      ≤ ((1 + Real.pi / 2) * Real.log t) ^ a / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ p := by
        gcongr
    _ ≤ ((1 + Real.pi / 2) * Real.log t) ^ a / t := by
        refine div_le_div_of_nonneg_left (by positivity) htpos hden
    _ = (1 + Real.pi / 2) ^ a * (Real.log t ^ a / t) := by
        rw [mul_pow]
        ring

/-- The normalization factor of a jet datum `(a, b)`. -/
noncomputable def jetNormFactor (σ : ℝ) (a b : ℕ) (t : ℝ) : ℂ :=
  (vertLog t) ^ a / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ b

/-- **Dominance of jet data.**  A strictly larger argument degree, or an equal argument degree with
a strictly smaller log degree, makes the normalization factor negligible. -/
theorem tendsto_jetNormFactor_ratio (hσ : 0 < σ) {a₁ b₁ a₂ b₂ : ℕ}
    (h : b₂ < b₁ ∨ (b₂ = b₁ ∧ a₁ < a₂)) :
    Tendsto (fun t : ℝ => jetNormFactor σ a₁ b₁ t / jetNormFactor σ a₂ b₂ t) atTop (nhds 0) := by
  rcases h with hb | ⟨hbe, ha⟩
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, b₁ = b₂ + (k + 1) := ⟨b₁ - b₂ - 1, by omega⟩
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hwork : Tendsto (fun t : ℝ => ‖(vertLog t) ^ a₁
        / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (k + 1)‖) atTop (nhds 0) := by
      have := (tendsto_vertLog_pow_div_vertical_pow hσ a₁ (Nat.succ_pos k)).norm
      simpa using this
    refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hwork
    filter_upwards [tendsto_norm_vertLog.eventually_ge_atTop 1,
      eventually_vertical_ne_zero σ, eventually_vertLog_ne_zero] with t hL hs hLne
    have hspos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := norm_pos_iff.mpr hs
    have hLpos : (0 : ℝ) < ‖vertLog t‖ := lt_of_lt_of_le zero_lt_one hL
    have hnormratio : ‖jetNormFactor σ a₁ b₁ t / jetNormFactor σ a₂ b₂ t‖
        = ‖vertLog t‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ b₂
          / (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ b₁ * ‖vertLog t‖ ^ a₂) := by
      rw [jetNormFactor, jetNormFactor, norm_div, norm_div, norm_div, norm_pow, norm_pow,
        norm_pow, norm_pow]
      field_simp
    have hexp : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ b₁
        = ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ b₂ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (k + 1) := by
      rw [hk, pow_add]
    have hLa : (1 : ℝ) ≤ ‖vertLog t‖ ^ a₂ := one_le_pow₀ hL
    rw [hnormratio, hexp, norm_div, norm_pow, norm_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖vertLog t‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ b₂
          * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (k + 1)
        = (‖vertLog t‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ b₂
            * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (k + 1)) * 1 := by ring
      _ ≤ (‖vertLog t‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ b₂
            * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (k + 1)) * ‖vertLog t‖ ^ a₂ :=
          mul_le_mul_of_nonneg_left hLa (by positivity)
      _ = ‖vertLog t‖ ^ a₁ * (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ b₂
            * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (k + 1) * ‖vertLog t‖ ^ a₂) := by ring
  · subst hbe
    obtain ⟨k, hk⟩ : ∃ k : ℕ, a₂ = a₁ + (k + 1) := ⟨a₂ - a₁ - 1, by omega⟩
    have hlim := tendsto_one_div_vertLog_pow (k := k + 1) (Nat.succ_pos k)
    refine hlim.congr' ?_
    filter_upwards [eventually_vertical_ne_zero σ, eventually_vertLog_ne_zero] with t hs hL
    rw [jetNormFactor, jetNormFactor, hk, pow_add]
    field_simp
    ring

end GaloisForLFunctions
