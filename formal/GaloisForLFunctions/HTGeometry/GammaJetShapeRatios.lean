import GaloisForLFunctions.HTGeometry.GammaFieldCollapseFromResidues

/-!
# Ratios of Gamma-jet shapes

The shape of a Gamma-field term is a power of `Γ` times the shape of its lowest coefficient.  The
ratio of two such shapes therefore splits into a Gamma-power ratio and a jet-shape ratio: the second
has at most polynomial growth, so a strictly larger Gamma power makes the whole ratio vanish, and at
equal Gamma powers the jet dominance decides.

These are the shape-ratio limits that the collapse from residues consumes.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- The shape of a Gamma-field term: a power of `Γ` times the shape of its lowest coefficient. -/
noncomputable def gammaJetShape (σ : ℝ) (u a dP b : ℕ) (t : ℝ) : ℂ :=
  gammaLine σ t ^ u * polyJetShape σ a dP b t

theorem eventually_gammaJetShape_ne_zero (hσ : 0 < σ) (u a dP b : ℕ) :
    ∀ᶠ t : ℝ in atTop, gammaJetShape σ u a dP b t ≠ 0 := by
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  rw [gammaJetShape, polyJetShape]
  refine mul_ne_zero (pow_ne_zero _ (gammaLine_ne_zero hσ t)) ?_
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hs)) (pow_ne_zero _ hs)

/-- A ratio of jet shapes has at most polynomial growth on a vertical line. -/
theorem hasPolyGrowthLine_polyJetShape_ratio (hσ : 0 < σ) (a₁ dP₁ b₁ a₂ dP₂ b₂ : ℕ) :
    HasPolyGrowthLine (fun t : ℝ =>
      polyJetShape σ a₁ dP₁ b₁ t / polyJetShape σ a₂ dP₂ b₂ t) := by
  refine ⟨a₁ + (dP₁ + b₂), (1 + Real.pi / 2) ^ a₁ * (1 + σ) ^ (dP₁ + b₂), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1), tendsto_norm_vertLog.eventually_ge_atTop 1,
    eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t ht hL1 hL hs
  have ht1 : (1 : ℝ) ≤ t := le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hlog1 : (1 : ℝ) ≤ Real.log t := by
    have := Real.log_le_log (Real.exp_pos 1) ht
    rwa [Real.log_exp] at this
  have hsle : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ (1 + σ) * t := by
    have h := norm_add_le ((σ : ℂ)) ((t : ℂ) * Complex.I)
    have h1 : ‖(σ : ℂ)‖ = σ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ.le]
    have h2 : ‖(t : ℂ) * Complex.I‖ = t := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_trans zero_le_one ht1)]
    rw [h1, h2] at h
    nlinarith
  have hLle : ‖vertLog t‖ ≤ (1 + Real.pi / 2) * t := by
    have h := norm_vertLog_le ht1
    have hlogt : Real.log t ≤ t := by
      have := Real.log_le_sub_one_of_pos htpos
      linarith
    have hpi : Real.pi / 2 ≤ Real.pi / 2 * t := by
      have hpi0 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
      exact le_mul_of_one_le_right hpi0 ht1
    calc ‖vertLog t‖ ≤ Real.log t + Real.pi / 2 := h
      _ ≤ t + Real.pi / 2 * t := by linarith
      _ = (1 + Real.pi / 2) * t := by ring
  have hspos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := norm_pos_iff.mpr hs
  have hs1 : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    have him : ‖((σ : ℂ) + (t : ℂ) * Complex.I).im‖ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      Complex.abs_im_le_norm _
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [hval, Real.norm_eq_abs, abs_of_nonneg htpos.le] at him
    linarith
  have hLpos : (0 : ℝ) < ‖vertLog t‖ := lt_of_lt_of_le zero_lt_one hL1
  have hnorm : ‖polyJetShape σ a₁ dP₁ b₁ t / polyJetShape σ a₂ dP₂ b₂ t‖
      = (‖vertLog t‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₁ + b₂))
        / (‖vertLog t‖ ^ a₂ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₂ + b₁)) := by
    rw [polyJetShape, polyJetShape, norm_div, norm_div, norm_div, norm_mul, norm_mul,
      norm_pow, norm_pow, norm_pow, norm_pow, norm_pow, norm_pow, pow_add, pow_add]
    field_simp
  rw [hnorm]
  have hden : (1 : ℝ) ≤ ‖vertLog t‖ ^ a₂ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₂ + b₁) := by
    have h1 : (1 : ℝ) ≤ ‖vertLog t‖ ^ a₂ := one_le_pow₀ hL1
    have h2 : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₂ + b₁) := one_le_pow₀ hs1
    nlinarith
  have hnum : ‖vertLog t‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₁ + b₂)
      ≤ ((1 + Real.pi / 2) * t) ^ a₁ * ((1 + σ) * t) ^ (dP₁ + b₂) := by
    have h1 : ‖vertLog t‖ ^ a₁ ≤ ((1 + Real.pi / 2) * t) ^ a₁ :=
      pow_le_pow_left₀ (norm_nonneg _) hLle _
    have h2 : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₁ + b₂) ≤ ((1 + σ) * t) ^ (dP₁ + b₂) :=
      pow_le_pow_left₀ (norm_nonneg _) hsle _
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hdiv : (‖vertLog t‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₁ + b₂))
      / (‖vertLog t‖ ^ a₂ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₂ + b₁))
      ≤ ‖vertLog t‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₁ + b₂) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (pow_nonneg (norm_nonneg (vertLog t)) a₁)
      (pow_nonneg (norm_nonneg ((σ : ℂ) + (t : ℂ) * Complex.I)) (dP₁ + b₂))]
  calc (‖vertLog t‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₁ + b₂))
        / (‖vertLog t‖ ^ a₂ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₂ + b₁))
      ≤ ‖vertLog t‖ ^ a₁ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (dP₁ + b₂) := hdiv
    _ ≤ ((1 + Real.pi / 2) * t) ^ a₁ * ((1 + σ) * t) ^ (dP₁ + b₂) := hnum
    _ = (1 + Real.pi / 2) ^ a₁ * (1 + σ) ^ (dP₁ + b₂) * t ^ (a₁ + (dP₁ + b₂)) := by
        rw [mul_pow, mul_pow, pow_add]
        ring

/-- **A strictly larger Gamma power dominates.**  Whatever the jet data, the shape ratio vanishes. -/
theorem tendsto_gammaJetShape_ratio_of_gamma_lt (hσ : 0 < σ) {u₁ u₂ a₁ dP₁ b₁ a₂ dP₂ b₂ : ℕ}
    (h : u₂ < u₁) :
    Tendsto (fun t : ℝ => gammaJetShape σ u₁ a₁ dP₁ b₁ t / gammaJetShape σ u₂ a₂ dP₂ b₂ t)
      atTop (nhds 0) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, u₁ = u₂ + (k + 1) := ⟨u₁ - u₂ - 1, by omega⟩
  have hlim := tendsto_gammaLine_pow_mul hσ
    (hasPolyGrowthLine_polyJetShape_ratio hσ a₁ dP₁ b₁ a₂ dP₂ b₂) k
  refine hlim.congr' ?_
  filter_upwards [eventually_gammaJetShape_ne_zero hσ u₂ a₂ dP₂ b₂,
    eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hne hL hs
  have hγ : gammaLine σ t ^ u₂ ≠ 0 := pow_ne_zero _ (gammaLine_ne_zero hσ t)
  have hshape : polyJetShape σ a₂ dP₂ b₂ t ≠ 0 := by
    rw [polyJetShape]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hs)) (pow_ne_zero _ hs)
  rw [gammaJetShape, gammaJetShape, hk, pow_add]
  field_simp
  ring

/-- **At equal Gamma powers the jet dominance decides.** -/
theorem tendsto_gammaJetShape_ratio_of_gamma_eq (hσ : 0 < σ) {u a₁ dP₁ b₁ a₂ dP₂ b₂ : ℕ}
    {r : ℂ} (hr : Tendsto (fun t : ℝ => polyJetShape σ a₁ dP₁ b₁ t / polyJetShape σ a₂ dP₂ b₂ t)
      atTop (nhds r)) :
    Tendsto (fun t : ℝ => gammaJetShape σ u a₁ dP₁ b₁ t / gammaJetShape σ u a₂ dP₂ b₂ t)
      atTop (nhds r) := by
  refine hr.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  have hγ : gammaLine σ t ^ u ≠ 0 := pow_ne_zero _ (gammaLine_ne_zero hσ t)
  have hshape : polyJetShape σ a₂ dP₂ b₂ t ≠ 0 := by
    rw [polyJetShape]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hL) (pow_ne_zero _ hs)) (pow_ne_zero _ hs)
  rw [gammaJetShape, gammaJetShape]
  field_simp

end GaloisForLFunctions
