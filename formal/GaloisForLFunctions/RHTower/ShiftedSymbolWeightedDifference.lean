import GaloisForLFunctions.RHTower.GammaJumpNearDiagonalLipschitz
import GaloisForLFunctions.RHTower.WallSymbolFrequencyJets

/-!
# `(35a)`: the weighted symbol difference on a shifted line

The order-minus-one commutator estimate `(32)` used exactly two facts about the real-line multiplier
`r`: that it grows at most linearly, and that its derivative decays like `(1+|η|)^{-1}`.  On the
shifted line `Im z = σ` the multiplier is `wallSymbol σ`, whose first frequency jet the corpus
already bounds by `2(1+π/2)/|x|` past the unit radius.  Continuity supplies the missing collar, and
the mean value theorem then converts the derivative bound into both the linear growth and the
near-diagonal Lipschitz estimate.  The far region needs nothing but the growth bound, so the same
two-region split gives the global weighted difference bound with a `σ`-dependent constant.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **The shifted symbol's derivative decays like the reciprocal frequency, uniformly.**  Past the
unit radius this is the polygamma jet bound; inside it, continuity on a compact collar. -/
theorem exists_deriv_wallSymbol_bound {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ t : ℝ, ‖wallSymbolJet σ 1 t‖ ≤ C₀ / (1 + |t|) := by
  have hcont : Continuous (wallSymbolJet σ 1) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (hasDerivAt_wallSymbolJet hσ0 hσ1 1 t).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max (4 * (1 + Real.pi / 2)) (2 * max M 0), by positivity, fun t => ?_⟩
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have ht0 : (0 : ℝ) < 1 + |t| := by positivity
  rcases le_or_gt 1 |t| with ht | ht
  · have hjet := norm_wallSymbolJet_succ_le hσ0 hσ1 ht 0
    have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
    have hjet' : ‖wallSymbolJet σ 1 t‖ ≤ 2 * (1 + Real.pi / 2) / |t| := by
      simpa using hjet
    have hstep : 2 * (1 + Real.pi / 2) / |t| ≤ 4 * (1 + Real.pi / 2) / (1 + |t|) := by
      rw [div_le_div_iff₀ htpos ht0]
      nlinarith [ht, hpi]
    refine le_trans hjet' (le_trans hstep ?_)
    refine div_le_div_of_nonneg_right ?_ ht0.le
    exact le_max_left _ _
  · have hmem : t ∈ Icc (-1 : ℝ) 1 := by
      rw [abs_lt] at ht
      exact ⟨ht.1.le, ht.2.le⟩
    have hb : ‖wallSymbolJet σ 1 t‖ ≤ max M 0 := le_trans (hM t hmem) (le_max_left _ _)
    have hle : (1 + |t|) ≤ 2 := by
      have := ht.le
      linarith
    have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    have hkey : max M 0 ≤ (2 * max M 0) / (1 + |t|) := by
      rw [le_div_iff₀ ht0]
      nlinarith [hle, hM0, ht0]
    refine le_trans hb (le_trans hkey ?_)
    refine div_le_div_of_nonneg_right ?_ ht0.le
    exact le_max_right _ _

theorem hasDerivAt_wallSymbol {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (t : ℝ) :
    HasDerivAt (wallSymbol σ) (wallSymbolJet σ 1 t) t := by
  have h := (hasDerivAt_wallSymbolJet hσ0 hσ1 0 t).add_const
    (2 * (Real.eulerMascheroniConstant : ℂ))
  have hfun : (fun x : ℝ => wallSymbolJet σ 0 x + 2 * (Real.eulerMascheroniConstant : ℂ))
      = wallSymbol σ := by
    funext x
    exact wallSymbolJet_zero σ x
  rwa [hfun] at h

/-- **The shifted symbol grows at most linearly.** -/
theorem exists_bound_wallSymbol_growth {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t : ℝ, ‖wallSymbol σ t‖ ≤ S * (1 + |t|) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_deriv_wallSymbol_bound hσ0 hσ1
  refine ⟨‖wallSymbol σ 0‖ + C₀, by positivity, fun t => ?_⟩
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) t, ‖deriv (wallSymbol σ) θ‖ ≤ C₀ := by
    intro θ _
    rw [(hasDerivAt_wallSymbol hσ0 hσ1 θ).deriv]
    refine le_trans (hbound θ) ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + |θ|)]
    nlinarith [abs_nonneg θ, hC₀]
  have hdiff : ∀ θ ∈ uIcc (0 : ℝ) t, DifferentiableAt ℝ (wallSymbol σ) θ :=
    fun θ _ => (hasDerivAt_wallSymbol hσ0 hσ1 θ).differentiableAt
  have hMVT := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_deriv_le hdiff hderiv
    left_mem_uIcc right_mem_uIcc
  have habs : ‖t - (0 : ℝ)‖ = |t| := by simp
  rw [habs] at hMVT
  have htri : ‖wallSymbol σ t‖ ≤ ‖wallSymbol σ 0‖ + C₀ * |t| := by
    have := norm_sub_norm_le (wallSymbol σ t) (wallSymbol σ 0)
    linarith [hMVT, this]
  nlinarith [htri, norm_nonneg (wallSymbol σ 0), hC₀, abs_nonneg t]

/-- **The weighted near-diagonal Lipschitz bound on the shifted line.** -/
theorem exists_bound_wallSymbol_nearDiagonal {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ η : ℝ, |ξ - η| ≤ (1 + |η|) / 2 →
      (1 + |ξ|) * ‖wallSymbol σ ξ - wallSymbol σ η‖ ≤ C * |ξ - η| := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_deriv_wallSymbol_bound hσ0 hσ1
  refine ⟨3 * C₀, by positivity, fun ξ η hnear => ?_⟩
  have hηpos : (0 : ℝ) < 1 + |η| := by positivity
  have hderivbound : ∀ θ ∈ uIcc η ξ, ‖deriv (wallSymbol σ) θ‖ ≤ 2 * C₀ / (1 + |η|) := by
    intro θ hθ
    have hθpos : (1 + |η|) / 2 ≤ 1 + |θ| := one_add_abs_ge_of_mem_uIcc hθ hnear
    have hθ0 : (0 : ℝ) < 1 + |θ| := by positivity
    rw [(hasDerivAt_wallSymbol hσ0 hσ1 θ).deriv]
    refine (hbound θ).trans ?_
    rw [div_le_div_iff₀ hθ0 hηpos]
    nlinarith [hC₀, hθpos, hηpos]
  have hdiff : ∀ θ ∈ uIcc η ξ, DifferentiableAt ℝ (wallSymbol σ) θ :=
    fun θ _ => (hasDerivAt_wallSymbol hσ0 hσ1 θ).differentiableAt
  have hMVT := (convex_uIcc η ξ).norm_image_sub_le_of_norm_deriv_le hdiff hderivbound
    left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs] at hMVT
  have hcomp : 1 + |ξ| ≤ 3 / 2 * (1 + |η|) := by
    have h1 : |ξ| ≤ |η| + |ξ - η| := by
      have := abs_sub_abs_le_abs_sub ξ η
      linarith
    linarith
  calc (1 + |ξ|) * ‖wallSymbol σ ξ - wallSymbol σ η‖
      ≤ (3 / 2 * (1 + |η|)) * (2 * C₀ / (1 + |η|) * |ξ - η|) := by
        refine mul_le_mul hcomp hMVT (norm_nonneg _) (by positivity)
    _ = 3 * C₀ * |ξ - η| := by field_simp

/-- **`(35a)`: the global weighted symbol-difference bound on the shifted line.** -/
theorem exists_bound_wallSymbol_global {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ η : ℝ,
      (1 + |ξ|) * ‖wallSymbol σ ξ - wallSymbol σ η‖ ≤ C * (|ξ - η| + |ξ - η| ^ 2) := by
  obtain ⟨C₁, hC₁, hnear⟩ := exists_bound_wallSymbol_nearDiagonal hσ0 hσ1
  obtain ⟨S, hS, hgrow⟩ := exists_bound_wallSymbol_growth hσ0 hσ1
  refine ⟨C₁ + 15 * S, by linarith, fun ξ η => ?_⟩
  have hsep : (0 : ℝ) ≤ |ξ - η| := abs_nonneg _
  rcases le_or_gt |ξ - η| ((1 + |η|) / 2) with h | h
  · have hb := hnear ξ η h
    nlinarith [hb, hC₁, hS, hsep, sq_nonneg (|ξ - η|)]
  · obtain ⟨hη, hξ⟩ := one_add_abs_le_of_far h
    have hbξ : ‖wallSymbol σ ξ‖ ≤ S * (1 + |ξ|) := hgrow ξ
    have hbη : ‖wallSymbol σ η‖ ≤ S * (1 + |η|) := hgrow η
    have hdiff : ‖wallSymbol σ ξ - wallSymbol σ η‖ ≤ 5 * S * |ξ - η| := by
      have htri : ‖wallSymbol σ ξ - wallSymbol σ η‖
          ≤ ‖wallSymbol σ ξ‖ + ‖wallSymbol σ η‖ := norm_sub_le _ _
      nlinarith [htri, hbξ, hbη, hS, hη, hξ]
    have hfar : (1 + |ξ|) * ‖wallSymbol σ ξ - wallSymbol σ η‖ ≤ 15 * S * |ξ - η| ^ 2 := by
      calc (1 + |ξ|) * ‖wallSymbol σ ξ - wallSymbol σ η‖
          ≤ (3 * |ξ - η|) * (5 * S * |ξ - η|) :=
            mul_le_mul hξ hdiff (norm_nonneg _) (by positivity)
        _ = 15 * S * |ξ - η| ^ 2 := by ring
    nlinarith [hfar, hC₁, hS, hsep, sq_nonneg (|ξ - η|)]

end GaloisForLFunctions.RHTower
