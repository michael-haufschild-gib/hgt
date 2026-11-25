import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.RightHalfZeroWindow
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.JensenMultiplicity
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.CharacterGrowth

/-! Pole removal allows a uniform Jensen estimate for the principal character. -/

open Complex Metric Finset Filter Topology
open DirichletCharacter

noncomputable section

namespace QH.PrimeProgressions

private theorem principal_growth_quarter (N : ℕ) [NeZero N] (s : ℂ) (hs : 1 / 4 ≤ s.re) :
    ‖LFunctionTrivChar₁ N s‖ ≤ 6 * N * (1 + ‖s‖) ^ 2 := by
  by_cases h₁ : 1 / 2 ≤ s.re
  · refine (dhl_triv_growth N s h₁).trans ?_
    gcongr
    norm_num
  have hne : s ≠ 1 := fun e => h₁ (by norm_num [e])
  rw [LFunctionTrivChar₁, Function.update_of_ne hne, LFunctionTrivChar_eq_mul_riemannZeta hne,
    norm_mul, norm_mul]
  have hP := dhl_prod_le N s (by linarith only [hs])
  have hζ := Zeta23.RvM.norm_riemannZeta_le_of_re_pos (by linarith only [hs] : 0 < s.re) hne
  rw [norm_sub_rev] at hζ
  have hζ' : ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re) := by
    refine hζ.trans ?_
    rw [div_eq_mul_one_div (‖s‖)]
    linarith only [norm_nonneg s]
  have hpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hle : ‖s - 1‖ ≤ 1 + ‖s‖ := by
    have h := norm_sub_le s 1
    rw [norm_one] at h
    linarith only [h]
  have hinv : 1 / s.re ≤ 4 := by
    rw [div_le_iff₀ (by linarith only [hs])]
    linarith only [hs]
  have hmain : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 6 * (1 + ‖s‖) ^ 2 := by
    calc
      _ ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) :=
        mul_le_mul_of_nonneg_left hζ' hpos.le
      _ = ‖s - 1‖ + 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by field_simp
      _ ≤ (1 + ‖s‖) + 1 + (1 + ‖s‖) * (‖s‖ * (1 + 4)) := by gcongr
      _ ≤ _ := by nlinarith only [norm_nonneg s, sq_nonneg ‖s‖]
  calc
    _ = ‖∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * (‖s - 1‖ * ‖riemannZeta s‖) := by ring
    _ ≤ N * (6 * (1 + ‖s‖) ^ 2) := mul_le_mul hP hmain (by positivity) (by positivity)
    _ = _ := by ring

theorem principal_analyticOrderNatAt {N : ℕ} [NeZero N] {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt (LFunctionTrivChar₁ N) s =
      analyticOrderNatAt (1 : DirichletCharacter ℂ N).LFunction s := by
  have hev : LFunctionTrivChar₁ N =ᶠ[𝓝 s]
      (fun z : ℂ => z - 1) * (1 : DirichletCharacter ℂ N).LFunction := by
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact Function.update_of_ne hz _ _
  have ha : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
  have hL : AnalyticAt ℂ (1 : DirichletCharacter ℂ N).LFunction s :=
    analyticAt_iff_eventually_differentiableAt.mpr
      ((eventually_ne_nhds hs).mono fun z hz => differentiableAt_LFunction _ z (.inl hz))
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul ha hL,
    ha.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs), zero_add]

/-- Principal zero multiplicities in the right half of the strip satisfy the same logarithmic window bound. -/
theorem principal_half_height_right_zero_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (Z : Finset ℂ) (t : ℝ),
      (∀ ρ ∈ Z, 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 / 2) →
      (∑ ρ ∈ Z, (analyticOrderNatAt (1 : DirichletCharacter ℂ N).LFunction ρ : ℝ)) ≤
        C * Real.log ((N : ℝ) * (|t| + 2)) := by
  have hlog : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5)) := Real.log_pos (by norm_num)
  have hlog192 : 0 < Real.log (192 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨2 * (Real.log 192 + 2) / Real.log ((7 / 4 : ℝ) / (8 / 5)),
    div_pos (by positivity) hlog, ?_⟩
  intro N _ Z t hZ
  let f := LFunctionTrivChar₁ N
  let c : ℂ := 2 + t * I
  let X : ℝ := N * (|t| + 2)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hX : 2 ≤ X := le_trans (by linarith only [abs_nonneg t]) (le_mul_of_one_le_left (by positivity) hN)
  have hc₁ : c ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [c] at hr
  have hlow : (1 / 3 : ℝ) ≤ ‖f c‖ := by
    have hcl : 1 ≤ ‖c - 1‖ := by
      have h := Complex.re_le_norm (c - 1)
      rw [sub_re, show c.re = 2 by simp [c], one_re] at h
      linarith only [h]
    have hl : (1 / 3 : ℝ) ≤ ‖(1 : DirichletCharacter ℂ N).LFunction c‖ :=
      Zeta23.ThmE.LFunction_lower_bound_two (by simp [c])
    change _ ≤ ‖LFunctionTrivChar₁ N c‖
    rw [LFunctionTrivChar₁, Function.update_of_ne hc₁, norm_mul]
    calc (1 / 3 : ℝ) = 1 * (1 / 3) := (one_mul _).symm
      _ ≤ ‖c - 1‖ * (1 / 3) := mul_le_mul_of_nonneg_right hcl (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (norm_nonneg _)
  have hne : f c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    norm_num at hlow
  have hbd : ∀ s ∈ sphere c (7 / 4), ‖f s‖ ≤ 64 * X ^ 2 := by
    intro s hs
    have hd : ‖s - c‖ ≤ (7 / 4 : ℝ) := (by simpa only [mem_sphere, Complex.dist_eq] using hs : ‖s - c‖ = (7 / 4 : ℝ)).le
    have hr := Complex.abs_re_le_norm (s - c)
    rw [sub_re, show c.re = 2 by simp [c]] at hr
    have hsre : 1 / 4 ≤ s.re := by linarith only [(abs_le.mp (hr.trans hd)).1]
    have hnc : ‖c‖ ≤ 2 + |t| := by
      simpa [c, norm_mul, norm_I, norm_real, Real.norm_eq_abs] using norm_add_le (2 : ℂ) ((t : ℂ) * I)
    have hns : ‖s‖ ≤ 7 / 4 + (2 + |t|) := by
      have h := norm_add_le (s - c) c
      rw [sub_add_cancel] at h
      exact h.trans (add_le_add hd hnc)
    have hs' : 1 + ‖s‖ ≤ 3 * (|t| + 2) := by linarith only [hns, abs_nonneg t]
    calc
      ‖f s‖ ≤ 6 * N * (1 + ‖s‖) ^ 2 := principal_growth_quarter N s hsre
      _ ≤ 6 * N * (3 * (|t| + 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs' 2) (by positivity)
      _ ≤ 64 * X ^ 2 := by
        have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN, mul_nonneg (by positivity : (0 : ℝ) ≤ N) (sub_nonneg.mpr hN)]
        have hp := mul_le_mul_of_nonneg_right hNN (sq_nonneg (|t| + 2))
        have hp₀ : (0 : ℝ) ≤ (N : ℝ) ^ 2 * (|t| + 2) ^ 2 := by positivity
        nlinarith only [hp, hp₀]
  have hM : 1 ≤ 64 * X ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hX 2
    linarith only [h]
  have hJ := sum_analyticOrderNatAt_le_jensen (differentiable_LFunctionTrivChar₁ N)
    (by norm_num : (0 : ℝ) < 8 / 5) (by norm_num : (8 / 5 : ℝ) < 7 / 4) hM hne hbd Z
    (fun ρ hρ => mem_half_height_right_disc (hZ ρ hρ).1 (hZ ρ hρ).2.1.le (hZ ρ hρ).2.2)
  have hchange : ∀ ρ ∈ Z, analyticOrderNatAt f ρ =
      analyticOrderNatAt (1 : DirichletCharacter ℂ N).LFunction ρ := by
    intro ρ hρ
    exact principal_analyticOrderNatAt (fun h => (lt_irrefl (1 : ℝ)) (by simpa [h] using (hZ ρ hρ).2.1))
  have hJ' : (∑ ρ ∈ Z, (analyticOrderNatAt (1 : DirichletCharacter ℂ N).LFunction ρ : ℝ)) ≤
      Real.log (64 * X ^ 2 / ‖f c‖) / Real.log ((7 / 4 : ℝ) / (8 / 5)) := by
    refine (Finset.sum_congr rfl ?_).le.trans hJ
    exact fun ρ hρ => congrArg (fun n : ℕ => (n : ℝ)) (hchange ρ hρ).symm
  have hr : 64 * X ^ 2 / ‖f c‖ ≤ 192 * X ^ 2 := by
    apply (div_le_iff₀ (norm_pos_iff.mpr hne)).2
    have h := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 192 * X ^ 2 by positivity)
    linarith only [h]
  refine hJ'.trans ((div_le_div_of_nonneg_right
    ((Real.log_le_log (by positivity) hr).trans (dhl_log 192 X (by norm_num) hX)) hlog.le).trans_eq ?_)
  ring

end QH.PrimeProgressions
