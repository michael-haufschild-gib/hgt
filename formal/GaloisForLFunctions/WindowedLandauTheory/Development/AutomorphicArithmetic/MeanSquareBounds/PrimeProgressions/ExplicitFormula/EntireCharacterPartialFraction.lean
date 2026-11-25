import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.CharacterWideGrowth
import Zeta23.WeilEF.Landau

/-! A local logarithmic-derivative expansion reaching the line `Re s = -1/2`. -/

open Complex DirichletCharacter Finset Metric

noncomputable section

namespace QH.PrimeProgressions

private theorem norm_entireCharacterL_center {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (t : ℝ) : (1 / 3 : ℝ) ≤ ‖entireCharacterL χ (2 + t * I)‖ := by
  let c : ℂ := 2 + t * I
  have hc : c.re = 2 := by simp [c]
  have hl : (1 / 3 : ℝ) ≤ ‖χ.LFunction c‖ := Zeta23.ThmE.LFunction_lower_bound_two (by rw [hc])
  change _ ≤ ‖entireCharacterL χ c‖
  unfold entireCharacterL
  split_ifs with hχ
  · have hc₁ : c ≠ 1 := by
      intro h
      norm_num [h] at hc
    have hn : 1 ≤ ‖c - 1‖ := by
      have h := re_le_norm (c - 1)
      rwa [sub_re, hc, one_re, show (2 - 1 : ℝ) = 1 by norm_num] at h
    rw [LFunctionTrivChar₁, Function.update_of_ne hc₁, norm_mul]
    rw [hχ] at hl
    exact hl.trans (le_mul_of_one_le_left (norm_nonneg _) hn)
  · exact hl

theorem entireCharacterL_partial_fraction :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ),
      ∃ Z : Finset ℂ,
        (↑Z = {ρ ∈ closedBall (2 + t * I) (341 / 125) | entireCharacterL χ ρ = 0}) ∧
        (∑ ρ ∈ Z, (analyticOrderNatAt (entireCharacterL χ) ρ : ℝ)) ≤
          C * Real.log ((N : ℝ) * (|t| + 2)) ∧
        ∀ s ∈ closedBall (2 + t * I) (51 / 20), entireCharacterL χ s ≠ 0 →
          ‖logDeriv (entireCharacterL χ) s -
            ∑ ρ ∈ Z, (analyticOrderNatAt (entireCharacterL χ) ρ : ℂ) / (s - ρ)‖ ≤
            C * Real.log ((N : ℝ) * (|t| + 2)) := by
  let R : ℝ := 31 / 10
  let J : ℝ := 1 / Real.log ((24 / 25) / (22 / 25))
  let D : ℝ := 44795000 / R
  let K : ℝ := 2 * Real.log 4992 + 3
  have hR : 0 < R := by norm_num [R]
  have hJ : 0 < J := one_div_pos.mpr (Real.log_pos (by norm_num))
  have hD : 0 < D := div_pos (by norm_num) hR
  have hK₀ : 0 ≤ Real.log (4992 : ℝ) := Real.log_nonneg (by norm_num)
  have hK : 0 < K := by dsimp only [K]; linarith only [hK₀]
  refine ⟨(J + D) * K, by positivity, ?_⟩
  intro N _ χ t
  let c : ℂ := 2 + t * I
  let f := entireCharacterL χ
  let X : ℝ := (N : ℝ) * (|t| + 2)
  let B : ℝ := 4992 * X ^ 3
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hX : 2 ≤ X := (by linarith only [abs_nonneg t] : (2 : ℝ) ≤ |t| + 2).trans
    (le_mul_of_one_le_left (by positivity) hN)
  have hX₀ : 0 < X := (by norm_num : (0 : ℝ) < 2).trans_le hX
  have hlogX : (1 / 2 : ℝ) ≤ Real.log X :=
    (by linarith only [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hX)
  have hKL : 0 ≤ K * Real.log X := mul_nonneg hK.le (by linarith only [hlogX])
  have hlogB : Real.log B ≤ K * Real.log X := by
    rw [show B = 4992 * X ^ 3 by rfl, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    dsimp only [K]
    nlinarith only [mul_nonneg hK₀ (sub_nonneg.mpr hlogX)]
  have hB : 2 ≤ B := by
    have hX₃ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hX 3
    dsimp only [B]
    linarith only [hX₃]
  have hlow := norm_entireCharacterL_center χ t
  have hc₀ : f c ≠ 0 := by
    intro h
    change (1 / 3 : ℝ) ≤ ‖f c‖ at hlow
    norm_num [h] at hlow
  have hcre : c.re = 2 := by simp [c]
  have hcn : ‖c‖ ≤ 2 + |t| := by
    simpa [c, norm_mul, norm_real, Real.norm_eq_abs] using norm_add_le (2 : ℂ) ((t : ℂ) * I)
  have hG : ∀ z ∈ closedBall c (24 / 25 * R), ‖f z‖ ≤ B * ‖f c‖ := by
    intro z hz
    have hdist := mem_closedBall.mp hz
    rw [Complex.dist_eq] at hdist
    have hre : -(49 / 50 : ℝ) ≤ z.re := by
      have h := (abs_le.mp ((abs_re_le_norm (z - c)).trans hdist)).1
      rw [sub_re, hcre] at h
      dsimp only [R] at h
      linarith only [h]
    have hn : ‖z‖ + 1 ≤ 4 * (|t| + 2) := by
      have h := norm_add_le (z - c) c
      rw [sub_add_cancel] at h
      dsimp only [R] at hdist
      linarith only [h, hdist, hcn, abs_nonneg t]
    calc
      ‖f z‖ ≤ 26 * (N : ℝ) ^ 3 * (‖z‖ + 1) ^ 3 := norm_entireCharacterL_le χ z hre
      _ ≤ 26 * (N : ℝ) ^ 3 * (4 * (|t| + 2)) ^ 3 := by gcongr
      _ = B * (1 / 3) := by dsimp only [B, X]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  have hf : AnalyticOnNhd ℂ f (closedBall c R) := fun z _ => (differentiable_entireCharacterL χ).analyticAt z
  obtain ⟨Z, hZ, hm, hpf⟩ := Zeta23.WeilEF.logDeriv_partial_fraction_disk hR hf hc₀ hB hG
  rw [show (22 / 25 : ℝ) * R = 341 / 125 by norm_num [R]] at hZ
  refine ⟨Z, hZ, ?_, ?_⟩
  · refine hm.trans ((mul_le_mul_of_nonneg_left hlogB hJ.le).trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) hKL
  · intro s hs hne
    have hs' : s ∈ closedBall c (83 / 100 * R) :=
      closedBall_subset_closedBall (by norm_num [R]) hs
    refine (hpf s hs' hne).trans ((mul_le_mul_of_nonneg_left hlogB hD.le).trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hJ.le) hKL

end QH.PrimeProgressions
