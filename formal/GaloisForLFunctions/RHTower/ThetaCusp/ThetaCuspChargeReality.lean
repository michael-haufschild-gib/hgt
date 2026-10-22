import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeDominance
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.Bottcher.ModularLambdaCovering

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

open Bottcher

/-! ### Reality of the charge transform on the real axis -/

theorem thetaFour_conj' (τ : ℂ) :
    (starRingEnd ℂ) (thetaFour τ) = thetaFour (-(starRingEnd ℂ) τ) := by
  unfold thetaFour; rw [jacobiTheta₂_conj]; congr 1; rw [map_div₀, map_one, map_ofNat]

theorem thetaGroupBasis_one_conj (τ : ℂ) :
    (starRingEnd ℂ) (thetaGroupBasis 1 τ) = thetaGroupBasis 1 (-(starRingEnd ℂ) τ) := by
  unfold thetaGroupBasis thetaGroupHauptmodul
  simp only [map_mul, map_div₀, map_pow, thetaThree_conj, thetaTwo_conj, thetaFour_conj']

theorem conj_modTail_thetaGroupBasis_one (x : ℝ) :
    (starRingEnd ℂ) (modTail (thetaGroupBasis 1) 0 x) = modTail (thetaGroupBasis 1) 0 x := by
  unfold modTail
  have hax : -(starRingEnd ℂ) (modAxisPoint x) = modAxisPoint x := by
    unfold modAxisPoint; rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  simp only [map_div₀, map_mul, map_sub, Complex.conj_ofReal, thetaGroupBasis_one_conj, hax,
    map_zero, map_ofNat]

/-- The tail transform of the charge form. -/
def chargeTailTransform (u : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-Complex.I * u * x) * modTail (thetaGroupBasis 1) 0 x

theorem chargeTailTransform_im (u : ℝ) : (chargeTailTransform u).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold chargeTailTransform
  have hS := thetaGroupBasis_axis 1
  set f : ℝ → ℂ := fun x => Complex.exp (-Complex.I * u * x) * modTail (thetaGroupBasis 1) 0 x
    with hf
  calc (starRingEnd ℂ) (∫ x : ℝ, f x) = ∫ x : ℝ, (starRingEnd ℂ) (f x) := integral_conj.symm
    _ = ∫ x : ℝ, f (-x) := by
        congr 1; funext x
        simp only [hf]
        rw [map_mul, conj_modTail_thetaGroupBasis_one, ← Complex.exp_conj,
          modTail_zero_even hS x]
        congr 2
        simp [Complex.conj_ofReal]
    _ = ∫ x : ℝ, f x := integral_neg_eq_self f volume

theorem thetaGroupXi_one_ofReal_im (u : ℝ) : (thetaGroupXi 1 (u : ℂ)).im = 0 := by
  obtain ⟨M, hM⟩ := exists_thetaGroupBasis_one_cusp
  have hM' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis 1 τ - 0‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; rw [sub_zero]; exact hM τ hτ
  unfold thetaGroupXi
  rw [modXi_eq_tailTransform (differentiableOn_thetaGroupBasis 1) (thetaGroupBasis_axis 1) hM' (u : ℂ)]
  have h := chargeTailTransform_im u
  unfold chargeTailTransform at h
  have hp : -((u : ℂ) ^ 2 + 1 / 4) = ((-(u ^ 2 + 1 / 4) : ℝ) : ℂ) := by push_cast; ring
  rw [hp, Complex.im_ofReal_mul, h, mul_zero]

/-! ### The dominance law in the frequency variable -/

/-- The saddle parameter of a frequency: `t(u) = (7π/(8u))^{1/4}`. -/
def chT (u : ℝ) : ℝ := Real.sqrt (Real.sqrt (7 * π / (8 * u)))

theorem chT_pos {u : ℝ} (hu : 0 < u) : 0 < chT u := by
  unfold chT; apply Real.sqrt_pos.mpr; apply Real.sqrt_pos.mpr; positivity

theorem chT_pow_four {u : ℝ} (hu : 0 < u) : chT u ^ 4 = 7 * π / (8 * u) := by
  unfold chT
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity)]

theorem chU_chT {u : ℝ} (hu : 0 < u) : chU (chT u) = u := by
  unfold chU; rw [chT_pow_four hu]; field_simp

theorem chT_le {u t₁ : ℝ} (hu : 0 < u) (ht₁ : 0 < t₁) (hU : 7 * π / (8 * t₁ ^ 4) ≤ u) :
    chT u ≤ t₁ := by
  have h4 : chT u ^ 4 ≤ t₁ ^ 4 := by
    rw [chT_pow_four hu, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hU
    nlinarith [pow_pos ht₁ 4]
  exact le_of_pow_le_pow_left₀ (by norm_num) ht₁.le h4

/-- **Cusp-charge law.**  For large frequencies the charge transform is strictly negative and
dominates `Ξ` by a factor `≍ u^{-1/4}`. -/
theorem cuspCharge_law :
    ∃ U : ℝ, 0 < U ∧ ∀ u : ℝ, U ≤ u →
      (thetaGroupXi 1 (u : ℂ)).re < 0 ∧
        ‖XiC (u : ℂ)‖ ≤ 2 ^ 16 * 3000000 * 3628800 * chT u * ‖thetaGroupXi 1 (u : ℂ)‖ := by
  obtain ⟨t₁, ht₁, hdom⟩ := cuspCharge_dominance_chU
  refine ⟨7 * π / (8 * t₁ ^ 4), by positivity, fun u hu => ?_⟩
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have h := hdom (chT u) (chT_pos hu0) (chT_le hu0 ht₁ hu)
  rwa [chU_chT hu0] at h

theorem tendsto_chT_atTop : Tendsto chT atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => 7 * π / (8 * u)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := 7 * π / 8)).div_atTop tendsto_id
    refine this.congr' (Eventually.of_forall fun u => ?_)
    simp only [id]; ring
  have h2 := (Real.continuous_sqrt.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp h1)
  simp only [Real.sqrt_zero] at h2
  exact h2

/-- **`Ξ` is negligible against the charge transform at high frequency.** -/
theorem XiC_le_eps_thetaGroupXi_one {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℝ, 0 < U ∧ ∀ u : ℝ, U ≤ u →
      (thetaGroupXi 1 (u : ℂ)).re < 0 ∧ ‖XiC (u : ℂ)‖ ≤ ε * ‖thetaGroupXi 1 (u : ℂ)‖ := by
  obtain ⟨U₀, hU₀, hlaw⟩ := cuspCharge_law
  set K : ℝ := 2 ^ 16 * 3000000 * 3628800 with hK
  have hKpos : 0 < K := by positivity
  have hev : ∀ᶠ u in atTop, chT u < ε / K :=
    tendsto_chT_atTop.eventually (gt_mem_nhds (by positivity))
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp hev
  refine ⟨max U₀ U₁, lt_of_lt_of_le hU₀ (le_max_left _ _), fun u hu => ?_⟩
  obtain ⟨hneg, hbd⟩ := hlaw u (le_trans (le_max_left _ _) hu)
  refine ⟨hneg, le_trans hbd ?_⟩
  have ht := hU₁ u (le_trans (le_max_right _ _) hu)
  have hu0 : 0 < u := lt_of_lt_of_le hU₀ (le_trans (le_max_left _ _) hu)
  have htpos := chT_pos hu0
  have : K * chT u ≤ ε := by rw [lt_div_iff₀ hKpos] at ht; linarith
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

end RHTower
