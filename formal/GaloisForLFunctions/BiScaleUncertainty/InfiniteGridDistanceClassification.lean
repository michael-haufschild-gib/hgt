import GaloisForLFunctions.BiScaleUncertainty.LogarithmicGridDistance

/-!
# Separated polar copies: exact center classification and distance cost

Nearest-grid pinning forces a correlation zero at the actual grid distance. Exact-node
centers are impossible. At every off-grid center a compressed smooth seed realizes all
grid zeros and exact polar balance with logarithmic cost in the reciprocal distance.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem subtractCopy_near_tail_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {D T a x : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ y, D < |y| → autocorr f y = 0) (hT : D + 1 < T)
    (ha : a ≠ 0) (hx : |x - T| ≤ 1) (hz : autocorr (subtractCopy f a T) x = 0) :
    autocorr f |x - T| = 0 := by
  have hxlo := (abs_le.mp hx).1
  have hx0 : autocorr f x = 0 := hsupp x
    (lt_of_lt_of_le (by linarith : D < x) (le_abs_self x))
  have hxp : autocorr f (x + T) = 0 := hsupp _
    (lt_of_lt_of_le (by linarith : D < x + T) (le_abs_self _))
  rw [autocorr_subtractCopy hf hfc, hx0, hxp, mul_zero, add_zero, zero_sub] at hz
  have hprod : a * autocorr f (x - T) = 0 := by linarith
  have hbase := (mul_eq_zero.mp hprod).resolve_left ha
  by_cases hxT : 0 ≤ x - T
  · rwa [abs_of_nonneg hxT]
  · rw [abs_of_neg (lt_of_not_ge hxT), autocorr_neg]
    exact hbase

/-- The nearest grid sample creates a genuine zero at its distance from the center. -/
theorem subtractCopy_infinite_grid_distance_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {D T a : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 < T) (hT2 : 2 ≤ T)
    (ha : a ≠ 0) (hgrid : ∀ n : ℕ, 2 ≤ n → autocorr (subtractCopy f a T) (Real.log (n : ℝ)) = 0) :
    autocorr f (logarithmicGridDistance T) = 0 := by
  obtain ⟨n, hn, hd⟩ := exists_logarithmicGridDistance_node hT2
  have hx : |Real.log (n : ℝ) - T| ≤ 1 := by rw [hd]; exact logarithmicGridDistance_le_one hT2
  have hz := subtractCopy_near_tail_zero hf hfc hD hsupp hT ha hx (hgrid n hn)
  rwa [hd] at hz

/-- No separated nonzero two-copy source can place its center on a grid node. -/
theorem subtractCopy_infinite_grid_center_off_grid {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {D T a : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 < T) (hT2 : 2 ≤ T)
    (ha : a ≠ 0) (hgrid : ∀ n : ℕ, 2 ≤ n → autocorr (subtractCopy f a T) (Real.log (n : ℝ)) = 0) :
    0 < logarithmicGridDistance T := by
  have hz := subtractCopy_infinite_grid_distance_zero hf hfc hD hsupp hT hT2 ha hgrid
  have hn := logarithmicGridDistance_nonneg hT2
  by_contra hp
  have heq : logarithmicGridDistance T = 0 := le_antisymm (le_of_not_gt hp) hn
  rw [heq] at hz
  linarith

/-- Every admissible separated copy pays the nearest-node logarithmic cost, as does its seed. -/
theorem subtractCopy_infinite_grid_distance_energy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {D T a : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 < T) (hT2 : 2 ≤ T)
    (ha : a ≠ 0) (hgrid : ∀ n : ℕ, 2 ≤ n → autocorr (subtractCopy f a T) (Real.log (n : ℝ)) = 0) :
    0 < logarithmicGridDistance T ∧
      Real.exp (-(1 / 2 : ℝ)) / 4 * (-Real.log (logarithmicGridDistance T)) ≤ normalizedArchEnergy f ∧
      Real.exp (-(1 / 2 : ℝ)) / 4 * (-Real.log (logarithmicGridDistance T)) ≤
        normalizedArchEnergy (subtractCopy f a T) := by
  have hd := subtractCopy_infinite_grid_center_off_grid hf.continuous hfc hR hD hsupp hT hT2 ha hgrid
  have hd1 := logarithmicGridDistance_le_one hT2
  have hz := subtractCopy_infinite_grid_distance_zero hf.continuous hfc hD hsupp hT hT2 ha hgrid
  have hzg : autocorr (subtractCopy f a T) (logarithmicGridDistance T) = 0 := by
    rw [autocorr_subtractCopy_local hf.continuous hfc hsupp hT
      (by rwa [abs_of_pos hd] : |logarithmicGridDistance T| ≤ 1), hz, mul_zero]
  have hRg : 0 < autocorr (subtractCopy f a T) 0 := by
    rw [autocorr_subtractCopy_local hf.continuous hfc hsupp hT (by norm_num : |(0 : ℝ)| ≤ 1)]
    exact mul_pos (by positivity) hR
  refine ⟨hd, ?_, ?_⟩
  · have h := autocorr_increment_mul_log_le hf hfc hd hd1
    rw [hz, sub_zero] at h
    unfold normalizedArchEnergy
    apply (le_div_iff₀ hR).mpr
    nlinarith
  · have h := autocorr_increment_mul_log_le (contDiff_subtractCopy hf a T)
      (hasCompactSupport_subtractCopy hfc a T) hd hd1
    rw [hzg, sub_zero] at h
    unfold normalizedArchEnergy
    apply (le_div_iff₀ hRg).mpr
    nlinarith

theorem polarCopy_grid_zero_of_distance_support {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {T : ℝ} (hT : 2 ≤ T) (hd : 0 < logarithmicGridDistance T)
    (hsupp : ∀ x, logarithmicGridDistance T / 4 < |x| → autocorr f x = 0) :
    ∀ n : ℕ, 2 ≤ n → autocorr (polarCopy f T) (Real.log (n : ℝ)) = 0 := by
  intro n hn
  have hd1 := logarithmicGridDistance_le_one hT
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogn : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := hlog2.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hz0 : autocorr f (Real.log (n : ℝ)) = 0 := hsupp _
    (lt_of_lt_of_le (by linarith) (le_abs_self _))
  have hdist := logarithmicGridDistance_le_node (T := T) hn
  have hzm : autocorr f (Real.log (n : ℝ) - T) = 0 := hsupp _ (by linarith)
  have hzp : autocorr f (Real.log (n : ℝ) + T) = 0 := hsupp _
    (lt_of_lt_of_le (by linarith) (le_abs_self _))
  rw [polarCopy, autocorr_subtractCopy hf hfc, hz0, hzm, hzp]
  ring

/-- At every off-grid center, actual smooth compact polar sources attain logarithmic distance cost. -/
theorem exists_smooth_polar_source_at_off_grid_center :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → (∀ n : ℕ, 2 ≤ n → T ≠ Real.log (n : ℝ)) →
      ∃ k : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) k ∧ HasCompactSupport k ∧
        0 < autocorr k 0 ∧ (∀ x, (1 / 2 : ℝ) < |x| → autocorr k x = 0) ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) (polarCopy k T) ∧ HasCompactSupport (polarCopy k T) ∧
        0 < autocorr (polarCopy k T) 0 ∧
        (∫ x in Ioi 0, autocorr (polarCopy k T) x * Real.cosh (x / 2)) = 0 ∧
        (∀ n : ℕ, 2 ≤ n → autocorr (polarCopy k T) (Real.log (n : ℝ)) = 0) ∧
        Real.exp (-(1 / 2 : ℝ)) / 4 * (-Real.log (logarithmicGridDistance T)) ≤
          normalizedArchEnergy (polarCopy k T) ∧
        normalizedArchEnergy (polarCopy k T) ≤ C - Real.log (logarithmicGridDistance T) := by
  obtain ⟨f, hf, hfc, hR⟩ := exists_smooth_compact_source_positive_mass
  have hr : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  obtain ⟨D, hD, hsupp⟩ := exists_pos_autocorr_support_radius hfc
  obtain ⟨A, hA⟩ := exists_sourceRescale_logarithmic_energy_bound_of_support
    (hf.of_le hr) hfc hR hD hsupp
  let P := polarEnergyErrorConstant f 1
  have hP : 0 ≤ P := by
    have he : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    dsimp [P, polarEnergyErrorConstant]
    exact div_nonneg (mul_nonneg (by positivity) (integral_nonneg fun x => abs_nonneg _))
      (mul_nonneg hR.le (by linarith))
  refine ⟨A + Real.log (4 * (D + 1)) + P, ?_⟩
  intro T hT hoff
  have hd := (logarithmicGridDistance_pos_iff hT).mpr hoff
  have hd1 := logarithmicGridDistance_le_one hT
  let d := logarithmicGridDistance T
  let L := 4 * (D + 1) / d
  let k := sourceRescale f L
  have hd0 : 0 < d := hd
  have hL : 0 < L := by dsimp [L]; positivity
  have hL1 : 1 ≤ L := by
    dsimp [L]
    apply (le_div_iff₀ hd0).mpr
    dsimp [d]
    linarith
  have hDL : D ≤ L := by
    dsimp [L]
    apply (le_div_iff₀ hd0).mpr
    have hh := mul_le_mul_of_nonneg_left hd1 hD.le
    change D * d ≤ D * 1 at hh
    nlinarith
  have hk := contDiff_sourceRescale hf L
  have hkc := hasCompactSupport_sourceRescale hfc hL
  have hkR : 0 < autocorr k 0 := by
    dsimp [k]
    rw [autocorr_sourceRescale f hL, mul_zero]
    positivity
  have hks : ∀ x, d / 4 < |x| → autocorr k x = 0 := by
    intro x hx
    dsimp [k]
    rw [autocorr_sourceRescale f hL, hsupp, mul_zero]
    rw [abs_mul, abs_of_pos hL]
    have hm := mul_lt_mul_of_pos_left hx hL
    have heq : L * (d / 4) = D + 1 := by dsimp [L]; field_simp
    rw [heq] at hm
    linarith
  have hksHalf : ∀ x, (1 / 2 : ℝ) < |x| → autocorr k x = 0 := by
    intro x hx
    apply hks x
    change d ≤ 1 at hd1
    linarith
  have hgrid := polarCopy_grid_zero_of_distance_support hk.continuous hkc hT hd hks
  have hgR : 0 < autocorr (polarCopy k T) 0 := by
    rw [polarCopy, autocorr_subtractCopy_local hk.continuous hkc hksHalf
      (show (1 / 2 : ℝ) + 0 < T by linarith) (by simp : |(0 : ℝ)| ≤ 0)]
    exact mul_pos (by positivity) hkR
  refine ⟨k, hk, hkc, hkR, hksHalf, contDiff_subtractCopy hk _ _,
    hasCompactSupport_subtractCopy hkc _ _, hgR,
    integral_polarCopy_autocorr_cosh (hk.of_le hr) hkc T, hgrid, ?_, ?_⟩
  · exact (subtractCopy_infinite_grid_distance_energy (hk.of_le hr) hkc hkR
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hksHalf
      (show (1 / 2 : ℝ) + 1 < T by linarith) hT (Real.exp_pos (-T / 2)).ne' hgrid).2.2
  · have hks1 : ∀ x, (1 : ℝ) < |x| → autocorr k x = 0 := fun x hx => hksHalf x (by linarith)
    have herr := normalizedArchEnergy_polarCopy_error (hk.of_le hr) hkc hkR hks1
      (show (1 : ℝ) + 1 ≤ T by linarith)
    have hPk : polarEnergyErrorConstant k 1 = L⁻¹ * P := polarEnergyErrorConstant_sourceRescale f hL 1
    rw [hPk] at herr
    have herrP : L⁻¹ * P * Real.exp (-T) ≤ P := by
      calc
        _ ≤ (1 : ℝ) * P * 1 := mul_le_mul
          (mul_le_mul_of_nonneg_right ((inv_le_one₀ hL).mpr hL1) hP)
          (Real.exp_le_one_iff.mpr (by linarith)) (Real.exp_pos _).le (by simpa using hP)
        _ = _ := by ring
    have hl : Real.log L = Real.log (4 * (D + 1)) - Real.log d := by
      exact Real.log_div (by positivity) hd0.ne'
    have he := (le_abs_self _).trans (herr.trans herrP)
    have hc := hA L hL hDL
    rw [hl] at hc
    change normalizedArchEnergy k ≤ A + (Real.log (4 * (D + 1)) - Real.log d) at hc
    change normalizedArchEnergy (polarCopy k T) ≤ _ - Real.log d
    linarith

/-- Exact existence classification within the uniformly separated smooth two-copy class. -/
theorem exists_smooth_separated_polar_grid_source_iff {T : ℝ} (hT : 2 ≤ T) :
    (∃ k : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) k ∧ HasCompactSupport k ∧
      0 < autocorr k 0 ∧ (∀ x, (1 / 2 : ℝ) < |x| → autocorr k x = 0) ∧
      ∀ n : ℕ, 2 ≤ n → autocorr (polarCopy k T) (Real.log (n : ℝ)) = 0) ↔
      ∀ n : ℕ, 2 ≤ n → T ≠ Real.log (n : ℝ) := by
  constructor
  · rintro ⟨k, hk, hkc, hR, hsupp, hgrid⟩
    apply (logarithmicGridDistance_pos_iff hT).mp
    exact subtractCopy_infinite_grid_center_off_grid hk.continuous hkc hR
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hsupp (by linarith) hT (Real.exp_pos (-T / 2)).ne' hgrid
  · intro hoff
    obtain ⟨C, hC⟩ := exists_smooth_polar_source_at_off_grid_center
    obtain ⟨k, hk, hkc, hR, hsupp, _, _, _, _, hgrid, _, _⟩ := hC T hT hoff
    exact ⟨k, hk, hkc, hR, hsupp, hgrid⟩

end

end GaloisForLFunctions.BiScaleUncertainty
