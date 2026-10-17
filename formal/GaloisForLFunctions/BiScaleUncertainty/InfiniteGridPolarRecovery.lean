import GaloisForLFunctions.BiScaleUncertainty.LogarithmicCompressionEnergy

/-!
# Actual smooth polar sources on the entire logarithmic grid

Compress a fixed smooth source and place its polar copy at a logarithmic midpoint.
Every grid node misses all three correlation packets. Compression and the polar-copy
error estimate give a linear upper energy bound; the tail-rigidity theorem gives a
linear lower bound. The final existence theorem has no analytic interface assumptions.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def logarithmicMidpoint (N : ℕ) : ℝ := (Real.log (N : ℝ) + Real.log ((N : ℝ) + 1)) / 2

theorem reciprocal_le_logarithmic_gap {N : ℕ} (hN : 1 ≤ N) :
    1 / ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) := by
  have hp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < ((N : ℝ) + 1) / N by positivity)
  rw [Real.log_div (by positivity) hp.ne'] at h
  have heq : 1 - (((N : ℝ) + 1) / N)⁻¹ = 1 / ((N : ℝ) + 1) := by
    field_simp; ring
  rwa [heq] at h

theorem logarithmicMidpoint_distance {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    1 / (2 * ((N : ℝ) + 1)) ≤ |Real.log (n : ℝ) - logarithmicMidpoint N| := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hgap := reciprocal_le_logarithmic_gap hN
  have hh : 1 / (2 * ((N : ℝ) + 1)) = (1 / ((N : ℝ) + 1)) / 2 := by field_simp
  rw [hh]
  by_cases hnN : n ≤ N
  · have hl := Real.log_le_log hnp (show (n : ℝ) ≤ N by exact_mod_cast hnN)
    have hab := neg_le_abs (Real.log (n : ℝ) - logarithmicMidpoint N)
    dsimp [logarithmicMidpoint] at hab ⊢
    linarith
  · have hnN' : N + 1 ≤ n := by omega
    have hl := Real.log_le_log (show 0 < (N : ℝ) + 1 by positivity)
      (show (N : ℝ) + 1 ≤ n by exact_mod_cast hnN')
    have hab := le_abs_self (Real.log (n : ℝ) - logarithmicMidpoint N)
    dsimp [logarithmicMidpoint] at hab ⊢
    linarith

theorem log_le_logarithmicMidpoint {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N : ℝ) ≤ logarithmicMidpoint N := by
  have hp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h := Real.log_le_log hp (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith)
  dsimp [logarithmicMidpoint]
  linarith

theorem log_succ_le_logarithmicMidpoint {N : ℕ} (hN : 1 ≤ N) :
    Real.log ((N : ℝ) + 1) ≤ Real.log 2 + logarithmicMidpoint N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := Real.log_le_log (show 0 < (N : ℝ) + 1 by positivity)
    (show (N : ℝ) + 1 ≤ 2 * N by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at h
  linarith [log_le_logarithmicMidpoint hN]

theorem two_le_logarithmicMidpoint {N : ℕ} (hN : ⌈Real.exp 2⌉₊ ≤ N) :
    2 ≤ logarithmicMidpoint N := by
  have he : Real.exp 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hp : 0 < (N : ℝ) := (Real.exp_pos _).trans_le he
  have hN1 : 1 ≤ N := by
    have : 0 < N := by exact_mod_cast hp
    omega
  have hl := Real.log_le_log (Real.exp_pos 2) he
  rw [Real.log_exp] at hl
  exact hl.trans (log_le_logarithmicMidpoint hN1)

theorem exists_arbitrarily_large_logarithmicMidpoint (B : ℝ) :
    ∃ N : ℕ, ⌈Real.exp 2⌉₊ ≤ N ∧ B ≤ logarithmicMidpoint N := by
  let N := max ⌈Real.exp 2⌉₊ ⌈Real.exp B⌉₊
  have hN0 : ⌈Real.exp 2⌉₊ ≤ N := le_max_left _ _
  have he : Real.exp B ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈Real.exp B⌉₊ ≤ N from le_max_right _ _))
  have hp : 0 < (N : ℝ) := (Real.exp_pos _).trans_le he
  have hN1 : 1 ≤ N := by
    have : 0 < N := by exact_mod_cast hp
    omega
  have hl := Real.log_le_log (Real.exp_pos B) he
  rw [Real.log_exp] at hl
  exact ⟨N, hN0, hl.trans (log_le_logarithmicMidpoint hN1)⟩

/-- A support packet strictly narrower than the midpoint gap misses the whole grid. -/
theorem polarCopy_logarithmicMidpoint_grid_zero {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {N : ℕ}
    (hN : 1 ≤ N) (hT : 2 ≤ logarithmicMidpoint N)
    (hsupp : ∀ x, 1 / (8 * ((N : ℝ) + 1)) < |x| → autocorr f x = 0) :
    ∀ n : ℕ, 2 ≤ n → autocorr (polarCopy f (logarithmicMidpoint N)) (Real.log (n : ℝ)) = 0 := by
  intro n hn
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hρ : 1 / (8 * ((N : ℝ) + 1)) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 8 * ((N : ℝ) + 1))).mpr
    linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogn : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := hlog2.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hz0 : autocorr f (Real.log (n : ℝ)) = 0 := hsupp _
    (by rw [abs_of_nonneg (by linarith : 0 ≤ Real.log (n : ℝ))]; linarith)
  have hdist := logarithmicMidpoint_distance hN (show 1 ≤ n by omega)
  have hρgap : 1 / (8 * ((N : ℝ) + 1)) < 1 / (2 * ((N : ℝ) + 1)) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith
  have hzm : autocorr f (Real.log (n : ℝ) - logarithmicMidpoint N) = 0 :=
    hsupp _ (hρgap.trans_le hdist)
  have hzp : autocorr f (Real.log (n : ℝ) + logarithmicMidpoint N) = 0 := hsupp _ (by
    rw [abs_of_nonneg (by linarith : 0 ≤ Real.log (n : ℝ) + logarithmicMidpoint N)]
    linarith)
  rw [polarCopy, autocorr_subtractCopy hf hfc, hz0, hzm, hzp]
  ring

theorem sourceRescale_midpoint_support {f : ℝ → ℝ} {D : ℝ} (hD : 0 < D)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (N : ℕ) :
    ∀ x, 1 / (8 * ((N : ℝ) + 1)) < |x| →
      autocorr (sourceRescale f (8 * (D + 1) * ((N : ℝ) + 1))) x = 0 := by
  intro x hx
  have hL : 0 < 8 * (D + 1) * ((N : ℝ) + 1) := by positivity
  rw [autocorr_sourceRescale f hL, hsupp, mul_zero]
  rw [abs_mul, abs_of_pos hL]
  have hh := mul_lt_mul_of_pos_left hx hL
  have heq : (8 * (D + 1) * ((N : ℝ) + 1)) * (1 / (8 * ((N : ℝ) + 1))) = D + 1 := by
    field_simp
  rw [heq] at hh
  linarith

/-- Nonvacuity and order-sharpness of infinite-grid tail rigidity, for actual smooth sources. -/
theorem exists_smooth_infinite_grid_polar_recovery :
    ∃ C : ℝ, ∀ N : ℕ, ⌈Real.exp 2⌉₊ ≤ N →
      ∃ k : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) k ∧ HasCompactSupport k ∧
        0 < autocorr k 0 ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) (polarCopy k (logarithmicMidpoint N)) ∧
        HasCompactSupport (polarCopy k (logarithmicMidpoint N)) ∧
        0 < autocorr (polarCopy k (logarithmicMidpoint N)) 0 ∧
        (∫ x in Ioi 0, autocorr (polarCopy k (logarithmicMidpoint N)) x * Real.cosh (x / 2)) = 0 ∧
        (∀ n : ℕ, 2 ≤ n → autocorr (polarCopy k (logarithmicMidpoint N)) (Real.log (n : ℝ)) = 0) ∧
        Real.exp (-(1 / 2 : ℝ)) / 4 * logarithmicMidpoint N ≤
          normalizedArchEnergy (polarCopy k (logarithmicMidpoint N)) ∧
        normalizedArchEnergy (polarCopy k (logarithmicMidpoint N)) ≤ C + logarithmicMidpoint N := by
  obtain ⟨f, hf, hfc, hR⟩ := exists_smooth_compact_source_positive_mass
  have hr : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hf2 := hf.of_le hr
  obtain ⟨D, hD, hsupp⟩ := exists_pos_autocorr_support_radius hfc
  obtain ⟨A, hA⟩ := exists_sourceRescale_logarithmic_energy_bound_of_support hf2 hfc hR hD hsupp
  let P := polarEnergyErrorConstant f 1
  have hP : 0 ≤ P := by
    have he : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    dsimp [P, polarEnergyErrorConstant]
    exact div_nonneg (mul_nonneg (by positivity) (integral_nonneg fun x => abs_nonneg _))
      (mul_nonneg hR.le (by linarith))
  refine ⟨A + Real.log (8 * (D + 1)) + Real.log 2 + P, ?_⟩
  intro N hN0
  have hT := two_le_logarithmicMidpoint hN0
  have hN : 1 ≤ N := by
    have he : 0 < (N : ℝ) := (Real.exp_pos 2).trans_le
      ((Nat.le_ceil _).trans (by exact_mod_cast hN0))
    have : 0 < N := by exact_mod_cast he
    omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let L := 8 * (D + 1) * ((N : ℝ) + 1)
  let ρ := 1 / (8 * ((N : ℝ) + 1))
  let k := sourceRescale f L
  have hL1 : 1 ≤ L := by dsimp [L]; nlinarith
  have hL : 0 < L := by linarith
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρhalf : ρ < (1 / 2 : ℝ) := by
    dsimp [ρ]
    apply (div_lt_iff₀ (by positivity : 0 < 8 * ((N : ℝ) + 1))).mpr
    linarith
  have hk := contDiff_sourceRescale hf L
  have hkc := hasCompactSupport_sourceRescale hfc hL
  have hkR : 0 < autocorr k 0 := by
    dsimp [k]
    rw [autocorr_sourceRescale f hL, mul_zero]
    positivity
  have hks : ∀ x, ρ < |x| → autocorr k x = 0 := sourceRescale_midpoint_support hD hsupp N
  have hgrid := polarCopy_logarithmicMidpoint_grid_zero hk.continuous hkc hN hT hks
  have hmass : autocorr (polarCopy k (logarithmicMidpoint N)) 0 =
      (1 + (Real.exp (-logarithmicMidpoint N / 2)) ^ 2) * autocorr k 0 := by
    exact autocorr_subtractCopy_local hk.continuous hkc hks
      (show ρ + 0 < logarithmicMidpoint N by linarith) (by simp : |(0 : ℝ)| ≤ 0) _
  have hgR : 0 < autocorr (polarCopy k (logarithmicMidpoint N)) 0 := by
    rw [hmass]
    exact mul_pos (by positivity) hkR
  refine ⟨k, hk, hkc, hkR, contDiff_subtractCopy hk _ _,
    hasCompactSupport_subtractCopy hkc _ _, hgR,
    integral_polarCopy_autocorr_cosh (hk.of_le hr) hkc _, hgrid, ?_, ?_⟩
  · let kc : C_c(ℝ, ℝ) := ⟨⟨k, hk.continuous⟩, hkc⟩
    have hb := (subtractCopy_zero_linear_energy_cost kc (hk.of_le hr) hρ.le hks
      (show ρ + 1 < logarithmicMidpoint N by linarith)
      (Real.exp_pos (-logarithmicMidpoint N / 2)).ne'
      (hgrid _ (logarithmicCeilNode_ge_two (by linarith)))).2
    change Real.exp (-(1 / 2 : ℝ)) * logarithmicMidpoint N *
      autocorr (polarCopy k (logarithmicMidpoint N)) 0 ≤
      4 * biScaleLevyEnergy (polarCopy k (logarithmicMidpoint N)) at hb
    unfold normalizedArchEnergy
    apply (le_div_iff₀ hgR).mpr
    nlinarith
  · have hks1 : ∀ x, (1 : ℝ) < |x| → autocorr k x = 0 :=
      fun x hx => hks x (by linarith)
    have herr := normalizedArchEnergy_polarCopy_error (hk.of_le hr) hkc hkR hks1
      (show (1 : ℝ) + 1 ≤ logarithmicMidpoint N by linarith)
    have hPk : polarEnergyErrorConstant k 1 = L⁻¹ * P := polarEnergyErrorConstant_sourceRescale f hL 1
    rw [hPk] at herr
    have hexp : Real.exp (-logarithmicMidpoint N) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have herrP : L⁻¹ * P * Real.exp (-logarithmicMidpoint N) ≤ P := by
      calc
        _ ≤ (1 : ℝ) * P * 1 := mul_le_mul
          (mul_le_mul_of_nonneg_right ((inv_le_one₀ hL).mpr hL1) hP) hexp
          (Real.exp_pos _).le (by simpa using hP)
        _ = _ := by ring
    have hlog : Real.log L ≤ Real.log (8 * (D + 1)) + Real.log 2 + logarithmicMidpoint N := by
      dsimp [L]
      rw [Real.log_mul (by positivity) (by positivity)]
      linarith [log_succ_le_logarithmicMidpoint hN]
    have he := (le_abs_self _).trans (herr.trans herrP)
    have hDL : D ≤ L := by dsimp [L]; nlinarith
    have hc := hA L hL hDL
    change normalizedArchEnergy k ≤ A + Real.log L at hc
    linarith

end

end GaloisForLFunctions.BiScaleUncertainty
