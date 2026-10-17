import GaloisForLFunctions.BiScaleUncertainty.FiniteTrainActiveLags

/-!
# Exact infinite-grid feasibility of finite common-seed trains

Only active positive correlation lags must avoid the grid. The converse constructs a
smooth compact seed by dilation, and inherits polar balance from the finite symbol.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def CopyTrainGridCompatible {m : ℕ} (c : Fin (m + 1) → ℝ) (S : ℝ) : Prop :=
  ∀ k : ℤ, 1 ≤ k → k ≤ (m : ℤ) → copyTrainLagCoefficient c k ≠ 0 →
    ∀ n : ℕ, 2 ≤ n → (k : ℝ) * S ≠ Real.log (n : ℝ)

theorem copyTrain_grid_compatible_of_zeros {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {m : ℕ} {c : Fin (m + 1) → ℝ} {D S : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hS : D + 1 < S)
    (hgrid : ∀ n : ℕ, 2 ≤ n → autocorr (copyTrain f c S) (Real.log (n : ℝ)) = 0) :
    CopyTrainGridCompatible c S := by
  intro k hk1 hkm hA n hn heq
  have hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    simp only [Finset.mem_Icc]
    omega
  have h := autocorr_copyTrain_near_lag hf hfc c hD hsupp hS hk
    (show |Real.log (n : ℝ) - (k : ℝ) * S| ≤ 1 by rw [← heq]; simp)
  rw [hgrid n hn, ← heq, sub_self] at h
  exact (mul_ne_zero hA hR.ne') h.symm

/-- Every active lag imposes its own nearest-grid energy cost, including interior lags. -/
theorem copyTrain_active_lag_energy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {m : ℕ} {c : Fin (m + 1) → ℝ} (hc : ∃ i, c i ≠ 0) {D S : ℝ}
    (hD : 0 ≤ D) (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hS : D + 1 < S)
    {k : ℤ} (hk : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ))
    (hA : copyTrainLagCoefficient c k ≠ 0) (hT : 2 ≤ (k : ℝ) * S)
    (hgrid : ∀ n : ℕ, 2 ≤ n → autocorr (copyTrain f c S) (Real.log (n : ℝ)) = 0) :
    0 < logarithmicGridDistance ((k : ℝ) * S) ∧
      Real.exp (-(1 / 2 : ℝ)) / 4 * (-Real.log (logarithmicGridDistance ((k : ℝ) * S))) ≤
        normalizedArchEnergy f ∧
      Real.exp (-(1 / 2 : ℝ)) / 4 * (-Real.log (logarithmicGridDistance ((k : ℝ) * S))) ≤
        normalizedArchEnergy (copyTrain f c S) := by
  obtain ⟨n, hn, hd⟩ := exists_logarithmicGridDistance_node hT
  have hd1 := logarithmicGridDistance_le_one hT
  have h := autocorr_copyTrain_near_lag hf.continuous hfc c hD hsupp hS hk
    (show |Real.log (n : ℝ) - (k : ℝ) * S| ≤ 1 by rwa [hd])
  rw [hgrid n hn] at h
  have hz := (mul_eq_zero.mp h.symm).resolve_left hA
  have hzabs : autocorr f |Real.log (n : ℝ) - (k : ℝ) * S| = 0 := by
    by_cases hp : 0 ≤ Real.log (n : ℝ) - (k : ℝ) * S
    · rwa [abs_of_nonneg hp]
    · rw [abs_of_neg (lt_of_not_ge hp), autocorr_neg]
      exact hz
  rw [hd] at hzabs
  have hd0 : 0 < logarithmicGridDistance ((k : ℝ) * S) := by
    by_contra hp
    have heq := le_antisymm (le_of_not_gt hp) (logarithmicGridDistance_nonneg hT)
    rw [heq] at hzabs
    linarith
  have hzg : autocorr (copyTrain f c S) (logarithmicGridDistance ((k : ℝ) * S)) = 0 := by
    rw [autocorr_copyTrain_local hf.continuous hfc c hD hsupp hS
      (by rwa [abs_of_pos hd0] : |logarithmicGridDistance ((k : ℝ) * S)| ≤ 1), hzabs, mul_zero]
  have hRg : 0 < autocorr (copyTrain f c S) 0 := by
    rw [autocorr_copyTrain_local hf.continuous hfc c hD hsupp hS (by norm_num : |(0 : ℝ)| ≤ 1)]
    exact mul_pos (copyTrainMass_pos_of_exists hc) hR
  refine ⟨hd0, ?_, ?_⟩
  · have hb := autocorr_increment_mul_log_le hf hfc hd0 hd1
    rw [hzabs, sub_zero] at hb
    unfold normalizedArchEnergy
    apply (le_div_iff₀ hR).mpr
    nlinarith
  · have hb := autocorr_increment_mul_log_le (contDiff_copyTrain hf c S)
      (hasCompactSupport_copyTrain hfc c S) hd0 hd1
    rw [hzg, sub_zero] at hb
    unfold normalizedArchEnergy
    apply (le_div_iff₀ hRg).mpr
    nlinarith

private theorem exists_positive_finite_radius {ι : Type*} (s : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 < d i) : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ ∀ i ∈ s, ρ < d i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1 / 4, by norm_num, le_rfl, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨ρ, hρ, hρ1, hρd⟩ := ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    have hda := hd a (Finset.mem_insert_self a s)
    refine ⟨min ρ (d a / 2), lt_min_iff.mpr ⟨hρ, by positivity⟩,
      (min_le_left _ _).trans hρ1, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    · exact lt_of_le_of_lt (min_le_left _ _) (hρd i hi)

theorem exists_smooth_compact_source_small_correlation_support {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      0 < autocorr f 0 ∧ ∀ x, ρ < |x| → autocorr f x = 0 := by
  obtain ⟨f, hf, hfc, hR⟩ := exists_smooth_compact_source_positive_mass
  obtain ⟨D, hD, hsupp⟩ := exists_pos_autocorr_support_radius hfc
  let L := (D + 1) / ρ
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨sourceRescale f L, contDiff_sourceRescale hf L,
    hasCompactSupport_sourceRescale hfc hL, ?_, ?_⟩
  · rw [autocorr_sourceRescale f hL, mul_zero]
    positivity
  · intro x hx
    rw [autocorr_sourceRescale f hL, hsupp, mul_zero]
    rw [abs_mul, abs_of_pos hL]
    have hm := mul_lt_mul_of_pos_left hx hL
    have heq : L * ρ = D + 1 := by dsimp [L]; field_simp
    rw [heq] at hm
    linarith

/-- Every compatible finite coefficient pattern is realized by an actual smooth compact seed. -/
theorem exists_smooth_copyTrain_grid_source {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hc : ∃ i, c i ≠ 0) {S : ℝ} (hS : 2 ≤ S) (hoff : CopyTrainGridCompatible c S) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      0 < autocorr f 0 ∧ (∀ x, (1 / 2 : ℝ) < |x| → autocorr f x = 0) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (copyTrain f c S) ∧ HasCompactSupport (copyTrain f c S) ∧
      0 < autocorr (copyTrain f c S) 0 ∧
      (∀ n : ℕ, 2 ≤ n → autocorr (copyTrain f c S) (Real.log (n : ℝ)) = 0) ∧
      (copyTrainExpSymbol c S (1 / 2) = 0 →
        (∫ x in Ioi 0, autocorr (copyTrain f c S) x * Real.cosh (x / 2)) = 0) := by
  classical
  let active := (Finset.Icc (1 : ℤ) (m : ℤ)).filter (fun k => copyTrainLagCoefficient c k ≠ 0)
  have hcenter (k : ℤ) (hk : 1 ≤ k) : 2 ≤ (k : ℝ) * S := by
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hm := mul_le_mul_of_nonneg_right hkR (show 0 ≤ S by linarith)
    nlinarith
  have hd : ∀ k ∈ active, 0 < logarithmicGridDistance ((k : ℝ) * S) := by
    intro k hk
    obtain ⟨hk, hA⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
    exact (logarithmicGridDistance_pos_iff (hcenter k hk1)).mpr (hoff k hk1 hkm hA)
  obtain ⟨ρ, hρ, hρ1, hρd⟩ := exists_positive_finite_radius active
    (fun k => logarithmicGridDistance ((k : ℝ) * S)) hd
  obtain ⟨f, hf, hfc, hR, hsupp⟩ := exists_smooth_compact_source_small_correlation_support hρ
  have hsHalf : ∀ x, (1 / 2 : ℝ) < |x| → autocorr f x = 0 :=
    fun x hx => hsupp x (by linarith)
  have hRg : 0 < autocorr (copyTrain f c S) 0 := by
    rw [autocorr_copyTrain_local hf.continuous hfc c (by norm_num : (0 : ℝ) ≤ 1 / 2)
      hsHalf (by linarith : (1 / 2 : ℝ) + 1 < S) (by norm_num : |(0 : ℝ)| ≤ 1)]
    exact mul_pos (copyTrainMass_pos_of_exists hc) hR
  refine ⟨f, hf, hfc, hR, hsHalf, contDiff_copyTrain hf c S,
    hasCompactSupport_copyTrain hfc c S, hRg, ?_, ?_⟩
  · intro n hn
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    have hlogn : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := hlog2.trans
      (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
    rw [autocorr_copyTrain_grouped hf.continuous hfc]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hA : copyTrainLagCoefficient c k = 0
    · rw [hA, zero_mul]
    · have hz : autocorr f (Real.log (n : ℝ) - (k : ℝ) * S) = 0 := by
        by_cases hk1 : 1 ≤ k
        · have hka : k ∈ active := Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hk1, (Finset.mem_Icc.mp hk).2⟩, hA⟩
          exact hsupp _ ((hρd k hka).trans_le (logarithmicGridDistance_le_node hn))
        · have hk0 : (k : ℝ) ≤ 0 := by exact_mod_cast (show k ≤ 0 by omega)
          have hm := mul_nonpos_of_nonpos_of_nonneg hk0 (show 0 ≤ S by linarith)
          exact hsupp _ (lt_of_lt_of_le (by linarith) (le_abs_self _))
      rw [hz, mul_zero]
  · intro hB
    have hr : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
      WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
    exact integral_copyTrain_autocorr_cosh_of_symbol_zero (hf.of_le hr) hfc c S hB

/-- Exact infinite-grid classification; zero interior coefficients remove their entire restriction. -/
theorem exists_smooth_copyTrain_grid_source_iff {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hc : ∃ i, c i ≠ 0) {S : ℝ} (hS : 2 ≤ S) :
    (∃ f : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      0 < autocorr f 0 ∧ (∀ x, (1 / 2 : ℝ) < |x| → autocorr f x = 0) ∧
      0 < autocorr (copyTrain f c S) 0 ∧
      ∀ n : ℕ, 2 ≤ n → autocorr (copyTrain f c S) (Real.log (n : ℝ)) = 0) ↔
      CopyTrainGridCompatible c S := by
  constructor
  · rintro ⟨f, hf, hfc, hR, hsupp, _, hgrid⟩
    exact copyTrain_grid_compatible_of_zeros hf.continuous hfc hR
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hsupp (by linarith) hgrid
  · intro hoff
    obtain ⟨f, hf, hfc, hR, hsupp, _, _, hRg, hgrid, _⟩ :=
      exists_smooth_copyTrain_grid_source c hc hS hoff
    exact ⟨f, hf, hfc, hR, hsupp, hRg, hgrid⟩

end

end GaloisForLFunctions.BiScaleUncertainty
