import GaloisForLFunctions.BiScaleUncertainty.LocalCorrelationEnergyStability

/-!
# Uniform finite-train energy law in the smallest active grid distance

A single constant works for every compatible finite coefficient pattern and spacing at
least two. The source is a fixed smooth bump compressed below all active grid distances.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def copyTrainActiveLags {m : ℕ} (c : Fin (m + 1) → ℝ) : Finset ℤ := by
  classical
  exact (Finset.Icc (1 : ℤ) (m : ℤ)).filter (fun k => copyTrainLagCoefficient c k ≠ 0)

def copyTrainGridDistances {m : ℕ} (c : Fin (m + 1) → ℝ) (S : ℝ) : Finset ℝ := by
  classical
  exact insert 1 ((copyTrainActiveLags c).image (fun k : ℤ => logarithmicGridDistance ((k : ℝ) * S)))

def copyTrainMinGridDistance {m : ℕ} (c : Fin (m + 1) → ℝ) (S : ℝ) : ℝ :=
  (copyTrainGridDistances c S).min' (by classical simp [copyTrainGridDistances])

theorem mem_copyTrainActiveLags {m : ℕ} {c : Fin (m + 1) → ℝ} {k : ℤ} :
    k ∈ copyTrainActiveLags c ↔ 1 ≤ k ∧ k ≤ (m : ℤ) ∧ copyTrainLagCoefficient c k ≠ 0 := by
  classical
  simp [copyTrainActiveLags, and_assoc]

theorem copyTrainActiveLags_center_ge_two {m : ℕ} {c : Fin (m + 1) → ℝ}
    {S : ℝ} (hS : 2 ≤ S) {k : ℤ} (hk : k ∈ copyTrainActiveLags c) : 2 ≤ (k : ℝ) * S := by
  have hk1 := (mem_copyTrainActiveLags.mp hk).1
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hb := mul_le_mul_of_nonneg_right hkR (show 0 ≤ S by linarith)
  nlinarith

theorem copyTrainMinGridDistance_le_one {m : ℕ} (c : Fin (m + 1) → ℝ) (S : ℝ) :
    copyTrainMinGridDistance c S ≤ 1 := by
  classical
  exact Finset.min'_le _ _ (by simp [copyTrainGridDistances])

theorem copyTrainMinGridDistance_le_active {m : ℕ} {c : Fin (m + 1) → ℝ}
    (S : ℝ) {k : ℤ} (hk : k ∈ copyTrainActiveLags c) :
    copyTrainMinGridDistance c S ≤ logarithmicGridDistance ((k : ℝ) * S) := by
  classical
  apply Finset.min'_le
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨k, hk, rfl⟩

theorem copyTrainMinGridDistance_attained {m : ℕ} (c : Fin (m + 1) → ℝ) (S : ℝ) :
    copyTrainMinGridDistance c S = 1 ∨ ∃ k ∈ copyTrainActiveLags c,
      copyTrainMinGridDistance c S = logarithmicGridDistance ((k : ℝ) * S) := by
  classical
  have hmem := Finset.min'_mem (copyTrainGridDistances c S)
    (by simp [copyTrainGridDistances] : (copyTrainGridDistances c S).Nonempty)
  change copyTrainMinGridDistance c S ∈ insert 1
    ((copyTrainActiveLags c).image (fun k : ℤ => logarithmicGridDistance ((k : ℝ) * S))) at hmem
  rcases Finset.mem_insert.mp hmem with h | h
  · exact Or.inl h
  · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨k, hk, heq.symm⟩

theorem copyTrainMinGridDistance_nonneg {m : ℕ} (c : Fin (m + 1) → ℝ)
    {S : ℝ} (hS : 2 ≤ S) : 0 ≤ copyTrainMinGridDistance c S := by
  rcases copyTrainMinGridDistance_attained c S with h | ⟨k, hk, h⟩
  · rw [h]; norm_num
  · rw [h]
    exact logarithmicGridDistance_nonneg (copyTrainActiveLags_center_ge_two hS hk)

theorem copyTrainMinGridDistance_pos_iff {m : ℕ} (c : Fin (m + 1) → ℝ)
    {S : ℝ} (hS : 2 ≤ S) :
    0 < copyTrainMinGridDistance c S ↔ CopyTrainGridCompatible c S := by
  constructor
  · intro hd k hk1 hkm hA
    have hk := mem_copyTrainActiveLags.mpr ⟨hk1, hkm, hA⟩
    exact (logarithmicGridDistance_pos_iff (copyTrainActiveLags_center_ge_two hS hk)).mp
      (hd.trans_le (copyTrainMinGridDistance_le_active S hk))
  · intro hoff
    rcases copyTrainMinGridDistance_attained c S with h | ⟨k, hk, h⟩
    · rw [h]; norm_num
    · rw [h]
      obtain ⟨hk1, hkm, hA⟩ := mem_copyTrainActiveLags.mp hk
      exact (logarithmicGridDistance_pos_iff (copyTrainActiveLags_center_ge_two hS hk)).mpr
        (hoff k hk1 hkm hA)

/-- The minimum active distance gives the strongest certified lower cost, including empty active sets. -/
theorem copyTrain_min_distance_energy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {m : ℕ}
    {c : Fin (m + 1) → ℝ} (hc : ∃ i, c i ≠ 0) {D S : ℝ}
    (hD : 0 ≤ D) (hsupp : ∀ x, D < |x| → autocorr f x = 0)
    (hS : 2 ≤ S) (hsep : D + 1 < S)
    (hgrid : ∀ n : ℕ, 2 ≤ n → autocorr (copyTrain f c S) (Real.log (n : ℝ)) = 0) :
    0 < copyTrainMinGridDistance c S ∧
      Real.exp (-(1 / 2 : ℝ)) / 4 * (-Real.log (copyTrainMinGridDistance c S)) ≤ normalizedArchEnergy f ∧
      Real.exp (-(1 / 2 : ℝ)) / 4 * (-Real.log (copyTrainMinGridDistance c S)) ≤
        normalizedArchEnergy (copyTrain f c S) := by
  have hd := (copyTrainMinGridDistance_pos_iff c hS).mpr
    (copyTrain_grid_compatible_of_zeros hf.continuous hfc hR hD hsupp hsep hgrid)
  refine ⟨hd, ?_⟩
  rcases copyTrainMinGridDistance_attained c S with h | ⟨k, hk, h⟩
  · rw [h, Real.log_one, neg_zero, mul_zero]
    have hRg : 0 < autocorr (copyTrain f c S) 0 := by
      rw [autocorr_copyTrain_local hf.continuous hfc c hD hsupp hsep (by norm_num : |(0 : ℝ)| ≤ 1)]
      exact mul_pos (copyTrainMass_pos_of_exists hc) hR
    exact ⟨div_nonneg (biScaleLevyEnergy_nonneg hfc hf.continuous) hR.le,
      div_nonneg (biScaleLevyEnergy_nonneg (hasCompactSupport_copyTrain hfc c S)
        (contDiff_copyTrain hf c S).continuous) hRg.le⟩
  · obtain ⟨hk1, hkm, hA⟩ := mem_copyTrainActiveLags.mp hk
    have hki : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [h]
    exact (copyTrain_active_lag_energy hf hfc hR hc hD hsupp hsep hki hA
      (copyTrainActiveLags_center_ge_two hS hk) hgrid).2

theorem copyTrain_grid_zero_of_min_distance_support {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {m : ℕ}
    (c : Fin (m + 1) → ℝ) {S : ℝ} (hS : 2 ≤ S)
    (hd : 0 < copyTrainMinGridDistance c S)
    (hsupp : ∀ x, copyTrainMinGridDistance c S / 4 < |x| → autocorr f x = 0) :
    ∀ n : ℕ, 2 ≤ n → autocorr (copyTrain f c S) (Real.log (n : ℝ)) = 0 := by
  intro n hn
  have hd1 := copyTrainMinGridDistance_le_one c S
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogn : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := hlog2.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  rw [autocorr_copyTrain_grouped hf hfc]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hA : copyTrainLagCoefficient c k = 0
  · rw [hA, zero_mul]
  · have hz : autocorr f (Real.log (n : ℝ) - (k : ℝ) * S) = 0 := by
      by_cases hk1 : 1 ≤ k
      · have hka := mem_copyTrainActiveLags.mpr ⟨hk1, (Finset.mem_Icc.mp hk).2, hA⟩
        have hdk := (copyTrainMinGridDistance_le_active S hka).trans
          (logarithmicGridDistance_le_node hn)
        exact hsupp _ (by linarith)
      · have hk0 : (k : ℝ) ≤ 0 := by exact_mod_cast (show k ≤ 0 by omega)
        have hm := mul_nonpos_of_nonpos_of_nonneg hk0 (show 0 ≤ S by linarith)
        exact hsupp _ (lt_of_lt_of_le (by linarith) (le_abs_self _))
    rw [hz, mul_zero]

/-- One constant controls every finite train pattern; only the smallest active grid distance matters. -/
theorem exists_smooth_copyTrain_uniform_distance_cost :
    ∃ C : ℝ, ∀ m : ℕ, ∀ c : Fin (m + 1) → ℝ, (∃ i, c i ≠ 0) →
      ∀ S : ℝ, 2 ≤ S → CopyTrainGridCompatible c S →
      ∃ f : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
        0 < autocorr f 0 ∧ (∀ x, (1 / 2 : ℝ) < |x| → autocorr f x = 0) ∧
        ContDiff ℝ (↑(⊤ : ℕ∞)) (copyTrain f c S) ∧ HasCompactSupport (copyTrain f c S) ∧
        0 < autocorr (copyTrain f c S) 0 ∧
        (∀ n : ℕ, 2 ≤ n → autocorr (copyTrain f c S) (Real.log (n : ℝ)) = 0) ∧
        Real.exp (-(1 / 2 : ℝ)) / 4 * (-Real.log (copyTrainMinGridDistance c S)) ≤
          normalizedArchEnergy (copyTrain f c S) ∧
        normalizedArchEnergy (copyTrain f c S) ≤ C - Real.log (copyTrainMinGridDistance c S) ∧
        (copyTrainExpSymbol c S (1 / 2) = 0 →
          (∫ x in Ioi 0, autocorr (copyTrain f c S) x * Real.cosh (x / 2)) = 0) := by
  obtain ⟨C₀, hC₀⟩ := exists_smooth_small_support_logarithmic_cost
  refine ⟨C₀ + Real.log 4 + 2 * (∫ x in Ioi (1 : ℝ), archLevySinhWeight x), ?_⟩
  intro m c hc S hS hoff
  let d := copyTrainMinGridDistance c S
  have hd : 0 < d := (copyTrainMinGridDistance_pos_iff c hS).mpr hoff
  have hd1 : d ≤ 1 := copyTrainMinGridDistance_le_one c S
  obtain ⟨f, hf, hfc, hR, hsupp, hE⟩ := hC₀ (d / 4) (by positivity) (by linarith)
  have hr : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hf2 := hf.of_le hr
  have hsHalf : ∀ x, (1 / 2 : ℝ) < |x| → autocorr f x = 0 :=
    fun x hx => hsupp x (by linarith)
  have hgrid := copyTrain_grid_zero_of_min_distance_support hf.continuous hfc c hS hd hsupp
  have hRg : 0 < autocorr (copyTrain f c S) 0 := by
    rw [autocorr_copyTrain_local hf.continuous hfc c (by norm_num : (0 : ℝ) ≤ 1 / 2)
      hsHalf (by linarith : (1 / 2 : ℝ) + 1 < S) (by norm_num : |(0 : ℝ)| ≤ 1)]
    exact mul_pos (copyTrainMass_pos_of_exists hc) hR
  refine ⟨f, hf, hfc, hR, hsHalf, contDiff_copyTrain hf c S,
    hasCompactSupport_copyTrain hfc c S, hRg, hgrid, ?_, ?_, ?_⟩
  · exact (copyTrain_min_distance_energy hf2 hfc hR hc (by norm_num : (0 : ℝ) ≤ 1 / 2)
      hsHalf hS (by linarith) hgrid).2.2
  · have herr := normalizedArchEnergy_copyTrain_uniform_error hf2 hfc hR c hc
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hsHalf (by linarith : (1 / 2 : ℝ) + 1 < S)
    have hb := (le_abs_self _).trans herr
    have hl : Real.log (d / 4) = Real.log d - Real.log 4 := Real.log_div hd.ne' (by norm_num)
    rw [hl] at hE
    change normalizedArchEnergy (copyTrain f c S) ≤ _ - Real.log d
    linarith
  · intro hB
    exact integral_copyTrain_autocorr_cosh_of_symbol_zero hf2 hfc c S hB

end

end GaloisForLFunctions.BiScaleUncertainty
