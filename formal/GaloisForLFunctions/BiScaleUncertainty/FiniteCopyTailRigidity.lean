import GaloisForLFunctions.BiScaleUncertainty.FiniteTranslationTrains

/-!
# Infinite-grid full-span energy cost for finite copy trains

The endpoint pair detects the entire span. A grid zero near that span forces a short
seed zero, which local diagonal preservation transfers to the complete train.
The final endpoint derives its support threshold from the compact C² source itself.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem copyTrain_near_span_zero {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {m : ℕ} {c : Fin (m + 1) → ℝ} {D S x : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ y, D < |y| → autocorr f y = 0) (hS : D + 1 < S)
    (hc0 : c 0 ≠ 0) (hcm : c (Fin.last m) ≠ 0)
    (hx : |x - (m : ℝ) * S| ≤ 1) (hz : autocorr (copyTrain f c S) x = 0) :
    autocorr f (x - (m : ℝ) * S) = 0 := by
  rw [autocorr_copyTrain_extremal hf hfc c hD hsupp hS hx] at hz
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hc0 hcm)

theorem copyTrain_infinite_grid_distance_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {m : ℕ} {c : Fin (m + 1) → ℝ} {D S : ℝ}
    (hD : 0 ≤ D) (hsupp : ∀ y, D < |y| → autocorr f y = 0) (hS : D + 1 < S)
    (hL : 2 ≤ (m : ℝ) * S) (hc0 : c 0 ≠ 0) (hcm : c (Fin.last m) ≠ 0)
    (hgrid : ∀ n : ℕ, 2 ≤ n → autocorr (copyTrain f c S) (Real.log (n : ℝ)) = 0) :
    autocorr f (logarithmicGridDistance ((m : ℝ) * S)) = 0 := by
  obtain ⟨n, hn, hd⟩ := exists_logarithmicGridDistance_node hL
  have hx : |Real.log (n : ℝ) - (m : ℝ) * S| ≤ 1 := by
    rw [hd]
    exact logarithmicGridDistance_le_one hL
  have hz := copyTrain_near_span_zero hf hfc hD hsupp hS hc0 hcm hx (hgrid n hn)
  have hzabs : autocorr f |Real.log (n : ℝ) - (m : ℝ) * S| = 0 := by
    by_cases hp : 0 ≤ Real.log (n : ℝ) - (m : ℝ) * S
    · rwa [abs_of_nonneg hp]
    · rw [abs_of_neg (lt_of_not_ge hp), autocorr_neg]
      exact hz
  rwa [hd] at hzabs

theorem autocorr_copyTrain_zero_pos {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {m : ℕ} {c : Fin (m + 1) → ℝ} {D S : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ y, D < |y| → autocorr f y = 0) (hS : D + 1 < S) (hc0 : c 0 ≠ 0) :
    0 < autocorr (copyTrain f c S) 0 := by
  rw [autocorr_copyTrain_local hf hfc c hD hsupp hS (by norm_num : |(0 : ℝ)| ≤ 1)]
  exact mul_pos (copyTrainMass_pos hc0) hR

/-- Interior interference cannot remove the nearest-grid energy cost at the full span. -/
theorem copyTrain_infinite_grid_distance_energy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {m : ℕ} {c : Fin (m + 1) → ℝ} {D S : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ y, D < |y| → autocorr f y = 0) (hS : D + 1 < S)
    (hL : 2 ≤ (m : ℝ) * S) (hc0 : c 0 ≠ 0) (hcm : c (Fin.last m) ≠ 0)
    (hgrid : ∀ n : ℕ, 2 ≤ n → autocorr (copyTrain f c S) (Real.log (n : ℝ)) = 0) :
    0 < logarithmicGridDistance ((m : ℝ) * S) ∧
      Real.exp (-(1 / 2 : ℝ)) / 4 * (-Real.log (logarithmicGridDistance ((m : ℝ) * S))) ≤ normalizedArchEnergy f ∧
      Real.exp (-(1 / 2 : ℝ)) / 4 * (-Real.log (logarithmicGridDistance ((m : ℝ) * S))) ≤
        normalizedArchEnergy (copyTrain f c S) := by
  have hz := copyTrain_infinite_grid_distance_zero hf.continuous hfc hD hsupp hS hL hc0 hcm hgrid
  have hd : 0 < logarithmicGridDistance ((m : ℝ) * S) := by
    by_contra hp
    have heq : logarithmicGridDistance ((m : ℝ) * S) = 0 :=
      le_antisymm (le_of_not_gt hp) (logarithmicGridDistance_nonneg hL)
    rw [heq] at hz
    linarith
  have hd1 := logarithmicGridDistance_le_one hL
  have hzg : autocorr (copyTrain f c S) (logarithmicGridDistance ((m : ℝ) * S)) = 0 := by
    rw [autocorr_copyTrain_local hf.continuous hfc c hD hsupp hS
      (by rwa [abs_of_pos hd] : |logarithmicGridDistance ((m : ℝ) * S)| ≤ 1), hz, mul_zero]
  have hRg := autocorr_copyTrain_zero_pos hf.continuous hfc hR hD hsupp hS hc0
  refine ⟨hd, ?_, ?_⟩
  · have hb := autocorr_increment_mul_log_le hf hfc hd hd1
    rw [hz, sub_zero] at hb
    unfold normalizedArchEnergy
    apply (le_div_iff₀ hR).mpr
    nlinarith
  · have hb := autocorr_increment_mul_log_le (contDiff_copyTrain hf c S)
      (hasCompactSupport_copyTrain hfc c S) hd hd1
    rw [hzg, sub_zero] at hb
    unfold normalizedArchEnergy
    apply (le_div_iff₀ hRg).mpr
    nlinarith

/-- Division-free full-span cost, including zero-mass seeds; only the detecting grid sample is used. -/
theorem copyTrain_zero_linear_energy_cost {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {m : ℕ} {c : Fin (m + 1) → ℝ} {D S : ℝ}
    (hD : 0 ≤ D) (hsupp : ∀ y, D < |y| → autocorr f y = 0) (hS : D + 1 < S)
    (hL : 0 ≤ (m : ℝ) * S) (hc0 : c 0 ≠ 0) (hcm : c (Fin.last m) ≠ 0)
    (hz : autocorr (copyTrain f c S) (Real.log (logarithmicCeilNode ((m : ℝ) * S) : ℝ)) = 0) :
    Real.exp (-(1 / 2 : ℝ)) * ((m : ℝ) * S) * autocorr f 0 ≤ 4 * biScaleLevyEnergy f ∧
      Real.exp (-(1 / 2 : ℝ)) * ((m : ℝ) * S) * autocorr (copyTrain f c S) 0 ≤
        4 * biScaleLevyEnergy (copyTrain f c S) := by
  have hb := logarithmicCeilLag_bounds ((m : ℝ) * S)
  have hd1 : |logarithmicCeilLag ((m : ℝ) * S)| ≤ 1 := by
    rw [abs_of_nonneg hb.1]
    exact hb.2.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hbase : autocorr f (logarithmicCeilLag ((m : ℝ) * S)) = 0 :=
    copyTrain_near_span_zero hf.continuous hfc hD hsupp hS hc0 hcm hd1 hz
  have htrain : autocorr (copyTrain f c S) (logarithmicCeilLag ((m : ℝ) * S)) = 0 := by
    rw [autocorr_copyTrain_local hf.continuous hfc c hD hsupp hS hd1, hbase, mul_zero]
  constructor
  · have h := autocorr_logarithmicCeilLag_energy_bound hf hfc hL
    simpa only [hbase, sub_zero] using h
  · have h := autocorr_logarithmicCeilLag_energy_bound (contDiff_copyTrain hf c S)
      (hasCompactSupport_copyTrain hfc c S) hL
    simpa only [htrain, sub_zero] using h

/-- The source supplies its own threshold; no support or analytic interface is assumed. -/
theorem exists_copyTrain_infinite_grid_energy_barrier
    (f : {f : C_c(ℝ, ℝ) // ContDiff ℝ 2 (f : ℝ → ℝ)}) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ m : ℕ, 1 ≤ m → ∀ S : ℝ, D + 1 < S →
      ∀ c : Fin (m + 1) → ℝ, c 0 ≠ 0 → c (Fin.last m) ≠ 0 →
      (∀ n : ℕ, 2 ≤ n → autocorr (copyTrain f.1 c S) (Real.log (n : ℝ)) = 0) →
      Real.exp (-(1 / 2 : ℝ)) * ((m : ℝ) * S) * autocorr f.1 0 ≤ 4 * biScaleLevyEnergy f.1 ∧
        Real.exp (-(1 / 2 : ℝ)) * ((m : ℝ) * S) * autocorr (copyTrain f.1 c S) 0 ≤
          4 * biScaleLevyEnergy (copyTrain f.1 c S) := by
  obtain ⟨D, hD, hsupp⟩ := exists_pos_autocorr_support_radius f.1.hasCompactSupport
  refine ⟨D + 1, by linarith, ?_⟩
  intro m hm S hS c hc0 hcm hgrid
  have hS0 : 0 < S := by linarith
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hL : 0 < (m : ℝ) * S := mul_pos hm0 hS0
  exact copyTrain_zero_linear_energy_cost f.2 f.1.hasCompactSupport hD.le hsupp
    (by linarith) hL.le hc0 hcm (hgrid _ (logarithmicCeilNode_ge_two hL))

end

end GaloisForLFunctions.BiScaleUncertainty
