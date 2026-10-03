import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMarkedMoments
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMixedPairSource
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthCubicTailIsolation
/-! Every mixed source convolution is controlled by marking a deep factor.
The bound holds for every sector order and every moment through nine. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

theorem momentConvolution_swap_nine (a b c : ℕ → ℝ) {j : ℕ} (hj : j ≤ 9) :
    momentConvolution a (momentConvolution b c) j=momentConvolution b (momentConvolution a c) j := by
  interval_cases j <;> norm_num [momentConvolution,Finset.sum_range_succ,Nat.choose] <;> ring

theorem momentConvolution_power_zero_nine (a m : ℕ → ℝ) {j : ℕ} (hj : j ≤ 9) :
    momentConvolution a (spectralPowerMoment m 0) j=a j := by
  interval_cases j <;>
    norm_num [momentConvolution,spectralPowerMoment,Finset.sum_range_succ,Nat.choose,Nat.factorial]

theorem spectralPowerMoment_nonneg_nine (m : ℕ → ℝ) (hm : ∀ i, 0 ≤ m i) (k : ℕ)
    {j : ℕ} (hj : j ≤ 9) : 0 ≤ spectralPowerMoment m k j := by
  induction k generalizing j with
  | zero =>
      by_cases hz : j=0
      · subst j; norm_num [spectralPowerMoment]
      · simp [spectralPowerMoment,PowerSeries.coeff_one,hz]
  | succ k ih =>
      rw [spectralPowerMoment_succ_nine m k hj]
      unfold momentConvolution
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (mul_nonneg (by positivity) (hm i)) (ih (by omega))

theorem spectralPowerMoment_mono_nine (a m : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ham : ∀ i, a i ≤ m i) (k : ℕ) {j : ℕ} (hj : j ≤ 9) :
    spectralPowerMoment a k j ≤ spectralPowerMoment m k j := by
  induction k generalizing j with
  | zero => simp [spectralPowerMoment]
  | succ k ih =>
      rw [spectralPowerMoment_succ_nine a k hj,spectralPowerMoment_succ_nine m k hj]
      unfold momentConvolution
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ham i) (by positivity))
        (ih (by omega)) (spectralPowerMoment_nonneg_nine a ha k (by omega))
        (mul_nonneg (by positivity) ((ha i).trans (ham i)))

theorem momentConvolution_mono_right (a m n : ℕ → ℝ) (j : ℕ)
    (ha : ∀ i, 0 ≤ a i) (hmn : ∀ i, i ≤ j → m i ≤ n i) :
    momentConvolution a m j ≤ momentConvolution a n j := by
  unfold momentConvolution
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hmn (j-i) (by omega)) (mul_nonneg (by positivity) (ha i))

theorem momentConvolution_marked_successor (a m : ℕ → ℝ) (k : ℕ)
    {j : ℕ} (hj : j ≤ 9) :
    momentConvolution m (momentConvolution a (spectralPowerMoment m k)) j=
      momentConvolution a (spectralPowerMoment m (k+1)) j := by
  rw [momentConvolution_swap_nine m a _ hj]
  unfold momentConvolution
  apply Finset.sum_congr rfl
  intro i hi
  rw [spectralPowerMoment_succ_nine m k (by omega : j-i ≤ 9)]
  rfl

theorem markedPower_difference_le (a d : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hd : ∀ i, 0 ≤ d i)
    (k : ℕ) {j : ℕ} (hj : j ≤ 9) :
    spectralPowerMoment (fun i => a i+d i) (k+1) j-spectralPowerMoment a (k+1) j ≤
      ((k+1:ℕ):ℝ)*momentConvolution d (spectralPowerMoment (fun i => a i+d i) k) j := by
  let m : ℕ → ℝ := fun i => a i+d i
  have hm : ∀ i, 0 ≤ m i := fun i => add_nonneg (ha i) (hd i)
  have ham : ∀ i, a i ≤ m i := fun i => le_add_of_nonneg_right (hd i)
  change spectralPowerMoment m (k+1) j-spectralPowerMoment a (k+1) j ≤
    ((k+1:ℕ):ℝ)*momentConvolution d (spectralPowerMoment m k) j
  induction k generalizing j with
  | zero =>
      rw [spectralPowerMoment_one_nine m hj,spectralPowerMoment_one_nine a hj,
        momentConvolution_power_zero_nine d m hj]
      simp [m]
  | succ k ih =>
      have he : spectralPowerMoment m (k+1+1) j-spectralPowerMoment a (k+1+1) j=
          momentConvolution m (fun i => spectralPowerMoment m (k+1) i-spectralPowerMoment a (k+1) i) j+
            momentConvolution d (spectralPowerMoment a (k+1)) j := by
        rw [spectralPowerMoment_succ_nine m (k+1) hj,spectralPowerMoment_succ_nine a (k+1) hj]
        unfold momentConvolution
        rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [m]
        ring
      have h1 : momentConvolution m
          (fun i => spectralPowerMoment m (k+1) i-spectralPowerMoment a (k+1) i) j ≤
          ((k+1:ℕ):ℝ)*momentConvolution m (momentConvolution d (spectralPowerMoment m k)) j := by
        have h := momentConvolution_mono_right m _
          (fun i => ((k+1:ℕ):ℝ)*momentConvolution d (spectralPowerMoment m k) i) j hm
          (fun i hi => ih (by omega))
        have hs : momentConvolution m
            (fun i => ((k+1:ℕ):ℝ)*momentConvolution d (spectralPowerMoment m k) i) j=
            ((k+1:ℕ):ℝ)*momentConvolution m (momentConvolution d (spectralPowerMoment m k)) j := by
          unfold momentConvolution
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        exact h.trans_eq hs
      rw [momentConvolution_marked_successor d m k hj] at h1
      have h2 : momentConvolution d (spectralPowerMoment a (k+1)) j ≤
          momentConvolution d (spectralPowerMoment m (k+1)) j :=
        momentConvolution_mono_right d _ _ j hd
          (fun i hi => spectralPowerMoment_mono_nine a m ha ham (k+1) (by omega))
      rw [he]
      have h := add_le_add h1 h2
      convert! h using 1
      push_cast
      ring

theorem mixedPowerMoment_marked_budget {q : ℝ} (hq : 0 < q) {k j : ℕ}
    (hk : 1 ≤ k) (hj : j ≤ 9) :
    mixedPowerMoment q k j ≤
      (k:ℝ)^(j+1)*thetaCuspHigherLikelihoodSpectralMoment q 0^(k-1)*thetaCuspDeepTailMoment q j := by
  let a := atomMoment 2 q
  let d := thetaCuspDeepTailMoment q
  let m := thetaCuspHigherLikelihoodSpectralMoment q
  have he : m=fun i => a i+d i := by
    funext i
    exact fullMoment_eq_atom_add_deep hq i
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    simpa only [a,atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspSecondAtomMoment_nonneg q i
  have hd : ∀ i, 0 ≤ d i := fun i => thetaCuspDeepTailMoment_nonneg q i
  change spectralPowerMoment m k j-spectralPowerMoment a k j ≤ (k:ℝ)^(j+1)*m 0^(k-1)*d j
  by_cases hk1 : k=1
  · subst k
    rw [spectralPowerMoment_one_nine m hj,spectralPowerMoment_one_nine a hj,he]
    simp
  · have hk2 : 2 ≤ k := by omega
    have h := markedPower_difference_le a d ha hd (k-1) hj
    rw [←he,show k-1+1=k by omega] at h
    have hb := deepMarkedConvolution_moment_le hq (k-2) hj
    rw [show k-2+1=k-1 by omega,show k-2+2=k by omega] at hb
    have hh := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ k by positivity)
    have ht := h.trans hh
    convert! ht using 1
    rw [pow_succ]
    ring

end
end RHTower.ThetaCuspDefect
