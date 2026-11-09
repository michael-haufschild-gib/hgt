import GaloisForLFunctions.InfiniteRankWeilTheory.ActualLagSamplingCover
import GaloisForLFunctions.InfiniteRankWeilTheory.ZetaResidualSampling
import GaloisForLFunctions.ArithmeticDiscreteness.TheExceptionalValuesHaveSmallHausdorffDimension

/-!
# Actual rapid cancellation is residual and zero-dimensional

Arithmetic-cell curvature bounds the number and radius of small-value covers. Exponentially
many cells are harmless when the accuracy exponent can be chosen arbitrarily large. Thus the
positive bases with recurrent actual Weil-lag cancellation at every exponential rate have
Hausdorff dimension zero, without any zero-location or abscissa-law assumption.
-/

open Set Metric MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

private theorem hausdorffMeasure_eq_zero_of_exponential_tail_covers
    (E : Set ℝ) (G : ℕ → Finset ℝ) {M K U b s : ℝ}
    (hM : 0 < M) (hK : 0 < K) (hb : 0 < b) (hs : 0 < s) (hgap : U < b * s)
    (hcard : ∀ n, ((G n).card : ℝ) ≤ M * Real.exp (U * (n : ℝ)))
    (hcover : ∀ N : ℕ, ∀ x ∈ E, ∃ n : ℕ, N ≤ n ∧
      ∃ y ∈ G n, |x - y| ≤ K * Real.exp (-b * (n : ℝ))) : μH[s] E = 0 := by
  let r : ℕ → ℝ := fun n => K * Real.exp (-b * (n : ℝ))
  let w : ℕ → ℝ := fun n => M * (2 * K) ^ s * Real.exp (-(b * s - U) * (n : ℝ))
  have hr (n : ℕ) : 0 ≤ r n := by dsimp [r]; positivity
  have hrmono : Antitone r := by
    intro n m hnm
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left (by exact_mod_cast hnm) (neg_nonpos.mpr hb.le))) hK.le
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have h := ((Real.summable_pow_mul_exp_neg_nat_mul 0 hb).tendsto_atTop_zero).const_mul K
    simpa only [pow_zero, one_mul, mul_zero] using h
  have hw (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have hwsum : Summable w := by
    have h := (Real.summable_pow_mul_exp_neg_nat_mul 0 (sub_pos.mpr hgap)).mul_left
      (M * (2 * K) ^ s)
    simpa only [pow_zero, one_mul] using h
  have hcost (n : ℕ) : (G n).card * (2 * r n) ^ s ≤ w n := by
    have hpow : (2 * r n) ^ s = (2 * K) ^ s * Real.exp (-(b * s) * (n : ℝ)) := by
      dsimp [r]
      rw [← mul_assoc, Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
      congr 2
      ring
    rw [hpow]
    calc ((G n).card : ℝ) * ((2 * K) ^ s * Real.exp (-(b * s) * (n : ℝ)))
        ≤ (M * Real.exp (U * (n : ℝ))) *
            ((2 * K) ^ s * Real.exp (-(b * s) * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right (hcard n) (by positivity)
      _ = M * (2 * K) ^ s *
          (Real.exp (U * (n : ℝ)) * Real.exp (-(b * s) * (n : ℝ))) := by ring
      _ = w n := by
        rw [← Real.exp_add]
        dsimp [w]
        congr 2
        ring
  have htail (N : ℕ) : Complex.ofReal '' E ⊆
      ⋃ n ≥ N, ⋃ y ∈ G n, closedBall (y : ℂ) (r n) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn, y, hy, hdist⟩ := hcover N x hx
    refine mem_iUnion₂.mpr ⟨n, hn, mem_iUnion₂.mpr ⟨y, hy, ?_⟩⟩
    rw [mem_closedBall, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    exact hdist
  have hzero := ArithmeticDiscreteness.hausdorffMeasure_eq_zero_of_tail_covers
    (Complex.ofReal '' E) G (fun _ y => (y : ℂ)) r w s hs hr hrmono hrlim hw hwsum hcost htail
  rwa [Complex.isometry_ofReal.hausdorffMeasure_image (Or.inl hs.le)] at hzero

/-- Every positive-dimensional Hausdorff measure vanishes on the rapid-cancellation bases
in a compact positive interval. -/
theorem hausdorffMeasure_lagRapidCancellationBases_inter_Icc_eq_zero
    {L U s : ℝ} (hL : 0 < L) (hU : 0 ≤ U) (hs : 0 < s) :
    μH[s] (lagRapidCancellationBases ∩ Icc L U) = 0 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * (U + (U + 1) / s))
  let b : ℝ := ((m : ℝ) + 1) / 2 - U
  have hbq : (U + 1) / s < b := by dsimp [b]; linarith only [hm]
  have hb : 0 < b := (div_pos (by linarith only [hU]) hs).trans hbq
  have hgap : U < b * s := by
    have h := (div_lt_iff₀ hs).mp hbq
    linarith only [h]
  choose G hGcard hGcover using (fun n : ℕ => exists_actualLag_sampled_cover hU m n)
  apply hausdorffMeasure_eq_zero_of_exponential_tail_covers
    (lagRapidCancellationBases ∩ Icc L U) G (M := 4) (K := lagSamplingCoverConstant)
    (U := U) (b := b) (by norm_num) lagSamplingCoverConstant_pos hb hs hgap
    (fun n => by simpa only [mul_comm] using hGcard n)
  intro N ℓ hℓ
  have hℓ0 : 0 < ℓ := hL.trans_le hℓ.2.1
  obtain ⟨J, hJ⟩ := exists_nat_gt (Real.log 2 / ℓ)
  have hfreq := mem_samplingCancellationBases_iff.mp hℓ.1 m
  obtain ⟨n, hn, hsmall⟩ := frequently_atTop.mp hfreq (max N (max 1 J))
  have hnN : N ≤ n := (le_max_left N (max 1 J)).trans hn
  have hn1 : 1 ≤ n := (le_max_left 1 J).trans ((le_max_right N (max 1 J)).trans hn)
  have hnJ : J ≤ n := (le_max_right 1 J).trans ((le_max_right N (max 1 J)).trans hn)
  have hlarge : 2 ≤ Real.exp ((n : ℝ) * ℓ) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    exact ((div_lt_iff₀ hℓ0).mp (hJ.trans_le (by exact_mod_cast hnJ))).le
  obtain ⟨z, hz, hdist⟩ := hGcover n ℓ ⟨hℓ0.le, hℓ.2.2⟩ hn1 hlarge hsmall.le
  exact ⟨n, hnN, z, hz, hdist⟩

private theorem dimH_lagRapidCancellationBases_inter_Icc_eq_zero
    {L U : ℝ} (hL : 0 < L) (hU : 0 ≤ U) :
    dimH (lagRapidCancellationBases ∩ Icc L U) = 0 := by
  apply le_antisymm ?_ bot_le
  apply dimH_le
  intro d hd
  by_contra hle
  have hd0 : 0 < (d : ℝ) := by
    have ht : (0 : ENNReal) < (d : ENNReal) := lt_of_not_ge hle
    exact_mod_cast ht
  have hz := hausdorffMeasure_lagRapidCancellationBases_inter_Icc_eq_zero hL hU hd0
  exact ENNReal.zero_ne_top (hz.symm.trans hd)

/-- Actual rapid-cancellation bases have Hausdorff dimension zero on the positive half-line,
unconditionally. -/
theorem dimH_positive_lagRapidCancellationBases_eq_zero :
    dimH (lagRapidCancellationBases ∩ Ioi 0) = 0 := by
  have hsub : lagRapidCancellationBases ∩ Ioi 0 ⊆
      ⋃ j : ℤ, lagRapidCancellationBases ∩ Icc ((2 : ℝ) ^ j) (2 * 2 ^ j) := by
    rintro ℓ ⟨hℓ, hℓ0⟩
    obtain ⟨j, hj1, hj2⟩ := exists_mem_Ico_zpow hℓ0 (show (1 : ℝ) < 2 by norm_num)
    rw [zpow_add_one₀ (by norm_num)] at hj2
    exact mem_iUnion.mpr ⟨j, hℓ, hj1, by linarith only [hj2]⟩
  have hz (j : ℤ) :
      dimH (lagRapidCancellationBases ∩ Icc ((2 : ℝ) ^ j) (2 * 2 ^ j)) = 0 :=
    dimH_lagRapidCancellationBases_inter_Icc_eq_zero (by positivity) (by positivity)
  apply le_antisymm ((dimH_mono hsub).trans ?_) (show (0 : ENNReal) ≤ _ from zero_le)
  rw [dimH_iUnion]
  simp only [hz, iSup_const, le_refl]

/-- Actual rapid cancellation is residual, while its positive bases form a dimension-zero set. -/
theorem actualLag_rapidCancellation_geometry :
    IsGδ lagRapidCancellationBases ∧ Dense lagRapidCancellationBases ∧
      lagRapidCancellationBases ∈ residual ℝ ∧
      dimH (lagRapidCancellationBases ∩ Ioi 0) = 0 :=
  ⟨lagRapidCancellationBases_residual.1, lagRapidCancellationBases_residual.2.1,
    lagRapidCancellationBases_residual.2.2, dimH_positive_lagRapidCancellationBases_eq_zero⟩

#print axioms hausdorffMeasure_lagRapidCancellationBases_inter_Icc_eq_zero
#print axioms dimH_positive_lagRapidCancellationBases_eq_zero
#print axioms actualLag_rapidCancellation_geometry

end GaloisForLFunctions.InfiniteRankWeilTheory
