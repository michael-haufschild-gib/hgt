import GaloisForLFunctions.HodgeTheoryOfAFixedPart.FiniteCombSamplingGrams
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion

/-!
# Smooth samples fit the original ratio

A packet supported strictly between `log 3` and `log (3Q)` can be sampled
at `⌊N/3⌋` inside the original window `(N,QN]`. Closed support supplies a
gap at the lower endpoint, while the decimated logarithm tends to its
fixed shift. Zero extension then preserves the existing comb limit.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ HTGeometry ArithmeticCastelnuovoSeveri ArithmeticIndexDescent

private theorem exists_lower_support_gap {f : ℝ → ℝ} {l r : ℝ}
    (hs : tsupport f ⊆ Set.Ioo l r) :
    ∃ b : ℝ, l < b ∧ ∀ u, u ≤ b → f u = 0 := by
  have hclosed : IsClosed (tsupport f) := isClosed_closure
  have hnot : l ∉ tsupport f := fun h => (lt_irrefl l) (hs h).1
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hnot)
  refine ⟨l + ε / 2, by linarith only [hε], fun u hu => ?_⟩
  by_contra hne
  have hmem : u ∈ tsupport f := subset_closure hne
  have hlu : l < u := (hs hmem).1
  have hdist : dist u l < ε := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hlu)]
    linarith only [hu, hε]
  exact hb hdist hmem

/-- The scalar comb limit holds on the original fixed-ratio window after
decimating the sampling scale by three. -/
theorem tendsto_combForm_originalRatio_sample {Q : ℕ} (hQ : 1 ≤ Q)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : tsupport f ⊆ Set.Ioo (Real.log 3) (Real.log ((3 * Q : ℕ) : ℝ))) :
    Tendsto (fun N : ℕ => combForm (Ioc N (Q * N)) (sampleCoord f (N / 3)))
      atTop (𝓝 (zeroSum f)) := by
  have hp : Tendsto (fun N : ℕ => N / 3) atTop atTop := by
    refine tendsto_atTop.mpr fun B => eventually_atTop.mpr ⟨B * 3, fun N hN => ?_⟩
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mpr hN
  have hvanish : ∀ u, u ≤ Real.log 3 ∨ Real.log ((3 * Q : ℕ) : ℝ) ≤ u → f u = 0 := by
    intro u hu
    by_contra hne
    have hm := hs (subset_closure hne)
    rcases hu with hu | hu
    · exact (not_lt_of_ge hu) hm.1
    · exact (not_lt_of_ge hu) hm.2
  have hconv := (tendsto_combForm_sample hf hfc (by omega : 1 ≤ 3 * Q) hvanish).comp hp
  obtain ⟨b, hb, hfb⟩ := exists_lower_support_gap hs
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) - Real.log ((N / 3 : ℕ) : ℝ))
      atTop (𝓝 (Real.log 3)) := by
    simpa only [neg_sub, neg_neg, Nat.cast_ofNat] using
      (tendsto_log_natDiv_sub_log (by norm_num : 0 < 3)).neg
  have hlarge : ∀ᶠ N : ℕ in atTop, Q ≤ N / 3 := hp.eventually (eventually_ge_atTop Q)
  refine hconv.congr' ?_
  filter_upwards [hlarge, hlog.eventually (Iio_mem_nhds hb)] with N hN hNb
  let p := N / 3
  have hp0 : 0 < p := by dsimp only [p]; omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hN0 : 0 < N := hp0.trans_le (Nat.div_le_self N 3)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsub : Ioc N (Q * N) ⊆ Ioc p (p + 3 * (3 * Q) * p) := by
    apply Finset.Ioc_subset_Ioc (Nat.div_le_self N 3)
    have hNlt : N ≤ 3 * (p + 1) := (Nat.lt_mul_div_succ N (by norm_num : 0 < 3)).le
    have hQN := Nat.mul_le_mul_left Q hNlt
    have hpp : p ≤ Q * p := by simpa only [one_mul] using Nat.mul_le_mul_right p hQ
    change Q ≤ p at hN
    nlinarith only [hQN, hpp, hN]
  apply combForm_of_subset hsub
  intro n hn hnot
  have hpn : p < n := (mem_Ioc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hp0.trans hpn
  have hzero : f (Real.log ((n : ℝ) / p)) = 0 := by
    by_cases hnN : n ≤ N
    · apply hfb
      have hratio : (n : ℝ) / p ≤ N / p :=
        div_le_div_of_nonneg_right (by exact_mod_cast hnN) hpR.le
      have hl := Real.log_le_log (div_pos hn0 hpR) hratio
      rw [Real.log_div hNR.ne' hpR.ne'] at hl
      exact hl.trans hNb.le
    · have hQn : Q * N < n := by
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at hnot
        rcases hnot with h | h
        · exact False.elim (hnN h)
        · exact h
      have h3p : 3 * p ≤ N := Nat.mul_div_le N 3
      have hprod : ((3 * Q : ℕ) : ℝ) * p < n := by
        have h := (Nat.mul_le_mul_left Q h3p).trans_lt hQn
        exact_mod_cast (show 3 * Q * p < n by nlinarith only [h])
      have hr : ((3 * Q : ℕ) : ℝ) < (n : ℝ) / p := (lt_div_iff₀ hpR).mpr hprod
      apply hvanish _ (Or.inr _)
      exact (Real.log_lt_log (by exact_mod_cast (show 0 < 3 * Q by omega)) hr).le
  simp only [sampleCoord, degreeSample, p, hzero, zero_div]

/-- Every mixed entry of a fixed real packet family converges on the
original ratio window. -/
theorem tendsto_combGram_originalRatio_sample {Q n : ℕ} (hQ : 1 ≤ Q)
    (f : Fin n → realTests)
    (hs : ∀ i, tsupport (f i).1 ⊆
      Set.Ioo (Real.log 3) (Real.log ((3 * Q : ℕ) : ℝ))) (i j : Fin n) :
    Tendsto (fun N : ℕ => realPolarGram (shiftedCombForm (Ioc N (Q * N)) 0)
      (fun k => sampleCoord (f k).1 (N / 3)) i j) atTop
      (𝓝 (complexWeilMixed f f i j)) := by
  have hi := tendsto_combForm_originalRatio_sample hQ (f i).2.1 (f i).2.2 (hs i)
  have hj := tendsto_combForm_originalRatio_sample hQ (f j).2.1 (f j).2.2 (hs j)
  have hsub : tsupport (f j - f i).1 ⊆
      Set.Ioo (Real.log 3) (Real.log ((3 * Q : ℕ) : ℝ)) := by
    apply Set.Subset.trans (show tsupport (f j - f i).1 ⊆
      tsupport (f j).1 ∪ tsupport (f i).1 from ?_) (Set.union_subset (hs j) (hs i))
    apply closure_minimal _ (isClosed_closure.union isClosed_closure)
    intro u hu
    by_cases hzero : (f i).1 u = 0
    · exact Or.inl (subset_closure (by
        change (f j).1 u ≠ 0
        simpa only [sub_apply, hzero, sub_zero] using hu))
    · exact Or.inr (subset_closure hzero)
  have hd := tendsto_combForm_originalRatio_sample hQ (f j - f i).2.1
    (f j - f i).2.2 hsub
  rw [← realPolarGram_zeroSum f]
  have ht := (Complex.continuous_ofReal.tendsto _).comp (((hi.add hj).sub hd).div_const 2)
  refine ht.congr' (Eventually.of_forall fun N => ?_)
  have he : sampleCoord (f j - f i).1 (N / 3) =
      fun u => sampleCoord (f j).1 (N / 3) u - sampleCoord (f i).1 (N / 3) u := by
    funext u
    exact sub_div _ _ _
  simp only [Function.comp_apply, realPolarGram, shiftedCombForm, zero_mul, add_zero, he]

/-- Every finite strict-interior packet index eventually appears in the
literal unshifted comb at the original ratio. -/
theorem eventually_realPacketIndex_le_originalRatio_combIndex {Q n : ℕ} (hQ : 1 ≤ Q)
    (f : Fin n → realTests)
    (hs : ∀ i, tsupport (f i).1 ⊆
      Set.Ioo (Real.log 3) (Real.log ((3 * Q : ℕ) : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      (HTGeometry.hermNegIndex (complexWeilMixed f f) : ℕ∞) ≤
        robustCombIndex (Ioc N (Q * N)) 0 := by
  filter_upwards [ArithmeticIndexDescent.eventually_negIndex_limit_le
    (fun N => realPolarGram (shiftedCombForm (Ioc N (Q * N)) 0)
      (fun k => sampleCoord (f k).1 (N / 3))) (complexWeilMixed f f)
    (tendsto_combGram_originalRatio_sample hQ f hs)] with N hN
  exact (ENat.coe_le_coe.mpr hN).trans
    (shiftedCombGram_negIndex_le _ 0 (fun k => sampleCoord (f k).1 (N / 3)))

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
