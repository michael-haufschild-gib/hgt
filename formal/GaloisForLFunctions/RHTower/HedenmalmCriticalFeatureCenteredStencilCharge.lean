import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureSevenTenthsShallowCharge

/-!
# Generic centered-stencil HCF charge propagation

A local lower bound on any finite integer stencil around the nearest height center propagates to
the corrected pole--Gamma lattice budget.  This removes duplicated three-, five-, seven-, and
wider-center packet summations from subsequent receiver improvements.
-/

open Complex

namespace RHTower

noncomputable section

/-- Any finite nearest-height stencil carrying local holomorphic charge `c` deposits `c` per
off-line multiplicity copy in the corrected lattice budget. -/
theorem finite_offLine_card_mul_centeredStencilLocalCharge_le_offLineLatticeBudget
    (J K : Finset ℤ) (S : Finset XiZeroCopy) (c : ℝ)
    (hoff : ∀ q ∈ S, (q.1 : ℂ).re ≠ 1 / 2)
    (hcenters : ∀ q ∈ S, ∀ j ∈ J, round (xiSpectralPoint q).re + j ∈ K)
    (hlocal : ∀ q ∈ S, c ≤ ∑ j ∈ J,
      ((criticalFeatureCauchyKernelTest
        ((round (xiSpectralPoint q).re + j : ℤ) : ℝ)
        (xiSpectralPoint q)) ^ 2).re) :
    (S.card : ℝ) * c ≤ criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  calc
    (S.card : ℝ) * c = ∑ _q ∈ S, c := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      gcongr with q hq
      let kq : ℤ := round (xiSpectralPoint q).re
      let Tq : Finset ℤ := J.image (fun j => kq + j)
      have hTq : Tq ⊆ K := by
        intro k hk
        change k ∈ J.image (fun j => kq + j) at hk
        rw [Finset.mem_image] at hk
        obtain ⟨j, hj, rfl⟩ := hk
        exact hcenters q hq j hj
      have hoffeq (j : ℤ) :
          ((criticalFeatureCauchyKernelTest (j : ℝ)
            (xiSpectralPoint q)) ^ 2).re =
            offLineCriticalFeatureHolomorphicEnergy (j : ℝ) q := by
        rw [offLineCriticalFeatureHolomorphicEnergy, if_neg (hoff q hq)]
      have hinj : Set.InjOn (fun j : ℤ => kq + j) J := by
        intro a ha b hb hab
        exact add_left_cancel hab
      have hsum :
          (∑ k ∈ Tq, offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q) =
            ∑ j ∈ J,
              offLineCriticalFeatureHolomorphicEnergy ((kq + j : ℤ) : ℝ) q := by
        change (∑ k ∈ J.image (fun j => kq + j),
          offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q) = _
        rw [Finset.sum_image]
        exact hinj
      calc
        c ≤ ∑ j ∈ J,
            offLineCriticalFeatureHolomorphicEnergy ((kq + j : ℤ) : ℝ) q := by
          have h := hlocal q hq
          dsimp only [kq] at h ⊢
          simpa only [hoffeq] using h
        _ = ∑ k ∈ Tq,
            offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := hsum.symm
        _ ≤ ∑ k ∈ K, offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hTq
          intro k hkK hkTq
          exact offLineCriticalFeatureHolomorphicEnergy_nonneg (k : ℝ) q
    _ = ∑ k ∈ K, ∑ q ∈ S,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      rw [Finset.sum_comm]
    _ ≤ ∑ k ∈ K, ∑' q : XiZeroCopy,
        offLineCriticalFeatureHolomorphicEnergy (k : ℝ) q := by
      gcongr with k hk
      exact (offLineCriticalFeatureHolomorphicEnergy_summable (k : ℝ)).sum_le_tsum S
        (fun q _ => offLineCriticalFeatureHolomorphicEnergy_nonneg (k : ℝ) q)
    _ = criticalFeaturePrimeGammaOffLineLatticeBudget K := by
      rw [criticalFeaturePrimeGammaOffLineLatticeBudget]
      apply Finset.sum_congr rfl
      intro k hk
      rw [criticalFeaturePrimeGammaOffLineExcess_eq_tsum_offLineHolomorphicEnergy]

end

end RHTower
