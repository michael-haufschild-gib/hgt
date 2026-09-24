import GaloisForLFunctions.RHTower.XiMeromorphicCauchyPairReflectionCorrectionNoGo
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.XiCenteredRealShiftDiagonalExtractor

open Complex Filter Topology

namespace RHTower

private theorem egc_correction_eq_relative_term_difference
    (eps : ℝ) (w : ℂ) (q : XiZeroCopy) :
    meromorphicCauchyPairShiftResidueCorrection eps w (xiSpectralPoint q) =
      (eps / 2 : ℂ) *
        (xiRelativeResolventTerm (w + (eps : ℂ)) q -
          xiRelativeResolventTerm (w - (eps : ℂ)) q) := by
  unfold meromorphicCauchyPairShiftResidueCorrection xiRelativeResolventTerm
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem egc_correction_tsum_eq_relative_trace_difference
    (eps : ℝ) (w : ℂ)
    (hp : XiC (w + (eps : ℂ)) ≠ 0)
    (hm : XiC (w - (eps : ℂ)) ≠ 0) :
    (∑' q : XiZeroCopy,
      meromorphicCauchyPairShiftResidueCorrection eps w (xiSpectralPoint q)) =
      (eps / 2 : ℂ) *
        (xiRelativeResolventTrace (w + (eps : ℂ)) -
          xiRelativeResolventTrace (w - (eps : ℂ))) := by
  have hP := summable_xiRelativeResolventTerm hp
  have hM := summable_xiRelativeResolventTerm hm
  calc
    (∑' q : XiZeroCopy,
      meromorphicCauchyPairShiftResidueCorrection eps w (xiSpectralPoint q)) =
        ∑' q : XiZeroCopy,
          (eps / 2 : ℂ) *
            (xiRelativeResolventTerm (w + (eps : ℂ)) q -
              xiRelativeResolventTerm (w - (eps : ℂ)) q) := by
          apply tsum_congr
          intro q
          exact egc_correction_eq_relative_term_difference eps w q
    _ = (eps / 2 : ℂ) *
          ∑' q : XiZeroCopy,
            (xiRelativeResolventTerm (w + (eps : ℂ)) q -
              xiRelativeResolventTerm (w - (eps : ℂ)) q) := by
          rw [tsum_mul_left]
    _ = _ := by
          rw [hP.tsum_sub hM]
          rfl

/-- The global shifted-pole correction is an exact multiplicity extractor at every
observation, not a uniformly vanishing error. -/
theorem tendsto_egc_correction_tsum (x : ℂ) :
    Tendsto
      (fun n : ℕ => ∑' q : XiZeroCopy,
        meromorphicCauchyPairShiftResidueCorrection
          (1 / ((n : ℝ) + 1)) x (xiSpectralPoint q))
      atTop (nhds (((analyticOrderAt XiC x).toNat : ℕ) : ℂ)) := by
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have heps : Tendsto eps atTop (nhds 0) := by
    simpa only [eps] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hepsC : Tendsto (fun n => (eps n : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp heps
  have heps_ne : ∀ n, eps n ≠ 0 := by
    intro n
    exact one_div_ne_zero (by positivity)
  have hplusWithin : Tendsto (fun n => x + (eps n : ℂ)) atTop (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using tendsto_const_nhds.add hepsC,
      Filter.Eventually.of_forall fun n => ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left] using
      (ofReal_ne_zero.mpr (heps_ne n))
  have hminusWithin : Tendsto (fun n => x - (eps n : ℂ)) atTop (𝓝[≠] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using tendsto_const_nhds.sub hepsC,
      Filter.Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    apply ofReal_ne_zero.mpr (heps_ne n)
    linear_combination -h
  have hpunct : ∀ᶠ w in 𝓝[≠] x, XiC w ≠ 0 :=
    (XiC_analytic x (Set.mem_univ x)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hzero => XiC_order_ne_top x (analyticOrderAt_eq_top.mpr hzero))
  have hplus_ne : ∀ᶠ n in atTop, XiC (x + (eps n : ℂ)) ≠ 0 :=
    hplusWithin.eventually hpunct
  have hminus_ne : ∀ᶠ n in atTop, XiC (x - (eps n : ℂ)) ≠ 0 :=
    hminusWithin.eventually hpunct
  apply (tendsto_centeredXiCRealShiftExtractor x).congr'
  filter_upwards [hplus_ne, hminus_ne] with n hpn hmn
  rw [egc_correction_tsum_eq_relative_trace_difference (eps n) x hpn hmn]
  rw [← logDeriv_XiC_eq_relativeResolventTrace hpn,
    ← logDeriv_XiC_eq_relativeResolventTrace hmn]
  rfl

end RHTower
