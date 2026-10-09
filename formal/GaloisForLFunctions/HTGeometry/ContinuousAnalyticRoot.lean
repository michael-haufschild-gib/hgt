import GaloisForLFunctions.HTGeometry.AnalyticZeroCoverCap

open Filter Topology Function Set

namespace GaloisForLFunctions.HTGeometry

/-- A continuous local root of an analytic germ is analytic, including at its zeros. -/
theorem analyticAt_of_eventually_continuousAt_pow_eq
    {f s : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticAt ℂ f a) (hsc : ∀ᶠ z in 𝓝 a, ContinuousAt s z)
    (hpow : ∀ᶠ z in 𝓝 a, s z ^ n = f z) : AnalyticAt ℂ s a := by
  by_cases hfa : f a = 0
  · rcases hf.eventually_eq_zero_or_eventually_ne_zero with hzero | hnz
    · apply (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) a).congr
      filter_upwards [hzero, hpow] with z hz hp
      exact (eq_zero_of_pow_eq_zero (hp.trans hz)).symm
    · have hsa : s a = 0 := eq_zero_of_pow_eq_zero (hpow.self_of_nhds.trans hfa)
      have hu := analyticAt_update_zero_of_punctured_continuous_root hn hf hfa
        (hsc.filter_mono nhdsWithin_le_nhds) hnz (hpow.filter_mono nhdsWithin_le_nhds)
      simpa only [← hsa, update_eq_self] using hu
  · exact Bottcher.analyticAt_of_continuousAt_pow_eq hn hsc.self_of_nhds hf hfa hpow

/-- On an open complex set a continuous positive-degree root of an analytic function is analytic. -/
theorem analyticOnNhd_of_continuousOn_pow_eq_allowing_zeros
    {U : Set ℂ} (hU : IsOpen U) {f s : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticOnNhd ℂ f U) (hsc : ContinuousOn s U)
    (hpow : ∀ z ∈ U, s z ^ n = f z) : AnalyticOnNhd ℂ s U := by
  intro a ha
  apply analyticAt_of_eventually_continuousAt_pow_eq hn (hf a ha)
  · filter_upwards [hU.mem_nhds ha] with z hz
    exact hsc.continuousAt (hU.mem_nhds hz)
  · exact eventually_of_mem (hU.mem_nhds ha) hpow

end GaloisForLFunctions.HTGeometry
