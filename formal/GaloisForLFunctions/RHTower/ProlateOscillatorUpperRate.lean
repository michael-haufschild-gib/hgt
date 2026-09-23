import GaloisForLFunctions.RHTower.ProlateIndexedOscillatorUpper
import GaloisForLFunctions.RHTower.ProlateTrialSpaceTransportQuantitative

/-!
# The upper half of the oscillator law, with a rate

`eventually_signedModeRadialBandwidth_mul_s_lt_evenOscillatorRung` fixes the margin `ε` first and
then asks for a large bandwidth.  Because the trial-space threshold has the uniform shape
`T ≤ ε · c`, the margin may instead be chosen as a function of the bandwidth: taking `ε = T/c`
makes the threshold an equality, and the same exhaustion contradiction gives

```text
c · s_n  ≤  4n+1 + T/c .
```

Together with the variational lower half this is the second-order form of the large-aperture
oscillator law, `c · s_n = (4n+1) + O(1/c)`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **The upper half of the large-aperture oscillator law, with a rate.**  There is one constant
`K`, depending only on the index, with

```text
signedModeRadialBandwidth a * s_n  ≤  4n+1 + K / signedModeRadialBandwidth a
```

at every large aperture.  Choosing the margin as `K` divided by the bandwidth makes the
trial-space threshold an equality, so the exhaustion contradiction still applies. -/
theorem exists_rate_signedModeRadialBandwidth_mul_s_le (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a n).s
        ≤ 4 * (n : ℝ) + 1 + K / signedModeRadialBandwidth a := by
  obtain ⟨T, hT0, hT⟩ := exists_threshold_rank_highProlateSpan_even_ge n
  refine ⟨T, hT0, ?_⟩
  have hrankC := eventually_rank_hermiteTrialSpan_evenRung_eq n
  have hrankA := tendsto_signedModeRadialBandwidth_atTop.eventually hrankC
  filter_upwards [eventually_gt_atTop (0 : ℝ), hrankA,
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (max T 1)]
    with a ha hrank hcbig
  by_contra hnot
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  have hcT : T ≤ c := le_trans (le_max_left _ _) hcbig
  have hc1 : (1 : ℝ) ≤ c := le_trans (le_max_right _ _) hcbig
  have hc : 0 < c := lt_of_lt_of_le one_pos hc1
  set ε : ℝ := T / c with hεdef
  have hεpos : 0 < ε := div_pos hT0 hc
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one hc]
    exact hcT
  have hεc : T ≤ ε * c := by
    rw [hεdef, div_mul_cancel₀ _ hc.ne']
  set Λ : ℝ := 4 * (n : ℝ) + 1 + ε with hΛdef
  have hΛle : Λ ≤ c * (signedModeRadialData a n).s := by
    have h : ¬ (c * (signedModeRadialData a n).s ≤ 4 * (n : ℝ) + 1 + T / c) := hnot
    rw [not_le] at h
    rw [hΛdef, hεdef]
    linarith
  have hcut : (signedModeRadialData a n).chi ≤ -(Λ * c) := by
    rw [signedModeRadialData_chi_eq_neg_bandwidth_sq_mul_s ha n]
    change -(c ^ (2 : ℕ)) * (signedModeRadialData a n).s ≤ -(Λ * c)
    nlinarith
  have hproj : (highProlateSpan c (Λ * c)).HasOrthogonalProjection :=
    highProlateSpan_hasOrthogonalProjection_of_chi_le ha n hcut
  have hlower : ((n : Cardinal) + 1) ≤ Module.rank ℝ (highProlateSpan c (Λ * c)) := by
    have h := hT ε c hεpos hε1 hεc hrank
    simpa [hΛdef] using h hproj
  have hupper : Module.rank ℝ (highProlateSpan c (Λ * c)) ≤ (n : Cardinal) :=
    rank_highProlateSpan_le_of_chi_le ha n hcut
  have hbad : ((n : Cardinal) + 1) ≤ (n : Cardinal) := hlower.trans hupper
  have hlt : (n : Cardinal) < (n : Cardinal) + 1 := by
    exact_mod_cast Nat.lt_succ_self n
  exact (not_le_of_gt hlt) hbad

end GaloisForLFunctions.RHTower

end
