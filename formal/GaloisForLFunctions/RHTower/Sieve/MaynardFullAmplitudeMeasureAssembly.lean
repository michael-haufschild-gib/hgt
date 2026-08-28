import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockSpatialL2

noncomputable section
namespace RHTower.Sieve

open Filter Set MeasureTheory

/-- Exact bad-measure assembly for a capped base-plus-dyadic-band packet decomposition. -/
theorem measureReal_maynardFixedAmbientPhysicalDefectPacket_full_le_base_add_sum_bands
    {x N R H v D : ℝ} {Q : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hv : 0 < v) (hD : 0 < D) (hQ : 0 < Q)
    (U : Finset ℕ) (a : ℝ → ℂ) (ha : Continuous a) (c : ℕ → ℝ)
    (hcap : ∀ m ∈ U, ‖a (c m)‖ < ((2 ^ Q : ℕ) : ℝ) * v)
    (Kbase : ℝ) (Kband : ℕ → ℝ)
    (hbaseMeasure :
      (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D / 2 ≤
          ‖maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellBaseAmplitudeSet U a c v)
            a lambda N R H 1‖} ≤ Kbase)
    (hbandMeasure : ∀ q ∈ Finset.range Q,
      (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D / (2 * (Q : ℝ)) ≤
          ‖maynardFixedAmbientPhysicalDefectPacket
            (maynardUnitCellAmplitudeBand U a c (((2 ^ q : ℕ) : ℝ) * v))
            a lambda N R H 1‖} ≤ Kband q) :
    (volume.restrict (Set.Icc x (2 * x))).real
      {lambda | D ≤
        ‖maynardFixedAmbientPhysicalDefectPacket U a lambda N R H 1‖} ≤
      Kbase + ∑ q ∈ Finset.range Q, Kband q := by
  let base : Finset ℕ := maynardUnitCellBaseAmplitudeSet U a c v
  let band : ℕ → Finset ℕ := fun q =>
    maynardUnitCellAmplitudeBand U a c (((2 ^ q : ℕ) : ℝ) * v)
  let E : Finset ℕ → ℝ → ℂ := fun S lambda =>
    maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1
  let bad : Set ℝ := {lambda | D ≤ ‖E U lambda‖}
  let badBase : Set ℝ := {lambda | D / 2 ≤ ‖E base lambda‖}
  let badBand : ℕ → Set ℝ := fun q =>
    {lambda | D / (2 * (Q : ℝ)) ≤ ‖E (band q) lambda‖}
  let μ : Measure ℝ := volume.restrict (Set.Icc x (2 * x))
  have hQreal : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hsub : ∀ᵐ lambda ∂μ,
      lambda ∈ bad →
        lambda ∈ badBase ∪ ⋃ q ∈ Finset.range Q, badBand q := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    intro hlambdaBad
    by_cases hbaseLarge : D / 2 ≤ ‖E base lambda‖
    · exact Set.mem_union_left _ hbaseLarge
    · have hlambdaPos : 0 < lambda :=
        lt_of_lt_of_le zero_lt_one (hx.trans hlambda.1)
      have hbaseSmall : ‖E base lambda‖ < D / 2 := lt_of_not_ge hbaseLarge
      obtain ⟨q, hqQ, hqLarge⟩ :=
        exists_large_maynardFixedAmbientPhysicalDefectPacket_amplitudeBand
          (U := U) (Aline := a) (c := c) hv hQ hcap
            ha hlambdaPos hN hR hH hlambdaBad hbaseSmall
      have hqLarge' : D / (2 * (Q : ℝ)) ≤ ‖E (band q) lambda‖ := by
        rw [show D / (2 * (Q : ℝ)) = (D / 2) / (Q : ℝ) by field_simp]
        apply (div_le_iff₀ hQreal).2
        simpa only [E, band, base, mul_comm] using hqLarge
      apply Set.mem_union_right
      apply Set.mem_iUnion_of_mem q
      apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr hqQ)
      exact hqLarge'
  have hmeasure : μ.real bad ≤
      μ.real (badBase ∪ ⋃ q ∈ Finset.range Q, badBand q) := by
    have hmono : μ bad ≤ μ (badBase ∪ ⋃ q ∈ Finset.range Q, badBand q) :=
      measure_mono_ae hsub
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) hmono
  have hunion : μ.real (⋃ q ∈ Finset.range Q, badBand q) ≤
      ∑ q ∈ Finset.range Q, μ.real (badBand q) :=
    measureReal_biUnion_finset_le _ _
  calc
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket U a lambda N R H 1‖} =
      μ.real bad := rfl
    _ ≤ μ.real (badBase ∪ ⋃ q ∈ Finset.range Q, badBand q) := hmeasure
    _ ≤ μ.real badBase + μ.real (⋃ q ∈ Finset.range Q, badBand q) :=
      measureReal_union_le _ _
    _ ≤ μ.real badBase + ∑ q ∈ Finset.range Q, μ.real (badBand q) :=
      add_le_add_right hunion _
    _ ≤ Kbase + ∑ q ∈ Finset.range Q, Kband q := by
      apply add_le_add
      · simpa only [μ, badBase, E, base] using hbaseMeasure
      · exact Finset.sum_le_sum fun q hq => by
          simpa only [μ, badBand, E, band] using hbandMeasure q hq

end RHTower.Sieve
