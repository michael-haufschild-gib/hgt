import GaloisForLFunctions.RHTower.ProlateCanonicalOscillatorLower

open Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Uniform asymptotic properness of the canonical index-to-separation map.  Above a fixed
aperture, every index past one finite cutoff has oscillator separation above any prescribed
energy.  Only one fixed-index lower law is needed; global index order propagates it to the entire
moving tail. -/
theorem eventually_uniform_indexedOscillatorSeparation_gt (M : ℝ) :
    ∃ N : ℕ, ∀ᶠ a : ProlatePositiveAperture in atTop,
      ∀ n : ℕ, N ≤ n → M < indexedOscillatorSeparation n a := by
  obtain ⟨N, hN⟩ := exists_nat_gt (M / 4)
  refine ⟨N, ?_⟩
  have hNlower :=
    eventually_evenOscillatorRung_sub_lt_indexedOscillatorSeparation
      N (ε := 1) zero_lt_one
  filter_upwards [hNlower] with a ha
  intro n hn
  have hMN : M < 4 * (N : ℝ) := by
    simpa [mul_comm] using
      (div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hN
  calc
    M < 4 * (N : ℝ) := hMN
    _ < indexedOscillatorSeparation N a := by linarith
    _ ≤ indexedOscillatorSeparation n a :=
      indexedOscillatorSeparation_monotone a hn

/-- Any moving canonical mode with eventually bounded oscillator energy has eventually bounded
index.  This is the varying-family compactness statement missing from fixed-rung asymptotics. -/
theorem exists_eventually_index_lt_of_indexedOscillatorSeparation_bounded
    (nu : ProlatePositiveAperture → ℕ) {M : ℝ}
    (hM : ∀ᶠ a : ProlatePositiveAperture in atTop,
      indexedOscillatorSeparation (nu a) a ≤ M) :
    ∃ N : ℕ, ∀ᶠ a : ProlatePositiveAperture in atTop, nu a < N := by
  obtain ⟨N, hproper⟩ := eventually_uniform_indexedOscillatorSeparation_gt M
  refine ⟨N, ?_⟩
  filter_upwards [hproper, hM] with a ha hbound
  by_contra hnot
  exact (not_lt_of_ge hbound) (ha (nu a) (Nat.le_of_not_gt hnot))

/-- Cofinal index escape forces oscillator energy escape. -/
theorem tendsto_indexedOscillatorSeparation_comp_atTop_of_tendsto_index
    (nu : ProlatePositiveAperture → ℕ) (hnu : Tendsto nu atTop atTop) :
    Tendsto (fun a => indexedOscillatorSeparation (nu a) a) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  obtain ⟨N, hproper⟩ := eventually_uniform_indexedOscillatorSeparation_gt M
  have hnuN : ∀ᶠ a : ProlatePositiveAperture in atTop, N ≤ nu a :=
    hnu.eventually (eventually_ge_atTop N)
  filter_upwards [hproper, hnuN] with a ha hna
  exact (ha (nu a) hna).le

/-- Conversely, oscillator-energy escape forces canonical index escape. -/
theorem tendsto_index_atTop_of_tendsto_indexedOscillatorSeparation_comp
    (nu : ProlatePositiveAperture → ℕ)
    (hmu : Tendsto (fun a => indexedOscillatorSeparation (nu a) a) atTop atTop) :
    Tendsto nu atTop atTop := by
  apply tendsto_atTop.2
  intro N
  have hmuBig : ∀ᶠ a : ProlatePositiveAperture in atTop,
      4 * (N : ℝ) + 2 ≤ indexedOscillatorSeparation (nu a) a :=
    hmu.eventually (eventually_ge_atTop (4 * (N : ℝ) + 2))
  have hNUpper :=
    eventually_indexedOscillatorSeparation_lt_evenOscillatorRung_add
      N (ε := 1) zero_lt_one
  filter_upwards [hmuBig, hNUpper] with a hbig hupp
  by_contra hnot
  have hnuN : nu a ≤ N := Nat.le_of_not_ge hnot
  have hle := indexedOscillatorSeparation_monotone a hnuN
  linarith

/-- Canonical mode index escapes exactly when its oscillator separation escapes. -/
theorem tendsto_indexedOscillatorSeparation_comp_atTop_iff
    (nu : ProlatePositiveAperture → ℕ) :
    Tendsto (fun a => indexedOscillatorSeparation (nu a) a) atTop atTop ↔
      Tendsto nu atTop atTop := by
  constructor
  · exact tendsto_index_atTop_of_tendsto_indexedOscillatorSeparation_comp nu
  · exact tendsto_indexedOscillatorSeparation_comp_atTop_of_tendsto_index nu

/-- **Moving-family index locking.**  If a varying canonical prolate mode has any finite
oscillator-separation limit, its index is eventually constant and the limit is exactly that
index's even Hermite rung.  Thus no moving-index subsequence can fake a finite rung. -/
theorem exists_eventually_index_eq_of_tendsto_indexedOscillatorSeparation
    (nu : ProlatePositiveAperture → ℕ) {m : ℝ}
    (hmu : Tendsto (fun a => indexedOscillatorSeparation (nu a) a) atTop (nhds m)) :
    ∃ n : ℕ, (∀ᶠ a : ProlatePositiveAperture in atTop, nu a = n) ∧
      m = 4 * (n : ℝ) + 1 := by
  have hmuUpper : ∀ᶠ a : ProlatePositiveAperture in atTop,
      indexedOscillatorSeparation (nu a) a ≤ m + 1 :=
    hmu.eventually (Iic_mem_nhds (by linarith))
  obtain ⟨N, hnuN⟩ :=
    exists_eventually_index_lt_of_indexedOscillatorSeparation_bounded nu hmuUpper
  have hfreqRange : ∃ᶠ a : ProlatePositiveAperture in atTop,
      ∃ n ∈ Finset.range N, nu a = n := by
    exact hnuN.frequently.mono fun a ha =>
      ⟨nu a, Finset.mem_range.mpr ha, rfl⟩
  obtain ⟨n, hnN, hfreqN⟩ :=
    (Finset.frequently_exists (Finset.range N)).mp hfreqRange
  have hfixedN := tendsto_indexedOscillatorSeparation_atTop n
  have heqN : m = 4 * (n : ℝ) + 1 :=
    tendsto_nhds_unique_of_frequently_eq hmu hfixedN
      (hfreqN.mono fun a ha => by simp [ha])
  refine ⟨n, ?_, heqN⟩
  by_contra hnotEventually
  have hfreqNe : ∃ᶠ a : ProlatePositiveAperture in atTop, nu a ≠ n :=
    Filter.not_eventually.mp hnotEventually
  have hfreqOther : ∃ᶠ a : ProlatePositiveAperture in atTop,
      ∃ k ∈ Finset.range N, k ≠ n ∧ nu a = k := by
    exact hnuN.and_frequently hfreqNe |>.mono fun a ha =>
      ⟨nu a, Finset.mem_range.mpr ha.1, ha.2, rfl⟩
  obtain ⟨k, hkN, hfreqK⟩ :=
    (Finset.frequently_exists (Finset.range N)).mp hfreqOther
  have hfixedK := tendsto_indexedOscillatorSeparation_atTop k
  have heqK : m = 4 * (k : ℝ) + 1 :=
    tendsto_nhds_unique_of_frequently_eq hmu hfixedK
      (hfreqK.mono fun a ha => by simp [ha.2])
  have hnk : n = k := by
    exact_mod_cast (by linarith [heqN, heqK] : (n : ℝ) = (k : ℝ))
  exact hfreqK (Filter.Eventually.of_forall fun _ ha => ha.1 hnk.symm)

end GaloisForLFunctions.RHTower
