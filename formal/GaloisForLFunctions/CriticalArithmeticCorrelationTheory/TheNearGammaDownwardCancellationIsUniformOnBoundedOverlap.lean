import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilResidualIsTheUpwardDefect

/-!
# Uniform near-Gamma and full downward cancellation

The exact Mangoldt divisor identity cancels the near-pair logarithm. On a bounded overlap
interval, the remaining coefficient and near-row geometry have common bounds. Exterior prime
products occupy one fixed boundary strip. Their full signed source and the near center block
therefore vanish uniformly after logarithmic normalization.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The near-row radius increases with nonnegative overlap. -/
theorem nearRowRadius_mono {c K : ℝ} (hc : 0 ≤ c) (hcK : c ≤ K) :
    nearRowRadius c ≤ nearRowRadius K := by
  have h2 := mul_le_mul_of_nonneg_left hcK zero_le_two
  exact mul_le_mul h2 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (mul_nonneg zero_le_two (hc.trans hcK))

/-- Every smaller overlap uses a smaller exterior prime-product strip. -/
theorem exteriorPrimeStrip_mono {c K : ℝ} (hc : 0 ≤ c) (hcK : c ≤ K) :
    exteriorPrimeStrip c ≤ exteriorPrimeStrip K := by
  apply Nat.ceil_mono
  exact mul_le_mul hcK (Real.exp_le_exp.mpr hcK) (Real.exp_pos c).le (hc.trans hcK)

/-- The exact logarithmic cancellation leaves a common bounded coefficient throughout the overlap interval. -/
theorem exists_nearGammaDownwardCoefficient_uniform_overlap_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) (m : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
      ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
        |nearGammaDownwardCoefficient φ c N m n j| ≤ E := by
  obtain ⟨C, hC, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let B := nearRowRadius K
  let A : ℝ := m.totient
  let J := ramanujanJetBound m
  have hB : 0 ≤ B := by
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    dsimp only [B, nearRowRadius]
    positivity
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hJ : 0 ≤ J := sum_nonneg fun _ _ => abs_nonneg _
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  refine ⟨(C + B + Real.log K) * A + J, by positivity, ?_⟩
  intro c hc1 hcK N hN hw1 n hn j hj
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hR := nearRowRadius_mono hc.le hcK
  have hlogc : |Real.log c| ≤ Real.log K := by
    rw [abs_of_nonneg (Real.log_nonneg hc1)]
    exact Real.log_le_log hc hcK
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hjN := (mem_filter.mp hj).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
  have hw0 : 0 < c / N := div_pos hc hN0
  have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
    have h := (mem_filter.mp hj).2.2
    change |Real.log j - Real.log n| ≤ 2 * c / N at h
    simpa only [mul_div_assoc] using h
  let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)
  let a := atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2)
  have hrem : |a - Real.log (1 / (c / N)) * q| ≤ C := by
    simpa only [a, q, mul_div_assoc] using hpair (c / N) hw0 hw1 n j hs
  have hq : |q| ≤ 1 := by
    have h := abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp)
      (|Real.log j - Real.log n| / (c / N))
    change |shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ ∫ u, φ u ^ 2 at h
    dsimp only [q]
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact h
  have hcm : |ramanujanLagCoefficient m j| ≤ A :=
    BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j
  have hjb : |ramanujanLogDivisorJet m j| ≤ J := abs_ramanujanLogDivisorJet_le m j
  have hquot : (N : ℝ) / j ≤ B :=
    ((div_le_iff₀ hj0).mpr (nearRow_geometry hc hn hj).2.2).trans hR
  have hloglow : 0 ≤ Real.log N - Real.log j := sub_nonneg.mpr
    (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
  have hloghigh : Real.log N - Real.log j ≤ B := by
    have h := Real.log_le_sub_one_of_pos (div_pos hN0 hj0)
    rw [Real.log_div hN0.ne' hj0.ne'] at h
    linarith only [h, hquot]
  have hlogeq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc.ne' hN0.ne']
    ring
  have hlog : |Real.log (1 / (c / N)) - Real.log j| ≤ B + |Real.log c| := by
    rw [hlogeq, show Real.log N - Real.log c - Real.log j =
      (Real.log N - Real.log j) - Real.log c by ring]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hloglow]; linarith only [hloghigh])
  have heq : nearGammaDownwardCoefficient φ c N m n j =
      (a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j +
      (Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j +
      q * ramanujanLogDivisorJet m j := by
    rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m
      (mem_Icc.mp hjN).1]
    dsimp only [a, q]
    ring
  rw [heq]
  calc
    _ ≤ |(a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j| +
        |(Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j| +
        |q * ramanujanLogDivisorJet m j| := abs_add_three _ _ _
    _ ≤ C * A + (B + |Real.log c|) * A + J := by
      simp only [abs_mul]
      have h1 := mul_le_mul hrem hcm (abs_nonneg _) hC
      have h2 := mul_le_mul (mul_le_mul hlog hq (abs_nonneg _) (by positivity))
        hcm (abs_nonneg _) (by positivity)
      have h3 := mul_le_mul hq hjb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simp only [mul_one, one_mul] at h2 h3
      linarith only [h1, h2, h3]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hlogc hA
      linarith only [h]

/-- Interior near-Gamma cancellation has bounded squared row mass uniformly on bounded overlap. -/
theorem exists_nearGammaDownwardRow_sq_uniform_overlap_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ N : ℕ, 1 ≤ N → c / N ≤ 1 / 3 →
      (∑ n ∈ Icc 1 N, nearGammaDownwardRow φ c N m n ^ 2) ≤ C := by
  obtain ⟨E, hE, hbound⟩ := exists_nearGammaDownwardCoefficient_uniform_overlap_bound hφ hsupp hM hK m
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  refine ⟨4 * nearRowRadius K ^ 3 * E ^ 2, by unfold nearRowRadius; positivity, ?_⟩
  intro c hc1 hcK N hN hw
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hR := nearRowRadius_mono hc.le hcK
  have hR0 : 0 ≤ nearRowRadius c := by unfold nearRowRadius; positivity
  have hpow : nearRowRadius c ^ 3 ≤ nearRowRadius K ^ 3 := by
    exact pow_le_pow_left₀ hR0 hR 3
  exact (sum_near_div_sqrt_sq_le hc hN (nearGammaDownwardCoefficient φ c N m)
    (hbound c hc1 hcK N hN hw)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (sq_nonneg E))

/-- The interior residual vanishes uniformly after logarithmic normalization. -/
theorem eventually_normalizedNearGammaDownwardVector_norm_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ‖normalizedNearGammaDownwardVector φ c N m‖ ≤ ε := by
  obtain ⟨C, hC, hbound⟩ := exists_nearGammaDownwardRow_sq_uniform_overlap_bound hφ hsupp hM hK m
  have hlim : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈3 * K⌉₊,
    hlim.eventually (ge_mem_nhds (sq_pos_of_pos hε))] with N hN hNK hsmall
  intro c hc1 hcK
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hKN : 3 * K ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNK)
  have hw : c / (N : ℝ) ≤ 1 / 3 := by
    rw [div_le_iff₀ hN0]
    linarith only [hKN, hcK]
  have h := (div_le_div_of_nonneg_right (hbound c hc1 hcK N hN hw) (Real.log_natCast_nonneg N)).trans hsmall
  rw [← normalizedNearGammaDownwardVector_norm_sq] at h
  nlinarith only [h, hε, norm_nonneg (normalizedNearGammaDownwardVector φ c N m)]

/-- Every exterior downward prime product has one vanishing normalized bound over bounded overlap. -/
theorem eventually_normalizedExteriorDownwardVector_norm_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      ‖normalizedExteriorDownwardVector φ c N m‖ ≤ ε := by
  let C := ((exteriorPrimeStrip K : ℝ) + 1) * (2 * m.totient * exteriorPrimeStrip K) ^ 2
  have hlim : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 1, hlim.eventually (ge_mem_nhds (sq_pos_of_pos hε))]
    with N hN hsmall
  intro c hc hcK
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hB : (exteriorPrimeStrip c : ℝ) ≤ exteriorPrimeStrip K := by
    exact_mod_cast exteriorPrimeStrip_mono hc.le hcK
  have hconst : ((exteriorPrimeStrip c : ℝ) + 1) * (2 * m.totient * exteriorPrimeStrip c) ^ 2 ≤ C := by
    dsimp only [C]
    gcongr
  have hsum := (sum_actualExteriorDownwardRow_sq_le hg.continuous hc hN hgsupp hG m).trans hconst
  have h := (div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)).trans hsmall
  rw [← normalizedExteriorDownwardVector_norm_sq] at h
  nlinarith only [h, hε, norm_nonneg (normalizedExteriorDownwardVector φ c N m)]

/-- Near Gamma cancels the full infinite downward action at one common bounded-overlap horizon. -/
theorem eventually_normalizedFullNearGammaDownwardVector_norm_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ‖normalizedFullNearGammaDownwardVector φ c N m‖ ≤ ε := by
  filter_upwards [eventually_normalizedNearGammaDownwardVector_norm_uniform_overlap hφ hsupp hM hK m
      (half_pos hε),
    eventually_normalizedExteriorDownwardVector_norm_uniform_overlap hφ hsupp hM (K := K) m (half_pos hε)] with N hnear hext
  intro c hc1 hcK
  have hc : 0 < c := zero_lt_one.trans_le hc1
  rw [normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc]
  exact (norm_sub_le _ _).trans (by linarith only [hnear c hc1 hcK, hext c hc hcK])

/-- The near center error has one vanishing norm bound throughout bounded overlap. -/
theorem eventually_nearCenterVector_norm_uniform_overlap {φ : ℝ → ℝ}
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ‖nearCenterVector φ c N m‖ ≤ ε := by
  let A := completeWeilPoleShift φ K * (1 + Real.exp (1 / 2)) *
    ∑ i ∈ range m, |normalizedRamanujanMode m i|
  let C := 4 * nearRowRadius K ^ 3 * A ^ 2
  have hlim : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈2 * K⌉₊,
    hlim.eventually (ge_mem_nhds (sq_pos_of_pos hε))] with N hN hNK hsmall
  intro c hc1 hcK
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hKN : 2 * K ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNK)
  have hcN : 2 * c ≤ (N : ℝ) := by linarith only [hKN, hcK]
  have hα : |completeWeilPoleShift φ c| ≤ completeWeilPoleShift φ K := by
    have hα0 : 0 ≤ completeWeilPoleShift φ c := by unfold completeWeilPoleShift; positivity
    rw [abs_of_nonneg hα0]
    unfold completeWeilPoleShift
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcK (sq_nonneg _)) hM.le
  have hentry (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ nearRowIndices c N n) :
      |completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j| ≤ A :=
    (abs_nearCenter_entry_le hm hN hcN hn hj).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hα (by positivity)) (sum_nonneg fun _ _ => abs_nonneg _))
  have hR : nearRowRadius c ≤ nearRowRadius K := nearRowRadius_mono hc.le hcK
  have hR0 : 0 ≤ nearRowRadius c := by unfold nearRowRadius; positivity
  have hsum := sum_near_div_sqrt_sq_le hc hN
    (fun n j => completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j)
    hentry
  have hconst : 4 * nearRowRadius c ^ 3 * A ^ 2 ≤ C :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR0 hR 3) (by norm_num)) (sq_nonneg A)
  have h := (div_le_div_of_nonneg_right (hsum.trans hconst) (Real.log_natCast_nonneg N)).trans hsmall
  rw [← nearCenterVector_norm_sq] at h
  nlinarith only [h, hε, norm_nonneg (nearCenterVector φ c N m)]

/-- The explicit spline has uniform full downward cancellation without a profile premise. -/
theorem eventually_tiltedUnitSpline_fullNearGammaDownward_norm_uniform_overlap
    {K : ℝ} (hK : 1 ≤ K) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ‖normalizedFullNearGammaDownwardVector tiltedUnitSpline c N m‖ ≤ ε :=
  eventually_normalizedFullNearGammaDownwardVector_norm_uniform_overlap contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hK m hε

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_normalizedFullNearGammaDownwardVector_norm_uniform_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_nearCenterVector_norm_uniform_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_fullNearGammaDownward_norm_uniform_overlap
