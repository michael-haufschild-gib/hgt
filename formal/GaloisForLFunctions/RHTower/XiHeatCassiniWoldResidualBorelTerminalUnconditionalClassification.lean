import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualMertensInverseAbel

/-!
# Unconditional positive-Borel terminal classification

This module removes the critical mesh-energy premise from the Route-T terminal criterion.
Terminal decay gives an ordered residual rate.  The corpus local increment theorem transfers that
rate to consecutive prime-log gaps.  A new exact between-prime interpolation then supplies every
strict natural-cutoff Wold rate, and the inverse-Abel criterion recovers RH.

The same argument classifies literal finite positive-ray Borel landing without any auxiliary
hypothesis.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every natural cutoff at least two lies in a unique consecutive-prime shell (existence form). -/
theorem exists_nthPrime_bracket (N : ℕ) (hN : 2 ≤ N) :
    ∃ k : ℕ, (nthPrimeSubtype k : ℕ) ≤ N ∧
      N < (nthPrimeSubtype (k + 1) : ℕ) := by
  let P : Finset ℕ := (Finset.Icc 0 N).filter Nat.Prime
  have hTwoMem : 2 ∈ P := by
    simp only [P, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hN⟩, Nat.prime_two⟩
  have hP : P.Nonempty := ⟨2, hTwoMem⟩
  let p : ℕ := P.max' hP
  have hpMem : p ∈ P := Finset.max'_mem P hP
  have hpBounds : 0 ≤ p ∧ p ≤ N := (Finset.mem_Icc.1 (Finset.mem_filter.1 hpMem).1)
  have hpPrime : p.Prime := (Finset.mem_filter.1 hpMem).2
  let k : ℕ := nthPrimeEquiv.symm ⟨p, hpPrime⟩
  have hkPrime : nthPrimeSubtype k = ⟨p, hpPrime⟩ := by
    exact nthPrimeEquiv.apply_symm_apply ⟨p, hpPrime⟩
  refine ⟨k, ?_, ?_⟩
  · simpa only [hkPrime] using hpBounds.2
  · by_contra hle
    have hsuccLe : (nthPrimeSubtype (k + 1) : ℕ) ≤ N := by omega
    have hsuccMem : (nthPrimeSubtype (k + 1) : ℕ) ∈ P := by
      simp only [P, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hsuccLe⟩, (nthPrimeSubtype (k + 1)).prop⟩
    have hmax : (nthPrimeSubtype (k + 1) : ℕ) ≤ p := by
      exact Finset.le_max' P _ hsuccMem
    have hstrict : p < (nthPrimeSubtype (k + 1) : ℕ) := by
      have := nthPrimeSubtype_strictMono (Nat.lt_succ_self k)
      simpa only [hkPrime] using this
    omega

/-- Wold cumulative mass is constant inside a consecutive-prime shell. -/
theorem woldNatWeightSum_eq_nthPrime_of_bracket
    {N k : ℕ} (hleft : (nthPrimeSubtype k : ℕ) ≤ N)
    (hright : N < (nthPrimeSubtype (k + 1) : ℕ)) :
    xiHeatCassiniWoldNatWeightSum N =
      xiHeatCassiniWoldNatWeightSum (nthPrimeSubtype k : ℕ) := by
  rw [xiHeatCassiniWoldNatWeightSum, xiHeatCassiniWoldNatWeightSum]
  symm
  apply Finset.sum_subset
  · exact Finset.Icc_subset_Icc le_rfl hleft
  · intro n hnLarge hnSmall
    have hnBounds := Finset.mem_Icc.1 hnLarge
    have hnLeft : (nthPrimeSubtype k : ℕ) < n := by
      by_contra hnot
      exact hnSmall (Finset.mem_Icc.2 ⟨hnBounds.1, Nat.le_of_not_gt hnot⟩)
    have hnRight : n < (nthPrimeSubtype (k + 1) : ℕ) := hnBounds.2.trans_lt hright
    have hnNotPrime : ¬ n.Prime := by
      intro hnPrime
      let m : ℕ := nthPrimeEquiv.symm ⟨n, hnPrime⟩
      have hmval : (nthPrimeSubtype m : ℕ) = n := by
        change ((nthPrimeEquiv m : Nat.Primes) : ℕ) = n
        rw [show nthPrimeEquiv m = (⟨n, hnPrime⟩ : Nat.Primes) by simp [m]]
      have hkm : k < m := by
        by_contra hnot
        have hmono := nthPrimeSubtype_strictMono.monotone (Nat.le_of_not_gt hnot)
        change (nthPrimeSubtype m : ℕ) ≤ (nthPrimeSubtype k : ℕ) at hmono
        rw [hmval] at hmono
        omega
      have hmk : m < k + 1 := by
        by_contra hnot
        have hmono := nthPrimeSubtype_strictMono.monotone (Nat.le_of_not_gt hnot)
        change (nthPrimeSubtype (k + 1) : ℕ) ≤ (nthPrimeSubtype m : ℕ) at hmono
        rw [hmval] at hmono
        omega
      omega
    simp only [xiHeatCassiniWoldNatWeight, dif_neg hnNotPrime]

/-- Between primes, natural residual is controlled exactly by left residual plus shell log-gap. -/
theorem abs_woldNatResidual_le_ordered_add_primeLogGap_of_bracket
    {N k : ℕ} (hleft : (nthPrimeSubtype k : ℕ) ≤ N)
    (hright : N < (nthPrimeSubtype (k + 1) : ℕ)) :
    |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| +
        xiHeatCassiniOrderedPrimeLogGap k := by
  have hmass := woldNatWeightSum_eq_nthPrime_of_bracket hleft hright
  have hp0 : (0 : ℝ) < (nthPrimeSubtype k : ℕ) := by
    exact_mod_cast (nthPrimeSubtype k).prop.pos
  have hN0 : (0 : ℝ) < N := hp0.trans_le (by exact_mod_cast hleft)
  have hleftReal : ((nthPrimeSubtype k : ℕ) : ℝ) ≤ N := by exact_mod_cast hleft
  have hrightReal : (N : ℝ) ≤ (nthPrimeSubtype (k + 1) : ℕ) := by
    exact_mod_cast hright.le
  have hlogLeft : Real.log (nthPrimeSubtype k : ℝ) ≤ Real.log N :=
    Real.log_le_log hp0 hleftReal
  have hlogRight : Real.log N ≤ Real.log (nthPrimeSubtype (k + 1) : ℝ) :=
    Real.log_le_log hN0 hrightReal
  have hsplit : xiHeatCassiniWoldNatResidualLogDiscrepancy N =
      xiHeatCassiniOrderedWoldResidualLogDiscrepancy k -
        (Real.log N - xiMassNthPrimeLogHeight k) := by
    rw [xiHeatCassiniWoldNatResidualLogDiscrepancy,
      xiHeatCassiniOrderedWoldResidualLogDiscrepancy,
      xiHeatCassiniOrderedWoldLogDiscrepancy,
      xiHeatCassiniOrderedWoldPartialMass_eq_natWeightSum,
      xiMassNthPrimeLogHeight, hmass]
    ring
  rw [hsplit]
  calc
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k -
        (Real.log N - xiMassNthPrimeLogHeight k)| ≤
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| +
        |Real.log N - xiMassNthPrimeLogHeight k| := abs_sub _ _
    _ = |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| +
        (Real.log N - xiMassNthPrimeLogHeight k) := by
      congr 1
      exact abs_of_nonneg (by
        simpa only [xiMassNthPrimeLogHeight] using sub_nonneg.mpr hlogLeft)
    _ ≤ |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| +
        xiHeatCassiniOrderedPrimeLogGap k := by
      apply add_le_add le_rfl
      unfold xiHeatCassiniOrderedPrimeLogGap xiMassNthPrimeLogHeight
      linarith

/-- Terminal decay at rate `c` gives every natural Wold power rate `a<c`. -/
theorem exists_woldNatResidual_power_rate_of_ordered_terminal
    {a c : ℝ} (ha0 : 0 < a) (hac : a < c) (hcHalf : c < 1 / 2)
    (hterminal : Tendsto (fun k : ℕ ↦
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| *
        Real.exp (c * xiMassNthPrimeLogHeight k)) atTop (𝓝 0)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        D * (N : ℝ) ^ (-a) := by
  have hc0 : 0 < c := ha0.trans hac
  have hsmall : ∀ᶠ k : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| *
          Real.exp (c * xiMassNthPrimeLogHeight k) < 1 :=
    hterminal (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hrateC : ∀ᶠ k : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| ≤
        1 * Real.exp (-c * xiMassNthPrimeLogHeight k) := by
    filter_upwards [hsmall] with k hk
    calc
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| =
          (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| *
            Real.exp (c * xiMassNthPrimeLogHeight k)) *
              Real.exp (-c * xiMassNthPrimeLogHeight k) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
        simp
      _ ≤ 1 * Real.exp (-c * xiMassNthPrimeLogHeight k) :=
        mul_le_mul_of_nonneg_right hk.le (Real.exp_nonneg _)
  have hrateA : ∀ᶠ k : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| ≤
        Real.exp (-a * xiMassNthPrimeLogHeight k) := by
    filter_upwards [hrateC] with k hk
    calc
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| ≤
          1 * Real.exp (-c * xiMassNthPrimeLogHeight k) := hk
      _ ≤ Real.exp (-a * xiMassNthPrimeLogHeight k) := by
        simp only [one_mul]
        apply Real.exp_le_exp.mpr
        have hh := xiMassNthPrimeLogHeight_pos k
        nlinarith
  obtain ⟨C, hC, hgap⟩ :=
    exists_primeLogGap_exp_rate_of_residual_exp_height_rate
      ha0 hac (by linarith) (by norm_num) hrateC
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hrateA.and hgap)
  let D : ℝ := (1 + C) * Real.exp a
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  filter_upwards [eventually_ge_atTop (nthPrimeSubtype K : ℕ)] with N hN
  have hN2 : 2 ≤ N := (nthPrimeSubtype K).prop.two_le.trans hN
  obtain ⟨k, hkLeft, hkRight⟩ := exists_nthPrime_bracket N hN2
  have hKk : K ≤ k := by
    by_contra hnot
    have hkSuccK : k + 1 ≤ K := by omega
    have hmono := nthPrimeSubtype_strictMono.monotone hkSuccK
    change (nthPrimeSubtype (k + 1) : ℕ) ≤ (nthPrimeSubtype K : ℕ) at hmono
    omega
  obtain ⟨hRk, hGapk⟩ := hK k hKk
  have hinterp :=
    abs_woldNatResidual_le_ordered_add_primeLogGap_of_bracket hkLeft hkRight
  have hmeshOne := xiHeatCassiniOrderedPrimeLogGap_le_one k
  have hp0 : (0 : ℝ) < (nthPrimeSubtype k : ℕ) := by
    exact_mod_cast (nthPrimeSubtype k).prop.pos
  have hN0 : (0 : ℝ) < N := hp0.trans_le (by exact_mod_cast hkLeft)
  have hlogLeft : Real.log (nthPrimeSubtype k : ℝ) ≤ Real.log N :=
    Real.log_le_log hp0 (by exact_mod_cast hkLeft)
  have hlogRight : Real.log N ≤ Real.log (nthPrimeSubtype (k + 1) : ℝ) :=
    Real.log_le_log hN0 (by exact_mod_cast hkRight.le)
  have hlogWindow : Real.log N ≤ xiMassNthPrimeLogHeight k + 1 := by
    unfold xiHeatCassiniOrderedPrimeLogGap xiMassNthPrimeLogHeight at hmeshOne
    unfold xiMassNthPrimeLogHeight
    linarith
  have hconvert : Real.exp (-a * xiMassNthPrimeLogHeight k) ≤
      Real.exp a * (N : ℝ) ^ (-a) := by
    rw [Real.rpow_def_of_pos hN0]
    calc
      Real.exp (-a * xiMassNthPrimeLogHeight k) ≤
          Real.exp (-a * Real.log N + a) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = Real.exp a * Real.exp (Real.log N * -a) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| +
          xiHeatCassiniOrderedPrimeLogGap k := hinterp
    _ ≤ Real.exp (-a * xiMassNthPrimeLogHeight k) +
        C * Real.exp (-a * xiMassNthPrimeLogHeight k) :=
      add_le_add hRk hGapk
    _ = (1 + C) * Real.exp (-a * xiMassNthPrimeLogHeight k) := by ring
    _ ≤ (1 + C) * (Real.exp a * (N : ℝ) ^ (-a)) :=
      mul_le_mul_of_nonneg_left hconvert (by positivity)
    _ = D * (N : ℝ) ^ (-a) := by
      dsimp only [D]
      ring

/-- Exact positive-ray terminal decay throughout the strict half-sector is unconditionally RH. -/
theorem riemannHypothesis_iff_subhalf_woldResidualBorelTerminalWeight_unconditional :
    RiemannHypothesis ↔
      ∀ y : ℝ, 0 < y → y < 1 / 2 →
        Tendsto (fun k : ℕ ↦
          |xiHeatCassiniOrderedWoldResidualLogDiscrepancy k| *
            Real.exp (y * xiMassNthPrimeLogHeight k)) atTop (𝓝 0) := by
  constructor
  · intro hRH y hy0 hyHalf
    exact tendsto_woldResidualBorelTerminalWeight_zero_of_riemannHypothesis
      hRH hy0.le hyHalf
  · intro hterminal
    apply riemannHypothesis_iff_woldNatResidualAllStrictHalfPowerRate.2
    intro eps heps0 hepsHalf
    let a : ℝ := 1 / 2 - eps
    let c : ℝ := (a + 1 / 2) / 2
    have ha0 : 0 < a := by dsimp only [a]; linarith
    have hac : a < c := by dsimp only [c, a]; linarith
    have hcHalf : c < 1 / 2 := by dsimp only [c, a]; linarith
    obtain ⟨D, hD, hrate⟩ :=
      exists_woldNatResidual_power_rate_of_ordered_terminal
        ha0 hac hcHalf (hterminal c (ha0.trans hac) hcHalf)
    refine ⟨D, hD, ?_⟩
    simpa only [a] using hrate

/-- Literal finite positive-Borel landing throughout the strict half-sector is unconditionally RH. -/
theorem riemannHypothesis_iff_subhalf_woldResidualBorelFiniteLanding_unconditional :
    RiemannHypothesis ↔
      ∀ x y : ℝ, 0 < y → y < 1 / 2 →
        Tendsto (fun N : ℕ ↦
          xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent x y N -
            ∫ t : ℝ in Ioi 0,
              ∑ n ∈ Finset.range N,
                xiHeatCassiniWoldResidualBorelUpperRaySourceLaplaceAtom x y n t)
          atTop (𝓝 0) := by
  constructor
  · intro hRH x y hy0 hyHalf
    exact
      tendsto_woldResidualBorelFiniteRenormalized_sub_raw_zero_of_riemannHypothesis
        hRH x hy0.le hyHalf
  · intro hlanding
    apply
      riemannHypothesis_iff_subhalf_woldResidualBorelTerminalWeight_unconditional.2
    intro y hy0 hyHalf
    have h := hlanding 0 y hy0 hyHalf
    rw [tendsto_xiHeatCassiniWoldResidualBorelUpperRayFiniteRenormalizedCurrent_sub_edgeIntegral_zero_iff]
      at h
    simpa only [mul_comm] using h

end
end RHTower
