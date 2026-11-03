import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponent

/-!
# Maximal Möbius growth in the product topology

Every finite-coordinate Liouville tail has a nonzero linear mean. Continuity
of the finite sums therefore makes escape above any prescribed sublinear
benchmark residual. The exact Baire-generic exponent is one; its level set
has Haar measure zero.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- Arbitrarily late escape above every integer multiple of a benchmark. -/
private def sublinearEscape (b : ℕ → ℝ) : Set GaugeTorus :=
  {x | ∀ K M : ℕ, ∃ N : ℕ, M ≤ N ∧ (K : ℝ) * b N < ‖moebiusGaugeSum N x‖}

private theorem twinTail_mean_ne_zero (I : Finset ℕ) (x : GaugeTorus) :
    (BezoutValuationIncidence.coprimeSquarefreeDensity (tailModulus I) : ℂ) *
      (∑ d ∈ (tailModulus I).divisors, tailWeight x d / (d : ℂ)) ≠ 0 := by
  have hdens : 0 < BezoutValuationIncidence.coprimeSquarefreeDensity (tailModulus I) := by
    rw [BezoutValuationIncidence.coprimeSquarefreeDensity]
    refine mul_pos (by rw [RHTower.Sieve.squarefreeDensity_eq]; positivity)
      (prod_pos fun p hp => div_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
        (by positivity))
  exact mul_ne_zero (by exact_mod_cast hdens.ne') (sum_tailWeight_div_ne_zero I x)

private theorem twinTail_mem_sublinearEscape {b : ℕ → ℝ}
    (hb : Tendsto (fun N : ℕ => b N / N) atTop (𝓝 0))
    (I : Finset ℕ) (x : GaugeTorus) : twinTail I x ∈ sublinearEscape b := by
  let L := (BezoutValuationIncidence.coprimeSquarefreeDensity (tailModulus I) : ℂ) *
    ∑ d ∈ (tailModulus I).divisors, tailWeight x d / (d : ℂ)
  have hL : 0 < ‖L‖ := norm_pos_iff.mpr (twinTail_mean_ne_zero I x)
  have hnorm : Tendsto (fun N : ℕ => ‖moebiusGaugeSum N (twinTail I x)‖ / N)
      atTop (𝓝 ‖L‖) := by
    simpa only [norm_div, Complex.norm_natCast] using
      (tendsto_moebiusGaugeSum_twinTail_div I x).norm
  intro K M
  have hsmall : Tendsto (fun N : ℕ => (K : ℝ) * b N / N) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hb.const_mul (K : ℝ)
  obtain ⟨N, hNbig, hNsmall, hNM, hN1⟩ :=
    ((hnorm.eventually (Ioi_mem_nhds (show ‖L‖ / 2 < ‖L‖ by linarith))).and
      ((hsmall.eventually (Iio_mem_nhds (half_pos hL))).and
        ((eventually_ge_atTop M).and (eventually_ge_atTop 1)))).exists
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  exact ⟨N, hNM, (div_lt_div_iff_of_pos_right hN0).mp (hNsmall.trans hNbig)⟩

private theorem isGδ_sublinearEscape (b : ℕ → ℝ) : IsGδ (sublinearEscape b) := by
  have heq : sublinearEscape b = ⋂ K : ℕ, ⋂ M : ℕ, ⋃ N : ℕ,
      {x : GaugeTorus | M ≤ N ∧ (K : ℝ) * b N < ‖moebiusGaugeSum N x‖} := by
    ext x
    simp only [sublinearEscape, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  rw [heq]
  apply IsGδ.iInter
  intro K
  refine IsGδ.iInter_of_isOpen fun M => isOpen_iUnion fun N => ?_
  exact isOpen_const.inter (isOpen_lt continuous_const (continuous_moebiusGaugeSum N).norm)

private theorem dense_sublinearEscape {b : ℕ → ℝ}
    (hb : Tendsto (fun N : ℕ => b N / N) atTop (𝓝 0)) : Dense (sublinearEscape b) := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU x hx
  refine ⟨twinTail I x, hsub fun i hi => ?_, twinTail_mem_sublinearEscape hb I x⟩
  simp only [twinTail, if_pos (mem_coe.mp hi)]
  exact (hu i (mem_coe.mp hi)).2

/-- For every prescribed sublinear benchmark, Baire-generically the twisted
Möbius sums exceed every positive multiple at arbitrarily large horizons. -/
theorem residual_moebius_exceeds_sublinear {b : ℕ → ℝ}
    (hb : Tendsto (fun N : ℕ => b N / N) atTop (𝓝 0)) :
    {x : GaugeTorus | ∀ K : ℝ, 0 < K → ∀ M : ℕ, ∃ N : ℕ,
      M ≤ N ∧ K * b N < ‖moebiusGaugeSum N x‖} ∈ residual GaugeTorus := by
  refine mem_of_superset
    (residual_of_dense_Gδ (isGδ_sublinearEscape b) (dense_sublinearEscape hb)) ?_
  intro x hx K hK M
  obtain ⟨N, hNM, hlarge⟩ := hx ⌈K⌉₊ M
  refine ⟨N, hNM, ?_⟩
  by_cases hbN : 0 ≤ b N
  · exact (mul_le_mul_of_nonneg_right (Nat.le_ceil K) hbN).trans_lt hlarge
  · exact (mul_neg_of_pos_of_neg hK (lt_of_not_ge hbN)).trans_le (norm_nonneg _)

private theorem tendsto_power_benchmark_div {q : ℝ} (hq : q < 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ q / N) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show 0 < 1 - q by linarith)).comp
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  change (N : ℝ) ^ (-(1 - q)) = (N : ℝ) ^ q / N
  rw [show -(1 - q) = q - 1 by ring, Real.rpow_sub hN0, Real.rpow_one]

/-- The Möbius exponent equals its maximal possible value at a residual set
of gauges. Countably many power benchmarks suffice to force the exact value. -/
theorem moebius_exponent_one_residual :
    {x : GaugeTorus | gaugeExponent moebiusSource x = 1} ∈ residual GaugeTorus := by
  have hq : ∀ q : ℚ, ∀ᶠ x : GaugeTorus in residual GaugeTorus,
      (q : ℝ) < 1 → ∀ K : ℝ, 0 < K → ∀ M : ℕ, ∃ N : ℕ,
        M ≤ N ∧ K * (N : ℝ) ^ (q : ℝ) < ‖moebiusGaugeSum N x‖ := by
    intro q
    by_cases hq1 : (q : ℝ) < 1
    · exact mem_of_superset
        (residual_moebius_exceeds_sublinear (tendsto_power_benchmark_div hq1))
        fun x hx _ => hx
    · exact Eventually.of_forall fun _ h => (hq1 h).elim
  have hall := eventually_countable_forall.mpr hq
  filter_upwards [hall] with x hx
  apply le_antisymm (gaugeExponent_le_one norm_moebiusSource_le)
  by_contra hlt
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn (lt_of_not_ge hlt)
  have hq0 : 0 ≤ (q : ℝ) := (gaugeExponent_nonneg norm_moebiusSource_le).trans hqlo.le
  obtain ⟨C, hC, hbound⟩ := gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le hqlo
  obtain ⟨N, hN, hlarge⟩ := hx q hqhi (C * (2 : ℝ) ^ (q : ℝ) + 1) (by positivity) 1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : ((N : ℝ) + 1) ^ (q : ℝ) ≤ 2 ^ (q : ℝ) * (N : ℝ) ^ (q : ℝ) := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hq0
  have hupper := hbound N
  rw [sum_range_moebiusSource] at hupper
  have hle : ‖moebiusGaugeSum N x‖ ≤
      (C * (2 : ℝ) ^ (q : ℝ) + 1) * (N : ℝ) ^ (q : ℝ) := by
    calc
      _ ≤ C * ((N : ℝ) + 1) ^ (q : ℝ) := hupper
      _ ≤ C * (2 ^ (q : ℝ) * (N : ℝ) ^ (q : ℝ)) := mul_le_mul_of_nonneg_left hpow hC
      _ ≤ (C * (2 : ℝ) ^ (q : ℝ) + 1) * (N : ℝ) ^ (q : ℝ) := by
        nlinarith only [Real.rpow_nonneg (Nat.cast_nonneg N) (q : ℝ)]
  exact (not_lt_of_ge hle) hlarge

/-- Maximal exponent is topologically generic and has Haar measure zero. -/
theorem moebius_exponent_one_residual_and_null :
    {x : GaugeTorus | gaugeExponent moebiusSource x = 1} ∈ residual GaugeTorus ∧
      gaugeHaar {x : GaugeTorus | gaugeExponent moebiusSource x = 1} = 0 := by
  refine ⟨moebius_exponent_one_residual, measure_mono_null ?_
    moebius_exponent_exceptional_null_and_residual.2⟩
  intro x hx
  change (1 / 2 : ℝ) < gaugeExponent moebiusSource x
  rw [hx]
  norm_num

end GaloisForLFunctions.ArithmeticGaugeTheory

#print axioms GaloisForLFunctions.ArithmeticGaugeTheory.residual_moebius_exceeds_sublinear
#print axioms GaloisForLFunctions.ArithmeticGaugeTheory.moebius_exponent_one_residual
#print axioms GaloisForLFunctions.ArithmeticGaugeTheory.moebius_exponent_one_residual_and_null
