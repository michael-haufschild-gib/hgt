import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHolonomyExpRate
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovPrimeNumberTheorem
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheVinogradovKorobovBand

/-!
# Vinogradov–Korobov decay of the centered Wold residual

Abel summation expresses the prime harmonic discrepancy as a boundary error minus
an integrable tail of the Chebyshev error. Half the VK exponent bounds that tail
uniformly; the other half pays an integrable square-root-log density. The positive
Euler-depletion correction is smaller than this remainder.
-/

open Filter Topology MeasureTheory Set
open RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-- Removing proper prime powers preserves the VK Chebyshev remainder. -/
theorem exists_abs_theta_sub_self_vk_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ B * x * Real.exp (-(vkKappa * vkScale x / 24)) := by
  obtain ⟨B, hB, hpsi⟩ := exists_abs_sum_vonMangoldt_sub_self_vk_rate
  refine ⟨B + 8, by positivity, ?_⟩
  filter_upwards [hpsi, eventually_vk_conditions one_pos 0] with x hx hvk
  have hx0 : 0 < x := by linarith only [hvk.1]
  have hL0 : 0 ≤ Real.log x := by linarith only [hvk.2.1]
  have hsave := hvk.2.2.2.2.2.1
  rw [log_vkHeight] at hsave
  have hlog : Real.log x ≤ 4 * Real.exp (Real.log x / 4) := by
    linarith only [Real.add_one_le_exp (Real.log x / 4)]
  have hpp := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log
    (by linarith only [hvk.1] : 1 ≤ x)
  have hpp' : |Chebyshev.psi x - Chebyshev.theta x| ≤
      8 * x * Real.exp (-(vkKappa * vkScale x / 24)) := by
    calc _ ≤ 2 * Real.sqrt x * Real.log x := hpp
      _ ≤ 2 * Real.sqrt x * (4 * Real.exp (Real.log x / 4)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 8 * Real.exp (3 * Real.log x / 4) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0,
          show Real.log x * (1/2:ℝ) = Real.log x/2 by ring]
        rw [show 2 * Real.exp (Real.log x / 2) * (4 * Real.exp (Real.log x / 4)) =
          8 * (Real.exp (Real.log x / 2) * Real.exp (Real.log x / 4)) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ 8 * Real.exp (Real.log x - vkKappa * vkScale x / 24) := by
        gcongr
        linarith only [hsave, hL0]
      _ = 8 * x * Real.exp (-(vkKappa * vkScale x / 24)) := by
        rw [Real.exp_sub, Real.exp_log hx0, Real.exp_neg]
        ring
  have hp : |Chebyshev.psi x - x| ≤ B*x*Real.exp (-(vkKappa*vkScale x/24)) := by
    simpa only [Chebyshev.psi_eq_sum_range] using hx
  have ht := abs_sub (Chebyshev.psi x - x) (Chebyshev.psi x - Chebyshev.theta x)
  rw [show (Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x) =
    Chebyshev.theta x - x by ring] at ht
  calc _ ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := ht
    _ ≤ B*x*Real.exp (-(vkKappa*vkScale x/24)) +
        8*x*Real.exp (-(vkKappa*vkScale x/24)) := add_le_add hp hpp'
    _ = (B+8)*x*Real.exp (-(vkKappa*vkScale x/24)) := by ring

/-- The canonical prime harmonic discrepancy retains half the VK exponent. -/
theorem exists_abs_canonical_mertensA_vk_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |mertensA N - Real.log N - xiHeatCassiniMertensLogConstant| ≤
        B * Real.exp (-(vkKappa * vkScale N / 48)) := by
  obtain ⟨K, hK, htheta⟩ := exists_abs_theta_sub_self_vk_rate
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (htheta.and ((eventually_vk_conditions one_pos 0).and
      (eventually_ge_atTop (Real.exp (Real.exp (25/9))))))
  have hbd : ∀ t : ℝ, max T 2 < t →
      |Chebyshev.theta t-t| ≤ K*t*Real.exp (-(1/12 : ℝ)*Real.sqrt (Real.log t)) := by
    intro t ht
    obtain ⟨hp, hvk, -⟩ := hT t ((le_max_left _ _).trans ht.le)
    have hs := hvk.2.2.2.2.1
    rw [log_vkHeight] at hs
    refine hp.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_)
    · linarith only [hs]
    · exact mul_nonneg hK (by linarith only [hvk.1])
  have hInt := integrableOn_thetaErrorDensity_Ioi (by norm_num : (0:ℝ)<1/12)
    (le_max_right T 2) hbd
  let c₁ := 1 - Real.log 2 + ∫ t in Ioi (2:ℝ), thetaErrorDensity t
  have hreal : ∀ᶠ x : ℝ in atTop,
      |mertensA ⌊x⌋₊ - Real.log x - c₁| ≤
        (2305*K)*Real.exp (-(vkKappa*vkScale x/48)) := by
    filter_upwards [eventually_ge_atTop T] with x hx
    obtain ⟨hp, hvk, hxexp⟩ := hT x hx
    have hx2 : 2 ≤ x := by linarith only [hvk.1]
    have hx0 : 0 < x := by linarith only [hx2]
    have hs := hvk.2.2.2.2.1
    rw [log_vkHeight] at hs
    have hs0 : 0 ≤ vkKappa*vkScale x :=
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)).trans hs
    let A := K * Real.exp (-(vkKappa*vkScale x/48))
    have hA : 0 ≤ A := by dsimp only [A]; positivity
    have htail : |∫ t in Ioi x, thetaErrorDensity t| ≤ 2304*A := by
      have htbound : ∀ t : ℝ, x < t →
          |Chebyshev.theta t-t| ≤ A*t*Real.exp (-(1/24 : ℝ)*Real.sqrt (Real.log t)) := by
        intro t ht
        obtain ⟨hpt, hvkt, -⟩ := hT t (hx.trans ht.le)
        have hst := hvkt.2.2.2.2.1
        rw [log_vkHeight] at hst
        have hmono := mul_le_mul_of_nonneg_left (vkScale_le_vkScale hxexp ht.le) vkKappa_pos.le
        have he : Real.exp (-(vkKappa*vkScale t/24)) ≤
            Real.exp (-(vkKappa*vkScale x/48)) *
              Real.exp (-(1/24 : ℝ)*Real.sqrt (Real.log t)) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith only [hst, hmono])
        calc _ ≤ K*t*Real.exp (-(vkKappa*vkScale t/24)) := hpt
          _ ≤ K*t*(Real.exp (-(vkKappa*vkScale x/48))*
              Real.exp (-(1/24 : ℝ)*Real.sqrt (Real.log t))) :=
            mul_le_mul_of_nonneg_left he (mul_nonneg hK (by linarith only [hx0, ht]))
          _ = A*t*Real.exp (-(1/24 : ℝ)*Real.sqrt (Real.log t)) := by dsimp only [A]; ring
      have hi := abs_setIntegral_thetaErrorDensity_Ioi_le (by norm_num : (0:ℝ)<1/24)
        hA (by linarith only [hx2]) (hInt.mono_set (Ioi_subset_Ioi hx2)) htbound
      norm_num at hi
      have he : Real.exp (-((1/48 : ℝ)*Real.sqrt (Real.log x))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      nlinarith only [hi, mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ A*2304)]
    have hboundary : |(Chebyshev.theta x-x)/x| ≤ A := by
      rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
      refine hp.trans ?_
      dsimp only [A]
      rw [mul_right_comm K _ x]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith only [hs0])) (mul_nonneg hK hx0.le)
    have hsplit : (∫ t in Ioi (2:ℝ), thetaErrorDensity t) =
        (∫ t in Ioc 2 x, thetaErrorDensity t) + ∫ t in Ioi x, thetaErrorDensity t := by
      rw [← Ioc_union_Ioi_eq_Ioi hx2]
      exact setIntegral_union (Set.disjoint_left.mpr fun _ ha hb => not_lt_of_ge ha.2 hb)
        measurableSet_Ioi (hInt.mono_set Ioc_subset_Ioi_self)
        (hInt.mono_set (Ioi_subset_Ioi hx2))
    have hid : mertensA ⌊x⌋₊ - Real.log x - c₁ =
        (Chebyshev.theta x-x)/x - ∫ t in Ioi x, thetaErrorDensity t := by
      dsimp only [c₁]
      rw [mertensA_eq_theta_div_add_setIntegral hx2, setIntegral_theta_div_sq hx2, hsplit]
      field_simp
      ring
    rw [hid]
    have htri := (abs_sub ((Chebyshev.theta x-x)/x)
      (∫ t in Ioi x, thetaErrorDensity t)).trans (add_le_add hboundary htail)
    simpa only [A] using htri.trans_eq (by dsimp only [A]; ring)
  have hnat : ∀ᶠ N : ℕ in atTop,
      |mertensA N - Real.log N - c₁| ≤ (2305*K)*Real.exp (-(vkKappa*vkScale N/48)) := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hreal] with N hN
    simpa only [Nat.floor_natCast] using hN
  have hweak : ∀ᶠ N : ℕ in atTop,
      |mertensA N - Real.log N - c₁| ≤
        (2305*K)*Real.exp (-(1/24 : ℝ)*Real.sqrt (Real.log N)) := by
    filter_upwards [hnat, (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
      (eventually_vk_conditions one_pos 0)] with N hN hvk
    have hs := hvk.2.2.2.2.1
    rw [log_vkHeight] at hs
    exact hN.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith only [hs])) (by positivity))
  have hc : c₁ = xiHeatCassiniMertensLogConstant := tendsto_nhds_unique
    (tendsto_sieve_mertensA_sub_log_of_exp_rate (by norm_num : (0:ℝ)<1/24) hweak)
    tendsto_sieve_mertensA_sub_log
  exact ⟨2305*K, by positivity, hc ▸ hnat⟩

/-- The literal centered Wold residual has unconditional VK decay. -/
theorem exists_abs_woldResidual_vk_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniWoldNatResidualLogDiscrepancy N| ≤
        B * Real.exp (-(vkKappa * vkScale N / 48)) := by
  obtain ⟨B, hB, hM⟩ := exists_abs_canonical_mertensA_vk_rate
  refine ⟨B+15, by positivity, ?_⟩
  filter_upwards [hM, eventually_ge_atTop (3:ℕ),
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_vk_conditions one_pos 0)]
    with N hMN hN hvk
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL0 : 0 ≤ Real.log (N:ℝ) := by linarith only [hvk.2.1]
  have hsave := hvk.2.2.2.2.2.1
  rw [log_vkHeight] at hsave
  have hlog : Real.log (N:ℝ)+1 ≤ 5*Real.exp (Real.log N/4) := by
    have he := Real.one_le_exp (div_nonneg hL0 (by norm_num : (0:ℝ)≤4))
    linarith only [Real.add_one_le_exp (Real.log (N:ℝ)/4), he]
  have htail : xiHeatCassiniWoldNatTraceCorrectionMass -
      xiHeatCassiniWoldNatTraceCorrectionSum N ≤ 15*Real.exp (-(vkKappa*vkScale N/48)) := by
    refine (xiHeatCassiniWoldNatTraceCorrectionMass_sub_sum_le hN).trans ?_
    calc 3*((Real.log N+1)/N) ≤ 3*((5*Real.exp (Real.log N/4))/N) := by gcongr
      _ = 15*Real.exp (-(3*Real.log N/4)) := by
        have he : Real.exp (Real.log N/4)/(N:ℝ) =
            Real.exp (Real.log N/4-Real.log N) := by
          rw [Real.exp_sub, Real.exp_log hN0]
        rw [show 3*(5*Real.exp (Real.log N/4)/(N:ℝ)) =
          15*(Real.exp (Real.log N/4)/(N:ℝ)) by ring, he]
        congr 2
        ring
      _ ≤ 15*Real.exp (-(vkKappa*vkScale N/48)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (by linarith only [hsave, hL0])) (by norm_num)
  have htail0 := sub_nonneg.mpr (xiHeatCassiniWoldNatTraceCorrectionSum_le_mass N)
  have hid : xiHeatCassiniWoldNatResidualLogDiscrepancy N =
      (mertensA N-Real.log N-xiHeatCassiniMertensLogConstant) +
        (xiHeatCassiniWoldNatTraceCorrectionMass-xiHeatCassiniWoldNatTraceCorrectionSum N) := by
    rw [xiHeatCassiniWoldNatResidualLogDiscrepancy, xiHeatCassiniWoldLogHolonomyConstant,
      ← mertensPrimeWeightSum_eq_sieve_mertensA, mertensPrimeWeightSum_eq_wold_add_traceCorrection]
    ring
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg htail0]
  calc _ ≤ B*Real.exp (-(vkKappa*vkScale N/48)) +
      15*Real.exp (-(vkKappa*vkScale N/48)) := add_le_add hMN htail
    _ = (B+15)*Real.exp (-(vkKappa*vkScale N/48)) := by ring

#print axioms exists_abs_theta_sub_self_vk_rate
#print axioms exists_abs_canonical_mertensA_vk_rate
#print axioms exists_abs_woldResidual_vk_rate

end GaloisForLFunctions.ArithmeticCompensationTheory
