import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePLinearLowerThreshold
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevCoupling
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevKernel
import GaloisForLFunctions.RHTower.Sieve.ChebyshevErrorPowerBound

open Filter MeasureTheory Set ArithmeticFunction
open scoped BigOperators Chebyshev Topology

namespace RHTower

open RiemannGaussian

private theorem routeP_mass_eq_suzuki_weightedMass (K : ℕ) :
    ccmActualHeadParabolicMass K =
      suzukiChebyshevWeightedMass (((K + 2 : ℕ) : ℝ)) := by
  have hw (j : ℕ) :
      criticalMellinAtomWeight (j + 2) = suzukiPrimeWeight j := by
    have hp : (((j + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) =
        (((j + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
      convert Real.rpow_neg
        (by positivity : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ)) (1 / 2 : ℝ) using 1; ring_nf
    rw [criticalMellinAtomWeight, suzukiPrimeWeight, Real.sqrt_eq_rpow, hp]
    rw [div_eq_mul_inv]
    ring
  have h := screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass (K + 1)
  calc
    ccmActualHeadParabolicMass K =
        screwPrefixMass suzukiPrimeWeight (K + 1) := by
          simp only [ccmActualHeadParabolicMass, screwPrefixMass]
          exact Finset.sum_congr rfl (fun j _ => hw j)
    _ = _ := by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem routeP_integrable_psi_weight {b : ℝ} (_hb : 1 ≤ b) :
    IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ) * Chebyshev.psi t)
      (Ioc 1 b) := by
  have hpower : IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ)) (Icc 1 b) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t (-3 / 2 : ℝ)
      (Or.inl (zero_lt_one.trans_le ht.1).ne')).continuousWithinAt
  have hpsi := integrableOn_mul_sum_Icc
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (a := (1 : ℝ)) (b := b) (m := 0) (by norm_num) hpower
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at hpsi
  exact hpsi.mono_set Ioc_subset_Icc_self

private theorem routeP_integrable_baseline_weight {b : ℝ} (_hb : 1 ≤ b) :
    IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Ioc 1 b) := by
  have hpower : IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Icc 1 b) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t (-1 / 2 : ℝ)
      (Or.inl (zero_lt_one.trans_le ht.1).ne')).continuousWithinAt
  exact hpower.mono_set Ioc_subset_Icc_self

private theorem routeP_baseline_weight_integral {b : ℝ} (hb : 1 ≤ b) :
    (∫ t in Ioc (1 : ℝ) b, t ^ (-1 / 2 : ℝ)) = 2 * (Real.sqrt b - 1) := by
  rw [← intervalIntegral.integral_of_le hb,
    integral_rpow (r := (-1 / 2 : ℝ)) (Or.inl (by norm_num))]
  rw [Real.sqrt_eq_rpow]
  norm_num
  ring

private theorem routeP_weightedMassError_eq_psi_error_integral
    {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevWeightedMassError b =
      b ^ (-1 / 2 : ℝ) * (Chebyshev.psi b - b) +
        (1 / 2 : ℝ) *
          ∫ t in Ioc (1 : ℝ) b,
            t ^ (-3 / 2 : ℝ) * (Chebyshev.psi t - t) := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hpsi := routeP_integrable_psi_weight hb
  have hbase := routeP_integrable_baseline_weight hb
  have hInt :
      (∫ t in Ioc (1 : ℝ) b,
          t ^ (-3 / 2 : ℝ) * Chebyshev.psi t) -
        (∫ t in Ioc (1 : ℝ) b, t ^ (-1 / 2 : ℝ)) =
      ∫ t in Ioc (1 : ℝ) b,
          t ^ (-3 / 2 : ℝ) * (Chebyshev.psi t - t) := by
    rw [← integral_sub hpsi hbase]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht.1
    have hpow : t ^ (-3 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) := by
      conv_lhs => rhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    change t ^ (-3 / 2 : ℝ) * Chebyshev.psi t - t ^ (-1 / 2 : ℝ) =
      t ^ (-3 / 2 : ℝ) * (Chebyshev.psi t - t)
    rw [mul_sub, hpow]
  have hroot : b ^ (-1 / 2 : ℝ) * b = Real.sqrt b := by
    rw [Real.sqrt_eq_rpow]
    conv_lhs => rhs; rw [← Real.rpow_one b]
    rw [← Real.rpow_add hb0]
    congr 1
    ring
  rw [suzukiChebyshevWeightedMassError,
    suzukiChebyshevContinuousMass,
    suzukiChebyshevWeightedMass_eq_explicit]
  have hbaseI := routeP_baseline_weight_integral hb
  rw [← hInt, hbaseI]
  simp only [Real.sqrt_eq_rpow] at hroot ⊢
  simp only [← hroot]
  ring

private theorem routeP_error_kernel_integral {b : ℝ} (hb : 1 ≤ b) :
    (∫ t in Ioc (1 : ℝ) b, t ^ (-7 / 8 : ℝ)) =
      8 * (b ^ (1 / 8 : ℝ) - 1) := by
  rw [← intervalIntegral.integral_of_le hb,
    integral_rpow (r := (-7 / 8 : ℝ)) (Or.inl (by norm_num))]
  norm_num
  ring

private theorem routeP_weightedMassError_le_power
    {C b : ℝ} (hC : 0 ≤ C) (hb : 1 ≤ b)
    (hE : ∀ t : ℝ, 1 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t ^ (5 / 8 : ℝ)) :
    |suzukiChebyshevWeightedMassError b| ≤
      5 * C * b ^ (1 / 8 : ℝ) := by
  let f : ℝ → ℝ := fun t => t ^ (-3 / 2 : ℝ) * (Chebyshev.psi t - t)
  let g : ℝ → ℝ := fun t => C * t ^ (-7 / 8 : ℝ)
  have hf : IntegrableOn f (Ioc 1 b) := by
    have h := (routeP_integrable_psi_weight hb).sub
      (routeP_integrable_baseline_weight hb)
    refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioc
    have ht0 : 0 < t := lt_trans zero_lt_one ht.1
    have hpow : t ^ (-3 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) := by
      conv_lhs => rhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    change t ^ (-3 / 2 : ℝ) * Chebyshev.psi t - t ^ (-1 / 2 : ℝ) =
      t ^ (-3 / 2 : ℝ) * (Chebyshev.psi t - t)
    rw [mul_sub, hpow]
  have hg : IntegrableOn g (Ioc 1 b) := by
    have hIcc : IntegrableOn g (Icc 1 b) := by
      apply ContinuousOn.integrableOn_Icc
      intro t ht
      exact (continuousAt_const.mul
        (Real.continuousAt_rpow_const t (-7 / 8 : ℝ)
          (Or.inl (zero_lt_one.trans_le ht.1).ne'))).continuousWithinAt
    exact hIcc.mono_set Ioc_subset_Icc_self
  have hfg : ∀ t ∈ Ioc (1 : ℝ) b, |f t| ≤ g t := by
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht.1
    have hp : t ^ (-3 / 2 : ℝ) * t ^ (5 / 8 : ℝ) =
        t ^ (-7 / 8 : ℝ) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    dsimp only [f, g]
    calc
      |t ^ (-3 / 2 : ℝ) * (Chebyshev.psi t - t)| =
          t ^ (-3 / 2 : ℝ) * |Chebyshev.psi t - t| := by
            rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      _ ≤ t ^ (-3 / 2 : ℝ) * (C * t ^ (5 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hE t ht.1.le)
          (Real.rpow_nonneg ht0.le _)
      _ = C * t ^ (-7 / 8 : ℝ) := by rw [← hp]; ring
  have hIupper : (∫ t in Ioc (1 : ℝ) b, f t) ≤
      ∫ t in Ioc (1 : ℝ) b, g t :=
    setIntegral_mono_on hf hg measurableSet_Ioc
      (fun t ht => (abs_le.mp (hfg t ht)).2)
  have hIlower : -(∫ t in Ioc (1 : ℝ) b, g t) ≤
      ∫ t in Ioc (1 : ℝ) b, f t := by
    have h := setIntegral_mono_on hg.neg hf measurableSet_Ioc
      (fun t ht => (abs_le.mp (hfg t ht)).1)
    change (∫ t in Ioc (1 : ℝ) b, -(g t)) ≤
      (∫ t in Ioc (1 : ℝ) b, f t) at h
    simpa only [integral_neg] using h
  have hIbound : |∫ t in Ioc (1 : ℝ) b, f t| ≤
      8 * C * b ^ (1 / 8 : ℝ) := by
    have hgi : (∫ t in Ioc (1 : ℝ) b, g t) =
        C * (8 * (b ^ (1 / 8 : ℝ) - 1)) := by
      dsimp only [g]
      rw [integral_const_mul, routeP_error_kernel_integral hb]
    have hnonneg : 0 ≤ 8 * C := by positivity
    have hupper : |∫ t in Ioc (1 : ℝ) b, f t| ≤
        ∫ t in Ioc (1 : ℝ) b, g t :=
      abs_le.mpr ⟨by linarith [hIlower], hIupper⟩
    rw [hgi] at hupper
    nlinarith
  have hendpoint : |b ^ (-1 / 2 : ℝ) * (Chebyshev.psi b - b)| ≤
      C * b ^ (1 / 8 : ℝ) := by
    have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
    have hp : b ^ (-1 / 2 : ℝ) * b ^ (5 / 8 : ℝ) =
        b ^ (1 / 8 : ℝ) := by
      rw [← Real.rpow_add hb0]
      congr 1
      ring
    calc
      |b ^ (-1 / 2 : ℝ) * (Chebyshev.psi b - b)| =
          b ^ (-1 / 2 : ℝ) * |Chebyshev.psi b - b| := by
            rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hb0.le _)]
      _ ≤ b ^ (-1 / 2 : ℝ) * (C * b ^ (5 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hE b hb)
          (Real.rpow_nonneg hb0.le _)
      _ = C * b ^ (1 / 8 : ℝ) := by rw [← hp]; ring
  rw [routeP_weightedMassError_eq_psi_error_integral hb]
  change |b ^ (-1 / 2 : ℝ) * (Chebyshev.psi b - b) +
    (1 / 2 : ℝ) * (∫ t in Ioc (1 : ℝ) b, f t)| ≤ _
  calc
    _ ≤ |b ^ (-1 / 2 : ℝ) * (Chebyshev.psi b - b)| +
        (1 / 2 : ℝ) * |∫ t in Ioc (1 : ℝ) b, f t| := by
          simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            using abs_add_le
              (b ^ (-1 / 2 : ℝ) * (Chebyshev.psi b - b))
              ((1 / 2 : ℝ) * (∫ t in Ioc (1 : ℝ) b, f t))
    _ ≤ 5 * C * b ^ (1 / 8 : ℝ) := by linarith

theorem routeP_mass_discrepancy_eighth_power_of_RH
    (hRH : RiemannHypothesis) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ K : ℕ,
      |ccmActualHeadParabolicMass K -
        2 * Real.sqrt (((K + 2 : ℕ) : ℝ))| ≤
          D * (((K + 2 : ℕ) : ℝ) ^ (1 / 8 : ℝ)) := by
  obtain ⟨C, hC, hψ⟩ :=
    Sieve.exists_chebyshevPsiReal_error_power_bound hRH
      (ε := 1 / 8) (by norm_num)
  have hE (t : ℝ) (ht : 1 ≤ t) :
      |Chebyshev.psi t - t| ≤ C * t ^ (5 / 8 : ℝ) := by
    have h := hψ t ht
    have hψid : chebyshevPsiReal t = Chebyshev.psi t := by
      rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_range]
    rw [hψid] at h
    convert h using 1; ring_nf
  refine ⟨5 * C + 1, by positivity, ?_⟩
  intro K
  let x : ℝ := (((K + 2 : ℕ) : ℝ))
  have hx : 1 ≤ x := by dsimp only [x]; exact_mod_cast (show 1 ≤ K + 2 by omega)
  have hxpow : 1 ≤ x ^ (1 / 8 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx
      (show (0 : ℝ) ≤ 1 / 8 by norm_num)
  have hmass := routeP_mass_eq_suzuki_weightedMass K
  have herr := routeP_weightedMassError_le_power hC.le hx hE
  change |suzukiChebyshevWeightedMassError x| ≤
    5 * C * x ^ (1 / 8 : ℝ) at herr
  have hid : ccmActualHeadParabolicMass K - 2 * Real.sqrt x =
      suzukiChebyshevWeightedMassError x - 1 := by
    rw [hmass, suzukiChebyshevWeightedMassError,
      suzukiChebyshevContinuousMass, Real.sqrt_eq_rpow]
    ring
  rw [hid]
  calc
    |suzukiChebyshevWeightedMassError x - 1| ≤
        |suzukiChebyshevWeightedMassError x| + 1 := by
          simpa using abs_sub_le
            (suzukiChebyshevWeightedMassError x) 0 (1 : ℝ)
    _ ≤ (5 * C + 1) * x ^ (1 / 8 : ℝ) := by nlinarith

private theorem routeP_algebra_linear_floor
    {t m E e μ q credit B C D F R : ℝ}
    (ht : 1 ≤ t) (_hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : 0 ≤ F) (hR : 0 ≤ R)
    (hmlo : t ^ (4 : ℕ) / 2 ≤ m) (hmup : m ≤ R * t ^ (4 : ℕ))
    (hE : |E| ≤ C * t ^ (5 : ℕ)) (he0 : 0 ≤ e) (he : e ≤ F)
    (hμ : |μ| ≤ D * t) (hq : 0 ≤ q)
    (hcredit : -2 * B * t ^ (8 : ℕ) ≤ credit) :
    -(2 * B + 2 * F + 2 * (2 * C + F + D) ^ (2 : ℕ) +
        (4 + R) * D ^ (2 : ℕ) / 12) * t ^ (8 : ℕ) ≤
      credit - 2 * t ^ (4 : ℕ) * e -
        (2 * E + e - t ^ (4 : ℕ) * μ) ^ (2 : ℕ) / m -
        (4 * t ^ (4 : ℕ) + m) / 12 * μ ^ (2 : ℕ) + 4 * q / 3 := by
  let A : ℝ := 2 * C + F + D
  have ht0 : 0 ≤ t := by linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have ht4 : 1 ≤ t ^ (4 : ℕ) := one_le_pow₀ ht
  have ht5 : 1 ≤ t ^ (5 : ℕ) := one_le_pow₀ ht
  have ht6le8 : t ^ (6 : ℕ) ≤ t ^ (8 : ℕ) := by
    calc
      t ^ (6 : ℕ) = t ^ (6 : ℕ) * 1 := by ring
      _ ≤ t ^ (6 : ℕ) * t ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left (one_le_pow₀ ht) (pow_nonneg ht0 _)
      _ = t ^ (8 : ℕ) := by ring
  have ht4le8 : t ^ (4 : ℕ) ≤ t ^ (8 : ℕ) := by
    calc
      t ^ (4 : ℕ) = t ^ (4 : ℕ) * 1 := by ring
      _ ≤ t ^ (4 : ℕ) * t ^ (4 : ℕ) := by
        exact mul_le_mul_of_nonneg_left ht4 (pow_nonneg ht0 _)
      _ = t ^ (8 : ℕ) := by ring
  have hmpos : 0 < m := by
    have hp : 0 < t ^ (4 : ℕ) := pow_pos (by linarith) _
    linarith
  have hμmul : |t ^ (4 : ℕ) * μ| ≤ D * t ^ (5 : ℕ) := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
    calc
      t ^ (4 : ℕ) * |μ| ≤ t ^ (4 : ℕ) * (D * t) :=
        mul_le_mul_of_nonneg_left hμ (pow_nonneg ht0 _)
      _ = D * t ^ (5 : ℕ) := by ring
  have harg : |2 * E + e - t ^ (4 : ℕ) * μ| ≤ A * t ^ (5 : ℕ) := by
    have hEbounds := abs_le.mp hE
    have hμbounds := abs_le.mp hμmul
    have hFpower : F ≤ F * t ^ (5 : ℕ) := by
      calc F = F * 1 := by ring
        _ ≤ F * t ^ (5 : ℕ) := mul_le_mul_of_nonneg_left ht5 hF
    rw [abs_le]
    constructor <;> dsimp only [A] <;> linarith
  have hargSq : (2 * E + e - t ^ (4 : ℕ) * μ) ^ (2 : ℕ) ≤
      (A * t ^ (5 : ℕ)) ^ (2 : ℕ) := by
    have hmul : 0 ≤
        (A * t ^ (5 : ℕ) - |2 * E + e - t ^ (4 : ℕ) * μ|) *
          (A * t ^ (5 : ℕ) + |2 * E + e - t ^ (4 : ℕ) * μ|) :=
      mul_nonneg (sub_nonneg.mpr harg)
        (add_nonneg (by positivity) (abs_nonneg _))
    nlinarith only [hmul, sq_abs (2 * E + e - t ^ (4 : ℕ) * μ)]
  have hfirst :
      (2 * E + e - t ^ (4 : ℕ) * μ) ^ (2 : ℕ) / m ≤
        2 * A ^ (2 : ℕ) * t ^ (8 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hmlo
      (by positivity : 0 ≤ 2 * A ^ (2 : ℕ) * t ^ (6 : ℕ))
    have hnum : (2 * E + e - t ^ (4 : ℕ) * μ) ^ (2 : ℕ) ≤
        2 * A ^ (2 : ℕ) * t ^ (6 : ℕ) * m := by
      nlinarith [hargSq, hmul]
    have hdiv : (2 * E + e - t ^ (4 : ℕ) * μ) ^ (2 : ℕ) / m ≤
        2 * A ^ (2 : ℕ) * t ^ (6 : ℕ) :=
      (div_le_iff₀ hmpos).mpr hnum
    exact hdiv.trans (mul_le_mul_of_nonneg_left ht6le8 (by positivity))
  have hμSq : μ ^ (2 : ℕ) ≤ (D * t) ^ (2 : ℕ) := by
    have hmul : 0 ≤ (D * t - |μ|) * (D * t + |μ|) :=
      mul_nonneg (sub_nonneg.mpr hμ)
        (add_nonneg (by positivity) (abs_nonneg μ))
    nlinarith only [hmul, sq_abs μ]
  have hcoeff : (4 * t ^ (4 : ℕ) + m) / 12 ≤
      ((4 + R) * t ^ (4 : ℕ)) / 12 := by linarith
  have hcoeff0 : 0 ≤ (4 * t ^ (4 : ℕ) + m) / 12 := by positivity
  have huppercoeff0 : 0 ≤ ((4 + R) * t ^ (4 : ℕ)) / 12 := by positivity
  have hsecond :
      (4 * t ^ (4 : ℕ) + m) / 12 * μ ^ (2 : ℕ) ≤
        ((4 + R) * D ^ (2 : ℕ) / 12) * t ^ (8 : ℕ) := by
    calc
      _ ≤ ((4 + R) * t ^ (4 : ℕ) / 12) * μ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg μ)
      _ ≤ ((4 + R) * t ^ (4 : ℕ) / 12) * (D * t) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hμSq huppercoeff0
      _ = ((4 + R) * D ^ (2 : ℕ) / 12) * t ^ (6 : ℕ) := by ring
      _ ≤ ((4 + R) * D ^ (2 : ℕ) / 12) * t ^ (8 : ℕ) :=
        mul_le_mul_of_nonneg_left ht6le8 (by positivity)
  have heterm : 2 * t ^ (4 : ℕ) * e ≤ 2 * F * t ^ (8 : ℕ) := by
    calc
      _ ≤ 2 * t ^ (4 : ℕ) * F :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = 2 * F * t ^ (4 : ℕ) := by ring
      _ ≤ 2 * F * t ^ (8 : ℕ) :=
        mul_le_mul_of_nonneg_left ht4le8 (by positivity)
  dsimp only [A] at hfirst
  linarith

theorem routeP_history_linear_floor_of_RH (hRH : RiemannHypothesis) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ K : ℕ, 3 ≤ K →
      -B * (((K + 2 : ℕ) : ℝ)) ≤
        ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K := by
  obtain ⟨B₀, hB₀, hsource⟩ :=
    exists_log_nat_bound_criticalMellinChebyshevResolventSource_of_riemannHypothesis hRH
  obtain ⟨C, hC, hψ⟩ :=
    Sieve.exists_chebyshevPsiReal_error_power_bound hRH
      (ε := 1 / 8) (by norm_num)
  obtain ⟨D, hD, hmassError⟩ :=
    routeP_mass_discrepancy_eighth_power_of_RH hRH
  let F : ℝ := ∑' n : ℕ, centroidAtomExcess n
  have hF : 0 ≤ F :=
    (ccmActualHeadMatchedCentroidChebyshevExcess_nonneg 0).trans
      (ccmActualHeadMatchedCentroidChebyshevExcess_le_tsum 0)
  let B : ℝ := 2 * B₀ + 2 * F + 2 * (2 * C + F + D) ^ (2 : ℕ) +
    (4 + (2 + D)) * D ^ (2 : ℕ) / 12
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro K hK
  let x : ℝ := (((K + 2 : ℕ) : ℝ))
  let t : ℝ := x ^ (1 / 8 : ℝ)
  let r : ℝ := Real.sqrt x
  let m : ℝ := ccmActualHeadParabolicMass K
  let E : ℝ := Chebyshev.psi x - x
  let e : ℝ := ccmActualHeadMatchedCentroidChebyshevExcess K
  let μ : ℝ := m - 2 * r
  let q : ℝ := routePWidthCubePrefix K
  have hx5 : 5 ≤ x := by dsimp only [x]; exact_mod_cast (show 5 ≤ K + 2 by omega)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have ht : 1 ≤ t := by
    dsimp only [t]
    simpa using Real.rpow_le_rpow_of_exponent_le hx1
      (show (0 : ℝ) ≤ 1 / 8 by norm_num)
  have ht4 : t ^ (4 : ℕ) = r := by
    dsimp only [t, r]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    congr 1
    ring
  have ht5 : t ^ (5 : ℕ) = x ^ (5 / 8 : ℝ) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    congr 1
    ring
  have ht8 : t ^ (8 : ℕ) = x := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hmMass : m = suzukiChebyshevWeightedMass x :=
    routeP_mass_eq_suzuki_weightedMass K
  have hr5 : Real.sqrt 5 ≤ r := by
    dsimp only [r]
    exact Real.sqrt_le_sqrt hx5
  have hmRaw := sqrt_sub_half_sqrt_five_le_suzukiChebyshevWeightedMass hx5
  rw [← hmMass] at hmRaw
  have hmlo : t ^ (4 : ℕ) / 2 ≤ m := by
    rw [ht4]
    linarith
  have hμ : |μ| ≤ D * t := by
    simpa only [μ, m, r, x, t] using hmassError K
  have hDt : D * t ≤ D * t ^ (4 : ℕ) := by
    have ht3 : 1 ≤ t ^ (3 : ℕ) := one_le_pow₀ ht
    have ht1le4 : t ≤ t ^ (4 : ℕ) := by
      calc t = t * 1 := by ring
        _ ≤ t * t ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_left ht3 (by linarith)
        _ = t ^ (4 : ℕ) := by ring
    exact mul_le_mul_of_nonneg_left ht1le4 hD
  have hmup : m ≤ (2 + D) * t ^ (4 : ℕ) := by
    have hμup := (abs_le.mp hμ).2
    dsimp only [μ] at hμup
    rw [ht4] at hDt
    rw [ht4]
    nlinarith
  have hψid : chebyshevPsiReal x = Chebyshev.psi x := by
    rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_range]
  have hE : |E| ≤ C * t ^ (5 : ℕ) := by
    have h := hψ x hx1
    rw [hψid] at h
    change |E| ≤ C * t ^ (5 : ℕ)
    rw [ht5]
    convert h using 1; ring_nf
  have he0 : 0 ≤ e := ccmActualHeadMatchedCentroidChebyshevExcess_nonneg K
  have he : e ≤ F := ccmActualHeadMatchedCentroidChebyshevExcess_le_tsum K
  have hq : 0 ≤ q := by
    unfold q routePWidthCubePrefix
    apply Finset.sum_nonneg
    intro n hn
    exact div_nonneg
      (pow_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _) _)
      (by norm_num)
  have hcredit : -2 * B₀ * t ^ (8 : ℕ) ≤
      4 * routePWeightedChebyshevNullCredit K := by
    rw [ht8, routePWeightedChebyshevNullCredit_eq_unitRiesz_resolvent_source]
    have hs := hsource (K + 2) (by omega)
    change |criticalMellinChebyshevResolventSource (Real.log x)| ≤ B₀ at hs
    have hsUp := (abs_le.mp hs).2
    have hmul := mul_nonneg (sub_nonneg.mpr hsUp)
      (show 0 ≤ 2 * x by positivity)
    nlinarith [hmul]
  have hfloor := routeP_algebra_linear_floor
    (t := t) (m := m) (E := E) (e := e) (μ := μ) (q := q)
    (credit := 4 * routePWeightedChebyshevNullCredit K)
    (B := B₀) (C := C) (D := D) (F := F) (R := 2 + D)
    ht hB₀ hC.le hD hF (by positivity) hmlo hmup hE he0 he hμ hq hcredit
  have hfloor' : -B * x ≤
      4 * routePWeightedChebyshevNullCredit K - 2 * r * e -
        (2 * E + e - r * μ) ^ (2 : ℕ) / m -
        (4 * r + m) / 12 * μ ^ (2 : ℕ) + 4 * q / 3 := by
    simpa only [B, ht4, ht8] using hfloor
  change -B * x ≤ ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K
  rw [routeP_normalized_history_eq_credit_sub_two_square_debts]
  exact hfloor'

theorem riemannHypothesis_iff_routeP_history_eventual_linear_floor :
    RiemannHypothesis ↔
      ∃ B : ℝ, 0 ≤ B ∧ ∀ K : ℕ, 3 ≤ K →
        -B * (((K + 2 : ℕ) : ℝ)) ≤
          ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K := by
  constructor
  · exact routeP_history_linear_floor_of_RH
  · rintro ⟨B, hB, hfloor⟩
    rcases routeP_normalized_history_superlinear_escape_or_RH with hRH | hescape
    · exact hRH
    · obtain ⟨K, hK, hlt⟩ := hescape B 3
      have hge := hfloor K hK
      linarith

end RHTower
