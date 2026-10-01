import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDyadicResolvent
import GaloisForLFunctions.RHTower.MertensOddWindowKnapsack
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeGrowth

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

def pmOddRawFermiPrefix (N : ℕ) (t : ℝ) : ℂ :=
  -(∑ d ∈ (Finset.Icc 1 N).filter Odd,
    (ArithmeticFunction.moebius d : ℂ) * fermiNymanGen (d : ℝ) t)

def pmOddMobiusFermiSource (t : ℝ) : ℂ := pmOddRawFermiPrefix ⌊1 / t⌋₊ t

theorem pm_fermiNymanGen_two_mul_nat (m : ℕ) (t : ℝ) :
    fermiNymanGen ((2 * m : ℕ) : ℝ) t = fermiNymanGen (m : ℝ) (2 * t) := by
  rw [pm_fermiNymanGen_dilate ((2 * m : ℕ) : ℝ) t, pm_fermiNymanGen_dilate (m : ℝ) (2 * t)]
  congr 1
  push_cast
  ring

theorem pm_rawMobiusFermiApprox_odd_split (N : ℕ) (t : ℝ) :
    rawMobiusFermiApprox N t = pmOddRawFermiPrefix N t - pmOddRawFermiPrefix (N / 2) (2 * t) := by
  classical
  have heven : ((Finset.Icc 1 N).filter (fun n => ¬ Odd n)) =
      (Finset.Icc 1 (N / 2)).image (fun m => 2 * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, hn⟩, hodd⟩
      obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hodd
      refine ⟨k, ⟨by omega, ?_⟩, by omega⟩
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
    · rintro ⟨m, ⟨h1, hm⟩, rfl⟩
      have hmN := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hm
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Nat.not_odd_iff_even]
      exact ⟨m, by ring⟩
  have hterm (m : ℕ) :
      (ArithmeticFunction.moebius (2 * m) : ℂ) * fermiNymanGen ((2 * m : ℕ) : ℝ) t =
      if Odd m then -((ArithmeticFunction.moebius m : ℂ) * fermiNymanGen (m : ℝ) (2 * t)) else 0 := by
    rw [moebius_two_mul, pm_fermiNymanGen_two_mul_nat]
    split_ifs <;> simp
  unfold rawMobiusFermiApprox pmOddRawFermiPrefix
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Odd,
    heven, Finset.sum_image (fun a _ b _ h => by omega)]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib]
  ring

theorem pm_floor_reciprocal_double (t : ℝ) : ⌊1 / (2 * t)⌋₊ = ⌊1 / t⌋₊ / 2 := by
  rw [show 1 / (2 * t) = (1 / t) / 2 by ring]
  exact Nat.floor_div_natCast (1 / t) 2

theorem pmOddMobiusFermiSource_eq_zero {t : ℝ} (ht : 1 < t) : pmOddMobiusFermiSource t = 0 := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hfloor : ⌊1 / t⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one ht0).mpr ht)
  rw [pmOddMobiusFermiSource, hfloor]
  simp [pmOddRawFermiPrefix]

theorem pmPowerDampedFermiSource_zero_eq_supportedHaar {t : ℝ} (ht : 0 < t) :
    pmPowerDampedFermiSource 0 t = pmSupportedDyadicHaar t := by
  by_cases ht1 : t ≤ 1
  · rw [pmPowerDampedFermiSource_zero_eq_haar ⟨ht, ht1⟩,
      pmSupportedDyadicHaar, Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩)]
  · rw [pmPowerDampedFermiSource_eq_zero_of_one_lt 0 (lt_of_not_ge ht1),
      pmSupportedDyadicHaar_eq_zero (lt_of_not_ge ht1)]

theorem pmOddMobiusFermiSource_eq {t : ℝ} (ht : 0 < t) :
    pmOddMobiusFermiSource t = pmSupportedDyadicHaar t + pmOddMobiusFermiSource (2 * t) := by
  have h := pm_rawMobiusFermiApprox_odd_split ⌊1 / t⌋₊ t
  rw [← pmPowerDampedFermiSource_zero_parameter,
    pmPowerDampedFermiSource_zero_eq_supportedHaar ht] at h
  unfold pmOddMobiusFermiSource
  rw [pm_floor_reciprocal_double]
  linear_combination -h

theorem pmOddMobiusFermiSource_eq_resolvent {t : ℝ} (ht : 0 < t) :
    pmOddMobiusFermiSource t = pmDyadicHaarResolvent t :=
  pmDyadicHaarResolvent_unique (fun _ hx => pmOddMobiusFermiSource_eq hx)
    (fun _ hx => pmOddMobiusFermiSource_eq_zero hx) ht

theorem memLp_pmOddMobiusFermiSource :
    MemLp pmOddMobiusFermiSource 2 (volume.restrict (Ioi 0)) := by
  apply (memLp_congr_ae (show pmOddMobiusFermiSource =ᵐ[volume.restrict (Ioi (0 : ℝ))]
    pmDyadicHaarResolvent from ?_)).mpr memLp_pmDyadicHaarResolvent
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact pmOddMobiusFermiSource_eq_resolvent ht

theorem pmOddMobiusFermiSource_eLpNorm :
    eLpNorm pmOddMobiusFermiSource 2 (volume.restrict (Ioi 0)) = ENNReal.ofReal (Real.sqrt 2) := by
  rw [← pmDyadicHaarResolvent_eLpNorm]
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact pmOddMobiusFermiSource_eq_resolvent ht

theorem pmOddMobiusFermiSource_integral :
    (∫ t in Ioi (0 : ℝ), pmOddMobiusFermiSource t) = 0 := by
  rw [← pmDyadicHaarResolvent_integral]
  exact setIntegral_congr_fun measurableSet_Ioi (fun _ ht => pmOddMobiusFermiSource_eq_resolvent ht)

def pmOddPrimeAperture (N : ℕ) : Finset ℕ := (mobiusFinitePrimeAperture N).erase 2

theorem pmOddPrimeAperture_prime (N : ℕ) : ∀ p ∈ pmOddPrimeAperture N, Nat.Prime p := by
  intro p hp
  exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2

theorem pmOddPrimeAperture_coefficient {N n : ℕ} (hn : n ≤ N) :
    finitePrimeApertureMobiusCoefficient (pmOddPrimeAperture N) n =
      if Odd n then (ArithmeticFunction.moebius n : ℂ) else 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [finitePrimeApertureMobiusCoefficient, mobiusComplexCoefficient]
  by_cases ho : Odd n
  · have hc : n.primeFactors ⊆ pmOddPrimeAperture N := by
      intro p hp
      obtain ⟨hpPrime, hpDvd, _⟩ := Nat.mem_primeFactors.mp hp
      have hpn := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpDvd
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        subst p
        exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hpDvd)
      · change p ∈ (Finset.range (N + 1)).filter Nat.Prime
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hpPrime⟩
    simp [finitePrimeApertureMobiusCoefficient, hc, ho, mobiusComplexCoefficient]
  · have h2 : 2 ∣ n := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ho)
    have hc : ¬ n.primeFactors ⊆ pmOddPrimeAperture N := by
      intro h
      have hh := h (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn0⟩)
      simp [pmOddPrimeAperture] at hh
    simp [finitePrimeApertureMobiusCoefficient, hc, ho]

theorem pm_fermiNymanGen_eq_zero_of_floor_lt {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : ⌊1 / t⌋₊ < n) : fermiNymanGen (n : ℝ) t = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hxt : 1 / t < (n : ℝ) :=
    (Nat.lt_floor_add_one (1 / t)).trans_le (by exact_mod_cast (show ⌊1 / t⌋₊ + 1 ≤ n by omega))
  have hit : 1 / (n : ℝ) < t := by
    apply (div_lt_iff₀ hn0).mpr
    have h := (div_lt_iff₀ ht).mp hxt
    nlinarith
  exact fermiNymanGen_eq_zero_of_inv_lt hn0 hit

theorem pmOddRawFermiPrefix_eq_sum (N : ℕ) (t : ℝ) :
    pmOddRawFermiPrefix N t = -(∑ d ∈ Finset.Icc 1 N,
      (if Odd d then (ArithmeticFunction.moebius d : ℂ) else 0) * fermiNymanGen (d : ℝ) t) := by
  simp only [pmOddRawFermiPrefix, Finset.sum_filter, ite_mul, zero_mul]

theorem pmOddMobiusFermiSource_eq_sum {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : ⌊1 / t⌋₊ ≤ N) :
    pmOddMobiusFermiSource t = -(∑ d ∈ Finset.Icc 1 N,
      (if Odd d then (ArithmeticFunction.moebius d : ℂ) else 0) * fermiNymanGen (d : ℝ) t) := by
  rw [pmOddMobiusFermiSource, pmOddRawFermiPrefix_eq_sum]
  congr 1
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hN)
  intro d hd hnot
  have hfloor : ⌊1 / t⌋₊ < d := by
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hn := mt Finset.mem_Icc.mpr hnot
    omega
  rw [pm_fermiNymanGen_eq_zero_of_floor_lt ht hfloor, mul_zero]

theorem pmFinitePrimePowerDampedFermiSource_odd_eq_of_covers {N : ℕ} {t : ℝ}
    (ht : 0 < t) (hN : ⌊1 / t⌋₊ ≤ N) :
    pmFinitePrimePowerDampedFermiSource (pmOddPrimeAperture N) 0 t = pmOddMobiusFermiSource t := by
  let S := pmOddPrimeAperture N
  let K := max (∏ p ∈ S, p) ⌊1 / t⌋₊
  have hext : pmFinitePrimePowerDampedFermiSource S 0 t =
      -(∑ d ∈ Finset.Icc 1 K, finitePrimeApertureMobiusCoefficient S d * fermiNymanGen (d : ℝ) t) := by
    unfold pmFinitePrimePowerDampedFermiSource
    simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
    congr 1
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (le_max_left _ _))
    intro d hd hnot
    have hgt : (∏ p ∈ S, p) < d := by
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hn := mt Finset.mem_Icc.mpr hnot
      omega
    rw [pm_finitePrime_coefficient_eq_zero_above_product (pmOddPrimeAperture_prime N) hgt, zero_mul]
  rw [hext, pmOddMobiusFermiSource_eq_sum ht (show ⌊1 / t⌋₊ ≤ K from le_max_right _ _)]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hsmall : d ≤ ⌊1 / t⌋₊
  · rw [pmOddPrimeAperture_coefficient (hsmall.trans hN)]
  · rw [pm_fermiNymanGen_eq_zero_of_floor_lt ht (lt_of_not_ge hsmall), mul_zero, mul_zero]

theorem tendsto_pmFinitePrimePowerDampedFermiSource_odd {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => pmFinitePrimePowerDampedFermiSource (pmOddPrimeAperture N) 0 t)
      atTop (𝓝 (pmOddMobiusFermiSource t)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ⌊1 / t⌋₊] with N hN
  exact (pmFinitePrimePowerDampedFermiSource_odd_eq_of_covers ht hN).symm

theorem pmOddPrimeFermiSource_norm_budget_floor {C : ENNReal}
    (hC : ∀ N : ℕ, eLpNorm (pmFinitePrimePowerDampedFermiSource (pmOddPrimeAperture N) 0) 2
      (volume.restrict (Ioi (0 : ℝ))) ≤ C) : ENNReal.ofReal (Real.sqrt 2) ≤ C := by
  rw [← pmOddMobiusFermiSource_eLpNorm]
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
    (Eventually.of_forall hC)
    (fun N => (memLp_pmFinitePrimePowerDampedFermiSource (pmOddPrimeAperture N) 0).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact tendsto_pmFinitePrimePowerDampedFermiSource_odd ht

theorem continuous_pmFinitePrimePowerDampedFermiSource_parameter (S : Finset ℕ) (t : ℝ) :
    Continuous (fun ε : ℝ => pmFinitePrimePowerDampedFermiSource S ε t) := by
  unfold pmFinitePrimePowerDampedFermiSource
  apply Continuous.neg
  apply continuous_finsetSum
  intro d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hp : Continuous (fun ε : ℝ => (d : ℝ) ^ (-ε)) :=
    (Real.continuous_const_rpow hd0.ne').comp continuous_neg
  exact (continuous_const.mul (Complex.continuous_ofReal.comp hp)).mul continuous_const

theorem pmFinitePrimePowerDampedFermiSource_zero_norm_le {S : Finset ℕ} {C : ENNReal}
    (hC : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
      eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C) :
    eLpNorm (pmFinitePrimePowerDampedFermiSource S 0) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C := by
  apply Lp.eLpNorm_le_of_ae_tendsto hC
    (fun ε => (memLp_pmFinitePrimePowerDampedFermiSource S ε).aestronglyMeasurable)
  exact Eventually.of_forall fun t =>
    (continuous_pmFinitePrimePowerDampedFermiSource_parameter S t).tendsto 0 |>.mono_left nhdsWithin_le_nhds

theorem pmFinitePrimePowerDampedFermiSource_all_subset_budget_floor {C : ENNReal}
    {δ : ℝ} (hδ : 0 < δ)
    (hC : ∀ ε : ℝ, 0 < ε → ε < δ → ∀ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) →
      eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C) :
    ENNReal.ofReal (Real.sqrt 2) ≤ C := by
  apply pmOddPrimeFermiSource_norm_budget_floor
  intro N
  apply pmFinitePrimePowerDampedFermiSource_zero_norm_le
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε hεδ
  exact hC ε hε hεδ (pmOddPrimeAperture N) (pmOddPrimeAperture_prime N)

theorem pmFinitePrimePowerDampedFermiSource_exceeds_dyadic_budget {C : ENNReal}
    (hC : C < ENNReal.ofReal (Real.sqrt 2)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      C < eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  by_contra hn
  apply (not_le_of_gt hC)
  apply pmFinitePrimePowerDampedFermiSource_all_subset_budget_floor hδ
  intro ε hε hεδ S hS
  exact le_of_not_gt (fun hg => hn ⟨ε, hε, hεδ, S, hS, hg⟩)

theorem pmFinitePrimePowerDampedFermiSource_exceeds_unit_budget {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      1 < eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply pmFinitePrimePowerDampedFermiSource_exceeds_dyadic_budget _ hδ
  rw [ENNReal.one_lt_ofReal]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

end RHTower
