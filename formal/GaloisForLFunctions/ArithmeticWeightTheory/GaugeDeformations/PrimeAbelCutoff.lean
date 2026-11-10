import GaloisForLFunctions.RHTower.WoldBooleanAcceleratedType
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

/-!
# Sparse-prime Abel bounds for a moving Euler cutoff

Prime density zero makes the normalized geometric prime sum vanish.
This controls the error between a smooth prime-phase transition and
its sharp Liouville cutoff.
-/

open Filter Topology Set Finset
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The natural density of the primes is zero. -/
theorem tendsto_primeCounting_div_nat_zero :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := tendsto_primeCounting_nat_ratio.mul hlog.inv_tendsto_atTop
  rw [mul_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hNr).ne'
  change (Nat.primeCounting N : ℝ) / ((N : ℝ) / Real.log N) * (Real.log N)⁻¹ = _
  field_simp

/-- Prime indices are negligible compared with their prime values. -/
theorem tendsto_prime_index_ratio_zero :
    Tendsto (fun n : ℕ => (n : ℝ) / (nthPrimeSubtype n : ℝ)) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (nthPrimeSubtype n : ℕ)) atTop atTop :=
    nthPrimeSubtype_strictMono.tendsto_atTop
  have hlim := tendsto_primeCounting_div_nat_zero.comp hp
  apply squeeze_zero (fun n => by positivity) _ hlim
  intro n
  have hn : n ≤ Nat.primeCounting (nthPrimeSubtype n) := by
    have hh := Nat.monotone_primeCounting' (Nat.le_succ (nthPrimeSubtype n : ℕ))
    change n ≤ Nat.primeCounting' ((nthPrimeSubtype n : ℕ) + 1)
    simpa only [nthPrimeSubtype, Nat.primeCounting'_nth_eq] using hh
  exact div_le_div_of_nonneg_right (by exact_mod_cast hn) (nthPrimeSubtype_pos n).le

/-- Every fixed integral slope eventually lies below the increasing prime enumeration. -/
theorem eventually_mul_index_le_prime (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, K * n ≤ (nthPrimeSubtype n : ℕ) := by
  by_cases hK : K = 0
  · subst K
    exact Eventually.of_forall (fun n => by simp only [zero_mul]; exact Nat.zero_le _)
  have hKr : 0 < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hh := tendsto_prime_index_ratio_zero.eventually (gt_mem_nhds (one_div_pos.mpr hKr))
  filter_upwards [hh] with n hn
  have hp := nthPrimeSubtype_pos n
  have hcross := (div_lt_iff₀ hp).mp hn
  have hmul := mul_lt_mul_of_pos_left hcross hKr
  have hineq : (K : ℝ) * n < (nthPrimeSubtype n : ℝ) := by
    simpa only [one_div, ← mul_assoc, mul_inv_cancel₀ hKr.ne', one_mul] using hmul
  exact_mod_cast hineq.le

/-- Geometric prime mass, convergent for parameters in the open unit interval. -/
def primeAbelMass (t : ℝ) : ℝ := ∑' p : Nat.Primes, t ^ (p : ℕ)

theorem summable_prime_geometric {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun p : Nat.Primes => t ^ (p : ℕ)) :=
  (summable_geometric_of_lt_one ht ht1).subtype Nat.Prime

/-- Eventual prime spacing bounds the full Abel mass by one geometric series. -/
theorem primeAbelMass_le_geometric {K J : ℕ} (hK : 0 < K)
    (hJ : ∀ n : ℕ, J ≤ n → K * n ≤ (nthPrimeSubtype n : ℕ))
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    primeAbelMass t ≤ (J : ℝ) + (1 - t ^ K)⁻¹ := by
  have hs : Summable (fun n : ℕ => t ^ (nthPrimeSubtype n : ℕ)) :=
    nthPrimeEquiv.summable_iff.mpr (summable_prime_geometric ht ht1)
  have htail : Summable (fun n : ℕ => t ^ (nthPrimeSubtype (n + J) : ℕ)) :=
    hs.comp_injective (show Function.Injective (fun n : ℕ => n + J) from
      fun _ _ h => Nat.add_right_cancel h)
  have htK : t ^ K < 1 := pow_lt_one₀ ht ht1 hK.ne'
  have hg := summable_geometric_of_lt_one (pow_nonneg ht K) htK
  have hterm (n : ℕ) : t ^ (nthPrimeSubtype (n + J) : ℕ) ≤ (t ^ K) ^ n := by
    rw [← pow_mul]
    have hexp := (Nat.mul_le_mul_left K (Nat.le_add_right n J)).trans (hJ (n + J) (by omega))
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hexp
    rw [hm, pow_add]
    have hpow : t ^ m ≤ 1 := pow_le_one₀ ht ht1.le
    nlinarith only [hpow, pow_nonneg ht (K * n)]
  have hfinite : (∑ n ∈ range J, t ^ (nthPrimeSubtype n : ℕ)) ≤ (J : ℝ) := by
    calc _ ≤ ∑ _n ∈ range J, (1 : ℝ) := sum_le_sum (fun n _ => pow_le_one₀ ht ht1.le)
         _ = _ := by simp
  have he : (∑' n : ℕ, t ^ (nthPrimeSubtype n : ℕ)) = primeAbelMass t :=
    nthPrimeEquiv.tsum_eq (fun p : Nat.Primes => t ^ (p : ℕ))
  rw [← he, ← hs.sum_add_tsum_nat_add J]
  exact add_le_add hfinite ((htail.tsum_le_tsum hterm hg).trans_eq
    (by simpa only [one_div] using tsum_geometric_of_lt_one (pow_nonneg ht K) htK))

private theorem one_sub_mul_geometric (t : ℝ) (K : ℕ) :
    (1 - t) * (∑ i ∈ range K, t ^ i) = 1 - t ^ K := by
  simpa only [mul_comm] using geom_sum_mul_neg t K

/-- Prime density zero forces normalized Abel mass to vanish at the unit endpoint. -/
theorem tendsto_normalized_primeAbelMass_zero :
    Tendsto (fun t : ℝ => (1 - t) * primeAbelMass t) (𝓝[<] 1) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / ε)
  have hKr : 0 < (K : ℝ) := (div_pos (by norm_num) hε).trans hK
  have hKn : 0 < K := by exact_mod_cast hKr
  have hKsmall : (K : ℝ)⁻¹ < ε := by
    have hh := (div_lt_iff₀ hε).mp hK
    rw [← one_div, div_lt_iff₀ hKr]
    nlinarith only [hh]
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (eventually_mul_index_le_prime K)
  have hpoly : Continuous (fun t : ℝ => ∑ i ∈ range K, t ^ i) := by fun_prop
  have hpoly1 : (∑ i ∈ range K, (1 : ℝ) ^ i) ≠ 0 := by
    simpa only [one_pow, sum_const, nsmul_eq_mul, card_range, mul_one] using hKr.ne'
  have hc : ContinuousAt (fun t : ℝ => (1 - t) * (J : ℝ) +
      (∑ i ∈ range K, t ^ i)⁻¹) 1 :=
    ((continuousAt_const.sub continuousAt_id).mul continuousAt_const).add
      (hpoly.continuousAt.inv₀ hpoly1)
  have hlim : Tendsto (fun t : ℝ => (1 - t) * (J : ℝ) +
      (∑ i ∈ range K, t ^ i)⁻¹) (𝓝[<] 1) (𝓝 ((K : ℝ)⁻¹)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have htpos : ∀ᶠ t : ℝ in 𝓝[<] 1, 0 < t :=
    (lt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, htpos, hlim.eventually (gt_mem_nhds hKsmall)]
    with t ht ht0 hsmall
  have ht1 : t < 1 := ht
  have hδ : 0 < 1 - t := sub_pos.mpr ht1
  have he : (1 - t) * ((J : ℝ) + (1 - t ^ K)⁻¹) =
      (1 - t) * (J : ℝ) + (∑ i ∈ range K, t ^ i)⁻¹ := by
    rw [← one_sub_mul_geometric t K, mul_inv, mul_add]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
  have hb := mul_le_mul_of_nonneg_left (primeAbelMass_le_geometric hKn hJ ht0.le ht1) hδ.le
  rw [he] at hb
  have hnonneg : 0 ≤ primeAbelMass t := tsum_nonneg
    (fun p : Nat.Primes => pow_nonneg ht0.le (p : ℕ))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hδ.le hnonneg)]
  exact hb.trans_lt hsmall

#print axioms tendsto_normalized_primeAbelMass_zero

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
