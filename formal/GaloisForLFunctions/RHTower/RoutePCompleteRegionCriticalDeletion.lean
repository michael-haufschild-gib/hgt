import GaloisForLFunctions.RHTower.RoutePTwoPrimePacketTimeResponse
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment
import GaloisForLFunctions.RHTower.DivisorCenteredHyperbola
import GaloisForLFunctions.HTGeometry.FarBandPowerTail
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap
import GaloisForLFunctions.RHTower.DivisorHyperbolaAbelBound
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorAbelProducer

/-!
# Critical deletion of the complete Möbius divisor region

For the native centered-divisor source, group original labels by their product
m = d*j. Once k >= m^2, every divisor of m is active. The quotient-ramp lift
and square-birth Abel estimate give a uniform allowance for every such channel.
The divisor-count sum then bounds the entire complete region by
R*(1+log R), R = floor(sqrt(M-1)). Its normalized response tends to zero.

Finite Fubini identifies this region with the literal active labels d*j <= sqrt(k).
The complementary active labels and smooth remainder retain all original signs.
Their joint normalized boundedness is exactly RH. No bound for that remainder
is proved here, and neither native Route-P square debt is declared paid.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction HTGeometry Filter Topology
namespace RHTower

private theorem small_modulus_bound {m d : ℕ} (hdm : d ≤ m) (N : ℕ) :
    -(1/16 : ℝ) ≤ ∑ t ∈ range N,
      centeredModularRamp d t * halfOrderAbelStep (m*m) t ∧
    (∑ t ∈ range N, centeredModularRamp d t * halfOrderAbelStep (m*m) t) ≤ 0 := by
  have h := sum_centeredModularRamp_mul_bounds d N (halfOrderAbelStep (m*m))
    (halfOrderAbelStep_nonneg _) (halfOrderAbelStep_antitone _)
  have hi := halfOrderAbelStep_square_initial m
  have hdmR : (d : ℝ) ≤ m := by exact_mod_cast hdm
  have hmul := mul_le_mul_of_nonneg_right hdmR (halfOrderAbelStep_nonneg (m*m) 0)
  exact ⟨by nlinarith [h.1], h.2⟩

theorem routeP_complete_quotient_channel_bound {m d : ℕ}
    (hd : d ∈ m.divisors) (M : ℕ) :
    |∑ k ∈ Ico (m*m) M, centeredModularRamp (m/d) (k/d) * halfOrderAbelStep 0 k| ≤ 1 := by
  have hm : 0 < m := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
  have hdvd := (Nat.mem_divisors.mp hd).1
  have hdpos := Nat.pos_of_dvd_of_pos hdvd hm
  have hdm := Nat.le_of_dvd hm hdvd
  have hj : 0 < m/d := Nat.div_pos hdm hdpos
  have hjR : (1 : ℝ) ≤ (m/d : ℕ) := by exact_mod_cast hj
  have hjRpos : (0 : ℝ) < (m/d : ℕ) := by positivity
  have hlift (k : ℕ) : centeredModularRamp (m/d) (k/d) =
      centeredModularRamp m k - centeredModularRamp d k / (m/d : ℕ) := by
    simpa only [Nat.mul_div_cancel' hdvd] using
      routeP_centeredModularRamp_quotient hdpos hj k
  have hshift (t : ℕ) : centeredModularRamp d (m*m+t) = centeredModularRamp d t := by
    have hzero := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hdvd m)
    simp [centeredModularRamp, Nat.add_mod, hzero]
  rw [sum_Ico_eq_sum_range]
  simp_rw [hlift, centeredModularRamp_mul_add, hshift]
  have hw (t : ℕ) : halfOrderAbelStep 0 (m*m+t) = halfOrderAbelStep (m*m) t := by
    simp only [halfOrderAbelStep, Nat.zero_add]
  simp_rw [hw, sub_mul, div_mul_eq_mul_div, sum_sub_distrib]
  rw [← sum_div]
  have ha := small_modulus_bound (le_refl m) (M-m*m)
  have hb := small_modulus_bound hdm (M-m*m)
  have hb0 := div_nonpos_of_nonpos_of_nonneg hb.2 hjRpos.le
  have hb1 : -(1/16 : ℝ) ≤
      (∑ t ∈ range (M-m*m), centeredModularRamp d t * halfOrderAbelStep (m*m) t) /
        (m/d : ℕ) := by
    apply (le_div_iff₀ hjRpos).mpr
    nlinarith [hb.1]
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2]

/-- Complete product row of the unweighted Möbius centered-divisor source. -/
def routePCompleteRampRow (m k : ℕ) : ℝ :=
  ∑ d ∈ m.divisors, (moebius d : ℝ) * centeredModularRamp (m/d) (k/d)

theorem routeP_complete_ramp_row_abel_bound (m M : ℕ) :
    |∑ k ∈ Ico (m*m) M, routePCompleteRampRow m k * halfOrderAbelStep 0 k| ≤
      (m.divisors.card : ℝ) := by
  unfold routePCompleteRampRow
  simp_rw [sum_mul]
  rw [sum_comm]
  simp_rw [mul_assoc, ← mul_sum]
  calc
    _ ≤ ∑ d ∈ m.divisors, |(moebius d : ℝ) *
        ∑ k ∈ Ico (m*m) M, centeredModularRamp (m/d) (k/d) * halfOrderAbelStep 0 k| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ m.divisors, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      have hmu : |(moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      exact (mul_le_mul hmu (routeP_complete_quotient_channel_bound hd M)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp

def routePCompleteRampAbel (M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 (Nat.sqrt (M-1)),
    ∑ k ∈ Ico (m*m) M, routePCompleteRampRow m k * halfOrderAbelStep 0 k

theorem routeP_complete_ramp_abel_bound {M : ℕ} (hM : 2 ≤ M) :
    |routePCompleteRampAbel M| ≤
      (Nat.sqrt (M-1) : ℝ) * (1 + Real.log (Nat.sqrt (M-1) : ℝ)) := by
  have hr : 1 ≤ Nat.sqrt (M-1) := Nat.le_sqrt.mpr (by omega)
  unfold routePCompleteRampAbel
  calc
    _ ≤ ∑ m ∈ Icc 1 (Nat.sqrt (M-1)),
        |∑ k ∈ Ico (m*m) M, routePCompleteRampRow m k * halfOrderAbelStep 0 k| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Icc 1 (Nat.sqrt (M-1)), (m.divisors.card : ℝ) :=
      sum_le_sum fun m _ => routeP_complete_ramp_row_abel_bound m M
    _ ≤ _ := by simpa using Sieve.sum_card_divisors_pow_le_polylog 1 _ hr

/-- The complete-row region is negligible at the RH critical normalization. -/
theorem routeP_complete_ramp_abel_critical_limit :
    Tendsto (fun M : ℕ => routePCompleteRampAbel M / M) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto (fun M : ℕ => (1 + Real.log M) / Real.sqrt M)
      atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      GaloisForLFunctions.tendsto_one_add_log_div_rpow_atTop_zero
        (t := (1/2 : ℝ)) (by positivity)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hM0 : (0 : ℝ) < M := by positivity
  have hs0 : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have hr1 : 1 ≤ Nat.sqrt (M-1) := Nat.le_sqrt.mpr (by omega)
  have hr0 : (0 : ℝ) < (Nat.sqrt (M-1) : ℕ) := by exact_mod_cast hr1
  have hrM : (Nat.sqrt (M-1) : ℝ) ≤ M := by
    exact_mod_cast (Nat.sqrt_le_self (M-1)).trans (Nat.sub_le M 1)
  have hrs : (Nat.sqrt (M-1) : ℝ) ≤ Real.sqrt M := by
    apply (Real.le_sqrt (by positivity) hM0.le).mpr
    have h := (Nat.sqrt_le (M-1)).trans (Nat.sub_le M 1)
    simpa only [sq] using (show (Nat.sqrt (M-1) : ℝ) * Nat.sqrt (M-1) ≤ M by exact_mod_cast h)
  have hlog := Real.log_le_log hr0 hrM
  have hlog0 : 0 ≤ 1 + Real.log (M : ℝ) := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    linarith [Real.log_nonneg this]
  have hbound := (routeP_complete_ramp_abel_bound hM).trans
    ((mul_le_mul_of_nonneg_left (show 1 + Real.log (Nat.sqrt (M-1) : ℝ) ≤
        1 + Real.log (M : ℝ) by linarith) (Nat.cast_nonneg (Nat.sqrt (M-1)))).trans
      (mul_le_mul_of_nonneg_right hrs hlog0))
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hM0]
  calc
    _ ≤ Real.sqrt M * (1 + Real.log M) / M := div_le_div_of_nonneg_right hbound hM0.le
    _ = _ := by
      have hs := Real.sq_sqrt hM0.le
      field_simp
      nlinarith

/-- All complete rows appear with their literal moving endpoints. -/
theorem routeP_complete_ramp_abel_eq_time_sum (M : ℕ) :
    routePCompleteRampAbel M = ∑ k ∈ range M,
      (∑ m ∈ Icc 1 (Nat.sqrt k), routePCompleteRampRow m k) * halfOrderAbelStep 0 k := by
  let D := Icc 1 (Nat.sqrt (M-1))
  have hfibre (k : ℕ) (hk : k ∈ range M) :
      Icc 1 (Nat.sqrt k) = D.filter (fun m => m*m ≤ k) := by
    have hkM : k ≤ M-1 := by have := mem_range.mp hk; omega
    ext m
    simp only [mem_Icc, mem_filter, D]
    constructor
    · intro hm
      exact ⟨⟨hm.1, hm.2.trans (Nat.sqrt_le_sqrt hkM)⟩, Nat.le_sqrt.mp hm.2⟩
    · intro hm
      exact ⟨hm.1.1, Nat.le_sqrt.mpr hm.2⟩
  have htime (m : ℕ) : (range M).filter (fun k => m*m ≤ k) = Ico (m*m) M := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  symm
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ k ∈ range M, ∑ m ∈ D,
          if m*m ≤ k then routePCompleteRampRow m k * halfOrderAbelStep 0 k else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [hfibre k hk, sum_filter]
    _ = ∑ m ∈ D, ∑ k ∈ range M,
          if m*m ≤ k then routePCompleteRampRow m k * halfOrderAbelStep 0 k else 0 := by
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro m _
      rw [← sum_filter, htime]

private theorem complete_rows_as_dilations (k : ℕ) :
    (∑ m ∈ Icc 1 (Nat.sqrt k), routePCompleteRampRow m k) =
      ∑ d ∈ Icc 1 k, (moebius d : ℝ) *
        ∑ j ∈ Icc 1 (Nat.sqrt k / d), centeredModularRamp j (k/d) := by
  unfold routePCompleteRampRow
  rw [Sieve.sum_divisors_swap _
    (fun d j => (moebius d : ℝ) * centeredModularRamp j (k/d))]
  simp_rw [← mul_sum]
  apply sum_subset (Icc_subset_Icc_right (Nat.sqrt_le_self k))
  intro d hd hnot
  have hdgt : Nat.sqrt k < d := by
    simp only [mem_Icc] at hd hnot
    omega
  simp [Nat.div_eq_of_lt hdgt]

private theorem complete_fibre (k d : ℕ) (hd : 0 < d) :
    (Icc 1 (Nat.sqrt (k/d))).filter (fun j => d*j ≤ Nat.sqrt k) =
      Icc 1 (Nat.sqrt k / d) := by
  ext j
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hj, _⟩, hprod⟩
    exact ⟨hj, (Nat.le_div_iff_mul_le hd).mpr (by simpa [mul_comm] using hprod)⟩
  · rintro ⟨hj, hquot⟩
    have hprod : d*j ≤ Nat.sqrt k := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hquot
    have hjprod : j ≤ d*j := by nlinarith
    have hsq : d*j*(d*j) ≤ k := Nat.le_sqrt.mp hprod
    have hsmall : (j*j)*d ≤ k := by
      have h := Nat.mul_le_mul_left (d*j) hjprod
      nlinarith
    exact ⟨⟨hj, Nat.le_sqrt.mpr ((Nat.le_div_iff_mul_le hd).mpr hsmall)⟩, hprod⟩

/-- The active complementary labels: their product has not reached its complete square birth. -/
def routePMovingRampRemainder (k : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 k, (moebius d : ℝ) *
    ∑ j ∈ (Icc 1 (Nat.sqrt (k/d))).filter (fun j => Nat.sqrt k < d*j),
      centeredModularRamp j (k/d)

/-- Exact partition of the native Möbius centered-divisor source. -/
theorem routeP_mobius_centered_source_partition (k : ℕ) :
    (∑ d ∈ Icc 1 k, (moebius d : ℝ) * centeredDivisorHyperbola (k/d)) =
      (∑ m ∈ Icc 1 (Nat.sqrt k), routePCompleteRampRow m k) +
        routePMovingRampRemainder k := by
  rw [complete_rows_as_dilations]
  unfold routePMovingRampRemainder centeredDivisorHyperbola
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [← mul_add, ← complete_fibre k d (mem_Icc.mp hd).1]
  congr 1
  simpa only [not_le] using (sum_filter_add_sum_filter_not
    (Icc 1 (Nat.sqrt (k/d))) (fun j => d*j ≤ Nat.sqrt k)
    (fun j => centeredModularRamp j (k/d))).symm

/-- Smooth source and moving complementary ramps, retaining their relative sign. -/
def routePUnpaidMobiusAbel (M : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (M-1), halfOrderAbelStep 0 k *
    ((∑ d ∈ Icc 1 k, (moebius d : ℝ) * divisorHyperbolaSmoothRemainder (k/d)) +
      2 * routePMovingRampRemainder k)

/-- Coefficient-exact deletion of the critically vanishing complete region. -/
theorem routeP_mobius_abel_eq_complete_add_unpaid (M : ℕ) :
    mobiusDivisorSquareRootAbelMoment M =
      2 * routePCompleteRampAbel M + routePUnpaidMobiusAbel M := by
  have htime : (∑ k ∈ Icc 1 (M-1),
      (∑ m ∈ Icc 1 (Nat.sqrt k), routePCompleteRampRow m k) * halfOrderAbelStep 0 k) =
        routePCompleteRampAbel M := by
    rw [routeP_complete_ramp_abel_eq_time_sum]
    apply sum_subset
    · intro k hk
      simp only [mem_Icc, mem_range] at hk ⊢
      omega
    · intro k hk hnot
      have hk0 : k = 0 := by
        simp only [mem_Icc, mem_range] at hk hnot
        omega
      subst k
      simp
  have hpoint (k : ℕ) : (∑ d ∈ Icc 1 k, (moebius d : ℝ) * primeFreeDivisorDefect (k/d)) =
      (∑ d ∈ Icc 1 k, (moebius d : ℝ) * divisorHyperbolaSmoothRemainder (k/d)) +
        2 * ((∑ m ∈ Icc 1 (Nat.sqrt k), routePCompleteRampRow m k) +
          routePMovingRampRemainder k) := by
    have hs (n : ℕ) : primeFreeDivisorDefect n =
        divisorHyperbolaSmoothRemainder n + 2 * centeredDivisorHyperbola n :=
      (divisorHyperbolaSmooth_add_centered n).symm
    simp_rw [hs, mul_add, sum_add_distrib]
    rw [← mul_add, ← routeP_mobius_centered_source_partition]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro d _
    ring
  unfold mobiusDivisorSquareRootAbelMoment routePUnpaidMobiusAbel
  simp_rw [hpoint]
  rw [← htime, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  simp only [halfOrderAbelStep, Nat.zero_add]
  ring

/-- Deleting the complete region leaves exactly the remaining RH obligation. -/
theorem riemannHypothesis_iff_routeP_unpaid_abel_bounded :
    RiemannHypothesis ↔ ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 2 ≤ M →
      |routePUnpaidMobiusAbel M / M| ≤ B := by
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto
    (fun M : ℕ => routePCompleteRampAbel M / M)
    routeP_complete_ramp_abel_critical_limit).exists_norm_le
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ ⟨0, rfl⟩)
  have hC (M : ℕ) : |routePCompleteRampAbel M / M| ≤ A := by
    simpa only [Real.norm_eq_abs] using hA _ ⟨M, rfl⟩
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded]
  constructor
  · rintro ⟨B, hB0, hB⟩
    refine ⟨B + 2*A, by positivity, fun M hM => ?_⟩
    have heq : routePUnpaidMobiusAbel M / M =
        mobiusDivisorSquareRootAbelMoment M / M - 2 * (routePCompleteRampAbel M / M) := by
      rw [routeP_mobius_abel_eq_complete_add_unpaid]
      ring
    rw [heq]
    calc
      _ ≤ |mobiusDivisorSquareRootAbelMoment M / M| +
          |2 * (routePCompleteRampAbel M / M)| := abs_sub _ _
      _ ≤ B + 2*A := by rw [abs_mul, abs_of_pos (by positivity : (0:ℝ)<2)]; nlinarith [hB M hM, hC M]
  · rintro ⟨B, hB0, hB⟩
    refine ⟨B + 2*A, by positivity, fun M hM => ?_⟩
    rw [routeP_mobius_abel_eq_complete_add_unpaid, add_div, mul_div_assoc]
    calc
      _ ≤ |2 * (routePCompleteRampAbel M / M)| + |routePUnpaidMobiusAbel M / M| := abs_add_le _ _
      _ ≤ B + 2*A := by rw [abs_mul, abs_of_pos (by positivity : (0:ℝ)<2)]; nlinarith [hB M hM, hC M]

end RHTower

