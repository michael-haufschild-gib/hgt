import GaloisForLFunctions.BezoutValuationIncidence.VaughanTailPowerGainsAtEveryPositiveDamping
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
Mertens square-root oscillation forces infinitely many reciprocal-tail and
empty-leg energy values at their endpoint scales. Finite Abel inversion
retains an explicit head constant before transferring the oscillation.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- An eventual reciprocal-tail bound controls Mertens sums with a separate finite-head constant. -/
theorem exists_eventual_mertens_sqrt_bound_of_vaughan_tail_bound
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hF : ∀ᶠ n : ℕ in atTop, |pmPronicVaughanReciprocalTail ε n| ≤
      δ * (n : ℝ) ^ (-ε - 1 / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |∑ n ∈ Icc 1 N, moebiusReal n| ≤ C +
        (2 ^ (1 + ε) + 3 * ((1 + ε) * 2 ^ ε)) * δ * Real.sqrt (N : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hF
  let A : ℝ := (1 + ε) * 2 ^ ε
  let term : ℕ → ℝ := fun n =>
    (((n : ℝ) + 1) ^ (1 + ε) - (n : ℝ) ^ (1 + ε)) * pmPronicVaughanReciprocalTail ε n
  let C : ℝ := |pmPronicVaughanReciprocalTail ε 0| + ∑ n ∈ Icc 1 N₀, |term n|
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hNstart
  have hN : 1 ≤ N := (le_max_right N₀ 1).trans hNstart
  have hN₀N : N₀ ≤ N := (le_max_left N₀ 1).trans hNstart
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hroot1 : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN1
  have hboundary : |((N : ℝ) + 1) ^ (1 + ε) * pmPronicVaughanReciprocalTail ε N| ≤
      2 ^ (1 + ε) * δ * Real.sqrt (N : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    calc
      _ ≤ (2 * (N : ℝ)) ^ (1 + ε) * (δ * (N : ℝ) ^ (-ε - 1 / 2)) :=
        mul_le_mul
          (Real.rpow_le_rpow (by positivity) (by linarith only [hN1]) (by positivity))
          (hN₀ N hN₀N) (abs_nonneg _) (Real.rpow_nonneg (by positivity) _)
      _ = 2 ^ (1 + ε) * δ * ((N : ℝ) ^ (1 + ε) * (N : ℝ) ^ (-ε - 1 / 2)) := by
        rw [Real.mul_rpow (by norm_num) hN0.le]
        ring
      _ = _ := by
        rw [← Real.rpow_add hN0, show (1 + ε) + (-ε - 1 / 2) = 1 / 2 by ring,
          ← Real.sqrt_eq_rpow]
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      |term n| ≤ (if n < N₀ then |term n| else 0) + A * δ * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    split_ifs with hhead
    · exact le_add_of_nonneg_right (by positivity)
    · rw [zero_add]
      have hinc : 0 ≤ ((n : ℝ) + 1) ^ (1 + ε) - (n : ℝ) ^ (1 + ε) :=
        sub_nonneg.mpr (Real.rpow_le_rpow hn0.le (by linarith) (by positivity))
      dsimp only [term]
      rw [abs_mul, abs_of_nonneg hinc]
      calc
        _ ≤ (A * (n : ℝ) ^ ε) * (δ * (n : ℝ) ^ (-ε - 1 / 2)) :=
          mul_le_mul (rpow_one_add_increment_le_of_nonneg hε hn1)
            (hN₀ n (not_lt.mp hhead)) (abs_nonneg _) (by positivity)
        _ = A * δ * ((n : ℝ) ^ ε * (n : ℝ) ^ (-ε - 1 / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hn0, show ε + (-ε - 1 / 2) = -(1 / 2 : ℝ) by ring]
  have hhead : (∑ n ∈ Icc 1 N with n < N₀, |term n|) ≤ ∑ n ∈ Icc 1 N₀, |term n| := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      omega
    · intro n _ _
      exact abs_nonneg _
  have hpowsum : (∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 3 * Real.sqrt (N : ℝ) := by
    have h := RHTower.Sieve.sum_rpow_neg_subcritical_le
      (η := (1 / 2 : ℝ)) (by norm_num) (by norm_num) N
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at h
    linarith only [h, hroot1]
  have hsum : |∑ n ∈ Icc 1 N, term n| ≤
      (∑ n ∈ Icc 1 N₀, |term n|) + 3 * A * δ * Real.sqrt (N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N,
          ((if n < N₀ then |term n| else 0) + A * δ * (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
      _ = (∑ n ∈ Icc 1 N with n < N₀, |term n|) +
          A * δ * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [sum_add_distrib, ← sum_filter, ← mul_sum]
      _ ≤ (∑ n ∈ Icc 1 N₀, |term n|) + A * δ * (3 * Real.sqrt (N : ℝ)) :=
        add_le_add hhead (mul_le_mul_of_nonneg_left hpowsum (mul_nonneg hA hδ))
      _ = _ := by ring
  rw [sum_moebiusReal_eq_reciprocalTail_abel]
  calc
    _ ≤ |pmPronicVaughanReciprocalTail ε 0| +
        |((N : ℝ) + 1) ^ (1 + ε) * pmPronicVaughanReciprocalTail ε N| +
          |∑ n ∈ Icc 1 N, term n| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ |pmPronicVaughanReciprocalTail ε 0| +
        2 ^ (1 + ε) * δ * Real.sqrt (N : ℝ) +
          ((∑ n ∈ Icc 1 N₀, |term n|) + 3 * A * δ * Real.sqrt (N : ℝ)) :=
      add_le_add (add_le_add le_rfl hboundary) hsum
    _ = _ := by dsimp only [C, A]; ring

/-- The signed reciprocal tail has a positive square-root-scaled floor infinitely often. -/
theorem frequent_vaughan_scaled_reciprocalTail_sqrt_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ N : ℕ in atTop,
      c < |(N : ℝ) ^ (ε + 1 / 2) * pmPronicVaughanReciprocalTail ε N| := by
  obtain ⟨c, hc, hfreq, _⟩ := mertens_omega_pm_sqrt
  let K : ℝ := 2 ^ (1 + ε) + 3 * ((1 + ε) * 2 ^ ε)
  have hK : 0 < K := by dsimp only [K]; positivity
  let δ : ℝ := c / (4 * K)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  by_contra hno
  have hsmall : ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) ^ (ε + 1 / 2) * pmPronicVaughanReciprocalTail ε N| ≤ δ :=
    (Filter.not_frequently.mp hno).mono fun N hN => not_lt.mp hN
  have htail : ∀ᶠ N : ℕ in atTop,
      |pmPronicVaughanReciprocalTail ε N| ≤ δ * (N : ℝ) ^ (-ε - 1 / 2) := by
    filter_upwards [hsmall, eventually_ge_atTop 1] with N hN hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hN0 _)] at hN
    have hdiv : |pmPronicVaughanReciprocalTail ε N| ≤ δ / (N : ℝ) ^ (ε + 1 / 2) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hN0 _)).mpr (by simpa only [mul_comm] using hN)
    refine hdiv.trans_eq ?_
    rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le]
    congr 2
    ring
  obtain ⟨C, hC, hM⟩ := exists_eventual_mertens_sqrt_bound_of_vaughan_tail_bound hε.le hδ.le htail
  have hKδ : K * δ = c / 4 := by dsimp only [δ]; field_simp
  have hrootlim : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  have hMhalf : ∀ᶠ N : ℕ in atTop,
      |∑ n ∈ Icc 1 N, moebiusReal n| ≤ (c / 2) * Real.sqrt (N : ℝ) := by
    filter_upwards [hM, hrootlim.eventually_ge_atTop (4 * C / c)] with N hN hhead
    change |∑ n ∈ Icc 1 N, moebiusReal n| ≤ C + K * δ * Real.sqrt (N : ℝ) at hN
    rw [hKδ] at hN
    have hpay : 4 * C ≤ Real.sqrt (N : ℝ) * c := (div_le_iff₀ hc).mp hhead
    linarith only [hN, hpay]
  have hreal : ∀ᶠ x : ℝ in atTop, |mertensFunctionReal x| ≤ (c / 2) * Real.sqrt x := by
    filter_upwards [tendsto_nat_floor_atTop.eventually hMhalf, eventually_ge_atTop (1 : ℝ)]
      with x hx hx1
    change |∑ n ∈ Icc 1 ⌊x⌋₊, moebiusReal n| ≤ _
    exact hx.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Nat.floor_le (zero_le_one.trans hx1))) (by positivity))
  obtain ⟨x, hxlarge, hxbound, hx1⟩ :=
    (hfreq.and_eventually (hreal.and (eventually_ge_atTop (1 : ℝ)))).exists
  have hxroot : 0 < Real.sqrt x := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx1)
  have hpos := mul_pos hc hxroot
  have hle := le_abs_self (mertensFunctionReal x)
  linarith only [hxlarge, hxbound, hpos, hle]

/-- The maximal square-root-normalized signed tail cannot converge to zero. -/
theorem not_tendsto_vaughan_scaled_reciprocalTail_sqrt_zero {ε : ℝ} (hε : 0 < ε) :
    ¬ Tendsto (fun N : ℕ => (N : ℝ) ^ (ε + 1 / 2) * pmPronicVaughanReciprocalTail ε N)
      atTop (𝓝 0) := by
  intro hzero
  obtain ⟨c, hc, hfreq⟩ := frequent_vaughan_scaled_reciprocalTail_sqrt_lower hε
  have hsmall : ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) ^ (ε + 1 / 2) * pmPronicVaughanReciprocalTail ε N| < c := by
    have hlim := hzero.abs
    rw [abs_zero] at hlim
    exact hlim.eventually (gt_mem_nhds hc)
  obtain ⟨N, hlarge, hsmallN⟩ := (hfreq.and_eventually hsmall).exists
  exact (lt_asymm hlarge hsmallN)

/-- The same oscillation can be stated directly at the unscaled reciprocal-tail power. -/
theorem frequent_vaughan_reciprocalTail_sqrt_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (-ε - 1 / 2) < |pmPronicVaughanReciprocalTail ε N| := by
  obtain ⟨c, hc, hfreq⟩ := frequent_vaughan_scaled_reciprocalTail_sqrt_lower hε
  refine ⟨c, hc, ?_⟩
  apply (hfreq.and_eventually (eventually_ge_atTop 1)).mono
  rintro N ⟨hN, hN1⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hN0 _)] at hN
  have hdiv : c / (N : ℝ) ^ (ε + 1 / 2) < |pmPronicVaughanReciprocalTail ε N| :=
    (div_lt_iff₀ (Real.rpow_pos_of_pos hN0 _)).mpr (by simpa only [mul_comm] using hN)
  convert hdiv using 1
  rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le]
  congr 2
  ring

/-- The square empty-leg energy has a positive reciprocal-cutoff-squared floor infinitely often. -/
theorem frequent_vaughan_square_energy_endpoint_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ N : ℕ in atTop,
      c < (N : ℝ) ^ 2 *
        (pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 /
          ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε)) := by
  obtain ⟨c, hc, hfreq⟩ := frequent_vaughan_scaled_reciprocalTail_sqrt_lower hε
  have hZ : 0 < pmPronicPowerDensity ε := by
    rw [pmPronicPowerDensity_eq_inv_density hε]
    exact inv_pos.mpr (pmPowerDampedDivisorDensity_re_pos hε)
  refine ⟨pmPronicPowerDensity ε ^ 2 / 2 * c ^ 4, by positivity, ?_⟩
  apply (hfreq.and_eventually (eventually_ge_atTop 1)).mono
  rintro N ⟨hN, hN1⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpow : |(N : ℝ) ^ (ε + 1 / 2) * pmPronicVaughanReciprocalTail ε N| ^ 4 =
      (N : ℝ) ^ 2 * ((N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N) ^ 4 := by
    have hscale : (N : ℝ) ^ (ε + 1 / 2) * pmPronicVaughanReciprocalTail ε N =
        Real.sqrt (N : ℝ) * ((N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N) := by
      rw [Real.rpow_add hN0, ← Real.sqrt_eq_rpow]
      ring
    rw [← abs_pow, abs_of_nonneg (by positivity), hscale, mul_pow,
      show Real.sqrt (N : ℝ) ^ 4 = (Real.sqrt (N : ℝ) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hN0.le]
  have hfour : c ^ 4 < |(N : ℝ) ^ (ε + 1 / 2) * pmPronicVaughanReciprocalTail ε N| ^ 4 :=
    pow_lt_pow_left₀ hc.le hN (by norm_num)
  calc
    _ < pmPronicPowerDensity ε ^ 2 / 2 *
        |(N : ℝ) ^ (ε + 1 / 2) * pmPronicVaughanReciprocalTail ε N| ^ 4 :=
      mul_lt_mul_of_pos_left hfour (by positivity)
    _ = (N : ℝ) ^ 2 * (pmPronicPowerDensity ε ^ 2 / 2 *
        ((N : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε N) ^ 4) := by rw [hpow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pmPronicVaughanCentredGram_square_scaled_bounds hε hN1).1 (sq_nonneg _)

/-- The endpoint empty-leg energy cannot be little-o of the reciprocal square horizon. -/
theorem not_tendsto_vaughan_square_energy_endpoint_zero {ε : ℝ} (hε : 0 < ε) :
    ¬ Tendsto (fun N : ℕ => (N : ℝ) ^ 2 *
      (pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 /
        ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  intro hzero
  obtain ⟨c, hc, hfreq⟩ := frequent_vaughan_square_energy_endpoint_lower hε
  obtain ⟨N, hlarge, hsmall⟩ := (hfreq.and_eventually (hzero.eventually (gt_mem_nhds hc))).exists
  exact lt_asymm hlarge hsmall

/-- The endpoint lower oscillation is equivalently a reciprocal-cutoff-squared lower bound. -/
theorem frequent_vaughan_square_energy_reciprocal_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (-2 : ℝ) <
        pmPronicVaughanCentredGram ε N N (N ^ 2) 3 3 /
          ((N ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) := by
  obtain ⟨c, hc, hfreq⟩ := frequent_vaughan_square_energy_endpoint_lower hε
  refine ⟨c, hc, ?_⟩
  apply (hfreq.and_eventually (eventually_ge_atTop 1)).mono
  rintro N ⟨hN, hN1⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.rpow_neg hN0.le, Real.rpow_two, ← div_eq_mul_inv]
  exact (div_lt_iff₀ (sq_pos_of_pos hN0)).mpr (by simpa only [mul_comm] using hN)

#print axioms exists_eventual_mertens_sqrt_bound_of_vaughan_tail_bound
#print axioms frequent_vaughan_scaled_reciprocalTail_sqrt_lower
#print axioms not_tendsto_vaughan_scaled_reciprocalTail_sqrt_zero
#print axioms frequent_vaughan_reciprocalTail_sqrt_lower
#print axioms frequent_vaughan_square_energy_endpoint_lower
#print axioms not_tendsto_vaughan_square_energy_endpoint_zero
#print axioms frequent_vaughan_square_energy_reciprocal_lower
end GaloisForLFunctions.BezoutValuationIncidence
