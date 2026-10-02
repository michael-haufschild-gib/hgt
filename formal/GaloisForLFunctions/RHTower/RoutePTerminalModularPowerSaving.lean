import GaloisForLFunctions.RHTower.DivisorUnsignedChannelExactMean
import Mathlib.Analysis.PSeries

/-!
# A power saving for the actual terminal modular residue

The reciprocal-phase estimate controls a growing set of Fourier modes;
the absolutely summable Bernoulli coefficients pay the remaining modes.
A growing cutoff yields a positive-power remainder for the exact terminal
modular primitives. This is an input to the Route RP hyperbolic pair-sector
argument, not a bound on the complete signed pair energy.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower
open DeletionMixedRefinement


private def reciprocalTail (H : ℕ) (k : ℤ) : ℝ :=
  if H < k.natAbs then ((k : ℝ)^2)⁻¹ else 0

private lemma reciprocalTail_summable (H : ℕ) : Summable (reciprocalTail H) := by
  have hs : Summable (fun k : ℤ => ((k : ℝ)^2)⁻¹) := by
    simpa only [one_div] using (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2))
  exact Summable.of_nonneg_of_le (fun k => by unfold reciprocalTail; split_ifs <;> positivity)
    (fun k => by unfold reciprocalTail; split_ifs <;> first | exact le_rfl | positivity) hs

private lemma reciprocalTail_tsum_le (H : ℕ) :
    (∑' k : ℤ, reciprocalTail H k) ≤ 4/((H:ℝ)+1) := by
  have he : Function.Even (reciprocalTail H) := by
    intro k
    simp [reciprocalTail]
  have hs := reciprocalTail_summable H
  have hsn : Summable (fun n : ℕ => reciprocalTail H n) :=
    hs.comp_injective Nat.cast_injective
  have hn : (∑' n : ℕ, reciprocalTail H n) ≤ 2/((H:ℝ)+1) := by
    apply hsn.tsum_le_of_sum_range_le
    intro n
    have heq : (∑ i ∈ range n, reciprocalTail H i) =
        ∑ i ∈ Ioo H n, ((i:ℝ)^2)⁻¹ := by
      simp only [reciprocalTail, Int.natAbs_natCast, Int.cast_natCast]
      rw [← sum_filter]
      congr 1
      ext i
      simp only [mem_filter, mem_range, mem_Ioo]
      tauto
    rw [heq]
    exact sum_Ioo_inv_sq_le H n
  have ht := tsum_int_eq_zero_add_two_mul_tsum_pnat he hs
  have hz : reciprocalTail H 0 = 0 := by simp [reciprocalTail]
  rw [hz, zero_add, nsmul_eq_mul] at ht
  have hp : (∑' n : ℕ+, reciprocalTail H n) = ∑' n : ℕ, reciprocalTail H n := by
    exact tsum_pnat_eq_tsum_of_eq_zero (f := fun n : ℕ => reciprocalTail H n)
      (by simpa using hz)
  rw [hp] at ht
  rw [ht]
  norm_num only [Nat.cast_ofNat]
  calc
    2 * (∑' n : ℕ, reciprocalTail H n) ≤ 2 * (2/((H:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = 4/((H:ℝ)+1) := by ring

private lemma bernoulli_weight_le_inv_sq (k : ℤ) :
    bernoulliModeWeight k ≤ ((k:ℝ)^2)⁻¹ := by
  have hc : (4*Real.pi^2)⁻¹ ≤ (1:ℝ) := by
    apply (inv_le_one₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  rw [bernoulliModeWeight, one_div, mul_inv_rev]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ ((k:ℝ)^2)⁻¹)

private lemma bernoulli_series_bound (z : ℤ → ℂ) (v : ℂ) (H : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hz : ∀ k, ‖z k‖ ≤ 1)
    (hlow : ∀ k, k ≠ 0 → k.natAbs ≤ H → ‖z k‖ ≤ B)
    (hv : HasSum (fun k => (bernoulliModeWeight k:ℂ)*z k) v) :
    ‖v‖ ≤ B/12 + 4/((H:ℝ)+1) := by
  have hmajor := (hasSum_bernoulliModeWeight.mul_left B).add
    (reciprocalTail_summable H).hasSum
  have hb := hv.norm_le_of_bounded hmajor (fun k => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (bernoulliModeWeight_nonneg k)]
    by_cases hk : k = 0
    · subst k
      simp [bernoulliModeWeight_zero, reciprocalTail]
    by_cases hsmall : k.natAbs ≤ H
    · have h := mul_le_mul_of_nonneg_left (hlow k hk hsmall) (bernoulliModeWeight_nonneg k)
      simpa [reciprocalTail, not_lt_of_ge hsmall, mul_comm] using h
    · have h := (mul_le_mul_of_nonneg_left (hz k) (bernoulliModeWeight_nonneg k)).trans
        (by simpa only [mul_one] using bernoulli_weight_le_inv_sq k)
      have hpos := mul_nonneg hB (bernoulliModeWeight_nonneg k)
      simp only [reciprocalTail, if_pos (lt_of_not_ge hsmall)]
      linarith)
  linarith [reciprocalTail_tsum_le H]

private lemma low_mode_bound (M k : ℕ) (hk : 1 ≤ k) (hlarge : 8*k ≤ Nat.sqrt M)
    (h : ℤ) (hh : h ≠ 0) (hhk : h.natAbs ≤ k) :
    ‖divisorTerminalReciprocalMode M h‖ ≤
      3*(Nat.sqrt M:ℝ)*((Nat.sqrt M:ℝ)/k+1+
        (24*(k:ℝ)^4+12)*Real.sqrt (Nat.sqrt M)) / M := by
  have hN : 1 ≤ Nat.sqrt M := by omega
  have hM : 1 ≤ M := hN.trans (Nat.sqrt_le_self M)
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hlo : (Nat.sqrt M:ℝ)^2 ≤ M := by exact_mod_cast Nat.sqrt_le' M
  have hhi : (M:ℝ) ≤ 4*(Nat.sqrt M:ℝ)^2 := by
    have h := Nat.lt_succ_sqrt' M
    exact_mod_cast (show M ≤ 4*(Nat.sqrt M)^2 by nlinarith only [h,hN])
  have hpos (h : ℤ) (hh : 0 < h) (hhk : h.natAbs ≤ k) :
      ‖divisorTerminalReciprocalMode M h‖ ≤
        3*(Nat.sqrt M:ℝ)*((Nat.sqrt M:ℝ)/k+1+
          (24*(k:ℝ)^4+12)*Real.sqrt (Nat.sqrt M)) / M := by
    have hhk' : |h| ≤ (k:ℤ) := by
      simpa only [Int.natCast_natAbs] using (show (h.natAbs:ℤ) ≤ k by exact_mod_cast hhk)
    have hhkR : (h:ℝ) ≤ k := by exact_mod_cast (le_abs_self h).trans hhk'
    have hhR : (1:ℝ) ≤ h := by exact_mod_cast hh
    have hlargeR : 8*(h:ℝ) ≤ Nat.sqrt M := by
      have h := (show (8:ℝ)*k ≤ Nat.sqrt M by exact_mod_cast hlarge)
      linarith
    have hb := norm_divisor_reciprocal_weighted_sum_le (h:ℝ) M (Nat.sqrt M) k
      hhR hk hN hlo hhi hlargeR
    have hcoef : 24*(k:ℝ)^3*(h:ℝ)+12 ≤ 24*(k:ℝ)^4+12 := by
      have h := mul_le_mul_of_nonneg_left hhkR (show 0 ≤ 24*(k:ℝ)^3 by positivity)
      nlinarith only [h]
    have hb' : ‖∑ d ∈ Icc 1 (Nat.sqrt M), (d:ℂ) *
        Complex.exp (((2*Real.pi*((h:ℝ)*M/d):ℝ):ℂ)*Complex.I)‖ ≤
        3*(Nat.sqrt M:ℝ)*((Nat.sqrt M:ℝ)/k+1+
          (24*(k:ℝ)^4+12)*Real.sqrt (Nat.sqrt M)) := by
      apply hb.trans
      gcongr
    unfold divisorTerminalReciprocalMode
    rw [norm_div, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ hm.le
    convert hb' using 1
    congr 1
    congr 1
    apply sum_congr rfl
    intro d hd
    congr 1
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rcases lt_or_gt_of_ne hh with hneg | hpos'
  · have h := hpos (-h) (by omega) (by simpa using hhk)
    simpa only [divisorTerminalReciprocalMode_neg, norm_star] using h
  · exact hpos h hpos' hhk

/-- Finite cutoff estimate with the full reciprocal Fourier tail retained. -/
theorem routeP_terminal_bernoulli_mean_bound (M k : ℕ)
    (hk : 1 ≤ k) (hlarge : 8*k ≤ Nat.sqrt M) :
    |(∑ d ∈ Icc 1 (Nat.sqrt M),
        (d:ℝ)*(bernoulliPeriodic ((M:ℝ)/d)+1/12))/(M:ℝ)| ≤
      (3*(Nat.sqrt M:ℝ)*((Nat.sqrt M:ℝ)/k+1+
        (24*(k:ℝ)^4+12)*Real.sqrt (Nat.sqrt M)) / M)/12 + 4/((k:ℝ)+1) := by
  have h := bernoulli_series_bound (divisorTerminalReciprocalMode M) _ k _
    (by positivity) (divisorTerminalReciprocalMode_norm_le M)
    (low_mode_bound M k hk hlarge) (hasSum_divisor_terminal_bernoulli_mean M)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

private lemma cutoff_budget_le (n m k : ℝ) (hk : 1 ≤ k)
    (hn : k^10 ≤ n) (hm : n^2 ≤ m) :
    (3*n*(n/k+1+(24*k^4+12)*Real.sqrt n)/m)/12+4/(k+1) ≤ 14/k := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hk1 : k ≤ k^5 := by simpa only [pow_one] using
    (pow_right_mono₀ hk (show 1 ≤ 5 by norm_num))
  have hk10 : k ≤ k^10 := by simpa only [pow_one] using
    (pow_right_mono₀ hk (show 1 ≤ 10 by norm_num))
  have hnpos : 0 < n := hkpos.trans_le (hk10.trans hn)
  have hmpos : 0 < m := (sq_pos_of_pos hnpos).trans_le hm
  have hks : k^5 ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by nlinarith only [hn])
  have hc : k*(24*k^4+12) ≤ 36*Real.sqrt n := by
    nlinarith only [hk1,hks]
  have hcs := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg n)
  have hs2 := Real.sq_sqrt hnpos.le
  have hb : 3*n*(n/k+1+(24*k^4+12)*Real.sqrt n)/m ≤ 114/k := by
    rw [div_le_iff₀ hmpos, div_mul_eq_mul_div, le_div_iff₀ hkpos]
    have hkn : k ≤ n := hk10.trans hn
    have ht : k*(n/k+1+(24*k^4+12)*Real.sqrt n) ≤ 38*n := by
      rw [mul_add, mul_add, mul_div_cancel₀ _ hkpos.ne']
      nlinarith only [hcs,hs2,hkn]
    have hb := mul_le_mul_of_nonneg_left ht (show 0 ≤ 3*n by positivity)
    nlinarith only [hb,hm]
  have ht : 4/(k+1) ≤ 4/k :=
    div_le_div_of_nonneg_left (by norm_num) hkpos (by linarith)
  calc
    _ ≤ (114/k)/12+4/k := add_le_add (div_le_div_of_nonneg_right hb (by norm_num)) ht
    _ = (27/2:ℝ)/k := by ring
    _ ≤ 14/k := div_le_div_of_nonneg_right (by norm_num) hkpos.le

/-- A growing Fourier cutoff pays the actual terminal Bernoulli remainder. -/
theorem routeP_terminal_bernoulli_mean_cutoff (M k : ℕ)
    (hk : 1 ≤ k) (hlarge : 8*k^10 ≤ Nat.sqrt M) :
    |(∑ d ∈ Icc 1 (Nat.sqrt M),
        (d:ℝ)*(bernoulliPeriodic ((M:ℝ)/d)+1/12))/(M:ℝ)| ≤ 14/(k:ℝ) := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk10 : k ≤ k^10 := by simpa only [pow_one] using
    (pow_right_mono₀ hk (show 1 ≤ 10 by norm_num))
  apply (routeP_terminal_bernoulli_mean_bound M k hk (by nlinarith only [hlarge,hk10])).trans
  apply cutoff_budget_le _ _ _ hkR
  · exact_mod_cast (show k^10 ≤ Nat.sqrt M by omega)
  · exact_mod_cast Nat.sqrt_le' M

/-- The literal terminal Bernoulli mean has a positive-power saving. -/
theorem routeP_terminal_bernoulli_mean_power_saving :
    ∀ᶠ M : ℕ in atTop,
    |(∑ d ∈ Icc 1 (Nat.sqrt M),
        (d:ℝ)*(bernoulliPeriodic ((M:ℝ)/d)+1/12))/(M:ℝ)| ≤
      28 / (M:ℝ)^((1:ℝ)/40) := by
  have hlim : Tendsto (fun M : ℕ => (M:ℝ)^((1:ℝ)/40)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/40)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop (64:ℝ))] with M hlarge
  let t : ℝ := (M:ℝ)^((1:ℝ)/40)
  let k : ℕ := ⌊t⌋₊
  have ht : 64 ≤ t := hlarge
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hk : 1 ≤ k := Nat.le_floor (by simpa using ht1)
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hkt : (k:ℝ) ≤ t := Nat.floor_le ht0.le
  have htk : t/2 ≤ k := by
    have h := Nat.lt_floor_add_one t
    change t < (k:ℝ)+1 at h
    linarith
  have ht40 : t^40 = (M:ℝ) := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg M)]
    norm_num
  have ht20 : 64 ≤ t^20 := ht.trans (by
    simpa only [pow_one] using (pow_right_mono₀ ht1 (show 1 ≤ 20 by norm_num)))
  have hk20 : (k:ℝ)^20 ≤ t^20 := by gcongr
  have hs : 8*k^10 ≤ Nat.sqrt M := by
    apply Nat.le_sqrt.mpr
    have hb : (64:ℝ)*(k:ℝ)^20 ≤ (M:ℝ) := by
      calc
        _ ≤ t^20*t^20 := mul_le_mul ht20 hk20 (by positivity) (by positivity)
        _ = _ := by rw [← pow_add, ht40]
    exact_mod_cast (show ((8:ℝ)*(k:ℝ)^10)*((8:ℝ)*(k:ℝ)^10) ≤ M by
      nlinarith only [hb])
  apply (routeP_terminal_bernoulli_mean_cutoff M k hk hs).trans
  rw [div_le_div_iff₀ hk0 ht0]
  linarith

private lemma terminal_identity (M d : ℕ) :
    HTGeometry.centeredModularMeanMagnitude d+HTGeometry.centeredModularPrimitive d M =
      (d:ℝ)*(bernoulliPeriodic ((M:ℝ)/d)+1/12)-1/(12*(d:ℝ)) := by
  by_cases hd : d = 0
  · subst d
    simp [HTGeometry.centeredModularMeanMagnitude,HTGeometry.centeredModularPrimitive,bernoulliPeriodic]
  unfold HTGeometry.centeredModularMeanMagnitude HTGeometry.centeredModularPrimitive bernoulliPeriodic
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hdr : (d:ℝ) ≠ 0 := by exact_mod_cast hd
  field_simp
  ring

/-- The exact modular primitive, including its reciprocal correction, has a
positive-power saving at the terminal scale. -/
theorem routeP_terminal_modular_mean_power_saving :
    ∀ᶠ M : ℕ in atTop,
    |(∑ d ∈ Icc 1 (Nat.sqrt M),
        (HTGeometry.centeredModularMeanMagnitude d+HTGeometry.centeredModularPrimitive d M))/(M:ℝ)| ≤
      29 / (M:ℝ)^((1:ℝ)/40) := by
  filter_upwards [routeP_terminal_bernoulli_mean_power_saving, eventually_ge_atTop (1:ℕ)] with M hB hM
  have hm1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hm : (0:ℝ) < M := by positivity
  have hs : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr hm
  have ht : 0 < (M:ℝ)^((1:ℝ)/40) := Real.rpow_pos_of_pos hm _
  have hts : (M:ℝ)^((1:ℝ)/40) ≤ Real.sqrt M := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hcorr0 : 0 ≤ ∑ d ∈ Icc 1 (Nat.sqrt M), 1/(12*(d:ℝ)) :=
    sum_nonneg (fun _ _ => by positivity)
  have hcorr : (∑ d ∈ Icc 1 (Nat.sqrt M), 1/(12*(d:ℝ)))/(M:ℝ) ≤
      1/(M:ℝ)^((1:ℝ)/40) := by
    have hb : (∑ d ∈ Icc 1 (Nat.sqrt M), 1/(12*(d:ℝ))) ≤ Nat.sqrt M := by
      calc
        _ ≤ ∑ _ ∈ Icc 1 (Nat.sqrt M), (1:ℝ) := by
          apply sum_le_sum
          intro d hd
          have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (mem_Icc.mp hd).1
          apply (div_le_one (by positivity)).mpr
          linarith
        _ = _ := by simp
    calc
      _ ≤ (Nat.sqrt M:ℝ)/(M:ℝ) := div_le_div_of_nonneg_right hb hm.le
      _ ≤ 1/Real.sqrt M := by
        rw [div_le_div_iff₀ hm hs]
        have h := mul_le_mul_of_nonneg_right (Real.nat_sqrt_le_real_sqrt (a:=M)) hs.le
        nlinarith only [h,Real.sq_sqrt hm.le]
      _ ≤ 1/(M:ℝ)^((1:ℝ)/40) := one_div_le_one_div_of_le ht hts
  simp_rw [terminal_identity]
  rw [sum_sub_distrib,sub_div]
  calc
    _ ≤ |(∑ d ∈ Icc 1 (Nat.sqrt M), (d:ℝ)*(bernoulliPeriodic ((M:ℝ)/d)+1/12))/(M:ℝ)| +
        |(∑ d ∈ Icc 1 (Nat.sqrt M), 1/(12*(d:ℝ)))/(M:ℝ)| := abs_sub _ _
    _ ≤ 28/(M:ℝ)^((1:ℝ)/40)+1/(M:ℝ)^((1:ℝ)/40) := by
      rw [abs_of_nonneg (div_nonneg hcorr0 hm.le)]
      exact add_le_add hB hcorr
    _ = _ := by ring

end RHTower
