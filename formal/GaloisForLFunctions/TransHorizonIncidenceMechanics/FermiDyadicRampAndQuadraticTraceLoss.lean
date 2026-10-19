import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiCompleteTraceValuationStability
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompositeSquarefreeStepAndMultiOctaveL2Energy
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanMoment

/-!
# Dyadic ramps and the loss in complete selected traces

Finite coefficient columns synthesize disjoint valuation shells. A linear ramp
in the normalized sieve values has constant selected first differences.
-/

open Finset
open RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private abbrev shell (k n : ℕ) : Prop := 2 ^ (k + 1) ∣ n ∧ ¬ 2 ^ (k + 2) ∣ n

private theorem shell_unique {i j n : ℕ} (hi : shell i n) (hj : shell j n) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (hi.2 (dvd_trans (pow_dvd_pow 2 (by omega : i + 2 ≤ j + 1)) hj.1))
  · exact hij
  · exact False.elim (hj.2 (dvd_trans (pow_dvd_pow 2 (by omega : j + 2 ≤ i + 1)) hi.1))

private theorem shell_double (k n : ℕ) : shell (k + 1) (2 * n) ↔ shell k n := by
  have hd (j : ℕ) : 2 ^ (j + 1) ∣ 2 * n ↔ 2 ^ j ∣ n := by
    rw [pow_succ', Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)]
  change (2 ^ ((k + 1) + 1) ∣ 2 * n ∧ ¬ 2 ^ ((k + 2) + 1) ∣ 2 * n) ↔ _
  rw [hd (k + 1), hd (k + 2)]

private theorem shell_zero_double {n : ℕ} (hn : 2 ∣ n) : ¬ shell 0 (2 * n) := by
  intro h
  apply h.2
  norm_num
  simpa only [show 4 = 2 * 2 by norm_num] using mul_dvd_mul_left 2 hn

private def profile (L : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range L, if shell k n then f k else 0

private theorem profile_at_shell {L k n : ℕ} (hk : k < L) (hn : shell k n)
    (f : ℕ → ℝ) : profile L f n = f k := by
  unfold profile
  rw [Finset.sum_eq_single k]
  · simp only [if_pos hn]
  · intro j _ hj
    exact if_neg (fun h => hj (shell_unique h hn))
  · exact fun h => (h (Finset.mem_range.mpr hk)).elim

private theorem profile_double {L n : ℕ} (hn : 2 ∣ n) (f : ℕ → ℝ) (hf : f L = 0) :
    profile L f (2 * n) = profile L (fun k => f (k + 1)) n := by
  have h : profile (L + 1) f (2 * n) = profile L (fun k => f (k + 1)) n := by
    unfold profile
    rw [Finset.sum_range_succ']
    simp only [shell_double, if_neg (shell_zero_double hn), add_zero]
  have ht : profile (L + 1) f (2 * n) = profile L f (2 * n) := by
    unfold profile
    rw [Finset.sum_range_succ]
    simp [hf]
  exact ht.symm.trans h

private theorem profile_sq (L n : ℕ) (f : ℕ → ℝ) :
    (profile L f n) ^ 2 = ∑ k ∈ Finset.range L, if shell k n then (f k) ^ 2 else 0 := by
  by_cases h : ∃ k ∈ Finset.range L, shell k n
  · obtain ⟨k, hk, hn⟩ := h
    rw [profile_at_shell (Finset.mem_range.mp hk) hn]
    exact (profile_at_shell (Finset.mem_range.mp hk) hn (fun j => (f j) ^ 2)).symm
  · have hn (k : ℕ) (hk : k ∈ Finset.range L) : ¬ shell k n :=
      fun hs => h ⟨k, hk, hs⟩
    have hz : profile L f n = 0 := Finset.sum_eq_zero (fun k hk => if_neg (hn k hk))
    rw [hz, zero_pow (by omega : 2 ≠ 0)]
    exact (Finset.sum_eq_zero (fun k hk => if_neg (hn k hk))).symm

private def ramp (L k : ℕ) : ℝ := (2 : ℝ) ^ (k + 1) * ((L : ℝ) - k)

private theorem ramp_diff (L k : ℕ) : 2 * ramp L k - ramp L (k + 1) = 2 ^ (k + 2) := by
  unfold ramp
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  ring

private theorem ramp_profile_difference {L n : ℕ} (hn : 2 ∣ n) :
    2 * profile L (ramp L) n - profile L (ramp L) (2 * n) =
      profile L (fun k => 2 ^ (k + 2)) n := by
  rw [profile_double hn (ramp L) (by simp [ramp])]
  unfold profile
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : shell k n
  · simp only [if_pos hk]
    exact ramp_diff L k
  · simp only [if_neg hk, mul_zero, sub_zero]

private theorem shell_power (k : ℕ) : shell k (2 ^ (k + 1)) := by
  refine ⟨dvd_refl _, ?_⟩
  intro h
  have hp : 0 < (2 : ℕ) ^ (k + 1) := by positivity
  have hd := Nat.le_of_dvd hp h
  have hlt : (2 : ℕ) ^ (k + 1) < 2 ^ (k + 2) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

private theorem profile_odd (L m : ℕ) (f : ℕ → ℝ) : profile L f (2 * m + 1) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  apply if_neg
  intro h
  have hp : (2 : ℕ) ^ 1 ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (by omega)
  have htwo := dvd_trans hp h.1
  norm_num only [pow_one] at htwo
  omega

private theorem dilated_weight_le {a t : ℝ} (ha : 1 ≤ a) (ht : 1 ≤ t) :
    a ^ 2 / ((a * t) * (a * t + 1)) ≤ 2 / (t * (t + 1)) := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h : 0 ≤ a * (t - 1) + 2 := by positivity
  nlinarith [mul_nonneg (show 0 ≤ a * t by positivity) h]

private theorem power_weight_lower {a x : ℝ} (ha : 1 ≤ a) :
    x ^ 2 / 2 ≤ (a * x) ^ 2 / (a * (a + 1)) := by
  have ha0 : 0 < a := by linarith
  apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
  nlinarith [mul_nonneg (show 0 ≤ a - 1 by linarith)
    (show 0 ≤ a * x ^ 2 by positivity)]

private theorem ramp_sq_sum (L : ℕ) :
    (∑ k ∈ Finset.range L, ((L : ℝ) - k) ^ 2) =
      (L : ℝ) * (L + 1) * (2 * L + 1) / 6 := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    have h (k : ℕ) : ((L : ℝ) + 1 - (k + 1)) ^ 2 = ((L : ℝ) - k) ^ 2 := by ring
    simp_rw [h]
    rw [ih]
    ring

private theorem power_pair_boundary (k : ℕ) : 2 * (2 ^ k - 1) + 2 = 2 ^ (k + 1) := by
  have hp : 0 < (2 : ℕ) ^ k := by positivity
  rw [pow_succ]
  omega

private theorem power_pair_injective : Function.Injective (fun k : ℕ => 2 ^ k - 1) := by
  intro i j h
  change 2 ^ i - 1 = 2 ^ j - 1 at h
  have hi : 0 < (2 : ℕ) ^ i := by positivity
  have hj : 0 < (2 : ℕ) ^ j := by positivity
  apply Nat.pow_right_injective (by omega : 2 ≤ 2)
  change (2 : ℕ) ^ i = 2 ^ j
  omega

/-- A finite dyadic ramp, supported on powers of two through `2^(L+1)`. -/
def fermiDyadicRampWeight (L d : ℕ) : ℝ :=
  ∑ k ∈ Finset.range L,
    ((if d = 2 ^ (k + 1) then ramp L k else 0) -
      (if d = 2 ^ (k + 2) then ramp L k else 0))

private theorem ramp_sieve (L n : ℕ) :
    sieveSeq (2 ^ (L + 1)) (fermiDyadicRampWeight L) n = profile L (ramp L) n := by
  unfold sieveSeq fermiDyadicRampWeight profile
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hkL := Finset.mem_range.mp hk
  have hp1 : 0 < (2 : ℕ) ^ (k + 1) := by positivity
  have hp2 : 0 < (2 : ℕ) ^ (k + 2) := by positivity
  have hb1 : 2 ^ (k + 1) ≤ (2 : ℕ) ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hb2 : 2 ^ (k + 2) ≤ (2 : ℕ) ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_Icc,
    show 1 ≤ 2 ^ (k + 1) by omega, show 1 ≤ 2 ^ (k + 2) by omega, hb1, hb2,
    true_and]
  by_cases h2 : 2 ^ (k + 2) ∣ n
  · have h1 : 2 ^ (k + 1) ∣ n := dvd_trans (pow_dvd_pow 2 (by omega)) h2
    simp [h1, h2, shell]
  · by_cases h1 : 2 ^ (k + 1) ∣ n <;> simp [h1, h2, shell]

private theorem ramp_odd_jump (L m : ℕ) :
    fermiBoundaryJump (2 ^ (L + 1)) (fermiDyadicRampWeight L) (2 * m + 1) = 0 := by
  rw [fermiBoundaryJump_odd, ramp_sieve, profile_odd, neg_zero]

private theorem ramp_even_jump (L m : ℕ) :
    fermiBoundaryJump (2 ^ (L + 1)) (fermiDyadicRampWeight L) (4 * m + 4) =
      profile L (fun k => 2 ^ (k + 2)) (2 * m + 2) := by
  have hj := fermiBoundaryJump_even (2 ^ (L + 1)) (fermiDyadicRampWeight L) (2 * m + 1)
  rw [show 2 * (2 * m + 1) + 2 = 4 * m + 4 by omega,
    show 2 * m + 1 + 1 = 2 * m + 2 by omega] at hj
  rw [hj, ramp_sieve, ramp_sieve, show 4 * m + 4 = 2 * (2 * m + 2) by omega]
  exact ramp_profile_difference (by omega : 2 ∣ 2 * m + 2)

private theorem shell_pronic_term_le (k m : ℕ) :
    (if shell k (2 * m + 2) then ((2 : ℝ) ^ (k + 2)) ^ 2 else 0) /
        (pronicSeq (4 * m + 4) : ℝ) ≤
      if 2 ^ k ∣ m + 1 then ((2 : ℝ) ^ (k + 2)) ^ 2 /
        (pronicSeq (4 * (m + 1)) : ℝ) else 0 := by
  by_cases hs : shell k (2 * m + 2)
  · have hd := hs.1
    rw [pow_succ', show 2 * m + 2 = 2 * (m + 1) by omega,
      Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)] at hd
    simp only [if_pos hs, if_pos hd, show 4 * m + 4 = 4 * (m + 1) by omega, le_refl]
  · rw [if_neg hs, zero_div]
    split_ifs <;> positivity

private theorem dyadic_scaled_pronic_le (k t : ℕ) (ht : 1 ≤ t) :
    ((2 : ℝ) ^ (k + 2)) ^ 2 / (pronicSeq (4 * (2 ^ k * t)) : ℝ) ≤
      2 / ((t : ℝ) * (t + 1)) := by
  let A : ℝ := 2 ^ (k + 2)
  have hA_nat : 1 ≤ (2 : ℕ) ^ (k + 2) := by
    have hpos : 0 < (2 : ℕ) ^ (k + 2) := by positivity
    omega
  have hA : 1 ≤ A := by dsimp [A]; exact_mod_cast hA_nat
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hden : (pronicSeq (4 * (2 ^ k * t)) : ℝ) =
      (A * (t : ℝ)) * (A * (t : ℝ) + 1) := by
    simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_pow, Nat.cast_ofNat, A, pow_succ]
    ring
  rw [hden]
  exact dilated_weight_le hA ht1

private theorem reciprocal_partial_le (S : Finset ℕ) :
    (∑ t ∈ S, 1 / ((t : ℝ) * (t + 1))) ≤ 1 := by
  have hq := hasSum_pm_reciprocal_weight
  have hs := Summable.sum_le_tsum S (fun t _ => by positivity) hq.summable
  rw [hq.tsum_eq] at hs
  exact hs

private theorem shell_pronic_sum_le (k M : ℕ) :
    (∑ m ∈ Finset.range M,
      (if shell k (2 * m + 2) then ((2 : ℝ) ^ (k + 2)) ^ 2 else 0) /
        (pronicSeq (4 * m + 4) : ℝ)) ≤ 2 := by
  let A : ℝ := 2 ^ (k + 2)
  calc
    _ ≤ ∑ m ∈ Finset.range M,
        if 2 ^ k ∣ m + 1 then A ^ 2 / (pronicSeq (4 * (m + 1)) : ℝ) else 0 :=
      Finset.sum_le_sum (fun m _ => shell_pronic_term_le k m)
    _ = ∑ j ∈ Finset.Icc 1 M,
        if 2 ^ k ∣ j then A ^ 2 / (pronicSeq (4 * j) : ℝ) else 0 :=
      (sum_Icc_eq_sum_range_succ (fun j : ℕ =>
        if 2 ^ k ∣ j then A ^ 2 / (pronicSeq (4 * j) : ℝ) else 0) M).symm
    _ = ∑ t ∈ Finset.Icc 1 (M / 2 ^ k),
        A ^ 2 / (pronicSeq (4 * (2 ^ k * t)) : ℝ) := by
      rw [← Finset.sum_filter, sum_Icc_filter_dvd_eq_sum_Icc_div (by positivity)]
    _ ≤ ∑ t ∈ Finset.Icc 1 (M / 2 ^ k), 2 / ((t : ℝ) * (t + 1)) := by
      exact Finset.sum_le_sum (fun t ht => dyadic_scaled_pronic_le k t (Finset.mem_Icc.mp ht).1)
    _ ≤ 2 := by
      have hs := reciprocal_partial_le (Finset.Icc 1 (M / 2 ^ k))
      calc
        _ = 2 * ∑ t ∈ Finset.Icc 1 (M / 2 ^ k), 1 / ((t : ℝ) * (t + 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          ring
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hs (by norm_num)
        _ = 2 := by ring

private theorem ramp_selected_upper (L : ℕ) :
    fermiSelectedTotalPronicEnergy (2 ^ (L + 1)) (fermiDyadicRampWeight L) ≤ 2 * L := by
  unfold fermiSelectedTotalPronicEnergy
  apply Real.tsum_le_of_sum_range_le
    (fun m => by simp only [fermiSelectedPronicEnergy, Finset.sum_singleton]; positivity)
  intro M
  simp only [fermiSelectedPronicEnergy, Finset.sum_singleton, ramp_odd_jump,
    ramp_even_jump, zero_pow (by omega : 2 ≠ 0), zero_div, zero_add, profile_sq]
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _k ∈ Finset.range L, (2 : ℝ) :=
      Finset.sum_le_sum (fun k _ => shell_pronic_sum_le k M)
    _ = 2 * L := by simp; ring

private theorem ramp_sieve_lower (L : ℕ) :
    (L : ℝ) * (L + 1) * (2 * L + 1) / 12 ≤
      sieveTotalPronicEnergy (2 ^ (L + 1)) (fermiDyadicRampWeight L) := by
  let e (m : ℕ) := sievePairedPronicEnergy (2 ^ (L + 1)) (fermiDyadicRampWeight L) {m}
  have he (m : ℕ) : 0 ≤ e m := by
    simp only [e, sievePairedPronicEnergy, Finset.sum_singleton]
    positivity
  have hs := Summable.sum_le_tsum ((Finset.range L).image (fun k => 2 ^ k - 1))
    (fun m _ => he m) (sieve_fermi_pronic_summable (2 ^ (L + 1)) (fermiDyadicRampWeight L)).1
  rw [Finset.sum_image (fun i _ j _ hij => power_pair_injective hij)] at hs
  have hterm (k : ℕ) (hk : k ∈ Finset.range L) : ((L : ℝ) - k) ^ 2 / 2 ≤ e (2 ^ k - 1) := by
    have hp_nat : 1 ≤ (2 : ℕ) ^ (k + 1) := by
      have hpos : 0 < (2 : ℕ) ^ (k + 1) := by positivity
      omega
    have hp : (1 : ℝ) ≤ 2 ^ (k + 1) := by exact_mod_cast hp_nat
    have hb := power_weight_lower (x := (L : ℝ) - k) hp
    have hv := ramp_sieve L (2 ^ (k + 1))
    rw [profile_at_shell (Finset.mem_range.mp hk) (shell_power k)] at hv
    simp only [e, sievePairedPronicEnergy, Finset.sum_singleton, power_pair_boundary, hv]
    have hd : (pronicSeq (2 ^ (k + 1)) : ℝ) =
        (2 : ℝ) ^ (k + 1) * (2 ^ (k + 1) + 1) := by
      simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    rw [hd]
    have hodd : 0 ≤ sieveSeq (2 ^ (L + 1)) (fermiDyadicRampWeight L)
        (2 * (2 ^ k - 1) + 1) ^ 2 / (pronicSeq (2 * (2 ^ k - 1) + 1) : ℝ) := by positivity
    dsimp [ramp]
    linarith
  calc
    _ = ∑ k ∈ Finset.range L, ((L : ℝ) - k) ^ 2 / 2 := by
      rw [← Finset.sum_div, ramp_sq_sum]
      ring
    _ ≤ ∑ k ∈ Finset.range L, e (2 ^ k - 1) := Finset.sum_le_sum hterm
    _ ≤ sieveTotalPronicEnergy (2 ^ (L + 1)) (fermiDyadicRampWeight L) := hs

/-- Explicit finite coefficients carry cubic sieve energy but only linear selected energy. -/
theorem fermiDyadicRamp_pronic_bounds (L : ℕ) :
    (L : ℝ) * (L + 1) * (2 * L + 1) / 12 ≤
        sieveTotalPronicEnergy (2 ^ (L + 1)) (fermiDyadicRampWeight L) ∧
      fermiSelectedTotalPronicEnergy (2 ^ (L + 1)) (fermiDyadicRampWeight L) ≤ 2 * L :=
  ⟨ramp_sieve_lower L, ramp_selected_upper L⟩

/-- Every nonempty ramp has a strictly positive complete selected trace. -/
theorem fermiDyadicRamp_selected_pos {L : ℕ} (hL : 0 < L) :
    0 < fermiSelectedTotalPronicEnergy (2 ^ (L + 1)) (fermiDyadicRampWeight L) := by
  have hv : profile L (fun k => (2 : ℝ) ^ (k + 2)) (2 * 0 + 2) = 4 := by
    have h := profile_at_shell hL (shell_power 0) (fun k => (2 : ℝ) ^ (k + 2))
    norm_num at h
    exact h
  have hcell : fermiSelectedPronicEnergy (2 ^ (L + 1)) (fermiDyadicRampWeight L) {0} =
      (4 : ℝ) / 5 := by
    simp only [fermiSelectedPronicEnergy, Finset.sum_singleton, ramp_odd_jump,
      ramp_even_jump, hv]
    norm_num [pronicSeq]
  have hs := Summable.sum_le_tsum ({0} : Finset ℕ)
    (fun m _ => by
      simp only [fermiSelectedPronicEnergy, Finset.sum_singleton]
      positivity)
    (sieve_fermi_pronic_summable (2 ^ (L + 1)) (fermiDyadicRampWeight L)).2
  simp only [Finset.sum_singleton, hcell] at hs
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4 / 5) hs

/-- Quadratic valuation-depth loss is forced by explicit finite coefficient ramps. -/
theorem fermiDyadicRamp_quadratic_loss (L : ℕ) :
    (((L : ℝ) + 1) * (2 * L + 1) / 24) *
        fermiSelectedTotalPronicEnergy (2 ^ (L + 1)) (fermiDyadicRampWeight L) ≤
      sieveTotalPronicEnergy (2 ^ (L + 1)) (fermiDyadicRampWeight L) := by
  have h := fermiDyadicRamp_pronic_bounds L
  calc
    _ ≤ (((L : ℝ) + 1) * (2 * L + 1) / 24) * (2 * L) :=
      mul_le_mul_of_nonneg_left h.2 (by positivity)
    _ = (L : ℝ) * (L + 1) * (2 * L + 1) / 12 := by ring
    _ ≤ _ := h.1

/-- No horizon-independent constant recovers arbitrary sieve energy from the complete selected trace. -/
theorem fermiSelectedTotal_no_uniform_inverse :
    ¬ ∃ C : ℝ, ∀ (N : ℕ) (c : ℕ → ℝ),
      sieveTotalPronicEnergy N c ≤ C * fermiSelectedTotalPronicEnergy N c := by
  rintro ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    by_contra hc
    have hlow := (fermiDyadicRamp_pronic_bounds 1).1
    have hbound := hC 4 (fermiDyadicRampWeight 1)
    have hpos : 0 < fermiSelectedTotalPronicEnergy 4 (fermiDyadicRampWeight 1) :=
      fermiDyadicRamp_selected_pos (by omega : 0 < 1)
    have hprod := mul_nonneg (show 0 ≤ -C by linarith) hpos.le
    norm_num only [Nat.cast_one] at hlow
    nlinarith
  obtain ⟨L, hL⟩ := exists_nat_gt (24 * C + 1)
  have hL0 : (0 : ℝ) < L := by linarith
  have hgap : 0 < ((L : ℝ) + 1) * (2 * L + 1) - 24 * C := by
    nlinarith [sq_nonneg (L : ℝ)]
  have h := fermiDyadicRamp_pronic_bounds L
  have hu := (hC (2 ^ (L + 1)) (fermiDyadicRampWeight L)).trans
    (mul_le_mul_of_nonneg_left h.2 hC0)
  nlinarith [mul_pos hL0 hgap]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
