import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RemainderEndpoint
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.Realization

/-!
# Recovery of the clock spectrum from the critical singular trace

The square-shell radix has a unique nonsquare base below its successive
square roots. This recovers the primitive product and the dyadic order
from a single logarithmic singular-value coefficient.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open Filter
open scoped Topology

private theorem unique_dyadic_base {a b : ℕ} (ha : ¬IsSquare a) (hb : ¬IsSquare b) (k l : ℕ)
    (h : a^(2^k) = b^(2^l)) : a = b ∧ k = l := by
  induction k generalizing l with
  | zero =>
    cases l with
    | zero => exact ⟨by simpa only [pow_zero,pow_one] using h,rfl⟩
    | succ l =>
      exact (ha ⟨b^(2^l),by simpa only [pow_zero,pow_one,pow_succ 2 l,pow_mul,pow_two] using h⟩).elim
  | succ k ih =>
    cases l with
    | zero =>
      exact (hb ⟨a^(2^k),by simpa only [pow_zero,pow_one,pow_succ 2 k,pow_mul,pow_two] using h.symm⟩).elim
    | succ l =>
      rw [pow_succ 2 k,pow_succ 2 l,pow_mul,pow_mul] at h
      obtain ⟨hab,hkl⟩ := ih l (Nat.pow_left_injective (by norm_num : (2:ℕ) ≠ 0) h)
      exact ⟨hab,congrArg Nat.succ hkl⟩

private theorem dyadic_base (N : ℕ) (hN : 1 < N) : ∃ H k : ℕ, (1 < H ∧ ¬IsSquare H) ∧ N = H^(2^k) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hs : IsSquare N
    · obtain ⟨v,hv⟩ := hs
      have hv1 : 1 < v := by
        by_contra! h
        have hv0 : v = 0 ∨ v = 1 := by omega
        rcases hv0 with rfl | rfl <;> simp_all
      have hvN : v < N := by
        rw [hv]
        simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hv1 (Nat.zero_lt_one.trans hv1)
      obtain ⟨H,k,hH,hk⟩ := ih v hvN hv1
      exact ⟨H,k+1,hH,by rw [hv,hk,pow_succ 2 k,pow_mul,pow_two]⟩
    · exact ⟨N,0,⟨hN,hs⟩,by rw [pow_zero,pow_one]⟩

private theorem order_exponent (t : ExceptionalTime) : ∃ k : ℕ, windingOrder t = 2^(k+1) := by
  obtain ⟨d,hd⟩ := order_dyadic t
  cases d with
  | zero => exact ((order_nontrivial t).ne' (hd.trans (pow_zero 2))).elim
  | succ k => exact ⟨k,hd⟩

private theorem radix_power (t : ExceptionalTime) (j k : ℕ) (hm : windingOrder t = 2^(k+1)) :
    (tailRadix t j).val = ((block t).val^(2^k))^(2^j) := by
  rw [tailRadix,PNat.pow_coe,(refined_parameters t j).2.2,hm,pow_succ 2 k,← Nat.mul_assoc,
    Nat.mul_div_cancel _ (by norm_num : 0 < 2),Nat.mul_comm,pow_mul]

/-- The coefficient of the logarithmic singular trace in the critical plane. -/
def criticalCoefficient (t : ExceptionalTime) (j : ℕ) : ℝ := 2/((tailRadix t j).val-1:ℝ)

theorem critical_coefficient_eq_iff (t u : ExceptionalTime) (j : ℕ) :
    criticalCoefficient t j = criticalCoefficient u j ↔ block t = block u ∧ windingOrder t = windingOrder u := by
  obtain ⟨k,hk⟩ := order_exponent t
  obtain ⟨l,hl⟩ := order_exponent u
  constructor
  · intro h
    have ht : (1:ℝ) < (tailRadix t j).val := by exact_mod_cast radix_gt_one t j
    have hu : (1:ℝ) < (tailRadix u j).val := by exact_mod_cast radix_gt_one u j
    have hd := (div_eq_div_iff (sub_ne_zero.mpr ht.ne') (sub_ne_zero.mpr hu.ne')).mp h
    have hc : (tailRadix t j).val = (tailRadix u j).val := by
      exact_mod_cast (show ((tailRadix t j).val:ℝ) = (tailRadix u j).val by linarith only [hd])
    rw [radix_power t j k hk,radix_power u j l hl] at hc
    have hroots := Nat.pow_left_injective (pow_ne_zero j (by norm_num : (2:ℕ) ≠ 0)) hc
    obtain ⟨hb,he⟩ := unique_dyadic_base (block_nonsquare t) (block_nonsquare u) k l hroots
    exact ⟨PNat.coe_injective hb,by rw [hk,hl,he]⟩
  · rintro ⟨hb,hm⟩
    simp only [criticalCoefficient,tailRadix,(refined_parameters t j).2.2,(refined_parameters u j).2.2,hb,hm]

/-- Across different refinement origins the reading recovers the current order. -/
theorem critical_coefficient_eq_across_levels (t u : ExceptionalTime) (j i : ℕ) :
    criticalCoefficient t j = criticalCoefficient u i ↔
      block t = block u ∧ 2^j*windingOrder t = 2^i*windingOrder u := by
  have h (v : ExceptionalTime) (k : ℕ) :
      criticalCoefficient v k = criticalCoefficient (refined v k) 0 := by
    simp only [criticalCoefficient,tailRadix,refined,(refined_parameters v k).2.1]
  rw [h t j,h u i,critical_coefficient_eq_iff,(refined_parameters t j).2.1,(refined_parameters u i).2.1,
    (refined_parameters t j).2.2,(refined_parameters u i).2.2]

/-- Exact range at each refinement, including every integer square-root cutoff permitted there. -/
theorem critical_coefficient_range (j : ℕ) (D : ℝ) :
    (∃ t : ExceptionalTime, criticalCoefficient t j = D) ↔
      ∃ N : ℕ, 1 < N ∧ D = 2/(((N^(2^j):ℕ):ℝ)-1) := by
  constructor
  · rintro ⟨t,rfl⟩
    obtain ⟨k,hk⟩ := order_exponent t
    exact ⟨(block t).val^(2^k),one_lt_pow₀ (block_nontrivial t) (pow_ne_zero _ (by norm_num)),
      by rw [criticalCoefficient,radix_power t j k hk]⟩
  · rintro ⟨N,hN,rfl⟩
    obtain ⟨H,k,⟨hH,hns⟩,hk⟩ := dyadic_base N hN
    let a : ℕ+ := ⟨H,Nat.zero_lt_one.trans hH⟩
    obtain ⟨t,ht,hm⟩ := (spectral_range a (2^(k+1))).mpr
      ⟨⟨hH,hns⟩,one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero _),⟨k+1,rfl⟩⟩
    have ha : a.val = H := rfl
    exact ⟨t,by rw [criticalCoefficient,radix_power t j k hm,ht,ha,hk]⟩

/-- An actual critical logarithmic measurement determines the coefficient uniquely. -/
theorem critical_log_trace_iff (t : ExceptionalTime) (j : ℕ) (τ D : ℝ) :
    let s : ℂ := ⟨1/2,τ⟩
    _root_.RHTower.HasSchattenLogResidue 1 (dampedRemainder t j ⟨s,by change (0:ℝ) ≤ 1/2; norm_num⟩) D ↔
      D = criticalCoefficient t j := by
  constructor
  · intro h
    exact tendsto_nhds_unique h (remainder_critical_log_trace t j τ)
  · rintro rfl
    exact remainder_critical_log_trace t j τ

#print axioms critical_coefficient_eq_iff
#print axioms critical_coefficient_eq_across_levels
#print axioms critical_coefficient_range
#print axioms critical_log_trace_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
