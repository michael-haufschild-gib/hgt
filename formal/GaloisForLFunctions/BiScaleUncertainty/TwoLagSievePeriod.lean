import GaloisForLFunctions.RHTower.Sieve.JointCongruenceClass
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp

/-!
# Exact joint divisor counts on a common period

Compatibility is divisibility of the additive lag by the gcd. Compatible
solutions form one residue class modulo the lcm, without a coprimality premise.
This is the finite counting bridge used by simultaneous additive-lag moments.
-/

namespace GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve
open RHTower.Sieve
set_option autoImplicit false

private theorem exists_joint_solution_of_gcd {a b h : ℕ}
    (hb : 0 < b) (hg : Nat.gcd a b ∣ h) :
    ∃ n₀, a ∣ n₀ ∧ b ∣ n₀+h := by
  have hs : Nat.gcd a b ∣ negShift b h :=
    (Nat.dvd_add_iff_left hg).mpr ((Nat.gcd_dvd_right a b).trans (negShift_add_dvd hb h))
  have hc : 0 ≡ negShift b h [MOD Nat.gcd a b] :=
    (Nat.modEq_zero_iff_dvd.mpr hs).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' hc
  refine ⟨k, Nat.modEq_zero_iff_dvd.mp hk1, ?_⟩
  exact Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.add_right h hk2).trans
    (Nat.modEq_zero_iff_dvd.mpr (negShift_add_dvd hb h)))

private theorem joint_iff_lcm_shift {a b h n₀ : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h0a : a ∣ n₀) (h0b : b ∣ n₀+h) (n : ℕ) :
    (a ∣ n ∧ b ∣ n+h) ↔ Nat.lcm a b ∣ n + negShift (Nat.lcm a b) n₀ := by
  let L := Nat.lcm a b
  let s := negShift L n₀
  have hbase : n₀+s ≡ 0 [MOD L] :=
    Nat.modEq_zero_iff_dvd.mpr (by simpa [Nat.add_comm] using negShift_add_dvd (Nat.lcm_pos ha hb) n₀)
  constructor
  · rintro ⟨hna, hnb⟩
    have hma : n ≡ n₀ [MOD a] := (Nat.modEq_zero_iff_dvd.mpr hna).trans
      (Nat.modEq_zero_iff_dvd.mpr h0a).symm
    have hmb : n ≡ n₀ [MOD b] := Nat.ModEq.add_right_cancel' h
      ((Nat.modEq_zero_iff_dvd.mpr hnb).trans (Nat.modEq_zero_iff_dvd.mpr h0b).symm)
    exact Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.add_right s (Nat.mod_lcm hma hmb)).trans hbase)
  · intro hd
    have hm : n ≡ n₀ [MOD L] := Nat.ModEq.add_right_cancel' s
      ((Nat.modEq_zero_iff_dvd.mpr hd).trans hbase.symm)
    have hma : n ≡ n₀ [MOD a] := hm.of_dvd (Nat.dvd_lcm_left a b)
    have hmb : n ≡ n₀ [MOD b] := hm.of_dvd (Nat.dvd_lcm_right a b)
    exact ⟨Nat.modEq_zero_iff_dvd.mp (hma.trans (Nat.modEq_zero_iff_dvd.mpr h0a)),
      Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.add_right h hmb).trans (Nat.modEq_zero_iff_dvd.mpr h0b))⟩

/-- Every residue class has exactly the same count in a complete period. -/
theorem card_shift_complete_period {M P : ℕ} (s : ℕ) (hP : M ∣ P) :
    ((Finset.Ioc 0 P).filter (fun k => M ∣ k+s)).card = P/M := by
  have hshift := card_filter_dvd_add_shift M s 0 P
  simp only [Nat.zero_add] at hshift
  rw [hshift, card_filter_dvd_Ioc M s (s+P) (Nat.le_add_right s P)]
  simp only [Nat.add_div_of_dvd_left hP, Nat.add_sub_cancel_left]

/-- Exact joint incidence count, including incompatible noncoprime divisors. -/
theorem card_joint_complete_period {a b h P : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hP : Nat.lcm a b ∣ P) :
    ((Finset.Ioc 0 P).filter (fun k => a ∣ k ∧ b ∣ k+h)).card =
      if Nat.gcd a b ∣ h then P / Nat.lcm a b else 0 := by
  classical
  by_cases hg : Nat.gcd a b ∣ h
  · obtain ⟨n₀, h0a, h0b⟩ := exists_joint_solution_of_gcd hb hg
    rw [if_pos hg]
    have hset := Finset.filter_congr (s := Finset.Ioc 0 P)
      (fun k _ => joint_iff_lcm_shift ha hb h0a h0b k)
    rw [hset, card_shift_complete_period _ hP]
  · rw [if_neg hg]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    obtain ⟨_, hka, hkb⟩ := Finset.mem_filter.mp hk
    have hgk : Nat.gcd a b ∣ k := (Nat.gcd_dvd_left a b).trans hka
    have hgkh : Nat.gcd a b ∣ k+h := (Nat.gcd_dvd_right a b).trans hkb
    exact hg ((Nat.dvd_add_iff_right hgk).mpr hgkh)

/-- Exact normalized joint density on any positive common period. -/
theorem joint_density_complete_period {a b h P : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hP : Nat.lcm a b ∣ P) (hPpos : 0 < P) :
    (((Finset.Ioc 0 P).filter (fun k => a ∣ k ∧ b ∣ k+h)).card : ℝ) / (P : ℝ) =
      if Nat.gcd a b ∣ h then (Nat.gcd a b : ℝ) / ((a : ℝ)*b) else 0 := by
  have hL0 : (Nat.lcm a b : ℝ) ≠ 0 := by exact_mod_cast (Nat.lcm_pos ha hb).ne'
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hG0 : (Nat.gcd a b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left b ha).ne'
  have hprod : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) = (a : ℝ)*b := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  rw [card_joint_complete_period ha hb hP]
  by_cases hg : Nat.gcd a b ∣ h
  · rw [if_pos hg, if_pos hg, Nat.cast_div hP hL0, ← hprod]
    field_simp
  · simp [hg]

end GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve
