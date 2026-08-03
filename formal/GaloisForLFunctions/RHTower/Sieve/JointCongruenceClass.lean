import GaloisForLFunctions.RHTower.Sieve.JointCongruence

/-!
# The two congruences cut out a single residue class

For coprime moduli the pair `a ∣ n`, `b ∣ n + h` is equivalent to one congruence modulo `ab`:

`a ∣ n ∧ b ∣ n + h  ↔  ab ∣ n + negShift (ab) n₀`,

where `n₀` is any common solution.  Both directions go through `Nat.ModEq`, so no natural
subtraction appears.

Consequently the joint count in a window differs from `L/(ab)` by less than one — the pair of
conditions is no harder to count than a single one, which is what makes a shifted correlation
tractable by sieve methods.
-/

namespace RHTower.Sieve

open Finset

/-- **The joint condition is a single residue class.** -/
theorem joint_iff_dvd_shift {a b h n₀ : ℕ} (hab : Nat.Coprime a b) (hpos : 0 < a * b)
    (h0a : a ∣ n₀) (h0b : b ∣ (n₀ + h)) (n : ℕ) :
    (a ∣ n ∧ b ∣ (n + h)) ↔ (a * b) ∣ (n + negShift (a * b) n₀) := by
  set s := negShift (a * b) n₀ with hs
  have hsol : (a * b) ∣ (s + n₀) := negShift_add_dvd hpos n₀
  have hn₀s : (n₀ + s) ≡ 0 [MOD a * b] := by
    rw [Nat.modEq_zero_iff_dvd, Nat.add_comm]
    exact hsol
  constructor
  · rintro ⟨hna, hnb⟩
    have hma : n ≡ n₀ [MOD a] :=
      ((Nat.modEq_zero_iff_dvd).mpr hna).trans ((Nat.modEq_zero_iff_dvd).mpr h0a).symm
    have hmb : n ≡ n₀ [MOD b] := by
      have h1 : (n + h) ≡ 0 [MOD b] := (Nat.modEq_zero_iff_dvd).mpr hnb
      have h2 : (n₀ + h) ≡ 0 [MOD b] := (Nat.modEq_zero_iff_dvd).mpr h0b
      exact Nat.ModEq.add_right_cancel' h (h1.trans h2.symm)
    have hm : n ≡ n₀ [MOD a * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hma, hmb⟩
    rw [← Nat.modEq_zero_iff_dvd]
    exact (Nat.ModEq.add_right s hm).trans hn₀s
  · intro hdvd
    have hm : n ≡ n₀ [MOD a * b] := by
      have h1 : (n + s) ≡ 0 [MOD a * b] := (Nat.modEq_zero_iff_dvd).mpr hdvd
      exact Nat.ModEq.add_right_cancel' s (h1.trans hn₀s.symm)
    have hma : n ≡ n₀ [MOD a] := hm.of_dvd ⟨b, rfl⟩
    have hmb : n ≡ n₀ [MOD b] := hm.of_dvd ⟨a, Nat.mul_comm a b⟩
    refine ⟨?_, ?_⟩
    · rw [← Nat.modEq_zero_iff_dvd]
      exact hma.trans ((Nat.modEq_zero_iff_dvd).mpr h0a)
    · rw [← Nat.modEq_zero_iff_dvd]
      exact (Nat.ModEq.add_right h hmb).trans ((Nat.modEq_zero_iff_dvd).mpr h0b)

/-- **The joint count differs from `L/(ab)` by less than one.** -/
theorem abs_card_joint_sub_lt {a b h n₀ : ℕ} (hab : Nat.Coprime a b) (hpos : 0 < a * b)
    (h0a : a ∣ n₀) (h0b : b ∣ (n₀ + h)) (t L : ℕ) :
    |(#{n ∈ Finset.Ioc t (t + L) | a ∣ n ∧ b ∣ (n + h)} : ℝ) - (L : ℝ) / ((a : ℝ) * b)| < 1 := by
  classical
  have hset : #{n ∈ Finset.Ioc t (t + L) | a ∣ n ∧ b ∣ (n + h)}
      = #{n ∈ Finset.Ioc t (t + L) | (a * b) ∣ (n + negShift (a * b) n₀)} := by
    refine congrArg Finset.card (Finset.filter_congr fun n _ => ?_)
    exact joint_iff_dvd_shift hab hpos h0a h0b n
  rw [hset]
  have h := abs_card_filter_dvd_add_shift_sub_lt (a * b) (negShift (a * b) n₀) t L hpos
  have hcast : ((a * b : ℕ) : ℝ) = (a : ℝ) * b := by push_cast; ring
  rwa [hcast] at h

end RHTower.Sieve
