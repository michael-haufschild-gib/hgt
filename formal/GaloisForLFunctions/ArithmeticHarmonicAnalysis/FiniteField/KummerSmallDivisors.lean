import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentGCD
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentPeriod
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResidueExtremal

/-!
# Geometric exponents dividing a plus-one covering degree

For a base at least two, a positive-length geometric sum divides
`q^n+1` only at length one, or at length two with `n` odd. The exact
ramification gcd and strict growth of geometric sums force these two
possibilities.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

private theorem geometric_succ (q a : ℕ) :
    kummerExponent q (a + 1) = kummerExponent q a + q ^ a :=
  Finset.sum_range_succ _ _

private theorem geometric_one (q : ℕ) : kummerExponent q 1 = 1 := by
  simp only [kummerExponent, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, pow_zero, zero_add]

private theorem geometric_two (q : ℕ) : kummerExponent q 2 = q + 1 := by
  rw [show 2 = 1 + 1 from rfl, geometric_succ, geometric_one, pow_one, add_comm]

private theorem geometric_le (q a b : ℕ) (h : a ≤ b) :
    kummerExponent q a ≤ kummerExponent q b := by
  induction b generalizing a with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases hab : a ≤ b
    · exact (ih a hab).trans (by rw [geometric_succ]; omega)
    · have ha : a = b + 1 := by omega
      rw [ha]

private theorem geometric_lt (q a b : ℕ) (hq : 0 < q) (h : a < b) :
    kummerExponent q a < kummerExponent q b := by
  have hpow : 0 < q ^ a := pow_pos hq a
  have hstep : kummerExponent q a < kummerExponent q (a + 1) := by
    rw [geometric_succ]
    omega
  exact hstep.trans_le (geometric_le q (a + 1) b h)

private theorem geometric_injective (q : ℕ) (hq : 0 < q) :
    Function.Injective (kummerExponent q) := by
  intro a b h
  by_cases hab : a < b
  · have hh := geometric_lt q a b hq hab
    omega
  · by_cases hba : b < a
    · have hh := geometric_lt q b a hq hba
      omega
    · omega

private theorem geometric_le_pow (q a : ℕ) (hq : 2 ≤ q) :
    kummerExponent q a ≤ q ^ a := by
  induction a with
  | zero =>
    simp only [kummerExponent, Finset.range_zero, Finset.sum_empty, pow_zero]
    exact Nat.zero_le _
  | succ a ih =>
    rw [geometric_succ, pow_succ]
    calc
      kummerExponent q a + q ^ a ≤ q ^ a + q ^ a := Nat.add_le_add_right ih _
      _ = q ^ a * 2 := by omega
      _ ≤ q ^ a * q := Nat.mul_le_mul_left _ hq

/-- A positive-length geometric branch exponent divides a plus-one covering degree exactly at lengths one and two, with odd covering exponent in the second case. -/
theorem kummerExponent_dvd_cover_iff (q n r : ℕ) (hq : 2 ≤ q) (hn : 0 < n) (hr : 0 < r) :
    kummerExponent q r ∣ q ^ n + 1 ↔ r = 1 ∨ r = 2 ∧ Odd n := by
  constructor
  · intro hd
    have hgcd : Nat.gcd (q ^ n + 1) (kummerExponent q r) = kummerExponent q r :=
      (Nat.gcd_comm _ _).trans (Nat.gcd_eq_left hd)
    by_cases heven : Even (r / Nat.gcd n r)
    · have heq := kummerExponent_gcd_eq_pow_add_one q n r hn heven
      rw [hgcd] at heq
      have hgpos : 0 < Nat.gcd n r := by
        by_contra h
        have hgzero : Nat.gcd n r = 0 := by omega
        have hh := Nat.gcd_dvd_left n r
        rw [hgzero] at hh
        obtain ⟨t, ht⟩ := hh
        rw [zero_mul] at ht
        omega
      have hfac : r = Nat.gcd n r * (r / Nat.gcd n r) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right n r)).symm
      obtain ⟨t, ht⟩ := heven
      have htpos : 0 < t := by
        by_contra h
        have htzero : t = 0 := by omega
        rw [ht, htzero, zero_add, mul_zero] at hfac
        omega
      have hdouble : 2 * Nat.gcd n r ≤ r := by
        have hh := Nat.mul_le_mul_left (Nat.gcd n r) (show 2 ≤ t + t by omega)
        rw [← ht, ← hfac] at hh
        simpa only [Nat.mul_comm (Nat.gcd n r) 2] using hh
      have hg : Nat.gcd n r = 1 := by
        by_contra h
        have hglt : Nat.gcd n r + 1 < r := by omega
        have hlt := geometric_lt q (Nat.gcd n r + 1) r (by omega) hglt
        have hbase := geometric_le q 1 (Nat.gcd n r) hgpos
        rw [geometric_one] at hbase
        rw [geometric_succ, heq] at hlt
        omega
      have hr2 : r = 2 := by
        apply geometric_injective q (by omega)
        rw [heq, hg, pow_one, geometric_two]
      have hnodd := odd_div_gcd_of_even_div_gcd n r hn ⟨t, ht⟩
      rw [hg, Nat.div_one] at hnodd
      exact Or.inr ⟨hr2, hnodd⟩
    · have hd2 := kummerExponent_gcd_dvd_two q n r hn heven
      rw [hgcd] at hd2
      have hupper := Nat.le_of_dvd (Nat.zero_lt_succ 1) hd2
      have hr2 : r < 2 := by
        by_contra h
        have hbound := geometric_le q 2 r (by omega)
        rw [geometric_two] at hbound
        omega
      exact Or.inl (by omega)
  · rintro (rfl | ⟨rfl, hnodd⟩)
    · rw [geometric_one]
      exact one_dvd _
    · rw [geometric_two]
      apply (ZMod.natCast_eq_zero_iff _ (q + 1)).mp
      have hqmod : (q : ZMod (q + 1)) = -1 := by
        have hh := ZMod.natCast_self (q + 1)
        simpa only [Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg] using hh
      simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      rw [hqmod, hnodd.neg_one_pow, neg_add_cancel]

/-- Within one covering exponent, the extremal conductor residue occurs only at lengths zero and one, or length two with odd covering exponent. -/
theorem kummerExponent_extremal_residue_iff (q n r : ℕ) (hq : 2 ≤ q) (hr : r ≤ n + 1) :
    (q ^ (n + 1) + 1 - 1) * kummerExponent q r % (q ^ (n + 1) + 1) =
        q ^ (n + 1) + 1 - Nat.gcd (q ^ (n + 1) + 1) (kummerExponent q r) ↔
      r = 0 ∨ r = 1 ∨ r = 2 ∧ Odd (n + 1) := by
  have hlt : kummerExponent q r < q ^ (n + 1) + 1 :=
    (geometric_le q r (n + 1) hr).trans_lt
      ((geometric_le_pow q (n + 1) hq).trans_lt (Nat.lt_succ_self _))
  rw [last_mul_residue_max_iff_dvd _ _ (Nat.succ_pos _), Nat.mod_eq_of_lt hlt]
  by_cases hrzero : r = 0
  · subst r
    simp only [kummerExponent, Finset.range_zero, Finset.sum_empty, true_or]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hrzero
    have hR : kummerExponent q r ≠ 0 := by
      have hh := geometric_le q 1 r hrpos
      rw [geometric_one] at hh
      omega
    rw [or_iff_right hR, or_iff_right hrzero,
      kummerExponent_dvd_cover_iff q (n + 1) r hq (Nat.succ_pos _) hrpos]

private theorem geometric_high_half_residue (q n t : ℕ) (hq : 2 ≤ q)
    (ht : n + 1 < t) (htop : t < 2 * (n + 1)) :
    kummerExponent q t % (q ^ (n + 1) + 1) ≠ 0 ∧
      ¬ kummerExponent q t % (q ^ (n + 1) + 1) ∣ q ^ (n + 1) + 1 := by
  let v := t - (n + 1)
  have hvpos : 0 < v := by dsimp only [v]; omega
  have hvlt : v < n + 1 := by dsimp only [v]; omega
  have hsplit : t = (n + 1) + v := by dsimp only [v]; omega
  have hsmall := geometric_lt q v (n + 1) (by omega) hvlt
  have hbound : kummerExponent q (n + 1) - kummerExponent q v < q ^ (n + 1) + 1 :=
    (Nat.sub_le _ _).trans_lt
      ((geometric_le_pow q (n + 1) hq).trans_lt (Nat.lt_succ_self _))
  have hres : kummerExponent q t % (q ^ (n + 1) + 1) =
      kummerExponent q (n + 1) - kummerExponent q v := by
    rw [hsplit, kummerExponent_add_length]
    have he : kummerExponent q (n + 1) + q ^ (n + 1) * kummerExponent q v =
        (q ^ (n + 1) + 1) * kummerExponent q v +
          (kummerExponent q (n + 1) - kummerExponent q v) := by
      rw [add_mul, one_mul]
      have hh := Nat.sub_add_cancel hsmall.le
      omega
    rw [he, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hbound]
  have hqdiv : q ∣ kummerExponent q (n + 1) - kummerExponent q v := by
    have hlen : v + (n + 1 - v) = n + 1 := by omega
    have he := kummerExponent_add_length q v (n + 1 - v)
    rw [hlen] at he
    have hdiff : kummerExponent q (n + 1) - kummerExponent q v =
        q ^ v * kummerExponent q (n + 1 - v) := by omega
    rw [hdiff]
    apply dvd_mul_of_dvd_left
    refine ⟨q ^ (v - 1), ?_⟩
    calc
      q ^ v = q ^ (v - 1 + 1) := congrArg (fun j : ℕ => q ^ j) (Nat.sub_add_cancel hvpos).symm
      _ = q * q ^ (v - 1) := by rw [pow_succ, mul_comm]
  refine ⟨by rw [hres]; exact Nat.ne_of_gt (Nat.sub_pos_of_lt hsmall), ?_⟩
  intro hd
  rw [hres] at hd
  have hqN : q ∣ q ^ (n + 1) + 1 := hqdiv.trans hd
  have hqpow : q ∣ q ^ (n + 1) := ⟨q ^ n, by rw [pow_succ, mul_comm]⟩
  have hqone : q ∣ 1 := by
    have h := Nat.dvd_sub hqN hqpow
    simpa only [Nat.add_sub_cancel_left] using h
  have hle := Nat.le_of_dvd (Nat.zero_lt_succ 0) hqone
  omega

/-- At every geometric length, the extremal conductor residue is classified by three possible residues modulo twice the covering exponent. -/
theorem kummerExponent_extremal_residue_period_iff (q n r : ℕ) (hq : 2 ≤ q) :
    (q ^ (n + 1) + 1 - 1) * kummerExponent q r % (q ^ (n + 1) + 1) =
        q ^ (n + 1) + 1 - Nat.gcd (q ^ (n + 1) + 1) (kummerExponent q r) ↔
      r % (2 * (n + 1)) = 0 ∨ r % (2 * (n + 1)) = 1 ∨
        r % (2 * (n + 1)) = 2 ∧ Odd (n + 1) := by
  rw [last_mul_residue_max_iff_dvd _ _ (Nat.succ_pos _), kummerExponent_mod_reduce]
  let t := r % (2 * (n + 1))
  change (kummerExponent q t % (q ^ (n + 1) + 1) = 0 ∨
      kummerExponent q t % (q ^ (n + 1) + 1) ∣ q ^ (n + 1) + 1) ↔
    t = 0 ∨ t = 1 ∨ t = 2 ∧ Odd (n + 1)
  have htop : t < 2 * (n + 1) := Nat.mod_lt _ (by omega)
  by_cases ht : t ≤ n + 1
  · have h := kummerExponent_extremal_residue_iff q n t hq ht
    rw [last_mul_residue_max_iff_dvd _ _ (Nat.succ_pos _)] at h
    exact h
  · have hbad := geometric_high_half_residue q n t hq (by omega) htop
    have htzero : t ≠ 0 := by omega
    have htone : t ≠ 1 := by omega
    have httwo : t ≠ 2 := by omega
    simp only [hbad.1, hbad.2, htzero, htone, httwo, false_or, false_and]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
