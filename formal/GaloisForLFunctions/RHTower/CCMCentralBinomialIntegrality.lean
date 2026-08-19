import GaloisForLFunctions.RHTower.CCMFiniteSemilocalHarmonic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic

/-!
# Central-binomial and semilocal Lambert integrality

This is the finite arithmetic core of Connes--Consani--Moscovici, Lemma 5.5.
The key integer-valued half-binomial polynomial is proved by the Pascal
recurrence used in the paper.  A separate recurrence identifies it with the
central-binomial quotient, yielding the divisibility statement.  That result
then clears every denominator in the literal finite harmonic coefficient
`p_ell(m)` from equation (49).
-/

open scoped Nat BigOperators

namespace RHTower

noncomputable section

/-- The half-integer polynomial used in CCM equation (52). -/
def ccmHalfBinomial (a u : ℕ) : ℚ :=
  (4 : ℚ) ^ u * Ring.choose ((a : ℚ) - 1 / 2) u

private theorem ccm_choose_succ_field_rat (a : ℚ) (n : ℕ) :
    ((n : ℚ) + 1) * Ring.choose a (n + 1) = Ring.choose a n * (a - n) := by
  have key := Ring.descPochhammer_eq_factorial_smul_choose (R := ℚ) a (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul,
      Ring.descPochhammer_eq_factorial_smul_choose (R := ℚ) a n] at key
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
    npow_one, pow_zero, mul_one, nsmul_eq_mul, Nat.factorial_succ] at key
  push_cast at key
  have hfac : (n ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h2 : (n ! : ℚ) * (((n : ℚ) + 1) * Ring.choose a (n + 1)) =
      (n ! : ℚ) * (Ring.choose a n * (a - n)) := by
    linear_combination -key
  exact mul_left_cancel₀ hfac h2

private theorem ccm_choose_neg_half_rat (n : ℕ) :
    Ring.choose (-1 / 2 : ℚ) n = (-1) ^ n * (Nat.centralBinom n : ℚ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrec := ccm_choose_succ_field_rat (-1 / 2 : ℚ) n
    rw [ih] at hrec
    have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
    have hcb : ((n : ℚ) + 1) * (Nat.centralBinom (n + 1) : ℚ) =
        2 * (2 * (n : ℚ) + 1) * (Nat.centralBinom n : ℚ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hchoose : Ring.choose (-1 / 2 : ℚ) (n + 1) =
        ((-1) ^ n * (Nat.centralBinom n : ℚ) / 4 ^ n) * (-1 / 2 - (n : ℚ)) /
          ((n : ℚ) + 1) := by
      rw [eq_div_iff hpos]
      linear_combination hrec
    have hkey : (Nat.centralBinom n : ℚ) * (-1 / 2 - (n : ℚ)) / ((n : ℚ) + 1) =
        -(Nat.centralBinom (n + 1) : ℚ) / 4 := by
      rw [div_eq_div_iff hpos (by norm_num : (4 : ℚ) ≠ 0)]
      linear_combination hcb
    rw [hchoose, pow_succ (-1 : ℚ), pow_succ (4 : ℚ),
      show ((-1 : ℚ) ^ n * (Nat.centralBinom n : ℚ) / 4 ^ n) *
          (-1 / 2 - (n : ℚ)) / ((n : ℚ) + 1) =
          ((-1 : ℚ) ^ n / 4 ^ n) *
            ((Nat.centralBinom n : ℚ) * (-1 / 2 - (n : ℚ)) / ((n : ℚ) + 1)) by ring,
      hkey]
    have h4 : (4 : ℚ) ^ n ≠ 0 := by positivity
    field_simp

private theorem ccmHalfBinomial_zero (u : ℕ) :
    ccmHalfBinomial 0 u = (-1 : ℚ) ^ u * (Nat.centralBinom u : ℚ) := by
  unfold ccmHalfBinomial
  norm_num
  rw [show (-(1 / 2) : ℚ) = (-1 / 2 : ℚ) by ring]
  rw [ccm_choose_neg_half_rat]
  have h4 : (4 : ℚ) ^ u ≠ 0 := by positivity
  field_simp

private theorem ccmHalfBinomial_succ_succ (a u : ℕ) :
    ccmHalfBinomial (a + 1) (u + 1) =
      ccmHalfBinomial a (u + 1) + 4 * ccmHalfBinomial a u := by
  unfold ccmHalfBinomial
  rw [show ((a + 1 : ℕ) : ℚ) - 1 / 2 = ((a : ℚ) - 1 / 2) + 1 by
      push_cast; ring,
    Ring.choose_succ_succ]
  ring

/-- The half-binomial expression in CCM equation (52) is an integer. -/
theorem ccmHalfBinomial_integral (a u : ℕ) :
    CCMRationalIntegral (ccmHalfBinomial a u) := by
  induction a generalizing u with
  | zero =>
      refine ⟨(-1 : ℤ) ^ u * (Nat.centralBinom u : ℤ), ?_⟩
      rw [ccmHalfBinomial_zero]
      norm_cast
  | succ a ih =>
      cases u with
      | zero =>
          refine ⟨1, ?_⟩
          simp [ccmHalfBinomial]
      | succ u =>
          obtain ⟨x, hx⟩ := ih (u + 1)
          obtain ⟨y, hy⟩ := ih u
          refine ⟨x + 4 * y, ?_⟩
          rw [ccmHalfBinomial_succ_succ, hx, hy]
          norm_num

/-- The rational quotient in CCM Lemma 5.5(i). -/
def ccmCentralRatio (a k : ℕ) : ℚ :=
  (Nat.centralBinom a : ℚ) * (a.choose k : ℚ) / (Nat.centralBinom k : ℚ)

private theorem ccmCentralRatio_zero (a : ℕ) :
    ccmCentralRatio a 0 = Nat.centralBinom a := by
  simp [ccmCentralRatio]

private theorem ccmCentralRatio_succ_succ (a k : ℕ) (hk : k ≤ a) :
    ccmCentralRatio (a + 1) (k + 1) =
      ccmCentralRatio a k + 4 * ccmCentralRatio a (k + 1) := by
  unfold ccmCentralRatio
  have hca : ((a : ℚ) + 1) * (Nat.centralBinom (a + 1) : ℚ) =
      2 * (2 * (a : ℚ) + 1) * (Nat.centralBinom a : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ a
  have hck : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) =
      2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hpascal : ((a + 1).choose (k + 1) : ℚ) = a.choose k + a.choose (k + 1) := by
    exact_mod_cast Nat.choose_succ_succ a k
  have hnext : (a.choose (k + 1) : ℚ) * ((k : ℚ) + 1) =
      (a.choose k : ℚ) * ((a : ℚ) - k) := by
    exact_mod_cast Nat.choose_succ_right_eq a k
  have hca0 : (Nat.centralBinom a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos a).ne'
  have hck0 : (Nat.centralBinom k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos k).ne'
  have hck10 : (Nat.centralBinom (k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos (k + 1)).ne'
  have ha1 : (a : ℚ) + 1 ≠ 0 := by positivity
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  rw [hpascal]
  field_simp
  have hinner :
      (2 * (a : ℚ) + 1) * ((a.choose k : ℚ) + a.choose (k + 1 : ℕ)) *
          ((k : ℚ) + 1) =
        (a.choose k : ℚ) * (2 * (k : ℚ) + 1) * ((a : ℚ) + 1) +
          2 * (a.choose (k + 1 : ℕ) : ℚ) * ((a : ℚ) + 1) * ((k : ℚ) + 1) := by
    calc
      (2 * (a : ℚ) + 1) * ((a.choose k : ℚ) + a.choose (k + 1 : ℕ)) *
          ((k : ℚ) + 1) =
          (2 * (a : ℚ) + 1) *
            ((a.choose k : ℚ) * ((k : ℚ) + 1) +
              (a.choose (k + 1 : ℕ) : ℚ) * ((k : ℚ) + 1)) := by ring
      _ = (2 * (a : ℚ) + 1) *
            ((a.choose k : ℚ) * ((k : ℚ) + 1) +
              (a.choose k : ℚ) * ((a : ℚ) - k)) := by rw [hnext]
      _ = (a.choose k : ℚ) * (2 * (a : ℚ) + 1) * ((a : ℚ) + 1) := by ring
      _ = (a.choose k : ℚ) * (2 * (k : ℚ) + 1) * ((a : ℚ) + 1) +
          2 * (a.choose (k + 1 : ℕ) : ℚ) * ((a : ℚ) + 1) * ((k : ℚ) + 1) := by
            rw [show 2 * (a.choose (k + 1 : ℕ) : ℚ) * ((a : ℚ) + 1) *
                ((k : ℚ) + 1) =
                2 * ((a.choose (k + 1 : ℕ) : ℚ) * ((k : ℚ) + 1)) *
                  ((a : ℚ) + 1) by ring, hnext]
            ring
  apply (mul_left_cancel₀ (mul_ne_zero ha1 hk1))
  calc
    (((a : ℚ) + 1) * ((k : ℚ) + 1) *
        ((Nat.centralBinom (a + 1) : ℚ) *
          ((a.choose k : ℚ) + a.choose (k + 1 : ℕ)) * (Nat.centralBinom k : ℚ))) =
        (((a : ℚ) + 1) * (Nat.centralBinom (a + 1) : ℚ)) *
          ((a.choose k : ℚ) + a.choose (k + 1 : ℕ)) *
            (Nat.centralBinom k : ℚ) * ((k : ℚ) + 1) := by ring
    _ = 2 * (2 * (a : ℚ) + 1) * (Nat.centralBinom a : ℚ) *
          ((a.choose k : ℚ) + a.choose (k + 1 : ℕ)) *
            (Nat.centralBinom k : ℚ) * ((k : ℚ) + 1) := by rw [hca]
    _ = 2 * (Nat.centralBinom a : ℚ) * (Nat.centralBinom k : ℚ) *
          ((2 * (a : ℚ) + 1) * ((a.choose k : ℚ) + a.choose (k + 1 : ℕ)) *
            ((k : ℚ) + 1)) := by ring
    _ = 2 * (Nat.centralBinom a : ℚ) * (Nat.centralBinom k : ℚ) *
          ((a.choose k : ℚ) * (2 * (k : ℚ) + 1) * ((a : ℚ) + 1) +
            2 * (a.choose (k + 1 : ℕ) : ℚ) * ((a : ℚ) + 1) * ((k : ℚ) + 1)) := by
              rw [hinner]
    _ = (Nat.centralBinom a : ℚ) * ((a : ℚ) + 1) *
          ((a.choose k : ℚ) *
              (2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ)) +
            4 * (a.choose (k + 1 : ℕ) : ℚ) * ((k : ℚ) + 1) *
              (Nat.centralBinom k : ℚ)) := by ring
    _ = (Nat.centralBinom a : ℚ) * ((a : ℚ) + 1) *
          ((a.choose k : ℚ) * (((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ)) +
            4 * (a.choose (k + 1 : ℕ) : ℚ) * ((k : ℚ) + 1) *
              (Nat.centralBinom k : ℚ)) := by rw [hck]
    _ = ((a : ℚ) + 1) * ((k : ℚ) + 1) *
          ((Nat.centralBinom a : ℚ) *
            ((a.choose k : ℚ) * (Nat.centralBinom (k + 1) : ℚ) +
              (a.choose (k + 1 : ℕ) : ℚ) * (Nat.centralBinom k : ℚ) * 4)) := by ring

private theorem ccmHalfBinomial_diag (a : ℕ) :
    ccmHalfBinomial a a = Nat.centralBinom a := by
  unfold ccmHalfBinomial
  have hneg := Ring.choose_neg (R := ℚ) (1 / 2 : ℚ) a
  have htop : (1 / 2 : ℚ) + a - 1 = (a : ℚ) - 1 / 2 := by ring
  rw [htop] at hneg
  have hneg' : Ring.choose (-1 / 2 : ℚ) a =
      (-1 : ℚ) ^ a * Ring.choose ((a : ℚ) - 1 / 2) a := by
    calc
      Ring.choose (-1 / 2 : ℚ) a = (a : ℤ).negOnePow •
          Ring.choose ((a : ℚ) - 1 / 2) a := by
            rw [show (-1 / 2 : ℚ) = -(1 / 2 : ℚ) by ring]
            exact hneg
      _ = (-1 : ℚ) ^ a * Ring.choose ((a : ℚ) - 1 / 2) a := by
        change (((a : ℤ).negOnePow : ℚ) * Ring.choose ((a : ℚ) - 1 / 2) a) = _
        rw [Int.cast_negOnePow_natCast]
  have hsign : (-1 : ℚ) ^ a * (-1 : ℚ) ^ a = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨a, by ring⟩
  have hsolve : Ring.choose ((a : ℚ) - 1 / 2) a =
      (-1 : ℚ) ^ a * Ring.choose (-1 / 2 : ℚ) a := by
    calc
      Ring.choose ((a : ℚ) - 1 / 2) a =
          1 * Ring.choose ((a : ℚ) - 1 / 2) a := by ring
      _ = (-1 : ℚ) ^ a * ((-1 : ℚ) ^ a *
          Ring.choose ((a : ℚ) - 1 / 2) a) := by
            rw [← mul_assoc, hsign, one_mul]
      _ = (-1 : ℚ) ^ a * Ring.choose (-1 / 2 : ℚ) a := by rw [← hneg']
  rw [hsolve, ccm_choose_neg_half_rat]
  have h4 : (4 : ℚ) ^ a ≠ 0 := by positivity
  field_simp
  rw [pow_two, hsign, one_mul]

private theorem ccmCentralRatio_eq_halfBinomial (a k : ℕ) (hk : k ≤ a) :
    ccmCentralRatio a k = ccmHalfBinomial a (a - k) := by
  induction a generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      rw [ccmCentralRatio_zero, Nat.sub_self, ccmHalfBinomial_diag]
  | succ a ih =>
      cases k with
      | zero =>
          rw [ccmCentralRatio_zero, Nat.sub_zero, ccmHalfBinomial_diag]
      | succ k =>
          have hka : k ≤ a := by omega
          by_cases hEq : k = a
          · subst k
            have hne : (Nat.centralBinom (a + 1) : ℚ) ≠ 0 := by
              exact_mod_cast (Nat.centralBinom_pos (a + 1)).ne'
            simp [ccmCentralRatio, ccmHalfBinomial, hne]
          · have hlt : k < a := lt_of_le_of_ne hka hEq
            have hpos : 0 < a - k := Nat.sub_pos_of_lt hlt
            have hsub : (a + 1) - (k + 1) = a - k := by omega
            have hsub' : a - (k + 1) = a - k - 1 := by omega
            rw [ccmCentralRatio_succ_succ a k hka, ih k hka,
              ih (k + 1) (Nat.succ_le_iff.mpr hlt), hsub, hsub']
            simpa only [Nat.sub_add_cancel hpos] using
              (ccmHalfBinomial_succ_succ a (a - k - 1)).symm

/-- CCM Lemma 5.5(i): the central binomial denominator divides the indicated
finite product. -/
theorem ccm_centralBinom_dvd_mul_choose (a k : ℕ) (hk : k ≤ a) :
    Nat.centralBinom k ∣ Nat.centralBinom a * a.choose k := by
  obtain ⟨z, hz⟩ := ccmHalfBinomial_integral a (a - k)
  rw [← ccmCentralRatio_eq_halfBinomial a k hk] at hz
  apply Int.natCast_dvd_natCast.mp
  refine ⟨z, ?_⟩
  have hden : (Nat.centralBinom k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos k).ne'
  have hmul := (div_eq_iff hden).mp hz
  have hmulInt : (Nat.centralBinom a * a.choose k : ℤ) =
      z * (Nat.centralBinom k : ℤ) := by
    exact_mod_cast hmul
  simpa [mul_comm] using hmulInt

private theorem ccmFiniteSemilocalHarmonicTerm_scaled_integral
    (ell m k : ℕ) :
    CCMRationalIntegral
      ((Nat.centralBinom ell : ℚ) * ccmFiniteSemilocalHarmonicTerm ell m k) := by
  by_cases hk : k ≤ ell
  · obtain ⟨q, hq⟩ :=
      exists_eq_mul_left_of_dvd (ccm_centralBinom_dvd_mul_choose ell k hk)
    refine ⟨(2 : ℤ) ^ (3 * k) * (m.choose k : ℤ) * q, ?_⟩
    unfold ccmFiniteSemilocalHarmonicTerm
    have hden : (Nat.centralBinom k : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.centralBinom_pos k).ne'
    field_simp
    push_cast
    have hqQ : (Nat.centralBinom ell : ℚ) * (ell.choose k : ℚ) =
        (q : ℚ) * (Nat.centralBinom k : ℚ) := by
      exact_mod_cast hq
    calc
      (Nat.centralBinom ell : ℚ) * (2 : ℚ) ^ (3 * k) * (m.choose k : ℚ) *
          (ell.choose k : ℚ) =
          (2 : ℚ) ^ (3 * k) * (m.choose k : ℚ) *
            ((Nat.centralBinom ell : ℚ) * (ell.choose k : ℚ)) := by ring
      _ = (2 : ℚ) ^ (3 * k) * (m.choose k : ℚ) *
            ((q : ℚ) * (Nat.centralBinom k : ℚ)) := by rw [hqQ]
      _ = (Nat.centralBinom k : ℚ) *
            ((2 : ℚ) ^ (3 * k) * (m.choose k : ℚ) * (q : ℚ)) := by ring
  · refine ⟨0, ?_⟩
    simp [ccmFiniteSemilocalHarmonicTerm, Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)]

private theorem CCMRationalIntegral_zero : CCMRationalIntegral 0 := ⟨0, rfl⟩

private theorem CCMRationalIntegral_add {x y : ℚ}
    (hx : CCMRationalIntegral x) (hy : CCMRationalIntegral y) :
    CCMRationalIntegral (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [ha, hb]
  norm_num

/-- CCM Lemma 5.5(ii): the scaled finite harmonic coefficient is integral. -/
theorem ccmFiniteSemilocalHarmonic_scaled_integral (ell m : ℕ) :
    CCMRationalIntegral
      ((Nat.centralBinom ell : ℚ) * ccmFiniteSemilocalHarmonic ell m) := by
  unfold ccmFiniteSemilocalHarmonic
  rw [Finset.mul_sum]
  induction Finset.range (ell + 1) using Finset.induction_on with
  | empty => exact CCMRationalIntegral_zero
  | insert k s hks ih =>
      rw [Finset.sum_insert hks]
      exact CCMRationalIntegral_add
        (ccmFiniteSemilocalHarmonicTerm_scaled_integral ell m k) ih

/-- CCM Lemma 5.5(iii): the symmetric quadratic coefficient is integral. -/
theorem ccmFiniteSemilocalHarmonic_sigma_integral (ell m : ℕ) :
    CCMRationalIntegral
      ((Nat.centralBinom ell : ℚ) * (Nat.centralBinom m : ℚ) *
        ccmFiniteSemilocalHarmonic ell m ^ 2) :=
  ccmFiniteSemilocalHarmonic_sigma_integral_of_scaled_integral
    ccmFiniteSemilocalHarmonic_scaled_integral ell m

end

end RHTower
