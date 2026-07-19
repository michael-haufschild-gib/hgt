import GaloisForLFunctions.RHTower.ScaleCovariantBernsteinPurityJet
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Divided-power completion and uniform positive-chamber stability

The signed divided-power transform turns the scale-covariant Bernstein purity polynomial into
an exact square.  The positive constant coefficient selects its unique root.  The natural
degree-adapted tail norm then gives a stability constant independent of the Bernstein degree.
-/

open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

theorem coeff_bernsteinPolynomial_closed (N k a : ℕ) :
    (bernsteinPolynomial ℝ N k).coeff a =
      if k ≤ a then (-1 : ℝ) ^ (a - k) * N.choose a * a.choose k else 0 := by
  rw [bernsteinPolynomial, mul_assoc]
  change (C (N.choose k : ℝ) * (X ^ k * (1 - X) ^ (N - k))).coeff a = _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs with hka
  · rw [show ((1 - X : Polynomial ℝ) ^ (N - k)).coeff (a - k) =
        (-1 : ℝ) ^ (a - k) * (N - k).choose (a - k) by
      simpa only [Nat.choose_zero_right, Nat.cast_one, one_mul] using
        (show ((1 - X : Polynomial ℝ) ^ (N - k)).coeff (a - k) =
            (-1 : ℝ) ^ (a - k) * (N - k).choose (a - k) by
          simpa [bernsteinPolynomial] using
            coeff_bernsteinPolynomial_zero (N - k) (a - k))]
    by_cases haN : a ≤ N
    · have hchoose := Nat.choose_mul (n := N) (k := a) (s := k) hka
      have hchooseR : (N.choose a : ℝ) * a.choose k =
          N.choose k * (N - k).choose (a - k) := by exact_mod_cast hchoose
      calc
        (N.choose k : ℝ) *
            ((-1 : ℝ) ^ (a - k) * (N - k).choose (a - k)) =
            (-1 : ℝ) ^ (a - k) *
              ((N.choose k : ℝ) * (N - k).choose (a - k)) := by ring
        _ = (-1 : ℝ) ^ (a - k) * ((N.choose a : ℝ) * a.choose k) := by
          rw [hchooseR]
        _ = _ := by ring
    · have hNa : N < a := Nat.lt_of_not_ge haN
      by_cases hkN : k ≤ N
      · have hNka : N - k < a - k := Nat.sub_lt_sub_right hkN hNa
        rw [Nat.choose_eq_zero_of_lt hNa, Nat.choose_eq_zero_of_lt hNka]
        simp
      · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkN),
          Nat.choose_eq_zero_of_lt hNa]
        simp
  · simp

theorem sum_choose_mul_choose_eq_choose_add (a b N : ℕ) (hb : b ≤ N) :
    ∑ k ∈ Finset.range (N + 1), a.choose k * b.choose k = (a + b).choose a := by
  have hsub : Finset.range (b + 1) ⊆ Finset.range (N + 1) :=
    Finset.range_mono (Nat.succ_le_succ hb)
  calc
    ∑ k ∈ Finset.range (N + 1), a.choose k * b.choose k =
        ∑ k ∈ Finset.range (b + 1), a.choose k * b.choose k := by
      symm
      apply Finset.sum_subset hsub
      intro k hkN hknb
      have hbk : b < k := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff, not_le] using hknb
      rw [Nat.choose_eq_zero_of_lt hbk, mul_zero]
    _ = ∑ k ∈ Finset.range (b + 1), a.choose k * b.choose (b - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkb : k ≤ b := Finset.mem_range_succ_iff.mp hk
      rw [Nat.choose_symm hkb]
    _ = (a + b).choose b := by
      rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = (a + b).choose a := Nat.choose_symm_add.symm

theorem coeff_bernsteinScalePurityPolynomial_closed (m : ℕ → ℝ) (N r : ℕ) :
    (bernsteinScalePurityPolynomial m N).coeff r =
      (-1 : ℝ) ^ r *
        ∑ ab ∈ Finset.antidiagonal r,
          (N.choose ab.1 : ℝ) * N.choose ab.2 * r.choose ab.1 *
            m ab.1 * m ab.2 := by
  rw [coeff_bernsteinScalePurityPolynomial]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  have hrab : ab.1 + ab.2 = r := Finset.mem_antidiagonal.mp hab
  by_cases haN : ab.1 ≤ N
  · by_cases hbN : ab.2 ≤ N
    · calc
        ∑ k ∈ Finset.range (N + 1),
            bernsteinPurityCoefficientKernel N k ab.1 ab.2 * m ab.1 * m ab.2 =
            ((-1 : ℝ) ^ r * (N.choose ab.1 : ℝ) * N.choose ab.2 *
              m ab.1 * m ab.2) *
              ∑ k ∈ Finset.range (N + 1),
                (ab.1.choose k : ℝ) * ab.2.choose k := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k hk
                rw [bernsteinPurityCoefficientKernel,
                  coeff_bernsteinPolynomial_closed, coeff_bernsteinPolynomial_closed]
                by_cases hka : k ≤ ab.1
                · by_cases hkb : k ≤ ab.2
                  · simp only [if_pos hka, if_pos hkb]
                    have hexp : (ab.1 - k) + (ab.2 - k) + 2 * k = r := by omega
                    have hsign :
                        (-1 : ℝ) ^ (ab.1 - k) * (-1 : ℝ) ^ (ab.2 - k) =
                          (-1 : ℝ) ^ r := by
                      calc
                        (-1 : ℝ) ^ (ab.1 - k) * (-1 : ℝ) ^ (ab.2 - k) =
                            (-1 : ℝ) ^ ((ab.1 - k) + (ab.2 - k)) := by
                              rw [pow_add]
                        _ = (-1 : ℝ) ^ ((ab.1 - k) + (ab.2 - k)) *
                            (-1 : ℝ) ^ (2 * k) := by
                              rw [pow_mul]
                              norm_num
                        _ = (-1 : ℝ) ^ r := by rw [← pow_add, hexp]
                    calc
                      (-1 : ℝ) ^ (ab.1 - k) * (N.choose ab.1 : ℝ) *
                            ab.1.choose k *
                            ((-1 : ℝ) ^ (ab.2 - k) * N.choose ab.2 *
                              ab.2.choose k) * m ab.1 * m ab.2 =
                          ((-1 : ℝ) ^ (ab.1 - k) *
                            (-1 : ℝ) ^ (ab.2 - k)) *
                            ((N.choose ab.1 : ℝ) * N.choose ab.2 *
                              m ab.1 * m ab.2) *
                            ((ab.1.choose k : ℝ) * ab.2.choose k) := by ring
                      _ = _ := by rw [hsign]; ring
                  · have hlt : ab.2 < k := Nat.lt_of_not_ge hkb
                    simp [hka, hkb, Nat.choose_eq_zero_of_lt hlt]
                · have hlt : ab.1 < k := Nat.lt_of_not_ge hka
                  simp [hka, Nat.choose_eq_zero_of_lt hlt]
        _ = ((-1 : ℝ) ^ r * (N.choose ab.1 : ℝ) * N.choose ab.2 *
              m ab.1 * m ab.2) * (ab.1 + ab.2).choose ab.1 := by
                have hsumR :
                    (∑ k ∈ Finset.range (N + 1),
                      (ab.1.choose k : ℝ) * ab.2.choose k) =
                      ((ab.1 + ab.2).choose ab.1 : ℝ) := by
                  exact_mod_cast sum_choose_mul_choose_eq_choose_add ab.1 ab.2 N hbN
                rw [hsumR]
        _ = (-1 : ℝ) ^ r *
            ((N.choose ab.1 : ℝ) * N.choose ab.2 * r.choose ab.1 *
              m ab.1 * m ab.2) := by rw [hrab]; ring
    · have hNb : N < ab.2 := Nat.lt_of_not_ge hbN
      simp [bernsteinPurityCoefficientKernel, coeff_bernsteinPolynomial_closed,
        Nat.choose_eq_zero_of_lt hNb]
  · have hNa : N < ab.1 := Nat.lt_of_not_ge haN
    simp [bernsteinPurityCoefficientKernel, coeff_bernsteinPolynomial_closed,
      Nat.choose_eq_zero_of_lt hNa]

/-- The unique pointed divided-power root underlying a degree-`N` purity polynomial. -/
def bernsteinDividedPowerRoot (m : ℕ → ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ r ∈ Finset.range (N + 1),
    Polynomial.monomial r ((N.choose r : ℝ) * m r / r.factorial)

@[simp] theorem coeff_bernsteinDividedPowerRoot (m : ℕ → ℝ) (N r : ℕ) :
    (bernsteinDividedPowerRoot m N).coeff r =
      if r ≤ N then (N.choose r : ℝ) * m r / r.factorial else 0 := by
  classical
  rw [bernsteinDividedPowerRoot, Polynomial.finsetSum_coeff]
  by_cases hr : r ≤ N
  · have hmem : r ∈ Finset.range (N + 1) := Finset.mem_range_succ_iff.mpr hr
    rw [if_pos hr]
    rw [Finset.sum_eq_single r]
    · simp
    · intro b hb hbr
      exact Polynomial.coeff_monomial_of_ne _ hbr.symm
    · exact fun h => (h hmem).elim
  · rw [Finset.sum_eq_zero]
    · rw [if_neg hr]
    · intro b hb
      have hbr : b ≠ r := by
        intro h
        subst h
        exact hr (Finset.mem_range_succ_iff.mp hb)
      simp [Polynomial.coeff_monomial, hbr]

/-- Exact signed divided-power square factorization of Bernstein purity. -/
theorem bernsteinScalePurityPolynomial_coeff_dividedPower_square (m : ℕ → ℝ) (N r : ℕ) :
    (bernsteinScalePurityPolynomial m N).coeff r =
      (-1 : ℝ) ^ r * (r.factorial : ℝ) *
        ((bernsteinDividedPowerRoot m N) ^ 2).coeff r := by
  rw [coeff_bernsteinScalePurityPolynomial_closed, pow_two, Polynomial.coeff_mul]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  have hrab : ab.1 + ab.2 = r := Finset.mem_antidiagonal.mp hab
  rw [coeff_bernsteinDividedPowerRoot, coeff_bernsteinDividedPowerRoot]
  by_cases haN : ab.1 ≤ N
  · by_cases hbN : ab.2 ≤ N
    · simp only [if_pos haN, if_pos hbN]
      have hfactNat := Nat.add_choose_mul_factorial_mul_factorial ab.2 ab.1
      have hfactR :
          (r.choose ab.1 : ℝ) * ab.1.factorial * ab.2.factorial = r.factorial := by
        rw [← hrab]
        norm_cast
        simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hfactNat
      have hfa : (ab.1.factorial : ℝ) ≠ 0 := by positivity
      have hfb : (ab.2.factorial : ℝ) ≠ 0 := by positivity
      have hden : (ab.1.factorial : ℝ) * ab.2.factorial ≠ 0 := mul_ne_zero hfa hfb
      have hratio : (r.choose ab.1 : ℝ) =
          (r.factorial : ℝ) / ((ab.1.factorial : ℝ) * ab.2.factorial) := by
        apply (eq_div_iff hden).2
        simpa only [mul_assoc] using hfactR
      rw [hratio]
      field_simp [hfa, hfb]
    · have hNb : N < ab.2 := Nat.lt_of_not_ge hbN
      simp [hbN, Nat.choose_eq_zero_of_lt hNb]
  · have hNa : N < ab.1 := Nat.lt_of_not_ge haN
    simp [haN, Nat.choose_eq_zero_of_lt hNa]

/-- The positive constant term chooses a unique square root and hence a unique moment prefix. -/
theorem moment_prefix_eq_of_bernsteinDividedPowerRoot_sq_eq
    {m m' : ℕ → ℝ} {N : ℕ}
    (hm0 : 0 < m 0) (hm0' : 0 < m' 0)
    (hsq : (bernsteinDividedPowerRoot m N) ^ 2 =
      (bernsteinDividedPowerRoot m' N) ^ 2) :
    ∀ r ≤ N, m r = m' r := by
  have hprod :
      (bernsteinDividedPowerRoot m N - bernsteinDividedPowerRoot m' N) *
        (bernsteinDividedPowerRoot m N + bernsteinDividedPowerRoot m' N) = 0 := by
    calc
      (bernsteinDividedPowerRoot m N - bernsteinDividedPowerRoot m' N) *
          (bernsteinDividedPowerRoot m N + bernsteinDividedPowerRoot m' N) =
          (bernsteinDividedPowerRoot m N) ^ 2 -
            (bernsteinDividedPowerRoot m' N) ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  have hroot : bernsteinDividedPowerRoot m N = bernsteinDividedPowerRoot m' N := by
    rcases mul_eq_zero.mp hprod with hminus | hplus
    · exact sub_eq_zero.mp hminus
    · exfalso
      have hc := congrArg (fun p : Polynomial ℝ => p.coeff 0) hplus
      simp only [Polynomial.coeff_add, coeff_bernsteinDividedPowerRoot, zero_le,
        if_pos, Nat.choose_zero_right, Nat.cast_one, Nat.factorial_zero,
        Nat.cast_one, div_one, one_mul, Polynomial.coeff_zero] at hc
      nlinarith
  intro r hr
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff r) hroot
  simp only [coeff_bernsteinDividedPowerRoot, if_pos hr] at hc
  have hchooseNat : 0 < N.choose r := Nat.choose_pos hr
  have hchoose : (N.choose r : ℝ) ≠ 0 := by
    exact_mod_cast hchooseNat.ne'
  have hfact : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hfact] at hc
  exact hc

/-- Exact analytic quotient: a pointed purity polynomial is the same datum as its moment prefix. -/
theorem bernsteinScalePurityPolynomial_eq_iff_moment_prefix_eq
    {m m' : ℕ → ℝ} {N : ℕ} (hm0 : 0 < m 0) (hm0' : 0 < m' 0) :
    bernsteinScalePurityPolynomial m N = bernsteinScalePurityPolynomial m' N ↔
      ∀ r ≤ N, m r = m' r := by
  constructor
  · exact bernsteinScalePurityPolynomial_injectiveOn_pointed hm0 hm0'
  · intro hprefix
    have hroot : bernsteinDividedPowerRoot m N = bernsteinDividedPowerRoot m' N := by
      ext r
      rw [coeff_bernsteinDividedPowerRoot, coeff_bernsteinDividedPowerRoot]
      by_cases hr : r ≤ N
      · simp only [if_pos hr]
        rw [hprefix r hr]
      · simp only [if_neg hr]
    ext r
    rw [bernsteinScalePurityPolynomial_coeff_dividedPower_square,
      bernsteinScalePurityPolynomial_coeff_dividedPower_square, hroot]

/-- The divided-power square root evaluated in its natural scale coordinate. -/
def bernsteinDividedPowerChart (m : ℕ → ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (N + 1),
    (N.choose r : ℝ) * m r * T ^ r / r.factorial

theorem bernsteinDividedPowerChart_eq_eval (m : ℕ → ℝ) (N : ℕ) (T : ℝ) :
    bernsteinDividedPowerChart m N T = (bernsteinDividedPowerRoot m N).eval T := by
  rw [bernsteinDividedPowerChart, bernsteinDividedPowerRoot, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- The exact weighted tail norm adapted to the degree-`N` divided-power chart. -/
def bernsteinDividedPowerTailNorm (m : ℕ → ℝ) (N : ℕ) (tau : ℝ) : ℝ :=
  ∑ r ∈ Finset.range N,
    (N.choose (r + 1) : ℝ) * |m (r + 1)| * tau ^ (r + 1) / (r + 1).factorial

theorem bernsteinDividedPowerChart_sub_mass_le_tailNorm
    (m : ℕ → ℝ) (N : ℕ) {T tau : ℝ}
    (hT : |T| ≤ tau) :
    |bernsteinDividedPowerChart m N T - m 0| ≤
      bernsteinDividedPowerTailNorm m N tau := by
  rw [bernsteinDividedPowerChart, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, mul_one, div_one]
  simp only [one_mul, add_sub_cancel_right]
  calc
    |∑ r ∈ Finset.range N,
        (N.choose (r + 1) : ℝ) * m (r + 1) * T ^ (r + 1) /
          (r + 1).factorial| ≤
        ∑ r ∈ Finset.range N,
          |(N.choose (r + 1) : ℝ) * m (r + 1) * T ^ (r + 1) /
            (r + 1).factorial| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ bernsteinDividedPowerTailNorm m N tau := by
      rw [bernsteinDividedPowerTailNorm]
      apply Finset.sum_le_sum
      intro r hr
      have hchoose0 : 0 ≤ (N.choose (r + 1) : ℝ) := by positivity
      have hfact0 : 0 ≤ ((r + 1).factorial : ℝ) := by positivity
      rw [abs_div, abs_mul, abs_mul, abs_pow, abs_of_nonneg hchoose0,
        abs_of_nonneg hfact0]
      have hpow : |T| ^ (r + 1) ≤ tau ^ (r + 1) := by
        exact pow_le_pow_left₀ (abs_nonneg T) hT _
      gcongr

/-- Positive square-root inversion is uniformly stable on every pointed tail chamber. -/
theorem positive_squareRoot_chamber_stability
    {F G m0 m0' mu theta : ℝ}
    (hmu : 0 < mu) (htheta1 : theta < 1)
    (hm0 : mu ≤ m0) (hm0' : mu ≤ m0')
    (hF : |F - m0| ≤ theta * mu) (hG : |G - m0'| ≤ theta * mu) :
    |F - G| ≤ |F ^ 2 - G ^ 2| / (2 * (1 - theta) * mu) := by
  have hF_lower : (1 - theta) * mu ≤ F := by
    have h := neg_abs_le (F - m0)
    nlinarith
  have hG_lower : (1 - theta) * mu ≤ G := by
    have h := neg_abs_le (G - m0')
    nlinarith
  have hden : 0 < 2 * (1 - theta) * mu := by positivity
  have hsum : 2 * (1 - theta) * mu ≤ |F + G| := by
    rw [abs_of_pos]
    · nlinarith
    · nlinarith
  rw [show F ^ 2 - G ^ 2 = (F - G) * (F + G) by ring, abs_mul]
  rw [le_div_iff₀ hden]
  exact mul_le_mul_of_nonneg_left hsum (abs_nonneg (F - G))

/-- Uniform chart stability in the exact degree-adapted weighted tail norm. -/
theorem bernsteinDividedPowerChart_stability
    (m m' : ℕ → ℝ) (N : ℕ) {T tau mu theta : ℝ}
    (hmu : 0 < mu) (htheta1 : theta < 1)
    (hm0 : mu ≤ m 0) (hm0' : mu ≤ m' 0)
    (hT : |T| ≤ tau)
    (hmTail : bernsteinDividedPowerTailNorm m N tau ≤ theta * mu)
    (hm'Tail : bernsteinDividedPowerTailNorm m' N tau ≤ theta * mu) :
    |bernsteinDividedPowerChart m N T - bernsteinDividedPowerChart m' N T| ≤
      |(bernsteinDividedPowerChart m N T) ^ 2 -
        (bernsteinDividedPowerChart m' N T) ^ 2| / (2 * (1 - theta) * mu) := by
  apply positive_squareRoot_chamber_stability hmu htheta1 hm0 hm0'
  · exact (bernsteinDividedPowerChart_sub_mass_le_tailNorm m N hT).trans hmTail
  · exact (bernsteinDividedPowerChart_sub_mass_le_tailNorm m' N hT).trans hm'Tail

end

end RHTower
