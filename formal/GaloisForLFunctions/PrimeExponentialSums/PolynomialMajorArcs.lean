import GaloisForLFunctions.RHTower.SelbergClass.DirichletFourier
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Log

/-!
# Polynomial major arcs with the exact nonunit correction

The character decomposition in Rakhmonov's short-prime-sum argument
(https://arxiv.org/abs/2611.16828, §3.1, equation (2)) applies to every polynomial
phase. Keeping the nonunit terms gives an exact identity for every finite window
and every weight. For von Mangoldt weights, only prime powers sharing a prime
with the modulus contribute to this correction.
-/

open Finset

namespace GaloisForLFunctions.PrimeExponentialSums

noncomputable section

variable {q : ℕ} [NeZero q]

/-- A polynomial additive phase on the residue ring. -/
def polynomialPhase (P : Polynomial (ZMod q)) (x : ZMod q) : ℂ :=
  ZMod.stdAddChar (P.eval x)

/-- The complete polynomial sum against an inverse Dirichlet character. -/
def polynomialPhaseCoeff (P : Polynomial (ZMod q)) (χ : DirichletCharacter ℂ q) : ℂ :=
  RHTower.dirichletCharacterFourierCoeff (polynomialPhase P) χ

/-- Terms outside the reduced residue classes, retained instead of absorbed in an error. -/
def polynomialNonunitCorrection (P : Polynomial (ZMod q)) (S : Finset ℕ)
    (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S.filter (fun n : ℕ => ¬ IsUnit (n : ZMod q)), polynomialPhase P n * w n

/-- Finite character inversion with no coprimality restriction on the original window. -/
theorem polynomialPhase_sum_eq (P : Polynomial (ZMod q)) (S : Finset ℕ)
    (w : ℕ → ℂ) :
    ∑ n ∈ S, polynomialPhase P n * w n =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        polynomialPhaseCoeff P χ * (∑ n ∈ S, χ n * w n) +
      polynomialNonunitCorrection P S w := by
  classical
  have hpoint (n : ℕ) :
      polynomialPhase P n * w n =
        (q.totient : ℂ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, polynomialPhaseCoeff P χ * (χ n * w n)) +
        (if ¬ IsUnit (n : ZMod q) then polynomialPhase P n * w n else 0) := by
    have h := congrArg (fun z : ℂ => z * w n)
      (RHTower.dirichletCharacterFourier_expansion (polynomialPhase P) (n : ZMod q))
    simp only [mul_assoc, Finset.sum_mul] at h
    by_cases hn : IsUnit (n : ZMod q)
    · simp only [MulChar.one_apply hn, one_mul] at h
      simpa only [polynomialPhaseCoeff, hn, not_true_eq_false, if_false, add_zero] using h
    · simp only [MulChar.map_nonunit _ hn, zero_mul, mul_zero, sum_const_zero, hn,
        not_false_eq_true, if_true, zero_add]
  rw [sum_congr rfl (fun n _ => hpoint n), sum_add_distrib, ← mul_sum, sum_comm]
  congr 1
  · congr 1
    exact sum_congr rfl fun χ _ => (mul_sum _ _ _).symm
  · exact (sum_filter _ _).symm

@[simp] theorem norm_polynomialPhase (P : Polynomial (ZMod q)) (x : ZMod q) :
    ‖polynomialPhase P x‖ = 1 := by
  simp only [polynomialPhase, ZMod.stdAddChar_apply, Circle.norm_coe]

/-- The exact correction costs only the mass on nonunit integers. -/
theorem norm_polynomialNonunitCorrection_le (P : Polynomial (ZMod q)) (S : Finset ℕ)
    (w : ℕ → ℂ) :
    ‖polynomialNonunitCorrection P S w‖ ≤
      ∑ n ∈ S.filter (fun n : ℕ => ¬ IsUnit (n : ZMod q)), ‖w n‖ := by
  unfold polynomialNonunitCorrection
  simpa only [norm_mul, norm_polynomialPhase, one_mul] using
    norm_sum_le (S.filter (fun n : ℕ => ¬ IsUnit (n : ZMod q)))
      (fun n => polynomialPhase P n * w n)

/-- Every polynomial major arc is bounded by its actual twisted sums and nonunit mass. -/
theorem norm_polynomialPhase_sum_le (P : Polynomial (ZMod q)) (S : Finset ℕ)
    (w : ℕ → ℂ) :
    ‖∑ n ∈ S, polynomialPhase P n * w n‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ‖polynomialPhaseCoeff P χ‖ * ‖∑ n ∈ S, χ n * w n‖ +
      ∑ n ∈ S.filter (fun n : ℕ => ¬ IsUnit (n : ZMod q)), ‖w n‖ := by
  rw [polynomialPhase_sum_eq]
  refine (norm_add_le _ _).trans (add_le_add ?_
    (norm_polynomialNonunitCorrection_le P S w))
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  simpa only [norm_mul] using norm_sum_le univ
    (fun χ : DirichletCharacter ℂ q =>
      polynomialPhaseCoeff P χ * (∑ n ∈ S, χ n * w n))

omit [NeZero q] in
/-- Every ramified prime power up to `N` divides one explicit power of the modulus. -/
private theorem ramified_prime_power_dvd {n N : ℕ}
    (hn : n ≤ N) (hc : ¬n.Coprime q)
    (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) : n ∣ q ^ Nat.log 2 N := by
  obtain ⟨p, k, hp, hk, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  have hpp : p.Prime := hp.nat_prime
  have hpq : p ∣ q := by
    by_contra hd
    exact hc ((hpp.coprime_iff_not_dvd.mpr hd).pow_left k)
  have htwo : 2 ^ k ≤ p ^ k := by
    gcongr
    exact hpp.two_le
  have hkN : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) (htwo.trans hn)
  have hpow : p ^ k ∣ q ^ k := by
    obtain ⟨d, hd⟩ := hpq
    rw [hd, mul_pow]
    exact dvd_mul_right _ _
  exact hpow.trans (Nat.pow_dvd_pow q hkN)

/-- The full bad-prime-power mass has a logarithmic divisor-envelope bound. -/
theorem ramified_mangoldt_mass_le (N : ℕ) :
    (∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Coprime q), ArithmeticFunction.vonMangoldt n) ≤
      (Nat.log 2 N : ℝ) * Real.log q := by
  classical
  calc
    _ = ∑ n ∈ ((Icc 1 N).filter (fun n => ¬n.Coprime q)).filter
        (fun n => ArithmeticFunction.vonMangoldt n ≠ 0), ArithmeticFunction.vonMangoldt n :=
      (sum_filter_ne_zero _).symm
    _ ≤ ∑ n ∈ (q ^ Nat.log 2 N).divisors, ArithmeticFunction.vonMangoldt n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn, hΛ⟩ := mem_filter.mp hn
        obtain ⟨hn, hc⟩ := mem_filter.mp hn
        exact Nat.mem_divisors.mpr
          ⟨ramified_prime_power_dvd (mem_Icc.mp hn).2 hc hΛ,
            pow_ne_zero _ (NeZero.ne q)⟩
      · intro n _ _
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by rw [ArithmeticFunction.vonMangoldt_sum, Nat.cast_pow, Real.log_pow]

/-- Mangoldt weights with an arbitrary unit-modulus oscillation. -/
def mangoldtPhaseWeight (z : ℕ → Circle) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * (z n : ℂ)

@[simp] theorem norm_mangoldtPhaseWeight (z : ℕ → Circle) (n : ℕ) :
    ‖mangoldtPhaseWeight z n‖ = ArithmeticFunction.vonMangoldt n := by
  simp only [mangoldtPhaseWeight, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- Polynomial major arcs have an explicit ramification error, uniform in phase and degree. -/
theorem norm_mangoldt_polynomialPhase_sum_le (P : Polynomial (ZMod q))
    (z : ℕ → Circle) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, polynomialPhase P n * mangoldtPhaseWeight z n‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ‖polynomialPhaseCoeff P χ‖ * ‖∑ n ∈ Icc 1 N, χ n * mangoldtPhaseWeight z n‖ +
      (Nat.log 2 N : ℝ) * Real.log q := by
  have h := norm_polynomialPhase_sum_le P (Icc 1 N) (mangoldtPhaseWeight z)
  simp only [norm_mangoldtPhaseWeight, ZMod.isUnit_iff_coprime] at h
  exact h.trans (add_le_add le_rfl (ramified_mangoldt_mass_le (q := q) N))

#print axioms polynomialPhase_sum_eq
#print axioms norm_polynomialPhase_sum_le
#print axioms ramified_mangoldt_mass_le
#print axioms norm_mangoldt_polynomialPhase_sum_le

end
end GaloisForLFunctions.PrimeExponentialSums
