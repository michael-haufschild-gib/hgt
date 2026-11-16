import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomialDegree
import GaloisForLFunctions.RHTower.StepanovHyperelliptic

/-!
# Higher jets of Frobenius trace substitutions

The hyperderivative mechanism in arXiv:2611.09821, Lemma 2.6, applies
to the existing relative trace polynomials. Below the first Frobenius
exponent, their jets are exactly affine: the first derivative is one
and every higher Hasse derivative vanishes. Every polynomial substitution
therefore commutes with Hasse differentiation below that threshold.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section
open Polynomial

variable (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharP K p]

/-- Every jet below the first nonlinear Frobenius term is determined explicitly. -/
theorem frobeniusTraceSum_low_hasse (d m : ℕ) (j : Fin (p ^ (d + 1))) :
    hasseDeriv j.val (frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])) =
      if j.val = 0 then frobeniusTraceSum p (d + 1) (m + 1) X
      else if j.val = 1 then 1 else 0 := by
  by_cases hj0 : j.val = 0
  · simp only [hj0, hasseDeriv_zero', ite_true]
  by_cases hj1 : j.val = 1
  · simp only [hj1, one_ne_zero, if_false, ite_true, hasseDeriv_one']
    exact frobeniusTraceSum_polynomial_derivative p d m
  rw [if_neg hj0, if_neg hj1]
  induction m with
  | zero =>
    simp only [frobeniusTraceSum, zero_add, Finset.sum_range_one, Nat.mul_zero, pow_zero, pow_one]
    exact hasseDeriv_X _ (by omega)
  | succ m ih =>
    have hs : frobeniusTraceSum p (d + 1) (m + 1 + 1) (X : K[X]) =
        frobeniusTraceSum p (d + 1) (m + 1) X + X ^ p ^ ((d + 1) * (m + 1)) :=
      Finset.sum_range_succ _ _
    rw [hs, map_add, ih]
    have hbound : j.val < p ^ ((d + 1) * (m + 1)) :=
      lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (Fact.out : p.Prime).pos
        (Nat.le_mul_of_pos_right (d + 1) (Nat.succ_pos m)))
    rw [GaloisForLFunctions.RHTower.Stepanov.hasseDeriv_X_pow_prime_pow
      (p := p) (by omega) hbound, add_zero]

section Powers
variable (d m : ℕ)
local notation "F" => frobeniusTraceSum p (d + 1) (m + 1) (X : K[X])

/-- Below the Frobenius threshold, multiplication by the trace has the affine Leibniz rule. -/
private theorem trace_power_step (N : ℕ) (j : Fin (p ^ (d + 1) - 1)) :
    hasseDeriv (j.val + 1) (F ^ (N + 1)) =
      hasseDeriv (j.val + 1) (F ^ N) * F + hasseDeriv j.val (F ^ N) := by
  rw [pow_succ F N, hasseDeriv_mul]
  have hbound : j.val + 1 < p ^ (d + 1) := by have := j.isLt; omega
  calc
    _ = ∑ a ∈ Finset.HasAntidiagonal.antidiagonal (j.val + 1),
        ((if a = (j.val + 1, 0) then hasseDeriv (j.val + 1) (F ^ N) * F else 0) +
         (if a = (j.val, 1) then hasseDeriv j.val (F ^ N) else 0)) := by
      apply Finset.sum_congr rfl
      rintro ⟨u, v⟩ ha
      have huv : u + v = j.val + 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
      have hv : v < p ^ (d + 1) := by omega
      have hj := frobeniusTraceSum_low_hasse (K := K) p d m ⟨v, hv⟩
      rw [hj]
      by_cases hv0 : v = 0
      · have hu : u = j.val + 1 := by omega
        subst v
        subst u
        simp
      by_cases hv1 : v = 1
      · have hu : u = j.val := by omega
        subst v
        subst u
        simp
      · simp [hv0, hv1, Prod.mk.injEq]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- The full binomial power law holds at every order below the first Frobenius exponent. -/
theorem frobeniusTraceSum_power_low_hasse (N : ℕ) (j : Fin (p ^ (d + 1))) :
    hasseDeriv j.val (F ^ N) = C ((N.choose j.val : ℕ) : K) * F ^ (N - j.val) := by
  induction N generalizing j with
  | zero =>
    by_cases hj : j.val = 0
    · simp [hj]
    · simp [hasseDeriv_apply_one _ (by omega : 0 < j.val),
        Nat.choose_eq_zero_of_lt (by omega : 0 < j.val)]
  | succ N ih =>
    by_cases hj0 : j.val = 0
    · simp [hj0]
    obtain ⟨k, hk⟩ : ∃ k, j.val = k + 1 := ⟨j.val - 1, by omega⟩
    have hsmall : k < p ^ (d + 1) - 1 := by have := j.isLt; omega
    have hsmall' : k < p ^ (d + 1) := by omega
    have hstep := trace_power_step (K := K) p d m N ⟨k, hsmall⟩
    rw [hk, hstep]
    have hi₁ := ih ⟨k + 1, by have := j.isLt; omega⟩
    have hi₀ := ih ⟨k, hsmall'⟩
    rw [hi₁, hi₀]
    by_cases hkN : k < N
    · rw [Nat.choose_succ_succ, Nat.cast_add, map_add, add_mul]
      have he₀ : N + 1 - (k + 1) = N - k := by omega
      have he₁ : N - k = (N - (k + 1)) + 1 := by omega
      simp only [he₀, he₁, pow_succ F (N - (k + 1))]
      ring
    · by_cases heq : k = N
      · subst k
        simp
      · have hNk : N < k := by omega
        have hNk' : N < k + 1 := by omega
        have hsucc : N + 1 < k + 1 := by omega
        simp [Nat.choose_eq_zero_of_lt hNk, Nat.choose_eq_zero_of_lt hNk',
          Nat.choose_eq_zero_of_lt hsucc]

/-- Every polynomial inherits the affine substitution rule below the Frobenius threshold. -/
theorem frobeniusTraceSum_comp_low_hasse (P : K[X]) (j : Fin (p ^ (d + 1))) :
    hasseDeriv j.val (P.comp F) = (hasseDeriv j.val P).comp F := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [add_comp, map_add, hP, hQ]
  | monomial N a =>
    rw [monomial_comp, ← smul_eq_C_mul, map_smul,
      frobeniusTraceSum_power_low_hasse, hasseDeriv_monomial, monomial_comp,
      smul_eq_C_mul, map_mul]
    ring

end Powers

#print axioms frobeniusTraceSum_low_hasse
#print axioms frobeniusTraceSum_power_low_hasse
#print axioms frobeniusTraceSum_comp_low_hasse

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
