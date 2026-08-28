import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPieceTypes

/-!
# Truncated Legendre factor for Proposition 2.2

The finite Legendre kernel is exactly a Dirichlet convolution of its truncated Möbius divisor
coefficient with the constant-one coefficient.  This is the algebraic input needed to partition
each repaired Harman main layer into the literal Proposition 2.2 piece shapes.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Möbius coefficient supported on divisors of the sifting modulus up to the truncation level. -/
def mtTruncLegendreCoefficient (z D e : ℕ) : ℂ :=
  if e ∣ siftModulus z ∧ e ≤ D then (moebius e : ℂ) else 0

theorem mtTruncLegendreCoefficient_support {z D e : ℕ}
    (he : mtTruncLegendreCoefficient z D e ≠ 0) :
    e ∣ siftModulus z ∧ e ≤ D := by
  by_contra h
  simp [mtTruncLegendreCoefficient, h] at he

/-- Truncated Möbius coefficients obey the source's polynomial divisor bound. -/
theorem mtTruncLegendreCoefficient_polynomialDivisorBounded (z D : ℕ) :
    MTPolynomialDivisorBounded (mtTruncLegendreCoefficient z D) := by
  refine ⟨1, zero_le_one, 0, ?_⟩
  intro n hn
  by_cases hsupport : n ∣ siftModulus z ∧ n ≤ D
  · rw [mtTruncLegendreCoefficient, if_pos hsupport]
    have hμ : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    simpa using hμ
  · simp [mtTruncLegendreCoefficient, hsupport]

/-- Exact Dirichlet-convolution factorization of the truncated Legendre kernel. -/
theorem mtTruncLegendreAF_eq_coefficient_mul_one (z D : ℕ) :
    mtTruncLegendreAF z D =
      mtCoefficientAF (mtTruncLegendreCoefficient z D) *
        mtCoefficientAF (fun _ => 1) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [mtTruncLegendreAF, mtCoefficientAF]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hgcdPos : 0 < Nat.gcd n (siftModulus z) :=
      Nat.gcd_pos_of_pos_left _ hnPos
    have hsets :
        n.divisors.filter (fun e => e ∣ siftModulus z ∧ e ≤ D) =
          (Nat.gcd n (siftModulus z)).divisors.filter (fun e => e ≤ D) := by
      ext e
      simp [Nat.mem_divisors, hn, hgcdPos.ne', Nat.dvd_gcd_iff,
        and_left_comm, and_comm]
    rw [mtTruncLegendreAF_apply_of_pos z D hnPos, ArithmeticFunction.mul_apply]
    rw [show
      (∑ x ∈ n.divisorsAntidiagonal,
          mtCoefficientAF (mtTruncLegendreCoefficient z D) x.1 *
            mtCoefficientAF (fun _ => 1) x.2) =
        ∑ e ∈ n.divisors,
          mtCoefficientAF (mtTruncLegendreCoefficient z D) e *
            mtCoefficientAF (fun _ => 1) (n / e) by
      exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
        (fun e m => mtCoefficientAF (mtTruncLegendreCoefficient z D) e *
          mtCoefficientAF (fun _ => 1) m)]
    calc
      (truncLegendre n z D : ℂ) =
          ∑ e ∈ (Nat.gcd n (siftModulus z)).divisors.filter (fun e => e ≤ D),
            (moebius e : ℂ) := by
        simp [truncLegendre]
      _ = ∑ e ∈ n.divisors.filter (fun e => e ∣ siftModulus z ∧ e ≤ D),
            (moebius e : ℂ) := by rw [hsets]
      _ = ∑ e ∈ n.divisors,
            mtCoefficientAF (mtTruncLegendreCoefficient z D) e *
              mtCoefficientAF (fun _ => 1) (n / e) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e he
        have hePos : 0 < e := Nat.pos_of_mem_divisors he
        have heDvd : e ∣ n := Nat.dvd_of_mem_divisors he
        have hquotPos : 0 < n / e :=
          Nat.div_pos (Nat.le_of_dvd hnPos heDvd) hePos
        rw [mtCoefficientAF_apply_of_pos _ hePos,
          mtCoefficientAF_apply_of_pos _ hquotPos]
        by_cases hsupport : e ∣ siftModulus z ∧ e ≤ D
        · simp [hsupport, mtTruncLegendreCoefficient]
        · simp [hsupport, mtTruncLegendreCoefficient]

end

end RHTower.Sieve
