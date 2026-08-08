import Mathlib

/-!
# The Liouville Dirichlet series

The Liouville function is completely multiplicative with `λ (p ^ k) = (-1) ^ k`, so its Dirichlet
convolution with the constant-one function is the indicator of the perfect squares
(`zeta_mul_liouvilleC_apply`).  Summing that identity on the half-plane of absolute convergence
gives the classical closed form

`L ↗λ s * ζ s = ζ (2 * s)`     (`LSeries_liouvilleC_mul_riemannZeta`).

The square-indicator step rests on the elementary characterisation of squares by even
factorisation exponents (`isSquare_iff_factorization_even`).
-/

open Complex Filter ArithmeticFunction
open scoped LSeries.notation

namespace RHTower

/-! ### Squares and factorisation exponents -/

theorem factorization_even_of_isSquare {n : ℕ} (h : IsSquare n) (p : ℕ) :
    Even (n.factorization p) := by
  obtain ⟨k, hk⟩ := h
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [hk]
  · have : n = k ^ 2 := by rw [hk]; ring
    subst this
    rw [Nat.factorization_pow]
    exact ⟨(k.factorization p), by simp [two_mul]⟩

theorem isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨n.factorization.prod fun p e => p ^ (e / 2), ?_⟩
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_add]
  congr 1
  obtain ⟨m, hm⟩ := h p
  omega

theorem isSquare_iff_factorization_even {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) :=
  ⟨fun h p => factorization_even_of_isSquare h p, isSquare_of_factorization_even hn⟩

/-! ### The complex Liouville arithmetic function -/

/-- The Liouville function with complex values. -/
noncomputable def liouvilleC : ArithmeticFunction ℂ :=
  (ArithmeticFunction.liouville : ArithmeticFunction ℂ)

theorem liouvilleC_apply (n : ℕ) : liouvilleC n = ((ArithmeticFunction.liouville n : ℤ) : ℂ) := rfl

theorem isMultiplicative_liouvilleC : liouvilleC.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_liouville.intCast

theorem liouvilleC_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    liouvilleC (p ^ k) = (-1 : ℂ) ^ k := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  rw [liouvilleC_apply, ArithmeticFunction.liouville_apply hpk,
    ArithmeticFunction.cardFactors_apply_prime_pow hp]
  push_cast
  ring

theorem liouvilleC_mul (m n : ℕ) : liouvilleC (m * n) = liouvilleC m * liouvilleC n := by
  simp only [liouvilleC_apply, ArithmeticFunction.liouville_apply_mul]
  push_cast
  ring

theorem liouvilleC_two : liouvilleC 2 = -1 := by
  have h := liouvilleC_prime_pow Nat.prime_two 1
  simpa using h

theorem norm_liouvilleC_le_one (n : ℕ) : ‖liouvilleC n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [liouvilleC_apply]
  · rw [liouvilleC_apply, ArithmeticFunction.liouville_apply hn]
    push_cast
    rw [norm_pow]
    simp

theorem conj_liouvilleC (n : ℕ) : (starRingEnd ℂ) (liouvilleC n) = liouvilleC n := by
  rw [liouvilleC_apply, Complex.conj_intCast]

/-! ### The square-indicator convolution -/

/-- The indicator of the perfect squares. -/
noncomputable def squareIndicator (n : ℕ) : ℂ := if IsSquare n then 1 else 0

theorem sum_divisors_liouvilleC {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, liouvilleC d = squareIndicator n := by
  have hmul : ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * liouvilleC).IsMultiplicative :=
    (ArithmeticFunction.isMultiplicative_zeta.natCast).mul isMultiplicative_liouvilleC
  have hpp : ∀ p k : ℕ, p.Prime →
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * liouvilleC) (p ^ k) =
        if Even k then 1 else 0 := by
    intro p k hp
    rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.divisors_prime_pow hp, Finset.sum_map]
    have : ∀ j ∈ Finset.range (k + 1), liouvilleC (p ^ j) = (-1 : ℂ) ^ j := by
      intro j _
      exact liouvilleC_prime_pow hp j
    rw [Finset.sum_congr rfl this, neg_one_geom_sum]
    by_cases hk : Even k
    · rw [if_pos hk, if_neg (by simpa [Nat.even_add_one] using hk)]
    · rw [if_neg hk, if_pos (by simpa [Nat.even_add_one] using hk)]
  rw [← ArithmeticFunction.coe_zeta_mul_apply,
    hmul.multiplicative_factorization _ hn, squareIndicator, Finsupp.prod]
  by_cases hsq : IsSquare n
  · rw [if_pos hsq]
    refine Finset.prod_eq_one fun p _ => ?_
    rw [hpp p (n.factorization p) (Nat.prime_of_mem_primeFactors (by
      simpa [Nat.support_factorization] using ‹p ∈ n.factorization.support›)),
      if_pos (factorization_even_of_isSquare hsq p)]
  · rw [if_neg hsq]
    obtain ⟨p, hp⟩ : ∃ p, ¬ Even (n.factorization p) := by
      by_contra hcon
      push_neg at hcon
      exact hsq (isSquare_of_factorization_even hn fun p => not_not.mp (hcon p))
    have hpsupp : p ∈ n.factorization.support := by
      rw [Finsupp.mem_support_iff]
      intro h0
      exact hp (by rw [h0]; exact even_zero)
    have hprime : p.Prime :=
      Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hpsupp)
    refine Finset.prod_eq_zero hpsupp ?_
    rw [hpp p (n.factorization p) hprime, if_neg hp]

/-! ### The closed form of the Liouville Dirichlet series -/

theorem LSeriesSummable_liouvilleC {s : ℂ} (hs : 1 < s.re) : LSeriesSummable ↗liouvilleC s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_liouvilleC_le_one n) hs

theorem LSeriesSummable_zetaC {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn => ?_) hs
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn]

theorem LSeries_squareIndicator {s : ℂ} (hs : 1 < (2 * s).re) :
    LSeries squareIndicator s = riemannZeta (2 * s) := by
  have hs0 : (0 : ℝ) < s.re := by
    rw [Complex.mul_re] at hs
    simp at hs
    linarith
  have hterm : ∀ k : ℕ,
      LSeries.term squareIndicator s (k ^ 2) =
        LSeries.term (fun n : ℕ => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) (2 * s) k := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [LSeries.term]
    · have hk2 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      have hknz : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
      have hcast : ((k ^ 2 : ℕ) : ℂ) = ((((k : ℝ) * (k : ℝ)) : ℝ) : ℂ) := by push_cast; ring
      have hcpow : ((k ^ 2 : ℕ) : ℂ) ^ s = (k : ℂ) ^ s * (k : ℂ) ^ s := by
        rw [hcast, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg k)]
        norm_cast
      have hsplit : (k : ℂ) ^ (2 * s) = (k : ℂ) ^ s * (k : ℂ) ^ s := by
        rw [two_mul, Complex.cpow_add _ _ hk2]
      rw [LSeries.term_of_ne_zero hknz, LSeries.term_of_ne_zero hk, squareIndicator,
        if_pos ⟨k, by ring⟩, hcpow, hsplit]
      simp [ArithmeticFunction.zeta_apply, hk]
  have hsupp : Function.support (LSeries.term squareIndicator s) ⊆ Set.range fun k : ℕ => k ^ 2 := by
    intro n hn
    rw [Function.mem_support] at hn
    rcases eq_or_ne n 0 with rfl | h0
    · exact absurd (LSeries.term_zero (f := squareIndicator) (s := s)) hn
    have hsq : squareIndicator n ≠ 0 := by
      intro h
      exact hn (by rw [LSeries.term_of_ne_zero h0, h, zero_div])
    have : IsSquare n := by
      by_contra hcon
      exact hsq (by rw [squareIndicator, if_neg hcon])
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by rw [hk]; ring⟩
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, LSeries, LSeries]
  rw [← Function.Injective.tsum_eq (g := fun k : ℕ => k ^ 2)
    (fun p q h => by simpa using (Nat.pow_left_injective (by norm_num) h)) hsupp]
  exact tsum_congr hterm

/-- **Closed form of the Liouville Dirichlet series.**  On the half-plane of absolute convergence,
`L ↗λ s * ζ s = ζ (2 * s)`. -/
theorem LSeries_liouvilleC_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗liouvilleC s * riemannZeta s = riemannZeta (2 * s) := by
  have hs2 : 1 < (2 * s).re := by
    rw [Complex.mul_re]
    simp
    linarith
  have hprod :=
    LSeries_mul' (f := (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (g := liouvilleC)
      (LSeriesSummable_zetaC hs) (LSeriesSummable_liouvilleC hs)
  have hcongr : LSeries ↗((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * liouvilleC) s =
      LSeries squareIndicator s := by
    refine LSeries_congr s fun n hn => ?_
    rw [← sum_divisors_liouvilleC hn, ArithmeticFunction.coe_zeta_mul_apply]
  rw [hcongr, LSeries_squareIndicator hs2] at hprod
  rw [← hprod, ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  ring

end RHTower
