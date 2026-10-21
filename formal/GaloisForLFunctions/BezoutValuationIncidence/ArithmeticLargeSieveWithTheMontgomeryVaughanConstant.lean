import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticLargeSieveForSquarefreeModuli
import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveWithTheMontgomeryVaughanConstant

/-!
# The arithmetic large sieve with constant `N + Q² − 1`

For `A ⊆ [0, N)` occupying `c_p` classes modulo each prime `p` and
`h(q) = Π_{p ∣ q} (p − c_p)/c_p`,

`|A| Σ_{q ≤ Q squarefree} h(q) ≤ N + Q² − 1`.

Montgomery's inequality at each squarefree modulus is unchanged; the large sieve over the roots of
unity of order at most `Q` now carries the Montgomery–Vaughan constant `N + Q² − 1`.
-/

open Finset RHTower.Sieve
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- Response frequencies are roots of unity of order at most `Q`. -/
theorem exists_pow_eq_one_of_mem_responseRoots {Q : ℕ} {ζ : ℂ} (hζ : ζ ∈ responseRoots Q) :
    ∃ d, 1 ≤ d ∧ d ≤ Q ∧ ζ ^ d = 1 := by
  obtain ⟨d, hd, hζd⟩ := mem_biUnion.mp hζ
  have hd' := mem_Icc.mp hd
  exact ⟨d, hd'.1, hd'.2, (Polynomial.mem_nthRootsFinset (by omega) 1).mp hζd⟩

/-- **The arithmetic large sieve with constant `N + Q² − 1`.** -/
theorem arithmetic_largeSieve_montgomeryVaughanConstant (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q)
    (A : Finset ℕ) (hA : A ⊆ range N) (hAne : A.Nonempty) :
    (A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors,
        ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card ≤
      (N : ℝ) + (Q : ℝ) ^ 2 - 1 := by
  classical
  set h : ℕ → ℝ := fun q => ∏ p ∈ q.primeFactors,
    ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card with hh
  set E : ℂ → ℝ := fun ζ => ‖∑ n ∈ A, ζ ^ n‖ ^ 2 with hE
  have hE0 : ∀ ζ, 0 ≤ E ζ := fun ζ => sq_nonneg _
  have hcardsq : ‖∑ n ∈ A, (1 : ℂ)‖ ^ 2 = (A.card : ℝ) ^ 2 := by
    rw [sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast]
  -- Montgomery at every squarefree modulus
  have hmont : ∀ q ∈ (Icc 1 Q).filter Squarefree,
      h q * (A.card : ℝ) ^ 2 ≤ ∑ ζ ∈ primitiveRoots q ℂ, E ζ := by
    intro q hq
    have hsq := (mem_filter.mp hq).2
    have hm := montgomery_prod_primes_ge hAne (fun _ => 1) q.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hsq, hcardsq] at hm
    simpa only [one_mul, hE] using hm
  have hsum : (A.card : ℝ) ^ 2 * ∑ q ∈ (Icc 1 Q).filter Squarefree, h q ≤
      ∑ ζ ∈ responseRoots Q, E ζ := by
    have h1 : ∑ ζ ∈ responseRoots Q, (E ζ : ℂ) =
        ((∑ q ∈ Icc 1 Q, ∑ ζ ∈ primitiveRoots q ℂ, E ζ : ℝ) : ℂ) := by
      rw [sum_responseRoots_eq_sum_primitiveRoots]
      push_cast
      rfl
    have h2 : ∑ ζ ∈ responseRoots Q, E ζ = ∑ q ∈ Icc 1 Q, ∑ ζ ∈ primitiveRoots q ℂ, E ζ := by
      exact_mod_cast h1
    rw [h2, mul_sum]
    calc ∑ q ∈ (Icc 1 Q).filter Squarefree, (A.card : ℝ) ^ 2 * h q
        ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∑ ζ ∈ primitiveRoots q ℂ, E ζ :=
          sum_le_sum fun q hq => by rw [mul_comm]; exact hmont q hq
      _ ≤ ∑ q ∈ Icc 1 Q, ∑ ζ ∈ primitiveRoots q ℂ, E ζ :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun q _ _ =>
            sum_nonneg fun ζ _ => hE0 ζ
  -- the large sieve over the roots of order at most `Q`, constant `N + Q² − 1`
  set y : ℕ → ℂ := fun n => if n ∈ A then 1 else 0 with hy
  have hls := largeSieve_rootsOfUnity_range_sharp hQ
    (fun ζ hζ => exists_pow_eq_one_of_mem_responseRoots hζ) N y
  have hyA : ∀ ζ : ℂ, ∑ n ∈ range N, y n * ζ ^ n = ∑ n ∈ A, ζ ^ n := by
    intro ζ
    simp only [hy, ite_mul, one_mul, zero_mul]
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hA]
  have hyn : ∑ n ∈ range N, ‖y n‖ ^ 2 = (A.card : ℝ) := by
    simp only [hy, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_one, one_pow, norm_zero,
      zero_pow two_ne_zero]
    rw [sum_ite_mem, inter_eq_right.mpr hA, sum_const, nsmul_eq_mul, mul_one]
  simp only [hyA, hyn] at hls
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast card_pos.mpr hAne
  have key : (A.card : ℝ) * ((A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, h q) ≤
      (A.card : ℝ) * ((N : ℝ) + (Q : ℝ) ^ 2 - 1) := by
    calc (A.card : ℝ) * ((A.card : ℝ) * ∑ q ∈ (Icc 1 Q).filter Squarefree, h q)
        = (A.card : ℝ) ^ 2 * ∑ q ∈ (Icc 1 Q).filter Squarefree, h q := by ring
      _ ≤ ∑ ζ ∈ responseRoots Q, E ζ := hsum
      _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2 - 1) * (A.card : ℝ) := hls
      _ = _ := by ring
  exact le_of_mul_le_mul_left key hcard

/-- **The sieve bound.** `|A| ≤ (N + Q² − 1)/L` whenever `L ≤ Σ_{q ≤ Q squarefree} h(q)`. -/
theorem card_le_of_arithmetic_largeSieve_montgomeryVaughanConstant (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q)
    (A : Finset ℕ) (hA : A ⊆ range N) (hAne : A.Nonempty) {L : ℝ} (hL : 0 < L)
    (hLle : L ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors,
        ((p : ℝ) - (occupiedClasses p A).card) / (occupiedClasses p A).card) :
    (A.card : ℝ) ≤ ((N : ℝ) + (Q : ℝ) ^ 2 - 1) / L := by
  rw [le_div_iff₀ hL]
  exact (mul_le_mul_of_nonneg_left hLle (Nat.cast_nonneg _)).trans
    (arithmetic_largeSieve_montgomeryVaughanConstant N hQ A hA hAne)

end

end GaloisForLFunctions.BezoutValuationIncidence
