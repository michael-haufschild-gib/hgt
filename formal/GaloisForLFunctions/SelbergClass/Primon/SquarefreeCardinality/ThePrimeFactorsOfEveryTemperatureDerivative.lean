import GaloisForLFunctions.RHTower.MobiusGibbsCardinalityBoundary

/-!
# The full temperature jet of the squarefree cardinality partition

At zero inverse temperature every derivative in temperature factors
linearly in the particle activity. Its roots are reciprocal powers
of the primes. One positive-order derivative identifies the entire
support, hence determines all the other derivatives.
-/

open Finset Polynomial RHTower
namespace GaloisForLFunctions.SelbergClass.Primon

noncomputable section

/-- The real cardinality polynomial with energy equal to the product of occupied primes. -/
def squarefreeCardinalityPolynomial (P : Finset ℕ) (β : ℝ) : ℝ[X] :=
  ∑ S ∈ P.powerset, C (Real.exp (-(finitePrimeSubsetProduct S : ℝ)*β))*X^S.card

/-- Evaluation gives the original complex partition at every complex activity. -/
theorem squarefreeCardinality_aeval (P : Finset ℕ) (β : ℝ) (z : ℂ) :
    aeval z (squarefreeCardinalityPolynomial P β) = finitePrimeCardinalityPartition P β z := by
  simp only [squarefreeCardinalityPolynomial,finitePrimeCardinalityPartition,map_sum,map_mul,map_pow,
    aeval_C,aeval_X,Complex.algebraMap_apply,Complex.ofReal_exp,Complex.ofReal_mul,
    Complex.ofReal_neg,Complex.ofReal_natCast]
  exact sum_congr rfl fun _ _ => mul_comm _ _

/-- The nth physical-scale derivative at zero inverse temperature. -/
theorem temperature_derivative_factors (P : Finset ℕ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w => finitePrimeCardinalityPartition P w z) 0 =
      (-1:ℂ)^n*∏ p ∈ P, (1+z*(p:ℂ)^n) := by
  rw [iteratedDeriv_finitePrimeCardinalityPartition_zero,finitePrimeCardinalityMoment]
  congr 1
  have h := Finset.prod_add (fun p : ℕ => z*(p:ℂ)^n) (fun _ : ℕ => (1:ℂ)) P
  simpa only [add_comm (1:ℂ),prod_mul_distrib,prod_const,one_pow,mul_one] using h.symm

/-- A single nonzero-order physical derivative vanishes at −q⁻ⁿ exactly when
the integer q is an occupied letter of the model. -/
theorem temperature_derivative_reads_support (P : Finset ℕ) {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    iteratedDeriv n (fun w => finitePrimeCardinalityPartition P w (-((q:ℂ)^n)⁻¹)) 0 = 0 ↔ q ∈ P := by
  rw [temperature_derivative_factors,mul_eq_zero,or_iff_right (pow_ne_zero _ (by norm_num)),
    prod_eq_zero_iff]
  have hq' : (q:ℂ)^n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hq.ne')
  have h (p : ℕ) : 1 + -((q:ℂ)^n)⁻¹*(p:ℂ)^n = 0 ↔ p=q := by
    rw [neg_mul,←sub_eq_add_neg,sub_eq_zero,eq_comm,←div_eq_inv_mul,div_eq_one_iff_eq hq']
    exact_mod_cast ((Nat.pow_left_injective hn.ne').eq_iff : p^n = q^n ↔ p = q)
  simp [h]

/-- Equality of one derivative as a function of activity determines the entire
finite prime ensemble, with no bound on the largest prime. -/
theorem one_temperature_derivative_identifies_primes {P Q : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (hQ : ∀ p ∈ Q, Nat.Prime p) {n : ℕ} (hn : 0 < n) :
    (∀ z : ℂ, iteratedDeriv n (fun w => finitePrimeCardinalityPartition P w z) 0 =
      iteratedDeriv n (fun w => finitePrimeCardinalityPartition Q w z) 0) ↔ P=Q := by
  constructor
  · intro he
    ext q
    by_cases hq : 0 < q
    · rw [←temperature_derivative_reads_support P hq hn,he,temperature_derivative_reads_support Q hq hn]
    · exact iff_of_false (fun h => hq (hP q h).pos) (fun h => hq (hQ q h).pos)
  · rintro rfl _
    rfl


end

end GaloisForLFunctions.SelbergClass.Primon
