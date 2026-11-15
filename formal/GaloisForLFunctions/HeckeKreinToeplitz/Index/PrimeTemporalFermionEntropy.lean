import GaloisForLFunctions.HilbertMetric.QuantumInformation.TwoModeTemporalSampling
import GaloisForLFunctions.HeckeKreinToeplitz.AllButFinitelyManyPrimesSeeTheWholeIndex

/-!
# Prime sampling and the entropy of a two-mode collision

The finite temporal compression mechanism of arXiv:2611.13085 applies to the
corpus's arithmetic character samples. Distinct exponents can alias at at most
one prime. Consequently the two-mode compression entropy is supported on at
most one prime, and the product of its values at two primes is diagonal.
The exponent gap is explicitly nonzero, so no distinctness premise is assumed.
-/

noncomputable section
open scoped Matrix BigOperators
namespace GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HilbertMetric

/-- An explicitly distinct exponent, with a positive imaginary gap. -/
def temporalPartnerExponent (rho : ℂ) (u : ℝ) : ℂ := rho + (Real.exp u : ℂ) * Complex.I

theorem temporalPartnerExponent_ne (rho : ℂ) (u : ℝ) : rho ≠ temporalPartnerExponent rho u := by
  intro h
  have hi := congrArg Complex.im h
  simp only [temporalPartnerExponent, Complex.add_im, Complex.mul_I_im, Complex.ofReal_re] at hi
  linarith [Real.exp_pos u]

/-- Spectral entropy of the occupied/empty pair sampled along a prime tower. -/
def primeTemporalFermionEntropy (rho : ℂ) (u : ℝ) (p : Nat.Primes) : ℝ :=
  fermionSpectralEntropy (twoModeTemporalCorrelation
    (zeroChar rho (primeElt p.property))
    (zeroChar (temporalPartnerExponent rho u) (primeElt p.property)))

/-- A prime contributes one bit exactly when it aliases the two character values. -/
theorem primeTemporalFermionEntropy_eq (rho : ℂ) (u : ℝ) (p : Nat.Primes) :
    primeTemporalFermionEntropy rho u p =
      if zeroChar rho (primeElt p.property) =
          zeroChar (temporalPartnerExponent rho u) (primeElt p.property)
      then Real.log 2 else 0 :=
  twoModeTemporalCorrelation_entropy _ _

/-- Two prime observations cannot both carry collision entropy unless their primes agree. -/
theorem primeTemporalFermionEntropy_unique (rho : ℂ) (u : ℝ) (p q : Nat.Primes) :
    primeTemporalFermionEntropy rho u p = 0 ∨ p = q ∨ primeTemporalFermionEntropy rho u q = 0 := by
  by_cases hp : zeroChar rho (primeElt p.property) =
      zeroChar (temporalPartnerExponent rho u) (primeElt p.property)
  · by_cases hq : zeroChar rho (primeElt q.property) =
        zeroChar (temporalPartnerExponent rho u) (primeElt q.property)
    · exact Or.inr (Or.inl (Subtype.ext
        (eq_of_alias_of_alias (temporalPartnerExponent_ne rho u) p.property q.property hp hq)))
    · exact Or.inr (Or.inr (by rw [primeTemporalFermionEntropy_eq, if_neg hq]))
  · exact Or.inl (by rw [primeTemporalFermionEntropy_eq, if_neg hp])

/-- Entropy products vanish off the prime diagonal. -/
theorem primeTemporalFermionEntropy_product (rho : ℂ) (u : ℝ) (p q : Nat.Primes) :
    primeTemporalFermionEntropy rho u p * primeTemporalFermionEntropy rho u q =
      if p = q then primeTemporalFermionEntropy rho u p ^ 2 else 0 := by
  by_cases h : p = q
  · subst q
    simp [pow_two]
  · rw [if_neg h]
    rcases primeTemporalFermionEntropy_unique rho u p q with hp | hpq | hq
    · rw [hp, zero_mul]
    · exact (h hpq).elim
    · rw [hq, mul_zero]

/-- A prime observation is either pure or has the maximal one-mode entropy. -/
theorem primeTemporalFermionEntropy_values (rho : ℂ) (u : ℝ) (p : Nat.Primes) :
    primeTemporalFermionEntropy rho u p = 0 ∨
      primeTemporalFermionEntropy rho u p = Real.log 2 := by
  rw [primeTemporalFermionEntropy_eq]
  split_ifs <;> simp

/-- Summing arbitrarily many distinct prime observations never exceeds one bit
of collision entropy. -/
theorem primeTemporalFermionEntropy_sum_le (rho : ℂ) (u : ℝ) (s : Finset Nat.Primes) :
    ∑ p ∈ s, primeTemporalFermionEntropy rho u p ≤ Real.log 2 := by
  classical
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hzero : ∀ p ∈ s, primeTemporalFermionEntropy rho u p = 0
  · simpa only [Finset.sum_eq_zero hzero] using hlog
  push Not at hzero
  obtain ⟨p, hp, hne⟩ := hzero
  have hsum : ∑ q ∈ s, primeTemporalFermionEntropy rho u q =
      primeTemporalFermionEntropy rho u p := by
    apply Finset.sum_eq_single p
    · intro q _ hqp
      rcases primeTemporalFermionEntropy_unique rho u p q with hz | he | hz
      · exact (hne hz).elim
      · exact (hqp he.symm).elim
      · exact hz
    · intro hnot
      exact (hnot hp).elim
  rw [hsum]
  rcases primeTemporalFermionEntropy_values rho u p with hz | hz
  · exact (hne hz).elim
  · exact hz.le

/-- A prescribed prime resonates with the explicit positive gap `2π/log p`. -/
theorem temporalPartnerExponent_resonance (rho : ℂ) (p : Nat.Primes) :
    zeroChar rho (primeElt p.property) =
      zeroChar (temporalPartnerExponent rho (Real.log (2 * Real.pi / Real.log (p : ℕ))))
        (primeElt p.property) := by
  have hlog : 0 < Real.log (p : ℕ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hgap : 0 < 2 * Real.pi / Real.log (p : ℕ) := by positivity
  apply (zeroChar_prime_eq_iff p.property).mpr
  refine ⟨-1, ?_⟩
  rw [temporalPartnerExponent, Real.exp_log hgap]
  have hprod := congrArg (fun x : ℝ => (x : ℂ))
    (div_mul_cancel₀ (2 * Real.pi) hlog.ne')
  norm_num only [Complex.ofReal_mul] at hprod
  rw [show ((2 : ℝ) : ℂ) = 2 by norm_num] at hprod
  norm_num only
  linear_combination -Complex.I * hprod

/-- Every single-prime entropy profile is realized explicitly; the one-bit bound is sharp. -/
theorem primeTemporalFermionEntropy_spike (rho : ℂ) (p q : Nat.Primes) :
    primeTemporalFermionEntropy rho (Real.log (2 * Real.pi / Real.log (p : ℕ))) q =
      if q = p then Real.log 2 else 0 := by
  rw [primeTemporalFermionEntropy_eq]
  by_cases hqp : q = p
  · subst q
    rw [if_pos (temporalPartnerExponent_resonance rho p), if_pos rfl]
  · rw [if_neg hqp, if_neg]
    intro hq
    apply hqp
    exact Subtype.ext (eq_of_alias_of_alias
      (temporalPartnerExponent_ne rho (Real.log (2 * Real.pi / Real.log (p : ℕ))))
      q.property p.property hq (temporalPartnerExponent_resonance rho p))

end GaloisForLFunctions.HeckeKreinToeplitz
