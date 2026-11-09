import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.RationalOrbitPreserversAreLaurentAdams

/-!
# Real rational orbit preservers have no time translation

Reality at the prime-orbit origin makes every translation factor a sign.
Two distinct prime coordinates have no nonzero common torsion return, so
the translation vanishes. Real and integer rational orbit preservers are
therefore exactly the signed Adams power maps.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
open InfiniteRankWeilTheory
variable {P : Finset Nat.Primes}

/-- Conjugation-fixed coefficients give a conjugation-fixed value at the prime-orbit origin. -/
theorem complexOrbitValue_zero_conj (F : MvPolynomial P ℂ)
    (h : ∀ α, (starRingEnd ℂ) (F.coeff α) = F.coeff α) :
    (starRingEnd ℂ) (complexOrbitValue F 0) = complexOrbitValue F 0 := by
  simp only [complexOrbitValue_eq_wave, finiteExpWave, expChar, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, map_sum, h]

/-- Reality at the orbit origin removes every time translation. -/
theorem rational_preserver_of_real_origin (p q : P) (hpq : p ≠ q)
    (N D : P → MvPolynomial P ℂ) (hR : RationalPreservesPrimeOrbit N D)
    (hN : ∀ r, (starRingEnd ℂ) (complexOrbitValue (N r) 0) = complexOrbitValue (N r) 0)
    (hD : ∀ r, (starRingEnd ℂ) (complexOrbitValue (D r) 0) = complexOrbitValue (D r) 0) :
    ∃ n : ℤ, LaurentAdamsRelation N D n 0 := by
  obtain ⟨_, n, b, hrel⟩ := (rationalPreservesPrimeOrbit_iff p q hpq N D).mp hR
  have hc := (laurentAdamsRelation_iff_clock N D hR.1 n b).mp hrel
  have hconj (r : P) : (starRingEnd ℂ) (orbitPoint P b r) = orbitPoint P b r := by
    have hb := hc 0 r
    simp only [mul_zero, zero_add] at hb
    rw [← hb, map_div₀, hN r, hD r]
  have hpow (r : P) : phase ((r : Nat.Primes) : ℕ) b ^ 2 = 1 := by
    change (orbitPoint P b r) ^ 2 = 1
    calc
      _ = orbitPoint P b r * (starRingEnd ℂ) (orbitPoint P b r) := by
        rw [hconj r, pow_two]
      _ = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        change ((‖phase ((r : Nat.Primes) : ℕ) b‖ ^ 2 : ℝ) : ℂ) = 1
        rw [norm_phase]
        simp
  have hb : b = 0 := eq_zero_of_torsion_return p.val.property q.val.property
    (fun he => hpq (Subtype.ext (Subtype.ext he))) (Nat.succ_pos 1) (hpow p) (hpow q)
  exact ⟨n, hb ▸ hrel⟩

private theorem translatedAdams_zero_translation (k : ℕ) (r : P) :
    translatedAdams k 0 r = MvPolynomial.X r ^ k := by
  simp only [translatedAdams, orbitPoint, phase, zero_mul, neg_zero,
    Complex.ofReal_zero, Complex.exp_zero, ← MvPolynomial.X_pow_eq_monomial]

/-- Real rational prime-orbit preservers are exactly integer powers of each coordinate. -/
theorem real_rational_preserver_is_laurentAdams (p q : P) (hpq : p ≠ q)
    (N D : P → MvPolynomial P ℝ)
    (hR : RationalPreservesPrimeOrbit
      (fun r => MvPolynomial.map (algebraMap ℝ ℂ) (N r))
      (fun r => MvPolynomial.map (algebraMap ℝ ℂ) (D r))) :
    ∃ n : ℤ, ∀ r : P, N r * MvPolynomial.X r ^ (-n).toNat =
      D r * MvPolynomial.X r ^ n.toNat := by
  obtain ⟨n, hn⟩ := rational_preserver_of_real_origin p q hpq _ _ hR
    (fun r => complexOrbitValue_zero_conj _ (fun α => by simp [MvPolynomial.coeff_map]))
    (fun r => complexOrbitValue_zero_conj _ (fun α => by simp [MvPolynomial.coeff_map]))
  refine ⟨n, fun r => ?_⟩
  apply MvPolynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
  have hr := hn r
  simpa only [map_mul, map_pow, MvPolynomial.map_X,
    translatedAdams_zero_translation] using hr

/-- Integer rational prime-orbit preservers allow exactly the signed Adams exponents. -/
theorem integer_rational_preserver_is_laurentAdams (p q : P) (hpq : p ≠ q)
    (N D : P → MvPolynomial P ℤ)
    (hR : RationalPreservesPrimeOrbit
      (fun r => MvPolynomial.map (Int.castRingHom ℂ) (N r))
      (fun r => MvPolynomial.map (Int.castRingHom ℂ) (D r))) :
    ∃ n : ℤ, ∀ r : P, N r * MvPolynomial.X r ^ (-n).toNat =
      D r * MvPolynomial.X r ^ n.toNat := by
  obtain ⟨n, hn⟩ := rational_preserver_of_real_origin p q hpq _ _ hR
    (fun r => complexOrbitValue_zero_conj _ (fun α => by simp [MvPolynomial.coeff_map]))
    (fun r => complexOrbitValue_zero_conj _ (fun α => by simp [MvPolynomial.coeff_map]))
  refine ⟨n, fun r => ?_⟩
  apply MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
  have hr := hn r
  simpa only [map_mul, map_pow, MvPolynomial.map_X,
    translatedAdams_zero_translation] using hr

#print axioms real_rational_preserver_is_laurentAdams
#print axioms integer_rational_preserver_is_laurentAdams

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
