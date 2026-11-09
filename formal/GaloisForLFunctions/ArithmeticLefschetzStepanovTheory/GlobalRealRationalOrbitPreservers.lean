import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.GlobalRationalOrbitPreservers

/-!
# Real rational preservers of the full prime orbit

Reality at the prime-orbit origin makes every translation factor a sign.
Two distinct prime coordinates have no nonzero common torsion return, so
the translation vanishes. Real and integer rational orbit preservers are
therefore exactly the signed Adams power maps.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
open InfiniteRankWeilTheory

/-- Conjugation-fixed coefficients give a conjugation-fixed value at the prime-orbit origin. -/
theorem globalOrbitValue_zero_conj (F : MvPolynomial Nat.Primes ℂ)
    (h : ∀ α, (starRingEnd ℂ) (F.coeff α) = F.coeff α) :
    (starRingEnd ℂ) (globalOrbitValue F 0) = globalOrbitValue F 0 := by
  simp only [globalOrbitValue_eq_wave, finiteExpWave, expChar, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, map_sum, h]

/-- Reality at the orbit origin removes every time translation. -/
theorem global_rational_preserver_of_real_origin
    (N D : Nat.Primes → MvPolynomial Nat.Primes ℂ) (hR : GlobalRationalPreservesPrimeOrbit N D)
    (hN : ∀ r, (starRingEnd ℂ) (globalOrbitValue (N r) 0) = globalOrbitValue (N r) 0)
    (hD : ∀ r, (starRingEnd ℂ) (globalOrbitValue (D r) 0) = globalOrbitValue (D r) 0) :
    ∃ n : ℤ, GlobalLaurentAdamsRelation N D n 0 := by
  obtain ⟨_, n, b, hrel⟩ := (globalRationalPreservesPrimeOrbit_iff N D).mp hR
  have hc := (globalLaurentAdamsRelation_iff_clock N D hR.1 n b).mp hrel
  have hconj (r : Nat.Primes) : (starRingEnd ℂ) (globalOrbitPoint b r) = globalOrbitPoint b r := by
    have hb := hc 0 r
    simp only [mul_zero, zero_add] at hb
    rw [← hb, map_div₀, hN r, hD r]
  have hpow (r : Nat.Primes) : phase (r : ℕ) b ^ 2 = 1 := by
    change (globalOrbitPoint b r) ^ 2 = 1
    calc
      _ = globalOrbitPoint b r * (starRingEnd ℂ) (globalOrbitPoint b r) := by
        rw [hconj r, pow_two]
      _ = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        change ((‖phase (r : ℕ) b‖ ^ 2 : ℝ) : ℂ) = 1
        rw [norm_phase]
        simp
  have hb : b = 0 := eq_zero_of_torsion_return Nat.prime_two Nat.prime_three
    (by norm_num) (Nat.succ_pos 1)
    (hpow ⟨2, Nat.prime_two⟩) (hpow ⟨3, Nat.prime_three⟩)
  exact ⟨n, hb ▸ hrel⟩

private theorem globalTranslatedAdams_zero_translation (k : ℕ) (r : Nat.Primes) :
    globalTranslatedAdams k 0 r = MvPolynomial.X r ^ k := by
  simp only [globalTranslatedAdams, globalOrbitPoint, phase, zero_mul, neg_zero,
    Complex.ofReal_zero, Complex.exp_zero, map_one, one_mul]

/-- Real rational prime-orbit preservers are exactly integer powers of each coordinate. -/
theorem global_real_rational_preserver_is_laurentAdams
    (N D : Nat.Primes → MvPolynomial Nat.Primes ℝ)
    (hR : GlobalRationalPreservesPrimeOrbit
      (fun r => MvPolynomial.map (algebraMap ℝ ℂ) (N r))
      (fun r => MvPolynomial.map (algebraMap ℝ ℂ) (D r))) :
    ∃ n : ℤ, ∀ r : Nat.Primes, N r * MvPolynomial.X r ^ (-n).toNat =
      D r * MvPolynomial.X r ^ n.toNat := by
  obtain ⟨n, hn⟩ := global_rational_preserver_of_real_origin _ _ hR
    (fun r => globalOrbitValue_zero_conj _ (fun α => by simp [MvPolynomial.coeff_map]))
    (fun r => globalOrbitValue_zero_conj _ (fun α => by simp [MvPolynomial.coeff_map]))
  refine ⟨n, fun r => ?_⟩
  apply MvPolynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
  have hr := hn r
  simpa only [map_mul, map_pow, MvPolynomial.map_X,
    globalTranslatedAdams_zero_translation] using hr

/-- Integer rational prime-orbit preservers allow exactly the signed Adams exponents. -/
theorem global_integer_rational_preserver_is_laurentAdams
    (N D : Nat.Primes → MvPolynomial Nat.Primes ℤ)
    (hR : GlobalRationalPreservesPrimeOrbit
      (fun r => MvPolynomial.map (Int.castRingHom ℂ) (N r))
      (fun r => MvPolynomial.map (Int.castRingHom ℂ) (D r))) :
    ∃ n : ℤ, ∀ r : Nat.Primes, N r * MvPolynomial.X r ^ (-n).toNat =
      D r * MvPolynomial.X r ^ n.toNat := by
  obtain ⟨n, hn⟩ := global_rational_preserver_of_real_origin _ _ hR
    (fun r => globalOrbitValue_zero_conj _ (fun α => by simp [MvPolynomial.coeff_map]))
    (fun r => globalOrbitValue_zero_conj _ (fun α => by simp [MvPolynomial.coeff_map]))
  refine ⟨n, fun r => ?_⟩
  apply MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
  have hr := hn r
  simpa only [map_mul, map_pow, MvPolynomial.map_X,
    globalTranslatedAdams_zero_translation] using hr

#print axioms global_real_rational_preserver_is_laurentAdams
#print axioms global_integer_rational_preserver_is_laurentAdams

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
