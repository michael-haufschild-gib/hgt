import GaloisForLFunctions.RHTower.GaussPrimeScaleFourier

/-!
# Normalization correction to Connes--Consani Lemma 3.3

Lemma 3.3 of *Quasi-inner functions and local factors* uses the multiplier
`s_p(x) = p^(1-x)` but prints its Fourier coefficient without the numerator `p - 1`.
The exact integral is

`∫₀¹ p exp(-x log p) exp(-2πijx) dx = (p-1)/(log p + 2πij)`.

Consequently the printed Gram identity is valid at frequency zero exactly at `p = 2`; for every
odd prime it misses the positive scalar `p - 1`.  This correction fixes the source-isometry and
Dixmier-residue normalization of the distinguished finite-prime block.
-/

open Complex intervalIntegral

namespace RHTower

noncomputable section

/-- Exact Fourier coefficient of the squared prime-scale multiplier `s_p(x)=p^(1-x)`. -/
theorem intervalIntegral_connesConsaniPrimeGramMultiplier_fourier
    {p : ℝ} (hp : 1 < p) (j : ℤ) :
    (∫ x in (0 : ℝ)..1,
        ((p : ℂ) * Complex.exp (-((Real.log p : ℂ) * (x : ℂ)))) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ)))) =
      (((p - 1 : ℝ) : ℂ) /
        (((Real.log p : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp2 : 1 < p ^ 2 := by nlinarith
  have h := intervalIntegral_gaussPrimeScale_fourier hp2 j
  rw [gaussPrimeScaleFourierCoefficient] at h
  have hsqrt : Real.sqrt (p ^ 2) = p := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hp0]
  have hlog : Real.log (p ^ 2) / 2 = Real.log p := by
    rw [Real.log_pow]
    ring
  rw [hsqrt, hlog] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp
  unfold gaussPrimeScale
  rw [Real.log_pow]
  rw [show ((Real.exp ((1 - x) * ((2 : ℕ) * Real.log p) / 2) : ℝ) : ℂ) =
      (p : ℂ) * Complex.exp (-((Real.log p : ℂ) * (x : ℂ))) by
    rw [show (1 - x) * ((2 : ℕ) * Real.log p) / 2 = Real.log p - Real.log p * x by
      push_cast
      ring]
    rw [Real.exp_sub, Real.exp_log hp0, Complex.ofReal_div, Complex.ofReal_exp]
    push_cast
    rw [Complex.exp_neg]
    ring]

/-- At frequency zero, the coefficient printed in Connes--Consani Lemma 3.3 is correct exactly for
the accidental normalization `p=2`.  Every odd prime has a missing factor `p-1`. -/
theorem connesConsaniLemma33_printed_zeroCoefficient_iff
    {p : ℝ} (hp : 1 < p) :
    (∫ x in (0 : ℝ)..1,
        (p : ℂ) * Complex.exp (-((Real.log p : ℂ) * (x : ℂ)))) =
      (1 : ℂ) / (Real.log p : ℂ) ↔ p = 2 := by
  have h := intervalIntegral_connesConsaniPrimeGramMultiplier_fourier hp (0 : ℤ)
  have h' : (∫ x in (0 : ℝ)..1,
        (p : ℂ) * Complex.exp (-((Real.log p : ℂ) * (x : ℂ)))) =
      ((p - 1 : ℝ) : ℂ) / (Real.log p : ℂ) := by
    simpa using h
  rw [h']
  have hlog : (Real.log p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hp).ne'
  constructor
  · intro heq
    field_simp [hlog] at heq
    norm_cast at heq
    linarith
  · rintro rfl
    norm_num

/-- For every odd rational prime, the zero-frequency identity printed in Lemma 3.3 is false. -/
theorem connesConsaniLemma33_printed_zeroCoefficient_ne_of_oddPrime
    (p : Nat.Primes) (hp : p.1 ≠ 2) :
    (∫ x in (0 : ℝ)..1,
        ((p : ℂ) * Complex.exp (-((Real.log p : ℂ) * (x : ℂ))))) ≠
      (1 : ℂ) / (Real.log p : ℂ) := by
  intro h
  have hpgt : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have htwo := (connesConsaniLemma33_printed_zeroCoefficient_iff hpgt).mp h
  exact hp (by exact_mod_cast htwo)

end

end RHTower
