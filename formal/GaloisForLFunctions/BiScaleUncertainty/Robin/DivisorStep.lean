import GaloisForLFunctions.BiScaleUncertainty.Robin.LocalDivisorGain

/-!
# Exact improvement criterion for the normalized divisor sum

Multiplicativity cancels every unchanged Euler factor. Increasing the
valuation of a prime improves `σ(n)/(n log log n)` precisely when its
logarithm lies below the unique step threshold. The criterion applies to
every integer in the stated range, with no extremality assumption.
-/

noncomputable section

open ArithmeticFunction RHTower

namespace GaloisForLFunctions.BiScaleUncertainty.Robin

private theorem sigma_div_prime_pow_mul (p : Nat.Primes) (v m : ℕ)
    (hcop : (p : ℕ).Coprime m) :
    ((sigma 1 ((p : ℕ) ^ v * m) : ℕ) : ℝ) / ((p : ℕ) ^ v * m) =
      robinLocal p v * (((sigma 1 m : ℕ) : ℝ) / m) := by
  rw [(isMultiplicative_sigma (k := 1)).map_mul_of_coprime (hcop.pow_left v)]
  push_cast
  rw [mul_div_mul_comm, sigma_prime_pow_div p.property]
  rfl

/-- Zimov's crossing criterion for the actual divisor sum, with all local factors evaluated. -/
theorem normalized_divisor_step_iff (p : Nat.Primes) (v m : ℕ)
    (hm : 0 < m) (hcop : (p : ℕ).Coprime m)
    (hL : 1 < Real.log (((p : ℕ) ^ v * m : ℕ) : ℝ)) :
    (((sigma 1 ((p : ℕ) ^ v * m) : ℕ) : ℝ) / ((p : ℕ) ^ v * m)) /
        Real.log (Real.log (((p : ℕ) ^ v * m : ℕ) : ℝ)) <
      (((sigma 1 ((p : ℕ) ^ (v + 1) * m) : ℕ) : ℝ) / ((p : ℕ) ^ (v + 1) * m)) /
        Real.log (Real.log (((p : ℕ) ^ (v + 1) * m : ℕ) : ℝ)) ↔
      Real.log (p : ℕ) < stepThreshold v (Real.log (((p : ℕ) ^ v * m : ℕ) : ℝ)) := by
  let L : ℝ := Real.log (((p : ℕ) ^ v * m : ℕ) : ℝ)
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlogp : 0 < Real.log ((p : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hnext : Real.log (((p : ℕ) ^ (v + 1) * m : ℕ) : ℝ) = L + Real.log (p : ℕ) := by
    have heq : ((p : ℕ) ^ (v + 1) * m : ℕ) = ((p : ℕ) ^ v * m) * (p : ℕ) := by
      rw [pow_succ]; ring
    rw [heq, Nat.cast_mul, Real.log_mul (by positivity) hp0.ne']
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hlogNext : 0 < Real.log (L + Real.log (p : ℕ)) :=
    Real.log_pos (by dsimp [L]; linarith only [hL, hlogp])
  have hσ : 0 < ((sigma 1 m : ℕ) : ℝ) := by
    exact_mod_cast sigma_pos 1 m (Nat.ne_of_gt hm)
  have hC : 0 < ((sigma 1 m : ℕ) : ℝ) / m := div_pos hσ hm0
  rw [sigma_div_prime_pow_mul p v m hcop, sigma_div_prime_pow_mul p (v + 1) m hcop,
    hnext, div_lt_div_iff₀ hlogL hlogNext]
  have hcrit := robinLocal_ratio_gt_iff p v hL
  rw [div_lt_div_iff₀ hlogL (robinLocal_pos p.property v)] at hcrit
  change _ ↔ Real.log (p : ℕ) < stepThreshold v L at hcrit ⊢
  rw [← hcrit]
  constructor <;> intro h
  · exact (mul_lt_mul_left hC).mp (by nlinarith only [h])
  · have hmul := (mul_lt_mul_left hC).mpr h
    nlinarith only [hmul]

#print axioms normalized_divisor_step_iff
#print axioms stepThreshold_succ_lt
#print axioms robinLocal_ratio_succ_lt
#print axioms robinLocal_strict_logConcave

end GaloisForLFunctions.BiScaleUncertainty.Robin
