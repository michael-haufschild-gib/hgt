import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinWhittakerArithmeticEnvelope

/-!
# Hecke relation for the Eisenstein Whittaker coefficients

The arithmetic coefficient of the nonconstant Fourier terms of the completed Eisenstein series is
`W_u(n) = n^u Σ_{d ∣ n} d^{-2u}`.  Writing `n = p^k m` with `p ∤ m`, the divisor sum factors over
the coprime parts and its `p`-part is a geometric sum in `p^{-2u}`.  This gives the Hecke relation

`W_u(pn) + 1_{p ∣ n} W_u(n/p) = (p^u + p^{-u}) W_u(n)`

for every prime `p` and every `n ≥ 1`, the arithmetic input of the Hecke eigen-equation
`T_p E_u = (p^u + p^{-u}) E_u` of the Eisenstein line model.
-/

open ArithmeticFunction Finset

namespace RHTower

noncomputable section

/-- The power function `n ↦ n^s` as an arithmetic function. -/
def cpowArithmetic (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n : ℂ) ^ s, by simp⟩

theorem cpowArithmetic_apply (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    cpowArithmetic s n = (n : ℂ) ^ s := by
  simp [cpowArithmetic, hn]

theorem natCast_mul_cpow' (a b : ℕ) (s : ℂ) :
    ((a * b : ℕ) : ℂ) ^ s = (a : ℂ) ^ s * (b : ℂ) ^ s := by
  have h := Complex.mul_cpow_ofReal_nonneg (a := (a : ℝ)) (b := (b : ℝ)) (by positivity)
    (by positivity) s
  simpa using h

theorem isMultiplicative_cpowArithmetic (s : ℂ) : (cpowArithmetic s).IsMultiplicative := by
  refine ⟨by simp [cpowArithmetic], ?_⟩
  intro m n _
  by_cases hm : m = 0
  · subst hm
    simp [cpowArithmetic]
  by_cases hn : n = 0
  · subst hn
    simp [cpowArithmetic]
  rw [cpowArithmetic_apply s (mul_ne_zero hm hn), cpowArithmetic_apply s hm,
    cpowArithmetic_apply s hn]
  exact natCast_mul_cpow' m n s

/-- The complex divisor power sum `Σ_{d ∣ n} d^s`. -/
def divisorPowerSum (s : ℂ) (n : ℕ) : ℂ := ∑ d ∈ n.divisors, (d : ℂ) ^ s

theorem divisorPowerSum_eq_zeta_mul (s : ℂ) (n : ℕ) :
    divisorPowerSum s n =
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) *
        cpowArithmetic s) n := by
  rw [coe_zeta_mul_apply]
  unfold divisorPowerSum
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [cpowArithmetic_apply s (Nat.pos_of_mem_divisors hd).ne']

theorem divisorPowerSum_mul_coprime (s : ℂ) {a b : ℕ} (hab : a.Coprime b) :
    divisorPowerSum s (a * b) = divisorPowerSum s a * divisorPowerSum s b := by
  rw [divisorPowerSum_eq_zeta_mul, divisorPowerSum_eq_zeta_mul, divisorPowerSum_eq_zeta_mul]
  exact (isMultiplicative_zeta.natCast.mul (isMultiplicative_cpowArithmetic s)).map_mul_of_coprime
    hab

/-- The truncated geometric sum `Σ_{j ≤ k} Q^j`. -/
def geomSumTo (Q : ℂ) (k : ℕ) : ℂ := ∑ j ∈ range (k + 1), Q ^ j

theorem geomSumTo_succ (Q : ℂ) (k : ℕ) : geomSumTo Q (k + 1) = geomSumTo Q k + Q ^ (k + 1) := by
  unfold geomSumTo
  rw [Finset.sum_range_succ]

theorem geomSumTo_zero (Q : ℂ) : geomSumTo Q 0 = 1 := by
  simp [geomSumTo]

theorem divisorPowerSum_prime_pow (s : ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divisorPowerSum s (p ^ k) = geomSumTo ((p : ℂ) ^ s) k := by
  unfold divisorPowerSum geomSumTo
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  exact natCast_pow_cpow p j s

/-- The Eisenstein Whittaker coefficient `n^u Σ_{d ∣ n} d^{-2u}` in raw form. -/
def whittakerCoeff (u : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ u * divisorPowerSum (-2 * u) n

theorem whittakerCoeff_eq (u : ℂ) (n : D4BMPositiveIndex) :
    d4BMCompletedEisensteinWhittakerCoefficient u n = whittakerCoeff u n.1 := rfl

theorem whittakerCoeff_prime_pow_mul (u : ℂ) {p : ℕ} (hp : p.Prime) {m : ℕ} (hpm : ¬ p ∣ m)
    (j : ℕ) :
    whittakerCoeff u (p ^ j * m) =
      ((p : ℂ) ^ u) ^ j * (m : ℂ) ^ u *
        (geomSumTo ((p : ℂ) ^ (-2 * u)) j * divisorPowerSum (-2 * u) m) := by
  have hcop : (p ^ j).Coprime m :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  unfold whittakerCoeff
  rw [natCast_mul_cpow', natCast_pow_cpow, divisorPowerSum_mul_coprime _ hcop,
    divisorPowerSum_prime_pow _ hp]

/-- **Hecke relation of the Whittaker coefficients.**  For every prime `p` and `n ≥ 1`,
`W_u(pn) + 1_{p ∣ n} W_u(n/p) = (p^u + p^{-u}) W_u(n)`. -/
theorem whittakerCoeff_hecke (u : ℂ) {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    whittakerCoeff u (p * n) + (if p ∣ n then whittakerCoeff u (n / p) else 0) =
      ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * whittakerCoeff u n := by
  obtain ⟨k, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set P : ℂ := (p : ℂ) ^ u with hP
  set Q : ℂ := (p : ℂ) ^ (-2 * u) with hQ
  set S : ℂ := divisorPowerSum (-2 * u) m with hS
  have hPQ : P * P * Q = 1 := by
    rw [hP, hQ, ← Complex.cpow_add _ _ hp0, ← Complex.cpow_add _ _ hp0,
      show u + u + -2 * u = 0 by ring, Complex.cpow_zero]
  have hneg : (p : ℂ) ^ (-u) = P * Q := by
    rw [hP, hQ, ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  have hW : ∀ j : ℕ, whittakerCoeff u (p ^ j * m) =
      P ^ j * (m : ℂ) ^ u * (geomSumTo Q j * S) := fun j =>
    whittakerCoeff_prime_pow_mul u hp hpm j
  have hmul : p * (p ^ k * m) = p ^ (k + 1) * m := by ring
  rw [hmul, hW (k + 1), hW k, hneg]
  cases k with
  | zero =>
      have hnd : ¬ p ∣ p ^ 0 * m := by simpa using hpm
      rw [if_neg hnd, geomSumTo_succ, geomSumTo_zero]
      ring
  | succ k' =>
      have hd : p ∣ p ^ (k' + 1) * m := ⟨p ^ k' * m, by ring⟩
      have hdiv : p ^ (k' + 1) * m / p = p ^ k' * m := by
        rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
      rw [if_pos hd, hdiv, hW k', geomSumTo_succ, geomSumTo_succ]
      linear_combination (-(P ^ k' * (m : ℂ) ^ u * (geomSumTo Q k' * S))) * hPQ

end

end RHTower
