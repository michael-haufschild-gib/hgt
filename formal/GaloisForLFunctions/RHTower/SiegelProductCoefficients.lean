import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Nonnegative coefficients of `ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)`

For quadratic Dirichlet characters `χ₁`, `χ₂` the Dirichlet series
`ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)` (the Dedekind zeta function of a biquadratic field, up to
finitely many Euler factors) has nonnegative coefficients.  This is the positivity input of
Siegel's lower bound for `L(1, χ)`.

With `b = 1 ⋆ χ₁` the coefficients are `a = b ⋆ (χ₂ · b)` (`siegelCoeff`), because `χ₂` is
completely multiplicative.  The same function is `b' ⋆ (χ₁ · b')` with `b' = 1 ⋆ χ₂`
(`siegelCoeff_comm`).  At a prime power `p^k`,
`a(p^k) = ∑_{i ≤ k} b(p^i) χ₂(p)^{k−i} b(p^{k−i})`, where `b(p^i) = ∑_{t ≤ i} χ₁(p)^t ≥ 0`.  Every term
is nonnegative unless `χ₂(p) = −1` and `χ₁(p) ≠ −1`; in that case every term of the swapped
representation is nonnegative.  When `χ₁(p) = χ₂(p) = −1` the odd-index values `b(p^{k−i})` vanish.
-/

open ArithmeticFunction

noncomputable section

namespace RHTower

variable {N₁ N₂ : ℕ}

/-- `(f ⋆ g)(p^k) = ∑_{i ≤ k} f(p^i) g(p^{k−i})`. -/
lemma mul_apply_prime_pow {R : Type*} [CommSemiring R] (f g : ArithmeticFunction R) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hi) hp.pos]

/-- The twist `n ↦ χ(n) f(n)`. -/
def charTwist (χ : DirichletCharacter ℂ N₂) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  (toArithmeticFunction (χ ·)).pmul f

lemma charTwist_apply (χ : DirichletCharacter ℂ N₂) (f : ArithmeticFunction ℂ) {n : ℕ}
    (hn : n ≠ 0) : charTwist χ f n = χ n * f n := by
  simp [charTwist, pmul_apply, toArithmeticFunction, hn]

/-- The coefficients of `ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)`: `(1 ⋆ χ₁) ⋆ (χ₂ · (1 ⋆ χ₁))`. -/
def siegelCoeff (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    ArithmeticFunction ℂ :=
  χ₁.zetaMul * charTwist χ₂ χ₁.zetaMul

/-- `χ₂ · (1 ⋆ χ₁) = χ₂ ⋆ (χ₁ χ₂)`. -/
lemma charTwist_zetaMul (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    charTwist χ₂ χ₁.zetaMul
      = toArithmeticFunction (χ₂ ·) * toArithmeticFunction (fun n : ℕ => χ₁ n * χ₂ n) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [charTwist_apply χ₂ _ hn, DirichletCharacter.zetaMul, coe_zeta_mul_apply, mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b => toArithmeticFunction (χ₂ ·) a
      * toArithmeticFunction (fun n : ℕ => χ₁ n * χ₂ n) b), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hnd : n / d ≠ 0 := by
    have := Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
    omega
  have hmul : n / d * d = n := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  simp only [toArithmeticFunction, coe_mk, hd0, hnd, if_false]
  have : (χ₂ (n : ZMod N₂)) = χ₂ ((n / d : ℕ) : ZMod N₂) * χ₂ (d : ZMod N₂) := by
    rw [← map_mul, ← Nat.cast_mul, hmul]
  rw [this]
  ring

/-- The symmetric representation `(1 ⋆ χ₂) ⋆ (χ₁ · (1 ⋆ χ₂))`. -/
lemma siegelCoeff_comm (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    siegelCoeff χ₁ χ₂ = siegelCoeff χ₂ χ₁ := by
  unfold siegelCoeff
  rw [charTwist_zetaMul, charTwist_zetaMul, DirichletCharacter.zetaMul,
    DirichletCharacter.zetaMul]
  have h : toArithmeticFunction (fun n : ℕ => χ₂ n * χ₁ n)
      = toArithmeticFunction (fun n : ℕ => χ₁ n * χ₂ n) := by
    congr 1; funext n; ring
  rw [h]
  ring

lemma isMultiplicative_charTwist (χ : DirichletCharacter ℂ N₂) {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) : (charTwist χ f).IsMultiplicative :=
  (DirichletCharacter.isMultiplicative_toArithmeticFunction χ).pmul hf

lemma isMultiplicative_siegelCoeff (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) : (siegelCoeff χ₁ χ₂).IsMultiplicative :=
  χ₁.isMultiplicative_zetaMul.mul (isMultiplicative_charTwist χ₂ χ₁.isMultiplicative_zetaMul)

open scoped ComplexOrder

/-- The prime-power expansion of the coefficients. -/
lemma siegelCoeff_prime_pow (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    siegelCoeff χ₁ χ₂ (p ^ k) = ∑ i ∈ Finset.range (k + 1),
      χ₁.zetaMul (p ^ i) * (χ₂ (p : ZMod N₂) ^ (k - i) * χ₁.zetaMul (p ^ (k - i))) := by
  rw [siegelCoeff, mul_apply_prime_pow _ _ hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [charTwist_apply χ₂ _ (pow_ne_zero _ hp.ne_zero), Nat.cast_pow, map_pow χ₂]

/-- `(1 ⋆ χ)(p^i) = ∑_{t ≤ i} χ(p)^t`. -/
lemma zetaMul_prime_pow_eq (χ : DirichletCharacter ℂ N₁) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    χ.zetaMul (p ^ i) = ∑ t ∈ Finset.range (i + 1), χ (p : ZMod N₁) ^ t := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, if_false,
    Nat.cast_pow, map_pow]

/-- Every term of the prime-power expansion is nonnegative unless `χ₂(p) = −1 ≠ χ₁(p)`. -/
lemma siegelCoeff_terms_nonneg {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hcase : χ₂ (p : ZMod N₂) ≠ -1 ∨ χ₁ (p : ZMod N₁) = -1) (k i : ℕ) :
    0 ≤ χ₁.zetaMul (p ^ i) * (χ₂ (p : ZMod N₂) ^ (k - i) * χ₁.zetaMul (p ^ (k - i))) := by
  have hb : ∀ j, 0 ≤ χ₁.zetaMul (p ^ j) := fun j =>
    DirichletCharacter.zetaMul_prime_pow_nonneg h₁ hp j
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr h₂ p with hv | hv | hv
  · -- χ₂(p) = 0
    rw [hv]
    rcases Nat.eq_zero_or_pos (k - i) with h0 | h0
    · rw [h0, pow_zero, one_mul]; exact mul_nonneg (hb _) (hb _)
    · rw [zero_pow h0.ne', zero_mul, mul_zero]
  · -- χ₂(p) = 1
    rw [hv, one_pow, one_mul]; exact mul_nonneg (hb _) (hb _)
  · -- χ₂(p) = −1, so χ₁(p) = −1 and the odd-index values vanish
    have hu : χ₁ (p : ZMod N₁) = -1 := by
      rcases hcase with h | h
      · exact absurd hv h
      · exact h
    rw [hv]
    rcases Nat.even_or_odd (k - i) with he | ho
    · rw [he.neg_one_pow, one_mul]; exact mul_nonneg (hb _) (hb _)
    · have hz : χ₁.zetaMul (p ^ (k - i)) = 0 := by
        rw [zetaMul_prime_pow_eq χ₁ hp, hu, neg_one_geom_sum, if_pos (by
          rcases ho with ⟨m, hm⟩; exact ⟨m + 1, by omega⟩)]
      rw [hz, mul_zero, mul_zero]

/-- The coefficients of `ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)` are nonnegative at prime powers. -/
lemma siegelCoeff_prime_pow_nonneg {χ₁ : DirichletCharacter ℂ N₁}
    {χ₂ : DirichletCharacter ℂ N₂} (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (k : ℕ) : 0 ≤ siegelCoeff χ₁ χ₂ (p ^ k) := by
  by_cases hcase : χ₂ (p : ZMod N₂) ≠ -1 ∨ χ₁ (p : ZMod N₁) = -1
  · rw [siegelCoeff_prime_pow χ₁ χ₂ hp]
    exact Finset.sum_nonneg fun i _ => siegelCoeff_terms_nonneg h₁ h₂ hp hcase k i
  · -- swap the two characters
    rw [not_or, not_not] at hcase
    rw [siegelCoeff_comm, siegelCoeff_prime_pow χ₂ χ₁ hp]
    exact Finset.sum_nonneg fun i _ =>
      siegelCoeff_terms_nonneg h₂ h₁ hp (Or.inr hcase.1) k i

/-- **Positivity.**  For quadratic characters `χ₁`, `χ₂`, every coefficient of
`ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)` is a nonnegative real number. -/
theorem siegelCoeff_nonneg {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (n : ℕ) : 0 ≤ siegelCoeff χ₁ χ₂ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [(isMultiplicative_siegelCoeff χ₁ χ₂).multiplicative_factorization _ hn]
    exact Finset.prod_nonneg fun p hp =>
      siegelCoeff_prime_pow_nonneg h₁ h₂ (Nat.prime_of_mem_primeFactors hp) _

end RHTower
