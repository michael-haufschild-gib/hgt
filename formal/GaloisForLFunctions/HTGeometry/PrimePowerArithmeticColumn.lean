import GaloisForLFunctions.HTGeometry.PrimePowerJacobianDeterminant
import GaloisForLFunctions.HTGeometry.FinitePrimeCoefficientField

/-!
# Prime-power arithmetic columns

The dilation layer indexed by `e` is represented by the arithmetic function supported at
`p^(e+1)`.  A prime-coordinate derivation lowers that support exactly one step and multiplies the
coefficient by `e+1`.  This is the arithmetic-function form of

`d/ds P_b((e+1)s+a) = -(e+1) P_{(log p)b(p)}((e+1)s+a)`.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

noncomputable section

/-- The prime selected by a witness that `n` is a `k`-th power of a prime. -/
def chosenPrimePowerBase (k n : ℕ)
    (h : ∃ p : Nat.Primes, n = (p : ℕ) ^ k) : Nat.Primes :=
  Classical.choose h

theorem chosenPrimePowerBase_spec (k n : ℕ)
    (h : ∃ p : Nat.Primes, n = (p : ℕ) ^ k) :
    n = (chosenPrimePowerBase k n h : ℕ) ^ k :=
  Classical.choose_spec h

/-- The arithmetic function carrying `a(p)` at `p^(e+1)` and vanishing elsewhere. -/
def arithmeticOfPrimePowerColumn (e : ℕ) (a : Nat.Primes → ℂ) : ArithmeticFunction ℂ := by
  classical
  exact
    { toFun := fun n => if h : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1) then
          a (chosenPrimePowerBase (e + 1) n h)
        else 0
      map_zero' := by
        rw [dif_neg]
        rintro ⟨p, hp⟩
        exact (pow_pos p.2.pos (e + 1)).ne' hp.symm }

/-- The chosen prime base is unique because the exponent is positive. -/
theorem chosenPrimePowerBase_eq (e : ℕ) (p : Nat.Primes)
    (h : ∃ q : Nat.Primes, (p : ℕ) ^ (e + 1) = (q : ℕ) ^ (e + 1)) :
    chosenPrimePowerBase (e + 1) ((p : ℕ) ^ (e + 1)) h = p := by
  apply Subtype.ext
  apply (Nat.pow_left_injective (Nat.succ_ne_zero e))
  exact (chosenPrimePowerBase_spec (e + 1) ((p : ℕ) ^ (e + 1)) h).symm

@[simp]
theorem arithmeticOfPrimePowerColumn_apply (e : ℕ) (a : Nat.Primes → ℂ)
    (p : Nat.Primes) :
    arithmeticOfPrimePowerColumn e a ((p : ℕ) ^ (e + 1)) = a p := by
  classical
  let h : ∃ q : Nat.Primes, (p : ℕ) ^ (e + 1) = (q : ℕ) ^ (e + 1) := ⟨p, rfl⟩
  change (if h' : ∃ q : Nat.Primes,
      (p : ℕ) ^ (e + 1) = (q : ℕ) ^ (e + 1) then
        a (chosenPrimePowerBase (e + 1) ((p : ℕ) ^ (e + 1)) h')
      else 0) = a p
  rw [dif_pos h]
  rw [chosenPrimePowerBase_eq e p h]

/-- Nonzero support is exactly contained in the `(e+1)`-st prime powers. -/
theorem arithmeticOfPrimePowerColumn_support (e : ℕ) (a : Nat.Primes → ℂ) {n : ℕ}
    (hn : arithmeticOfPrimePowerColumn e a n ≠ 0) :
    ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1) := by
  classical
  change (if h : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1) then
      a (chosenPrimePowerBase (e + 1) n h) else 0) ≠ 0 at hn
  by_cases hpow : ∃ p : Nat.Primes, n = (p : ℕ) ^ (e + 1)
  · exact hpow
  · rw [dif_neg hpow] at hn
    exact absurd rfl hn

/-- **Prime-power lowering law.**  The `q`-derivative of layer `e` is the point mass at `q^e`
with mass `(e+1)a(q)`. -/
theorem primeDeriv_arithmeticOfPrimePowerColumn
    (e : ℕ) (a : Nat.Primes → ℂ) (q : Nat.Primes) :
    primeDeriv q.1 (arithmeticOfPrimePowerColumn e a) =
      arithmeticPointMass ((q : ℕ) ^ e) (((e + 1 : ℕ) : ℂ) * a q) := by
  ext n
  rw [primeDeriv_apply]
  by_cases hn : n = (q : ℕ) ^ e
  · subst n
    have hmul : (q : ℕ) ^ e * q = (q : ℕ) ^ (e + 1) := by
      rw [pow_succ]
    rw [hmul, arithmeticOfPrimePowerColumn_apply]
    rw [arithmeticPointMass_apply_self (pow_ne_zero e q.2.ne_zero)]
    rw [Nat.Prime.factorization_pow q.2]
    simp
  · rw [arithmeticPointMass_apply_of_ne (pow_ne_zero e q.2.ne_zero) hn]
    by_cases hvalue : arithmeticOfPrimePowerColumn e a (n * q) = 0
    · rw [hvalue, mul_zero]
    · obtain ⟨p, hp⟩ := arithmeticOfPrimePowerColumn_support e a hvalue
      have hqdvd : (q : ℕ) ∣ (p : ℕ) ^ (e + 1) := by
        rw [← hp]
        exact ⟨n, by ring⟩
      have hpq : q = p := by
        apply Subtype.ext
        exact Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hqdvd
      subst p
      have hcancel : n = (q : ℕ) ^ e := by
        apply Nat.eq_of_mul_eq_mul_right q.2.pos
        calc
          n * q = (q : ℕ) ^ (e + 1) := hp
          _ = (q : ℕ) ^ e * q := by rw [pow_succ]
      exact absurd hcancel hn

/-- After embedding in the arithmetic-function fraction field, the same lowering law holds for
the extended prime derivations. -/
theorem primeFractionDerivation_arithmeticOfPrimePowerColumn
    (e : ℕ) (a : Nat.Primes → ℂ) (q : Nat.Primes) :
    primeFractionDerivation q
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimePowerColumn e a)) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticPointMass ((q : ℕ) ^ e) (((e + 1 : ℕ) : ℂ) * a q)) := by
  rw [primeFractionDerivation_algebraMap,
    primeDeriv_arithmeticOfPrimePowerColumn]

end

end GaloisForLFunctions.HTGeometry
