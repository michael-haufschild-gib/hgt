import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Complex extension of the integer prime-carry laws

The elementary Fermat-quotient operation `(z - z^p) / p` obeys the nonlinear
addition and multiplication carry laws on the whole complex plane, simultaneously
for every prime. Its restriction to the integers is integer-valued, by Fermat's
little theorem. Reconstructing `z^p + p * delta p z` gives the identity map.

Thus these laws, including their exact integer restriction and all prime indices,
do not impose a locus on a complex input. In particular, infinitude of the family
does not change that conclusion. This is an elementary source-model countertest,
not an RH theorem or an exclusion of arithmetic differential geometry equipped
with additional integral-completion conditions.
-/

namespace GaloisForLFunctions.HTGeometry.IntegerPrimeCarry

noncomputable def delta (p : Nat.Primes) (z : ℂ) : ℂ :=
  (z - z ^ (p : ℕ)) / (p : ℕ)

noncomputable def carry (p : Nat.Primes) (z w : ℂ) : ℂ :=
  (z ^ (p : ℕ) + w ^ (p : ℕ) - (z + w) ^ (p : ℕ)) / (p : ℕ)

private theorem prime_cast_ne_zero (p : Nat.Primes) : ((p : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast p.property.ne_zero

theorem delta_add (p : Nat.Primes) (z w : ℂ) :
    delta p (z + w) = delta p z + delta p w + carry p z w := by
  unfold delta carry
  field_simp [prime_cast_ne_zero p]
  ring

theorem delta_mul (p : Nat.Primes) (z w : ℂ) :
    delta p (z * w) = z ^ (p : ℕ) * delta p w +
      w ^ (p : ℕ) * delta p z + (p : ℕ) * delta p z * delta p w := by
  unfold delta
  rw [mul_pow]
  field_simp [prime_cast_ne_zero p]
  ring

theorem reconstructed_frobenius (p : Nat.Primes) (z : ℂ) :
    z ^ (p : ℕ) + (p : ℕ) * delta p z = z := by
  unfold delta
  field_simp [prime_cast_ne_zero p]
  ring

theorem delta_preserves_integers (p : Nat.Primes) (n : ℤ) :
    ∃ m : ℤ, delta p n = m := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
  have hz : ((n - n ^ (p : ℕ) : ℤ) : ZMod (p : ℕ)) = 0 := by
    push_cast
    rw [ZMod.pow_card]
    ring
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (n - n ^ (p : ℕ)) (p : ℕ)).mp hz
  refine ⟨m, ?_⟩
  unfold delta
  apply (div_eq_iff (prime_cast_ne_zero p)).2
  have hm' : (n : ℂ) - (n : ℂ) ^ (p : ℕ) = ((p : ℕ) : ℂ) * (m : ℂ) := by
    exact_mod_cast hm
  simpa only [mul_comm] using hm'

/-- One exact, integer-preserving model on all complex inputs and all primes. -/
theorem all_prime_carry_laws_on_complex_plane :
    ∃ d : Nat.Primes → ℂ → ℂ,
      (∀ p : Nat.Primes, d p 1 = 0) ∧
      (∀ (p : Nat.Primes) z w, d p (z + w) = d p z + d p w + carry p z w) ∧
      (∀ (p : Nat.Primes) z w, d p (z * w) = z ^ (p : ℕ) * d p w +
        w ^ (p : ℕ) * d p z + (p : ℕ) * d p z * d p w) ∧
      (∀ (p : Nat.Primes) (n : ℤ), ∃ m : ℤ, d p n = m) ∧
      (∀ (p : Nat.Primes) z, z ^ (p : ℕ) + (p : ℕ) * d p z = z) := by
  exact ⟨delta, by simp [delta], delta_add, delta_mul,
    delta_preserves_integers, reconstructed_frobenius⟩

end GaloisForLFunctions.HTGeometry.IntegerPrimeCarry
