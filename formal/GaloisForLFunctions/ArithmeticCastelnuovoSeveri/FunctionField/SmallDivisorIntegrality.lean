import Mathlib.RingTheory.DedekindDomain.AdicValuation


/-!
# Integrality from a small divisor

If all multiplicities of a divisor are below `N`, multiplying it by an
`N`th power cannot cancel a pole of that power's base. The Dedekind
valuation criterion therefore recovers membership in the original ring.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain

/-- An integral power product cannot conceal a pole when the other factor has order less than the power. -/
theorem valuation_le_one_of_power_mul_le_one {L : Type*} [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x b : L) (N m : ℕ)
    (hm : m < N) (hb : v b = WithZero.exp (-(m : ℤ)))
    (hx : v (x ^ N * b) ≤ 1) : v x ≤ 1 := by
  by_cases hx0 : v x = 0
  · rw [hx0]
    exact zero_le
  rw [map_mul, map_pow, hb, ← WithZero.exp_log hx0, ← WithZero.exp_nsmul,
    ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp, nsmul_eq_mul] at hx
  rw [← WithZero.exp_log hx0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  have hm' : (m : ℤ) < N := by exact_mod_cast hm
  by_contra h
  have hlog : 1 ≤ WithZero.log (v x) := by omega
  have hN : (0 : ℤ) < N := by omega
  have hprod : (N : ℤ) ≤ (N : ℤ) * WithZero.log (v x) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hN.le
  linarith only [hx, hm', hprod]

/-- A fraction whose power times a divisor of multiplicities below that power is integral already belongs to the base. -/
theorem mem_fractionRing_base_of_power_mul_mem
    {A L : Type*} [CommRing A] [IsDedekindDomain A] [Field L]
    [Algebra A L] [IsFractionRing A L] (x : L) (b : A) (N : ℕ)
    (hb : ∀ v : HeightOneSpectrum A, ∃ m : ℕ, m < N ∧
      v.valuation L (algebraMap A L b) = WithZero.exp (-(m : ℤ)))
    (hx : x ^ N * algebraMap A L b ∈ (algebraMap A L).range) :
    x ∈ (algebraMap A L).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one L x
  intro v
  obtain ⟨m, hm, hv⟩ := hb v
  apply valuation_le_one_of_power_mul_le_one (v.valuation L) x (algebraMap A L b) N m hm hv
  obtain ⟨a, ha⟩ := hx
  rw [← ha]
  exact v.valuation_le_one a

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
