import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SmallDivisorIntegrality

/-!
# Reduced power orders under ramification

If an `N`th power has order `e m` with `m<N`, its root has an
integral order strictly below `e`. Dividing a differential coefficient
of order `e-1` by this root therefore leaves a nonnegative order below `e`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A reduced power divisor gives a root order strictly below the ramification index. -/
theorem valuation_order_lt_of_power_order {L : Type*} [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (u : L) (N e m : ℕ)
    (he : 0 < e) (hm : m < N)
    (hu : v (u ^ N) = WithZero.exp (-((e * m : ℕ) : ℤ))) :
    ∃ a : ℕ, a < e ∧ N * a = e * m ∧ v u = WithZero.exp (-(a : ℤ)) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hm
  have hu0 : v u ≠ 0 := by
    intro h
    rw [map_pow, h, zero_pow (Nat.ne_zero_of_lt hN)] at hu
    exact WithZero.exp_ne_zero hu.symm
  have hl := congrArg WithZero.log hu
  rw [map_pow, WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul, Nat.cast_mul] at hl
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hem : (0 : ℤ) ≤ (e : ℤ) * m := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hnonpos : WithZero.log (v u) ≤ 0 := by
    nlinarith only [hl, hN', hem]
  let a := (-WithZero.log (v u)).toNat
  have ha : (a : ℤ) = -WithZero.log (v u) := by omega
  have horder : N * a = e * m := by
    apply Int.natCast_inj.mp
    push_cast
    rw [ha]
    nlinarith only [hl]
  have halt : a < e := by
    have hlt := Nat.mul_lt_mul_of_pos_left hm he
    rw [← horder, Nat.mul_comm e N] at hlt
    exact (Nat.mul_lt_mul_left hN).mp hlt
  refine ⟨a, halt, horder, ?_⟩
  rw [ha, neg_neg, WithZero.exp_log hu0]

/-- A tame differential coefficient divided by a reduced radical stays integral, with order below ramification. -/
theorem valuation_div_reduced_power_order {L : Type*} [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (t u : L) (N e m : ℕ)
    (he : 0 < e) (hm : m < N)
    (hu : v (u ^ N) = WithZero.exp (-((e * m : ℕ) : ℤ)))
    (ht : v t = WithZero.exp (-((e - 1 : ℕ) : ℤ))) :
    ∃ k : ℕ, k < e ∧ v (t / u) = WithZero.exp (-(k : ℤ)) := by
  obtain ⟨a, ha, _, hva⟩ := valuation_order_lt_of_power_order v u N e m he hm hu
  refine ⟨e - 1 - a, by omega, ?_⟩
  rw [map_div₀, ht, hva, ← WithZero.exp_sub]
  congr 1
  omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
