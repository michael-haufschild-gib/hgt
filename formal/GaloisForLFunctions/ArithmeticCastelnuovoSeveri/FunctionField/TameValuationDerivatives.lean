import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Tactic.Linarith

/-!
# Tame orders under an integral local derivation

A valuation-ring derivation sending a uniformizer to one lowers a
positive order by exactly one when that order is a valuation unit.
Writing the function as a unit times a uniformizer power separates the
leading derivative term from the term differentiating the unit.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Nonzero constants have value one whenever the valuation ring contains their field. -/
theorem valuation_constant_eq_one_of_constants_mem
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (hK : ∀ a : K, v (algebraMap K L a) ≤ 1) (a : K) (ha : a ≠ 0) :
    v (algebraMap K L a) = 1 := by
  apply le_antisymm (hK a)
  have hprod : v (algebraMap K L a) * v (algebraMap K L a⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
  calc
    1 = v (algebraMap K L a) * v (algebraMap K L a⁻¹) := hprod.symm
    _ ≤ v (algebraMap K L a) * 1 := mul_le_mul_of_nonneg_left (hK a⁻¹) zero_le
    _ = v (algebraMap K L a) := mul_one _

/-- An integral local derivation lowers every positive tame order by exactly one. -/
theorem valuation_derivation_of_tame_order
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (D : Derivation K L L)
    (π : L) (hπ : v π = WithZero.exp (-1 : ℤ)) (hDπ : D π = 1)
    (hD : ∀ u : L, v u ≤ 1 → v (D u) ≤ 1)
    (x : L) (e : ℕ) (he : 0 < e) (hx : v x = WithZero.exp (-(e : ℤ)))
    (htame : v (e : L) = 1) :
    v (D x) = WithZero.exp (-((e - 1 : ℕ) : ℤ)) := by
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hp : v (π ^ e) = WithZero.exp (-(e : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
  let u := x / π ^ e
  have hu : v u = 1 := by
    rw [show u = x / π ^ e from rfl, map_div₀, hx, hp, div_self WithZero.exp_ne_zero]
  have hDu : v (D u) ≤ 1 := hD u hu.le
  have hrep : x = π ^ e * u := by
    dsimp only [u]
    rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ hπ0), mul_one]
  have hDx : D x = u * (e : L) * π ^ (e - 1) + π ^ e * D u := by
    have h := congrArg D hrep
    rw [D.leibniz, D.leibniz_pow, hDπ] at h
    simpa only [smul_eq_mul, nsmul_eq_mul, mul_one, mul_assoc, add_comm] using h
  have hlead : v (u * (e : L) * π ^ (e - 1)) = WithZero.exp (-((e - 1 : ℕ) : ℤ)) := by
    rw [map_mul, map_mul, hu, htame, one_mul, one_mul, map_pow, hπ,
      ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
  have htail : v (π ^ e * D u) ≤ WithZero.exp (-(e : ℤ)) := by
    rw [map_mul, hp]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hDu
      zero_le
  have hexp : WithZero.exp (-(e : ℤ)) < WithZero.exp (-((e - 1 : ℕ) : ℤ)) := by
    rw [WithZero.exp_lt_exp]
    have hcast : ((e - 1 : ℕ) : ℤ) + 1 = e := by exact_mod_cast Nat.sub_add_cancel he
    omega
  rw [hDx, v.map_add_eq_of_lt_left (htail.trans_lt (by rw [hlead]; exact hexp)), hlead]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
