import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Polynomial rigidity behind the Fujiki radical

A power of exponent at least two has degree at most one precisely when its base
is constant. Applied to the restriction of a quadratic form to an affine line,
this detects its radical. This is the algebraic mechanism of Lemma 5.2 of
Kurnosov–Ríos Ortiz, https://arxiv.org/abs/2611.01210.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Degree at most the exponent means that the base polynomial is affine. -/
theorem power_natDegree_le_exponent_iff (p : R[X]) (n : ℕ) :
    (p ^ (n + 1)).natDegree ≤ n + 1 ↔ p.natDegree ≤ 1 := by
  rw [natDegree_pow]
  constructor
  · intro h
    by_contra hp
    have htwo : 2 ≤ p.natDegree := by omega
    have := Nat.mul_le_mul_left (n + 1) htwo
    omega
  · intro h
    simpa only [mul_one] using Nat.mul_le_mul_left (n + 1) h

/-- Below its exponent, a polynomial power has only a constant base. -/
theorem power_natDegree_lt_exponent_iff (p : R[X]) (n : ℕ) :
    (p ^ (n + 1)).natDegree < n + 1 ↔ p.natDegree = 0 := by
  rw [natDegree_pow]
  constructor
  · intro h
    by_contra hp
    have hpos : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hp
    have := Nat.mul_le_mul_left (n + 1) hpos
    omega
  · intro h
    simp only [h, mul_zero, Nat.zero_lt_succ]

/-- A nonconstant polynomial cannot acquire affine degree by taking a higher power. -/
theorem power_natDegree_le_one_iff (p : R[X]) (n : ℕ) :
    (p ^ (n + 2)).natDegree ≤ 1 ↔ p.natDegree = 0 := by
  rw [natDegree_pow]
  constructor
  · intro h
    by_contra hp
    have hpos : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hp
    have := Nat.mul_le_mul_left (n + 2) hpos
    omega
  · intro h
    simp only [h, mul_zero, zero_le]

/-- The quadratic and linear coefficients both vanish when a quadratic power is affine. -/
theorem quadratic_power_affine_iff (a b c : R) (n : ℕ) :
    ((C a + C b * X + C c * X ^ 2) ^ (n + 2)).natDegree ≤ 1 ↔
      b = 0 ∧ c = 0 := by
  rw [power_natDegree_le_one_iff]
  constructor
  · intro h
    have h₁ := coeff_eq_zero_of_natDegree_lt (p := C a + C b * X + C c * X ^ 2)
      (n := 1) (by omega)
    have h₂ := coeff_eq_zero_of_natDegree_lt (p := C a + C b * X + C c * X ^ 2)
      (n := 2) (by omega)
    simpa using And.intro h₁ h₂
  · rintro ⟨rfl, rfl⟩
    simp

/-- The same coefficient rigidity holds at every degree below the power exponent. -/
theorem quadratic_power_degree_lt_exponent_iff (a b c : R) (n : ℕ) :
    ((C a + C b * X + C c * X ^ 2) ^ (n + 1)).natDegree < n + 1 ↔
      b = 0 ∧ c = 0 := by
  rw [power_natDegree_lt_exponent_iff, ← power_natDegree_le_one_iff _ 0]
  exact quadratic_power_affine_iff a b c 0

/-- At the exponent threshold only the quadratic coefficient must vanish. -/
theorem quadratic_power_degree_le_exponent_iff (a b c : R) (n : ℕ) :
    ((C a + C b * X + C c * X ^ 2) ^ (n + 1)).natDegree ≤ n + 1 ↔ c = 0 := by
  rw [power_natDegree_le_exponent_iff]
  constructor
  · intro h
    have hc := coeff_eq_zero_of_natDegree_lt (p := C a + C b * X + C c * X ^ 2)
      (n := 2) (by omega)
    simpa using hc
  · rintro rfl
    simp only [map_zero, zero_mul, add_zero]
    exact (natDegree_add_le _ _).trans
      (max_le (by simp) (natDegree_mul_le.trans (by simp)))

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- Restriction of a quadratic form to `x + t • h`, as a polynomial in `t`. -/
def quadraticLine (q : QuadraticForm R V) (x h : V) : R[X] :=
  C (q x) + C (q.polarBilin x h) * X + C (q h) * X ^ 2

/-- The weak degree threshold detects isotropy, independently of the base point. -/
theorem quadraticLine_isotropic_iff (q : QuadraticForm R V) (x h : V) (n : ℕ) :
    ((quadraticLine q x h) ^ (n + 1)).natDegree ≤ n + 1 ↔ q h = 0 :=
  quadratic_power_degree_le_exponent_iff _ _ _ _

theorem quadraticLine_power_affine_iff (q : QuadraticForm R V) (x h : V) (n : ℕ) :
    ((quadraticLine q x h) ^ (n + 2)).natDegree ≤ 1 ↔
      q.polarBilin x h = 0 ∧ q h = 0 :=
  quadratic_power_affine_iff _ _ _ _

/-- The complete affine-line test detects exactly the quadratic radical. -/
theorem quadraticLine_radical_iff (q : QuadraticForm R V) (h : V) (n : ℕ) :
    (∀ x, ((quadraticLine q x h) ^ (n + 2)).natDegree ≤ 1) ↔
      q h = 0 ∧ ∀ x, q.polarBilin x h = 0 := by
  simp only [quadraticLine_power_affine_iff]
  exact ⟨fun H => ⟨(H 0).2, fun x => (H x).1⟩,
    fun H x => ⟨H.2 x, H.1⟩⟩

/-- A degree bound below the Fujiki exponent detects the same radical. -/
theorem quadraticLine_degree_threshold_iff (q : QuadraticForm R V) (h : V) (n : ℕ) :
    (∀ x, ((quadraticLine q x h) ^ (n + 1)).natDegree < n + 1) ↔
      q h = 0 ∧ ∀ x, q.polarBilin x h = 0 := by
  simp only [quadraticLine, quadratic_power_degree_lt_exponent_iff]
  exact ⟨fun H => ⟨(H 0).2, fun x => (H x).1⟩,
    fun H x => ⟨H.2 x, H.1⟩⟩

#print axioms quadratic_power_affine_iff
#print axioms quadraticLine_isotropic_iff
#print axioms quadraticLine_radical_iff
#print axioms quadraticLine_degree_threshold_iff
end GaloisForLFunctions.HodgeTheoryWithoutVarieties
