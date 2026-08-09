import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.IdentityWall

/-!
# Reflection orientation and the energy identities

Write `σ` for the reflection `q ↦ q⁻¹` of the universal monodromy line, and set

`E(q) = q + q⁻¹ - 2`,  `K(q) = q - q⁻¹`,  `E_M(q) = q^M + q^{-M} - 2`.

All the algebra is an identity in a commutative ring carrying a pair `q u` with `q u = 1`:

* `mul_reflEnergy` — `q E = (q-1)²`, hence `reflEnergy_eq` gives `E = u (q-1)² ∈ I²`;
* `mul_ambiCurvature_sq` — `q K² = (q+1)² E`;
* `ambiCurvature_sub_two_wall` — `K - 2(q-1) = -E`, so `K ≡ 2(q-1)` modulo `I²`;
* `monodromyRefl_wall_add_mem_sq` — `σ(q-1) + (q-1) = u(q-1)² ∈ I²`, i.e. reflection acts by `-1`
  on the conormal line `I/I²`;
* `span_reflEnergy_eq` — the equality of principal ideals `(E) = I²`.

The Laurent specialisation records the reflection invariance `σ(E) = E` and the corresponding
conormal statements on `R = k[q,q⁻¹]`.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

universe u

section Identities

variable {R : Type u} [CommRing R] {q v : R}

/-- The reflected two-leg energy `E = q + q⁻¹ - 2`. -/
def reflEnergy (q v : R) : R := q + v - 2

/-- The ambidexterity curvature `K = q - q⁻¹`. -/
def ambiCurvature (q v : R) : R := q - v

/-- `q E = (q-1)²`. -/
theorem mul_reflEnergy (h : q * v = 1) : q * reflEnergy q v = (q - 1) ^ 2 := by
  rw [reflEnergy]; linear_combination h

/-- `E = q⁻¹ (q-1)²`, so the energy lies in the square of the wall ideal. -/
theorem reflEnergy_eq (h : q * v = 1) : reflEnergy q v = (q - 1) ^ 2 * v := by
  rw [reflEnergy]; linear_combination (2 - q) * h

/-- `q K² = (q+1)² E`. -/
theorem mul_ambiCurvature_sq (h : q * v = 1) :
    q * ambiCurvature q v ^ 2 = (q + 1) ^ 2 * reflEnergy q v := by
  rw [ambiCurvature, reflEnergy]; linear_combination (-3 * q + v - 2) * h

/-- `K - 2(q-1) = -E`: the curvature is twice the wall equation modulo `I²`. -/
theorem ambiCurvature_sub_two_wall :
    ambiCurvature q v - 2 * (q - 1) = -reflEnergy q v := by
  rw [ambiCurvature, reflEnergy]; ring

/-- `(q+1) K = ... `: the curvature factors as `q⁻¹(q-1)(q+1)`. -/
theorem ambiCurvature_eq (h : q * v = 1) :
    ambiCurvature q v = (q - 1) * (q + 1) * v := by
  rw [ambiCurvature]; linear_combination (-q) * h

theorem reflEnergy_mem_sq (h : q * v = 1) :
    reflEnergy q v ∈ (Ideal.span {q - 1} : Ideal R) ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨v, reflEnergy_eq h⟩

/-- **The Fitting-energy identity, ideal form.**  `(E) = I²`. -/
theorem span_reflEnergy_eq (h : q * v = 1) :
    (Ideal.span {reflEnergy q v} : Ideal R) = (Ideal.span {q - 1} : Ideal R) ^ 2 := by
  have hv : IsUnit v := ⟨⟨v, q, by rw [mul_comm]; exact h, h⟩, rfl⟩
  rw [Ideal.span_singleton_pow, reflEnergy_eq h]
  exact Ideal.span_singleton_mul_right_unit hv _

/-- The rank-`M` central port energy `E_M = q^M + q^{-M} - 2`. -/
theorem mul_reflEnergy_pow (h : q * v = 1) (M : ℕ) :
    q ^ M * reflEnergy (q ^ M) (v ^ M) = (q ^ M - 1) ^ 2 :=
  mul_reflEnergy (by rw [← mul_pow, h, one_pow])

theorem span_reflEnergy_pow_eq (h : q * v = 1) (M : ℕ) :
    (Ideal.span {reflEnergy (q ^ M) (v ^ M)} : Ideal R)
      = (Ideal.span {q ^ M - 1} : Ideal R) ^ 2 :=
  span_reflEnergy_eq (by rw [← mul_pow, h, one_pow])

end Identities

section Laurent

open LaurentPolynomial

variable {k : Type u} [Field k]

/-- The reflection variable `q⁻¹ = T (-1)`. -/
noncomputable def monodromyInv : MonodromyRing k := T (-1 : ℤ)

theorem monodromy_mul_inv : monodromyParam k * monodromyInv = 1 := by
  rw [monodromyParam, monodromyInv, ← T_add]; simp

/-- The reflected two-leg energy on the universal monodromy line. -/
noncomputable def monodromyEnergy : MonodromyRing k :=
  reflEnergy (monodromyParam k) monodromyInv

/-- The ambidexterity curvature on the universal monodromy line. -/
noncomputable def monodromyCurvature : MonodromyRing k :=
  ambiCurvature (monodromyParam k) monodromyInv

/-- The rank-`M` central port energy. -/
noncomputable def monodromyEnergyPow (M : ℕ) : MonodromyRing k :=
  reflEnergy (monodromyParam k ^ M) (monodromyInv ^ M)

@[simp] theorem monodromyRefl_monodromyInv :
    (monodromyRefl (k := k)) monodromyInv = monodromyParam k := by
  simp [monodromyInv, monodromyParam]

/-- **Theorem 5.1, invariance half.**  The reflection fixes the two-leg energy. -/
@[simp] theorem monodromyRefl_energy :
    (monodromyRefl (k := k)) monodromyEnergy = monodromyEnergy := by
  simp only [monodromyEnergy, reflEnergy, monodromyInv, monodromyParam, map_sub, map_add,
    map_ofNat, LaurentPolynomial.invert_T, neg_neg]
  ring

/-- **Theorem 5.1, orientation half.**  Reflection reverses the conormal class of the wall
equation: `σ(q-1) + (q-1) ∈ I²`. -/
theorem monodromyRefl_wall_add_mem_sq :
    (monodromyRefl (k := k)) (wallEquation k) + wallEquation k ∈ (identityIdeal k) ^ 2 := by
  rw [identityIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    monodromyRefl_wallEquation]
  refine ⟨monodromyInv, ?_⟩
  have h := monodromy_mul_inv (k := k)
  simp only [wallEquation, monodromyParam, monodromyInv] at h ⊢
  linear_combination (1 - (T 1 : MonodromyRing k)) * h

/-- The class of the wall equation in the conormal module `I/I²`. -/
noncomputable def wallConormalClass : (identityIdeal k).Cotangent :=
  Ideal.toCotangent _ ⟨wallEquation k, Ideal.mem_span_singleton_self _⟩

/-- **Theorem 5.1 (5.11).**  Reflection acts by `-1` on the conormal line `I/I²`. -/
theorem toCotangent_monodromyRefl_wall :
    Ideal.toCotangent (identityIdeal k)
        ⟨(monodromyRefl (k := k)) (wallEquation k),
          monodromyRefl_mem_identityIdeal (Ideal.mem_span_singleton_self _)⟩
      = -wallConormalClass := by
  rw [eq_neg_iff_add_eq_zero, wallConormalClass, ← map_add, Ideal.toCotangent_eq_zero]
  exact monodromyRefl_wall_add_mem_sq

/-- **Theorem 5.1 (5.3).**  The reflected positive energy generates the square of the wall ideal. -/
theorem span_monodromyEnergy_eq :
    (Ideal.span {monodromyEnergy} : Ideal (MonodromyRing k)) = (identityIdeal k) ^ 2 := by
  rw [identityIdeal, wallEquation]
  exact span_reflEnergy_eq monodromy_mul_inv

/-- **Corollary 5.3 (5.8).**  `q K² = (q+1)² E`. -/
theorem monodromy_mul_curvature_sq :
    monodromyParam k * monodromyCurvature ^ 2
      = (monodromyParam k + 1) ^ 2 * monodromyEnergy :=
  mul_ambiCurvature_sq monodromy_mul_inv

/-- **Corollary 5.3 (5.9).**  `K ≡ 2(q-1)` modulo `I²`. -/
theorem monodromyCurvature_sub_two_wall_mem_sq :
    monodromyCurvature - 2 * wallEquation k ∈ (identityIdeal k) ^ 2 := by
  rw [monodromyCurvature, wallEquation, ambiCurvature_sub_two_wall, identityIdeal, wallEquation]
  exact Submodule.neg_mem _ (reflEnergy_mem_sq monodromy_mul_inv)

/-- **Corollary 5.2 (5.4).**  `q^M E_M = (q^M-1)²`. -/
theorem monodromy_mul_energyPow (M : ℕ) :
    monodromyParam k ^ M * monodromyEnergyPow M = (monodromyParam k ^ M - 1) ^ 2 :=
  mul_reflEnergy_pow monodromy_mul_inv M

/-- **Corollary 5.2, ideal form.**  `(E_M) = ((q^M-1))²`. -/
theorem span_monodromyEnergyPow_eq (M : ℕ) :
    (Ideal.span {monodromyEnergyPow (k := k) M} : Ideal (MonodromyRing k))
      = (Ideal.span {monodromyParam k ^ M - 1} : Ideal (MonodromyRing k)) ^ 2 :=
  span_reflEnergy_pow_eq monodromy_mul_inv M

end Laurent

end GaloisForLFunctions.HTGeometry.DerivedSelection
