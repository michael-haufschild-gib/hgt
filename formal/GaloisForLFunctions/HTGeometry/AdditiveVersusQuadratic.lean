import Mathlib

/-!
# Additive invariants cannot determine a quadratic energy

On a free commutative monoid of exponent vectors, an invariant that is *additive* under
multiplication is a linear form in the exponents.  The energy `∑ eᵢ²` is quadratic.  Two exponent
vectors with equal linear-form values can have different energies, so no family of additive
invariants whose weights are constant across the generators can determine the energy.

The witness is `(1,1)` against `(2,0)`: equal total weight `2`, energies `2` and `4`.

This is the abstract form of the following fact about the Selberg class.  Every integer the Selberg
axioms attach to an element — the number of gamma factors, the pole order at `s = 1`, the degree when
it is an integer — is additive under multiplication of Dirichlet series, hence a linear form in the
exponents of the primitive factorisation, whereas Selberg's prime energy `n_F = ∑ eᵢ²` is quadratic.
Concretely, for two distinct primitive even characters `χ₁, χ₂` of the same modulus, the products
`L(·,χ₁)L(·,χ₂)` and `L(·,χ₁)²` share degree, conductor, gamma factor and pole order, yet have
energies `2` and `4`.
-/

open Finset

namespace HTGeometry

/-- **Additive invariants do not determine the quadratic energy.**  For any constant weight `w`, the
exponent vectors `(1,1)` and `(2,0)` have the same weighted total but different energies. -/
theorem additive_not_determine_energy (w : ℤ) :
    (∑ i : Fin 2, w * (![1, 1] : Fin 2 → ℤ) i) = (∑ i : Fin 2, w * (![2, 0] : Fin 2 → ℤ) i)
      ∧ (∑ i : Fin 2, ((![1, 1] : Fin 2 → ℤ) i) ^ 2)
          ≠ (∑ i : Fin 2, ((![2, 0] : Fin 2 → ℤ) i) ^ 2) := by
  constructor
  · simp [Fin.sum_univ_two]
    ring
  · simp [Fin.sum_univ_two]

/-- The same statement for an arbitrary family of additive invariants with generator-independent
weights: all of them agree on the two exponent vectors, while the energies differ. -/
theorem additive_family_not_determine_energy {ι : Type*} (w : ι → ℤ) (k : ι) :
    (∑ i : Fin 2, w k * (![1, 1] : Fin 2 → ℤ) i)
        = (∑ i : Fin 2, w k * (![2, 0] : Fin 2 → ℤ) i)
      ∧ (∑ i : Fin 2, ((![1, 1] : Fin 2 → ℤ) i) ^ 2)
          ≠ (∑ i : Fin 2, ((![2, 0] : Fin 2 → ℤ) i) ^ 2) :=
  additive_not_determine_energy (w k)

/-- The energy of an exponent vector is unchanged by permuting the generators, but is not a function
of the total exponent: `1² + 1² = 2` while `2² + 0² = 4` for the same total `2`. -/
theorem energy_ne_of_same_total :
    (1 : ℤ) + 1 = 2 + 0 ∧ (1 : ℤ) ^ 2 + 1 ^ 2 ≠ 2 ^ 2 + 0 ^ 2 := by
  constructor <;> norm_num

end HTGeometry
