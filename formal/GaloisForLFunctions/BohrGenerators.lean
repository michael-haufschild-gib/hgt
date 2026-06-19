import GaloisForLFunctions.KroneckerFlow

/-!
# Finite Bohr-character generator identities

This file formalizes the finite algebraic skeleton of
`archimedean-generator-axis-mode.md`: prime-coordinate scaling acts diagonally
on finitely supported Bohr characters, and products of characters add their
exponent vectors. It deliberately does not formalize infinite torus analysis,
unbounded differential operators, or global holonomy.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- A finitely supported integer Bohr character on a commutative multiplicative
group. For the prime torus, this is `e_m(x)=∏_p x_p^{m_p}`. -/
def bohrCharacter {ι G : Type*} [CommGroup G] (m : ι →₀ ℤ) (x : ι → G) : G :=
  m.prod fun p n => x p ^ n

/-- Scale one coordinate of a torus point. For a prime lane this is
`x_p ↦ c*x_p` with all other coordinates unchanged. -/
def scaleCoordinate {ι G : Type*} [DecidableEq ι] [CommGroup G]
    (p : ι) (c : G) (x : ι → G) : ι → G :=
  Function.update x p (c * x p)

/-- The trivial exponent vector gives the trivial Bohr character. -/
theorem bohrCharacter_zero {ι G : Type*} [CommGroup G] (x : ι → G) :
    bohrCharacter (0 : ι →₀ ℤ) x = 1 := by
  simp [bohrCharacter]

/-- Products of Bohr characters add exponent vectors:
`e_{m+n}=e_m*e_n`. This is the finite algebraic identity behind the card's
statement that combination modes arise from the ring product. -/
theorem bohrCharacter_add {ι G : Type*} [DecidableEq ι] [CommGroup G]
    (m n : ι →₀ ℤ) (x : ι → G) :
    bohrCharacter (m + n) x = bohrCharacter m x * bohrCharacter n x := by
  unfold bohrCharacter
  rw [Finsupp.prod_add_index]
  · intro a
    simp
  · intro a _ b c
    rw [zpow_add]

/-- Scaling the `p` coordinate acts diagonally on a Bohr character:
`e_m(..., c*x_p, ...) = c^{m_p} e_m(x)`. For `c=p^{-1}` this is the finite
form of `σ_p e_m = p^{-m_p} e_m`. -/
theorem bohrCharacter_scaleCoordinate {ι G : Type*} [DecidableEq ι] [CommGroup G]
    (m : ι →₀ ℤ) (p : ι) (c : G) (x : ι → G) :
    bohrCharacter m (scaleCoordinate p c x) = c ^ (m p) * bohrCharacter m x := by
  classical
  unfold bohrCharacter scaleCoordinate
  rw [Finsupp.prod, Finsupp.prod]
  by_cases hp : p ∈ m.support
  · rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hp]
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hp]
    simp only [Function.update_self]
    have hprod :
        (∏ q ∈ m.support \ {p}, Function.update x p (c * x p) q ^ m q) =
          ∏ q ∈ m.support \ {p}, x q ^ m q := by
      refine Finset.prod_congr rfl ?_
      intro q hq
      have hqne : q ≠ p := by
        have hnot : q ∉ ({p} : Finset ι) := (Finset.mem_sdiff.mp hq).2
        exact Finset.notMem_singleton.mp hnot
      simp [Function.update_of_ne hqne]
    rw [hprod]
    rw [mul_zpow]
    group
  · have hmp : m p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hmp]
    refine Finset.prod_congr rfl ?_
    intro q hq
    have hqne : q ≠ p := by
      intro h
      subst h
      exact hp hq
    simp [Function.update_of_ne hqne]

end

end GaloisForLFunctions
