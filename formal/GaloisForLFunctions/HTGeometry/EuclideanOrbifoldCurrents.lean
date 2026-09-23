import GaloisForLFunctions.HTGeometry.ChebyshevQuadraticCurrent

/-!
# Transported currents of the compact Euclidean orbifold signatures

The four compact parabolic signatures `(2,2,2,2)`, `(3,3,3)`, `(2,4,4)` and `(2,3,6)` have the
additive plane as universal cover, a lattice (extended by a rotation of order `2`, `3`, `4`, `6`)
as deck group, and the translation-invariant Maurer–Cartan form `du` as the invariant current.
Their invariant coordinates on the quotient sphere are, respectively,

`y = ℘`,  `y = ℘′`,  `y = ℘²`,  `y = ℘³`,

and in each case the corresponding power of `du` transports to a rational differential in `y`.  All
four transports are exact algebraic consequences of the Weierstrass relation

`(℘′)² = 4℘³ - g₂℘ - g₃`

together with the chain rule, so they are identities in any differential field: no analysis and no
uniformization theorem is used, only the algebraic relation satisfied by the coordinate.

Written with `p = ℘ ∘ u`, `q = ℘′ ∘ u`, the hypotheses are the Weierstrass relation and the chain
rules `p′ = q·u′` and `q′ = (6p² - g₂/2)·u′`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {E : Type*} [Field E] [CharZero E] [Differential E]

omit [CharZero E] in
/-- **The `(2,2,2,2)` current.**  With the coordinate `y = ℘`, the square of the Maurer–Cartan form
transports to `(y′)²/(4y³ - g₂y - g₃)`; the denominator has three simple roots and a pole at
infinity, the four order-two points of the signature. -/
theorem weierstrass_square_current {p q u g₂ g₃ : E}
    (hq : q ^ (2 : ℕ) = 4 * p ^ (3 : ℕ) - g₂ * p - g₃) (hp : Differential.deriv p = q * Differential.deriv u) :
    (Differential.deriv p) ^ (2 : ℕ)
      = (4 * p ^ (3 : ℕ) - g₂ * p - g₃) * (Differential.deriv u) ^ (2 : ℕ) := by
  rw [hp, mul_pow, ← hq]

omit [CharZero E] in
/-- Quotient form of the `(2,2,2,2)` current. -/
theorem weierstrass_square_current_div {p q u g₂ g₃ : E}
    (hq : q ^ (2 : ℕ) = 4 * p ^ (3 : ℕ) - g₂ * p - g₃) (hp : Differential.deriv p = q * Differential.deriv u)
    (hne : 4 * p ^ (3 : ℕ) - g₂ * p - g₃ ≠ 0) :
    (Differential.deriv u) ^ (2 : ℕ)
      = (Differential.deriv p) ^ (2 : ℕ) / (4 * p ^ (3 : ℕ) - g₂ * p - g₃) := by
  rw [weierstrass_square_current hq hp, mul_comm, mul_div_assoc, div_self hne, mul_one]

omit [CharZero E] in
/-- **The `(3,3,3)` current.**  On the hexagonal lattice `g₂ = 0`, the coordinate `y = ℘′` is
invariant under the order-three rotation, and the cube of the Maurer–Cartan form transports to
`2(y′)³ = 27(y² + g₃)²(u′)³`. -/
theorem weierstrass_cubic_current {p q u g₃ : E}
    (hq : q ^ (2 : ℕ) = 4 * p ^ (3 : ℕ) - g₃)
    (hq' : Differential.deriv q = 6 * p ^ (2 : ℕ) * Differential.deriv u) :
    2 * (Differential.deriv q) ^ (3 : ℕ)
      = 27 * (q ^ (2 : ℕ) + g₃) ^ (2 : ℕ) * (Differential.deriv u) ^ (3 : ℕ) := by
  have hcube : q ^ (2 : ℕ) + g₃ = 4 * p ^ (3 : ℕ) := by rw [hq]; ring
  rw [hq', hcube, mul_pow, mul_pow]
  ring

omit [CharZero E] in
/-- **The `(2,4,4)` current.**  On the square lattice `g₃ = 0`, the coordinate `y = ℘²` is invariant
under the order-four rotation, and the fourth power of the Maurer–Cartan form transports to
`(y′)⁴ = 16 y³ (4y - g₂)² (u′)⁴`. -/
theorem weierstrass_quartic_current {p q u g₂ : E}
    (hq : q ^ (2 : ℕ) = 4 * p ^ (3 : ℕ) - g₂ * p) (hp : Differential.deriv p = q * Differential.deriv u) :
    (Differential.deriv (p ^ (2 : ℕ))) ^ (4 : ℕ)
      = 16 * (p ^ (2 : ℕ)) ^ (3 : ℕ) * (4 * p ^ (2 : ℕ) - g₂) ^ (2 : ℕ) * (Differential.deriv u) ^ (4 : ℕ) := by
  have hderiv : Differential.deriv (p ^ (2 : ℕ)) = 2 * p * (q * Differential.deriv u) := by
    rw [show (p : E) ^ (2 : ℕ) = p * p by ring, Differential.deriv.leibniz, hp]
    ring
  have hq2 : q ^ (2 : ℕ) = p * (4 * p ^ (2 : ℕ) - g₂) := by rw [hq]; ring
  have hexp : (2 * p * (q * Differential.deriv u)) ^ (4 : ℕ)
      = 16 * p ^ (4 : ℕ) * (q ^ (2 : ℕ)) ^ (2 : ℕ) * (Differential.deriv u) ^ (4 : ℕ) := by ring
  rw [hderiv, hexp, hq2]
  ring

omit [CharZero E] in
/-- **The `(2,3,6)` current.**  On the hexagonal lattice `g₂ = 0`, the coordinate `y = ℘³` is
invariant under the order-six rotation, and the sixth power of the Maurer–Cartan form transports to
`(y′)⁶ = 729 y⁴ (4y - g₃)³ (u′)⁶`. -/
theorem weierstrass_sextic_current {p q u g₃ : E}
    (hq : q ^ (2 : ℕ) = 4 * p ^ (3 : ℕ) - g₃) (hp : Differential.deriv p = q * Differential.deriv u) :
    (Differential.deriv (p ^ (3 : ℕ))) ^ (6 : ℕ)
      = 729 * (p ^ (3 : ℕ)) ^ (4 : ℕ) * (4 * p ^ (3 : ℕ) - g₃) ^ (3 : ℕ) * (Differential.deriv u) ^ (6 : ℕ) := by
  have hsq : Differential.deriv (p ^ (2 : ℕ)) = 2 * p * (q * Differential.deriv u) := by
    rw [show (p : E) ^ (2 : ℕ) = p * p by ring, Differential.deriv.leibniz, hp]
    ring
  have hderiv : Differential.deriv (p ^ (3 : ℕ)) = 3 * p ^ (2 : ℕ) * (q * Differential.deriv u) := by
    rw [show (p : E) ^ (3 : ℕ) = p ^ (2 : ℕ) * p by ring, Differential.deriv.leibniz, hsq, hp]
    ring
  have hexp : (3 * p ^ (2 : ℕ) * (q * Differential.deriv u)) ^ (6 : ℕ)
      = 729 * p ^ (12 : ℕ) * (q ^ (2 : ℕ)) ^ (3 : ℕ) * (Differential.deriv u) ^ (6 : ℕ) := by ring
  rw [hderiv, hexp, hq]
  ring

end

end GaloisForLFunctions.HTGeometry
