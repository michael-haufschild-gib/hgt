import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# The diagonal collapse

What can count sections on the square of `Spec ℤ`? The natural counts are theta series of lattices
in `ℝ²` with the product metric `x v₁² + y v₂²`, whose two-variable Mellin transforms are, up to
`Γ_ℝ(s₁) Γ_ℝ(s₂)`, the lattice zeta functions `Σ_{v ∈ L, v₁v₂ ≠ 0} |v₁|^{−s₁} |v₂|^{−s₂}`.

* **Rank one collapses to the diagonal** (`rankOne_latticeZeta`): the lattice `ℤ(n, m)` of a
  Hecke graph has lattice zeta `n^{−s₁} m^{−s₂} ζ(s₁ + s₂)`: its arithmetic sees one variable,
  `s₁ + s₂`.
* **Rank two is Künneth** (`fullLattice_latticeZeta`): `ℤ²` has lattice zeta `ζ(s₁) ζ(s₂)`, a
  product without coupling.
* **On the reflection plane** `s₂ = 1 − s̄₁` both degenerate. The diagonal variable is
  `s₁ + s₂ = 1 + 2i Im s₁` (`reflection_plane_diagonal`), on the line `Re = 1` where `ζ` has no
  zeros (`riemannZeta_reflection_plane_diagonal_ne_zero`): the diagonal count reads only the
  boundary, as multiplicative positivity does. The product becomes a modulus square,
  `ξ(s) ξ(1 − s̄) = |ξ(s)|²` (`xi_mul_xi_reflection_plane`): its positivity is a determinant, which
  pairs `ρ` with `ρ̄` and cannot see a sign.

So lattice counting on the square of `Spec ℤ` produces determinant positivity or boundary
positivity, never Rosati positivity: a section count with a quadratic Riemann–Roch whose quadratic
term is Weil's form must have rank growing with the class, which no lattice of the square has.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

/-- **Rank one collapses to the diagonal.** The positive points `k(n, m)` of the lattice of a
Hecke graph give `Σ_k (kn)^{−s₁} (km)^{−s₂} = n^{−s₁} m^{−s₂} ζ(s₁ + s₂)`. -/
theorem rankOne_latticeZeta (n m : ℕ) {s₁ s₂ : ℂ}
    (hs : 1 < (s₁ + s₂).re) :
    ∑' k : ℕ, 1 / (((k + 1) * n : ℕ) : ℂ) ^ s₁ * (1 / (((k + 1) * m : ℕ) : ℂ) ^ s₂) =
      1 / (n : ℂ) ^ s₁ * (1 / (m : ℂ) ^ s₂) * riemannZeta (s₁ + s₂) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have e : ∀ (j : ℕ) (s : ℂ), (((k + 1) * j : ℕ) : ℂ) ^ s = ((k : ℂ) + 1) ^ s * (j : ℂ) ^ s := by
    intro j s
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]; push_cast; ring
  rw [e, e, Complex.cpow_add _ _ hk]
  ring

/-- **Rank two is Künneth.** `Σ_{a, b ≥ 1} a^{−s₁} b^{−s₂} = ζ(s₁) ζ(s₂)`. -/
theorem fullLattice_latticeZeta {s₁ s₂ : ℂ} (h1 : 1 < s₁.re) (h2 : 1 < s₂.re) :
    (∑' a : ℕ, 1 / ((a : ℂ) + 1) ^ s₁) * (∑' b : ℕ, 1 / ((b : ℂ) + 1) ^ s₂) =
      riemannZeta s₁ * riemannZeta s₂ := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1, zeta_eq_tsum_one_div_nat_add_one_cpow h2]

/-- The diagonal variable on the reflection plane: `s + (1 − s̄) = 1 + 2i Im s`. -/
theorem reflection_plane_diagonal (s : ℂ) : s + (1 - conj s) = 1 + 2 * s.im * I := by
  apply Complex.ext <;> simp; ring

/-- **The diagonal count reads only the boundary.** On the reflection plane the diagonal variable
lies on `Re = 1`, where `ζ` does not vanish. -/
theorem riemannZeta_reflection_plane_diagonal_ne_zero (s : ℂ) :
    riemannZeta (s + (1 - conj s)) ≠ 0 := by
  rw [reflection_plane_diagonal]
  refine riemannZeta_ne_zero_of_one_le_re ?_
  simp

/-- **The product count is a modulus square on the reflection plane.** -/
theorem xi_mul_xi_reflection_plane (s : ℂ) :
    RHTower.xi s * RHTower.xi (1 - conj s) = (Complex.normSq (RHTower.xi s) : ℂ) := by
  rw [RHTower.xi_one_sub, RHTower.xi_conj, Complex.mul_conj]

end GaloisForLFunctions.ArithmeticPolarization
