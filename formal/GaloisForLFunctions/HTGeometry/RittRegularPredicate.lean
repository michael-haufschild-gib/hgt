import GaloisForLFunctions.HTGeometry.RittFirstOrderForm

/-!
# A regularity predicate for the base of a Ritt frame

The affine alternative `ψ u = q^I·ρ^J·u + h` is empty on its own: for any `u ≠ 0` the difference
`ψ u − q^I ρ^J u` is a legitimate `h`, and it is nonzero as soon as `u` is not an eigenvector.  What
makes the alternative refutable is not the shape of the equation but the *provenance* of `h`: the
pole count of an affine transport equation needs the inhomogeneity to be regular wherever the
chain-rule factor is a unit.

That condition is carried abstractly here by a predicate on the base closed under the operations the
descent performs — sums, negatives, products, the derivation, and multiplication by any integer
power of the linearizing multiplier or of the chain-rule factor.  Every inhomogeneity the descent
produces is a coefficient of an input inhomogeneity divided by such a monomial, so the predicate
propagates from the Faà di Bruno coefficients of the shift to the base relation.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **A regularity predicate on the base of a Ritt frame.**  A subring stable under the derivation
and containing every integer power of the shift multiplier and of the chain-rule factor. -/
structure RittRegular (Fr : RittFrame K L) (q : K) (P : K → Prop) : Prop where
  add : ∀ {x y : K}, P x → P y → P (x + y)
  neg : ∀ {x : K}, P x → P (-x)
  mul : ∀ {x y : K}, P x → P y → P (x * y)
  ratCast : ∀ r : ℚ, P (r : K)
  deriv : ∀ {x : K}, P x → P (Fr.dK x)
  qzpow : ∀ i : ℤ, P (q ^ i)
  rzpow : ∀ k : ℤ, P (Fr.ρ ^ k)
  fixed : ∀ κ : K, Fr.ψ κ = κ → P κ

namespace RittRegular

variable {Fr : RittFrame K L} {q : K} {P : K → Prop}

theorem zero (hP : RittRegular Fr q P) : P 0 := by
  have := hP.ratCast 0
  rwa [Rat.cast_zero] at this

theorem one (hP : RittRegular Fr q P) : P 1 := by
  have := hP.ratCast 1
  rwa [Rat.cast_one] at this

theorem natCast (hP : RittRegular Fr q P) (n : ℕ) : P (n : K) := by
  have := hP.ratCast (n : ℚ)
  rwa [Rat.cast_natCast] at this

/-- The inverse of a nonzero shift-fixed element is shift-fixed, hence in the class. -/
theorem fixed_inv (hP : RittRegular Fr q P) (κ : K) (_hκ : κ ≠ 0) (hf : Fr.ψ κ = κ) :
    P κ⁻¹ := by
  refine hP.fixed κ⁻¹ ?_
  rw [map_inv₀, hf]

theorem sub (hP : RittRegular Fr q P) {x y : K} (hx : P x) (hy : P y) : P (x - y) := by
  rw [sub_eq_add_neg]
  exact hP.add hx (hP.neg hy)

theorem q_mem (hP : RittRegular Fr q P) : P q := by
  have := hP.qzpow 1
  rwa [zpow_one] at this

theorem rho_mem (hP : RittRegular Fr q P) : P Fr.ρ := by
  have := hP.rzpow 1
  rwa [zpow_one] at this

/-- Multiplication by a monomial in the two multipliers preserves the predicate. -/
theorem mul_monomial (hP : RittRegular Fr q P) {x : K} (hx : P x) (i k : ℤ) :
    P (x * q ^ i * Fr.ρ ^ k) :=
  hP.mul (hP.mul hx (hP.qzpow i)) (hP.rzpow k)

/-- Division by a monomial in the two multipliers preserves the predicate. -/
theorem div_monomial (hP : RittRegular Fr q P) {x : K} (hx : P x) (i k : ℤ) :
    P (x / (q ^ i * Fr.ρ ^ k)) := by
  have hρ : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hrw : x / (q ^ i * Fr.ρ ^ k) = x * q ^ (-i) * Fr.ρ ^ (-k) := by
    rw [zpow_neg, zpow_neg, div_eq_mul_inv, mul_inv, mul_assoc]
  rw [hrw]
  exact hP.mul_monomial hx (-i) (-k)

/-- The inhomogeneity produced by one pass of the level-two classification stays in the predicate:
it is a coefficient of the input inhomogeneity divided by a monomial in the two multipliers. -/
theorem div_pass (hP : RittRegular Fr q P) (hq : q ≠ 0) {x : K} (hx : P x) (j k : ℕ) :
    P (x / ((q / Fr.ρ) ^ j * q ^ k)) := by
  have hρ : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hrw : ((q / Fr.ρ) ^ j * q ^ k) = q ^ ((j : ℤ) + (k : ℤ)) * Fr.ρ ^ (-(j : ℤ)) := by
    rw [div_pow, zpow_add₀ hq, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast,
      div_eq_mul_inv]
    ring
  rw [hrw]
  exact hP.div_monomial hx _ _

end RittRegular

end GaloisForLFunctions.HTGeometry
