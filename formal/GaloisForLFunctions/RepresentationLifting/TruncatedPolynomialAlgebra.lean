import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-!
# Annihilators in the truncated polynomial algebra

In `R[x]/(xᴺ)`, complementary powers have exactly complementary annihilators,
over every commutative ring. These are the exactness identities underlying
the two-periodic resolution in Proposition 6.4 and Example 6.7 of
Ait Mohamed–El-Baz, *Dual reflection groups of graded Ore extensions*.
-/

namespace GaloisForLFunctions.RepresentationLifting

open Polynomial

variable (R : Type*) [CommRing R]

/-- The actual quotient algebra `R[x]/(xᴺ)`. -/
abbrev TruncatedPolynomialAlgebra (N : ℕ) := AdjoinRoot (X ^ N : R[X])

/-- The residue class of the polynomial variable. -/
noncomputable def truncatedRoot (N : ℕ) : TruncatedPolynomialAlgebra R N :=
  AdjoinRoot.root (X ^ N : R[X])

@[simp] theorem truncatedRoot_pow_horizon (N : ℕ) :
    truncatedRoot R N ^ N = 0 := by
  rw [truncatedRoot, ← AdjoinRoot.mk_X, ← map_pow]
  exact AdjoinRoot.mk_self

/-- The entire annihilator, with an explicit divisibility witness in the quotient. -/
theorem truncatedRoot_annihilator (a b : ℕ) (v : TruncatedPolynomialAlgebra R (a + b)) :
    truncatedRoot R (a + b) ^ b * v = 0 ↔
      ∃ w, truncatedRoot R (a + b) ^ a * w = v := by
  constructor
  · intro h
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective v
    have hp : (X : R[X]) ^ (a + b) ∣ X ^ b * p := by
      apply AdjoinRoot.mk_eq_zero.mp
      simpa only [map_mul, map_pow, AdjoinRoot.mk_X, truncatedRoot] using h
    have hdiv : (X : R[X]) ^ a ∣ p := by
      apply X_pow_dvd_iff.mpr
      intro i hi
      have hc := X_pow_dvd_iff.mp hp (b + i) (by omega)
      simpa only [coeff_X_pow_mul', if_pos (Nat.le_add_right b i),
        Nat.add_sub_cancel_left] using hc
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨AdjoinRoot.mk _ q, ?_⟩
    rw [hq, map_mul, map_pow, AdjoinRoot.mk_X]
    rfl
  · rintro ⟨w, rfl⟩
    rw [← mul_assoc, ← pow_add, Nat.add_comm b a, truncatedRoot_pow_horizon, zero_mul]

/-- Multiplication by a power, viewed as an endomorphism over the quotient algebra itself. -/
noncomputable def truncatedRootMul (N k : ℕ) :
    Module.End (TruncatedPolynomialAlgebra R N) (TruncatedPolynomialAlgebra R N) :=
  LinearMap.mulLeft _ (truncatedRoot R N ^ k)

/-- The quotient algebra gives a rank-one exact pair over itself. -/
theorem truncatedRootMul_range_eq_ker (a b : ℕ) :
    LinearMap.range (truncatedRootMul R (a + b) a) =
      LinearMap.ker (truncatedRootMul R (a + b) b) := by
  ext v
  change (∃ w, truncatedRoot R (a + b) ^ a * w = v) ↔
    truncatedRoot R (a + b) ^ b * v = 0
  exact (truncatedRoot_annihilator R a b v).symm

/-- Both alternating differentials are exact, without restrictions on characteristic. -/
theorem truncatedRootMul_periodic_exact (n : ℕ) :
    LinearMap.range (truncatedRootMul R (n + 1) 1) =
        LinearMap.ker (truncatedRootMul R (n + 1) n) ∧
      LinearMap.range (truncatedRootMul R (n + 1) n) =
        LinearMap.ker (truncatedRootMul R (n + 1) 1) := by
  refine ⟨?_, truncatedRootMul_range_eq_ker R n 1⟩
  have h := truncatedRootMul_range_eq_ker R 1 n
  rw [Nat.add_comm 1 n] at h
  exact h

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.truncatedRoot_annihilator
#print axioms GaloisForLFunctions.RepresentationLifting.truncatedRootMul_periodic_exact
