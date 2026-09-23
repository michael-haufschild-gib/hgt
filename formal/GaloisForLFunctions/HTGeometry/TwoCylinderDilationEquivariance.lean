import GaloisForLFunctions.HTGeometry.TwoCylinderDifferential
import GaloisForLFunctions.HTGeometry.DilatedCotModelOrbitObstruction

/-!
# The two dilations are differential automorphisms of the two-cylinder field

The two structural translations act on the two-cylinder function field by dilating the outer
coordinate and by dilating the coefficient field.  Both commute with the total two-cylinder
derivation:

* dilating the outer variable by a constant leaves the coefficient derivation untouched and
  commutes with the Euler operator;
* dilating the coefficient field commutes with the coefficient derivation — it is the one-cylinder
  Euler-operator statement — and leaves the outer variable alone.

That makes each of them a differential automorphism of the base, which is what the source-boundary
matroid law requires of the translation action.
-/

open Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [Differential K]

noncomputable section

local instance tdeIntAlgebraPoly : Algebra ℤ (Polynomial K) := Ring.toIntAlgebra _
local instance tdeIntAlgebraRatFunc : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

local instance tdeIntTower : IsScalarTower ℤ (Polynomial K) (RatFunc K) :=
  IsScalarTower.of_algebraMap_eq fun n => by
    show ((n : ℤ) : RatFunc K) = algebraMap (Polynomial K) (RatFunc K) ((n : ℤ) : Polynomial K)
    rw [map_intCast]

/-! ### Powers of a constant -/

theorem deriv_pow_eq_zero {s : K} (hs : s′ = 0) (n : ℕ) : (s ^ n)′ = 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih, hs]
      ring

/-! ### The outer dilation is differential -/

omit [Differential K] in
theorem polyScale_monomial (s : K) (n : ℕ) (a : K) :
    polyScale s (Polynomial.monomial n a) = Polynomial.monomial n (a * s ^ n) := by
  rw [polyScale_eq_comp, Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
    ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]

theorem coeffDeriv_polyScale {s : K} (hs : s′ = 0) (p : Polynomial K) :
    coeffDeriv (polyScale s p) = polyScale s (coeffDeriv p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, coeffDeriv_add, coeffDeriv_add, hp, hq, map_add]
  | monomial n a =>
      rw [polyScale_monomial, coeffDeriv_monomial, coeffDeriv_monomial,
        Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul_X_pow_eq_monomial,
        polyScale_monomial]
      congr 1
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, deriv_pow_eq_zero hs]
      ring

theorem twoCylDerivation_ratFuncScale (lam : K) {s : K} (hsne : s ≠ 0) (hs : s′ = 0)
    (hlam : ratFuncScale s hsne (algebraMap K (RatFunc K) lam)
      = algebraMap K (RatFunc K) lam) (y : RatFunc K) :
    twoCylDerivation lam (ratFuncScale s hsne y)
      = ratFuncScale s hsne (twoCylDerivation lam y) := by
  classical
  have hD : ∀ x y : RatFunc K,
      twoCylDerivation lam (x * y)
        = x * twoCylDerivation lam y + y * twoCylDerivation lam x := by
    intro x y
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hD' : ∀ x y : RatFunc K,
      twoCylDerivation lam (ratFuncScale s hsne (x * y))
        = ratFuncScale s hsne x * twoCylDerivation lam (ratFuncScale s hsne y)
          + ratFuncScale s hsne y * twoCylDerivation lam (ratFuncScale s hsne x) := by
    intro x y
    rw [map_mul, hD]
  have hpoly : ∀ p : Polynomial K,
      twoCylDerivation lam (ratFuncScale s hsne (algebraMap (Polynomial K) (RatFunc K) p))
        = ratFuncScale s hsne
          (twoCylDerivation lam (algebraMap (Polynomial K) (RatFunc K) p)) := by
    intro p
    rw [ratFuncScale_algebraMap, twoCylDerivation_algebraMap, twoCylDerivation_algebraMap,
      coeffDeriv_polyScale hs, map_add, map_mul, map_mul, ratFuncScale_algebraMap,
      ratFuncScale_algebraMap, hlam, polyScale_derivative, polyScale_X,
      ratFuncScale_algebraMap, map_mul, map_mul]
    ring
  refine RatFunc.induction_on
    (P := fun y => twoCylDerivation lam (ratFuncScale s hsne y)
      = ratFuncScale s hsne (twoCylDerivation lam y)) y ?_
  intro p t ht
  set A : RatFunc K := algebraMap (Polynomial K) (RatFunc K) p with hA
  set B : RatFunc K := algebraMap (Polynomial K) (RatFunc K) t with hB
  have hBne : B ≠ 0 := RatFunc.algebraMap_ne_zero ht
  have hSB : ratFuncScale s hsne B ≠ 0 := by
    rw [hB, ratFuncScale_algebraMap]
    refine RatFunc.algebraMap_ne_zero ?_
    intro hcon
    exact ht (polyScale_injective hsne (by rw [hcon, map_zero]))
  have hdiv : ratFuncScale s hsne (A / B)
      = ratFuncScale s hsne A / ratFuncScale s hsne B := map_div₀ (ratFuncScale s hsne) A B
  have hpA := hpoly p
  have hpB := hpoly t
  rw [← hA] at hpA
  rw [← hB] at hpB
  have hpush : ratFuncScale s hsne
        ((twoCylDerivation lam A * B - A * twoCylDerivation lam B) / B ^ (2 : ℕ))
      = (ratFuncScale s hsne (twoCylDerivation lam A) * ratFuncScale s hsne B
          - ratFuncScale s hsne A * ratFuncScale s hsne (twoCylDerivation lam B))
        / (ratFuncScale s hsne B) ^ (2 : ℕ) := by
    rw [map_div₀ (ratFuncScale s hsne)
      (twoCylDerivation lam A * B - A * twoCylDerivation lam B) (B ^ (2 : ℕ)), map_sub, map_mul,
      map_mul, map_pow]
  rw [hdiv, leibniz_div (twoCylDerivation lam) hD hSB,
    leibniz_div (twoCylDerivation lam) hD hBne, hpA, hpB, hpush]

end

end GaloisForLFunctions.HTGeometry
