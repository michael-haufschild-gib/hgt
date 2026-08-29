import GaloisForLFunctions.HTGeometry.PrincipalPartDecomposition

/-!
# The dilation acts on principal-part monomials

`(qx − γ)^{-d} = q^{-d}(x − γ/q)^{-d}`, so the dilation permutes the principal-part monomials along
multiplicative orbits, rescaling by `q^{-d}`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

theorem polyScale_X_sub_C_pow {q : K} (hq : q ≠ 0) (γ : K) (d : ℕ) :
    polyScale q ((Polynomial.X - Polynomial.C γ) ^ d)
      = Polynomial.C (q ^ d) * (Polynomial.X - Polynomial.C (γ / q)) ^ d := by
  rw [map_pow, Polynomial.C_pow, ← mul_pow]
  congr 1
  have hC : polyScale q (Polynomial.C γ) = Polynomial.C γ := by
    rw [polyScale, Polynomial.aeval_C, Polynomial.algebraMap_eq]
  rw [map_sub, polyScale_X, hC, mul_sub, ← Polynomial.C_mul, mul_div_cancel₀ _ hq]

theorem ratFuncScale_invLinPow {q : K} (hq : q ≠ 0) (γ : K) (d : ℕ) :
    ratFuncScale q hq (invLinPow γ d)
      = algebraMap K (RatFunc K) (q ^ d)⁻¹ * invLinPow (γ / q) d := by
  have hmap : ratFuncScale q hq (algebraMap (Polynomial K) (RatFunc K)
      ((Polynomial.X - Polynomial.C γ) ^ d))
      = algebraMap (Polynomial K) (RatFunc K)
        (polyScale q ((Polynomial.X - Polynomial.C γ) ^ d)) := by
    have h := ratFuncScale_div q hq ((Polynomial.X - Polynomial.C γ) ^ d) 1
    simpa using h
  rw [invLinPow, map_inv₀, hmap, polyScale_X_sub_C_pow hq, map_mul, mul_inv,
    RatFunc.algebraMap_C, ← map_inv₀, invLinPow]
  rfl

end

end GaloisForLFunctions.HTGeometry
