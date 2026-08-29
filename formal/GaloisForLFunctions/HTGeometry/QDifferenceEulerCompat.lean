import GaloisForLFunctions.HTGeometry.QDifferenceRatFuncEmbedding
import GaloisForLFunctions.HTGeometry.DoubleSineOrbitResidueObstruction

/-!
# The Euler operator under Laurent expansion

The Euler operator `z d/dz` of `k(z)` becomes the grading `zⁿ ↦ n zⁿ` of `k((z))`.  Both are
derivations over `k`, so the identity only has to be checked on polynomials and then transported
across a quotient by cancelling the image of the denominator.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Multiplicative Polynomial

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

theorem coeff_algebraMap_polynomial (p : Polynomial k) (n : ℤ) :
    (algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap (Polynomial k) (RatFunc k) p)).coeff n
      = if n < 0 then 0 else p.coeff n.natAbs := by
  have hcoe : algebraMap (RatFunc k) (LaurentSeries k)
      (algebraMap (Polynomial k) (RatFunc k) p)
      = HahnSeries.ofPowerSeries ℤ k ((p : Polynomial k) : PowerSeries k) :=
    (RatFunc.coe_coe _).symm
  rw [hcoe, coeff_ofPowerSeries_polynomial]

/-- The Euler operator of a polynomial is the Laurent grading. -/
theorem algebraMap_ratFuncEulerOp_polynomial (p : Polynomial k) :
    algebraMap (RatFunc k) (LaurentSeries k)
        (ratFuncEulerOp (algebraMap (Polynomial k) (RatFunc k) p))
      = innerEuler (algebraMap (RatFunc k) (LaurentSeries k)
          (algebraMap (Polynomial k) (RatFunc k) p)) := by
  have hop : ratFuncEulerOp (algebraMap (Polynomial k) (RatFunc k) p)
      = algebraMap (Polynomial k) (RatFunc k) (Polynomial.X * Polynomial.derivative p) := by
    rw [ratFuncEulerOp, ratFuncDerivative_algebraMap, map_mul]
  rw [hop]
  ext n
  rw [coeff_algebraMap_polynomial, coeff_innerEuler, coeff_algebraMap_polynomial]
  by_cases h : n < 0
  · simp [h]
  · rw [if_neg h, if_neg h]
    by_cases h0 : n = 0
    · subst h0
      simp [Polynomial.mul_coeff_zero]
    · have hnat : n.natAbs = (n.natAbs - 1) + 1 := by omega
      rw [hnat, Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      have hsucc : ((n.natAbs - 1 : ℕ) : k) + 1 = (n : k) := by
        have h2 : ((n.natAbs - 1 : ℕ) : ℤ) + 1 = n := by omega
        exact_mod_cast congrArg (fun t : ℤ => (t : k)) h2
      rw [hsucc]
      ring

/-- **The Euler operator of `k(z)` is the Laurent grading of `k((z))`.** -/
theorem algebraMap_ratFuncEulerOp (f : RatFunc k) :
    algebraMap (RatFunc k) (LaurentSeries k) (ratFuncEulerOp f)
      = innerEuler (algebraMap (RatFunc k) (LaurentSeries k) f) := by
  have hleib : ∀ x y : RatFunc k, ratFuncEulerOp (x * y)
      = ratFuncEulerOp x * y + x * ratFuncEulerOp y := by
    intro x y
    rw [ratFuncEulerOp, ratFuncEulerOp, ratFuncEulerOp, Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  refine RatFunc.induction_on (P := fun f =>
    algebraMap (RatFunc k) (LaurentSeries k) (ratFuncEulerOp f)
      = innerEuler (algebraMap (RatFunc k) (LaurentSeries k) f)) f ?_
  intro p s hs
  set ψ := algebraMap (RatFunc k) (LaurentSeries k) with hψ
  set F : RatFunc k := algebraMap (Polynomial k) (RatFunc k) p /
    algebraMap (Polynomial k) (RatFunc k) s with hF
  have hsne : algebraMap (Polynomial k) (RatFunc k) s ≠ 0 := by
    simpa using RatFunc.algebraMap_ne_zero hs
  have hFs : F * algebraMap (Polynomial k) (RatFunc k) s
      = algebraMap (Polynomial k) (RatFunc k) p := by
    rw [hF, div_mul_cancel₀ _ hsne]
  have h1 := congrArg ψ (hleib F (algebraMap (Polynomial k) (RatFunc k) s))
  rw [hFs, map_add, map_mul, map_mul, algebraMap_ratFuncEulerOp_polynomial,
    algebraMap_ratFuncEulerOp_polynomial] at h1
  have h2 : innerEuler (ψ F * ψ (algebraMap (Polynomial k) (RatFunc k) s))
      = innerEuler (ψ F) * ψ (algebraMap (Polynomial k) (RatFunc k) s)
        + ψ F * innerEuler (ψ (algebraMap (Polynomial k) (RatFunc k) s)) :=
    innerEuler_leibniz _ _
  rw [← map_mul, hFs] at h2
  have hψs : ψ (algebraMap (Polynomial k) (RatFunc k) s) ≠ 0 := by
    simpa [hψ] using hsne
  exact mul_right_cancel₀ hψs (add_right_cancel (h1.symm.trans h2))

end

end GaloisForLFunctions.HTGeometry
