import GaloisForLFunctions.HTGeometry.MatrixHasDerivAt
import GaloisForLFunctions.HTGeometry.SutherlandLinearisation

/-!
# From the difference-form braid Yang--Baxter equation to the Sutherland identity

Differentiating the braid Yang--Baxter equation in its second spectral parameter at zero, for a
regular family with `Ř 0 = 1`, produces a relation that is *linear* in `Ř′`.  Only the product rule
and the two leg rules are used; the anchor `Ř 0 = 1` collapses the two boundary factors.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {κ : Type*} [DecidableEq κ] [Fintype κ]

/-- **The Sutherland identity.**  A regular difference-form braid family satisfies, at every
spectral value, the linear relation obtained by differentiating the braid equation at the anchor. -/
theorem sutherland_of_braid
    (Rf : ℂ → Matrix (κ × κ) (κ × κ) ℂ) (Rd : ℂ → Matrix (κ × κ) (κ × κ) ℂ)
    (hderiv : ∀ t, HasMatrixDerivAt Rf (Rd t) t)
    (hbraid : ∀ x y : ℂ, legLeft (Rf x) * legRight (Rf (x + y)) * legLeft (Rf y)
      = legRight (Rf y) * legLeft (Rf (x + y)) * legRight (Rf x))
    (hreg : Rf 0 = 1) (a : ℂ) :
    legLeft (Rf a) * legRight (Rd a) - legLeft (Rd a) * legRight (Rf a)
      = sutherlandSource (Rf a) (Rd 0) := by
  classical
  -- the two sides of the braid equation, as functions of the second parameter
  have hΦ : HasMatrixDerivAt
      (fun b => legLeft (Rf a) * legRight (Rf (a + b)) * legLeft (Rf b))
      ((0 * legRight (Rf (a + 0)) + legLeft (Rf a) * legRight (Rd a)) * legLeft (Rf 0)
        + legLeft (Rf a) * legRight (Rf (a + 0)) * legLeft (Rd 0)) 0 := by
    have hA : HasMatrixDerivAt (fun _ : ℂ => legLeft (Rf a)) 0 0 :=
      HasMatrixDerivAt.const _ 0
    have hB : HasMatrixDerivAt (fun b => legRight (Rf (a + b))) (legRight (Rd a)) 0 := by
      refine HasMatrixDerivAt.legRight ?_
      have h := HasMatrixDerivAt.comp_const_add (A := Rf) (A' := Rd (a + 0)) (a := a) (b := 0)
        (hderiv (a + 0))
      simpa using h
    have hC : HasMatrixDerivAt (fun b => legLeft (Rf b)) (legLeft (Rd 0)) 0 :=
      HasMatrixDerivAt.legLeft (hderiv 0)
    exact (hA.mul hB).mul hC
  have hΨ : HasMatrixDerivAt
      (fun b => legRight (Rf b) * legLeft (Rf (a + b)) * legRight (Rf a))
      ((legRight (Rd 0) * legLeft (Rf (a + 0)) + legRight (Rf 0) * legLeft (Rd a))
          * legRight (Rf a)
        + legRight (Rf 0) * legLeft (Rf (a + 0)) * 0) 0 := by
    have hA : HasMatrixDerivAt (fun b => legRight (Rf b)) (legRight (Rd 0)) 0 :=
      HasMatrixDerivAt.legRight (hderiv 0)
    have hB : HasMatrixDerivAt (fun b => legLeft (Rf (a + b))) (legLeft (Rd a)) 0 := by
      refine HasMatrixDerivAt.legLeft ?_
      have h := HasMatrixDerivAt.comp_const_add (A := Rf) (A' := Rd (a + 0)) (a := a) (b := 0)
        (hderiv (a + 0))
      simpa using h
    have hC : HasMatrixDerivAt (fun _ : ℂ => legRight (Rf a)) 0 0 :=
      HasMatrixDerivAt.const _ 0
    exact (hA.mul hB).mul hC
  have hfun : (fun b => legLeft (Rf a) * legRight (Rf (a + b)) * legLeft (Rf b))
      = fun b => legRight (Rf b) * legLeft (Rf (a + b)) * legRight (Rf a) := by
    funext b
    exact hbraid a b
  have hEq := (hΦ.congr hfun).unique hΨ
  rw [hreg, legLeft_one, legRight_one, add_zero] at hEq
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    zero_add, add_zero] at hEq
  rw [sutherlandSource]
  rw [Matrix.add_mul,
    Matrix.mul_assoc (legRight (Rd 0)) (legLeft (Rf a)) (legRight (Rf a))] at hEq
  linear_combination (norm := module) hEq

end GaloisForLFunctions.HTGeometry
