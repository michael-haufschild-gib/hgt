import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Algebra.Hom

/-!
# The powers of a separating element are independent

If `n` algebra maps of a `K`-algebra to the field `K` take pairwise distinct values on `θ`, then
`1, θ, …, θ^(n-1)` are linearly independent over `K` — the Vandermonde matrix of those values is
invertible.  Applied to the fibre of a finite free `ℂ[X]`-algebra, this is what makes the
determinant of `powerMatrix` nonvanishing at a parameter, which is the last input to the chart data
of `AlgebraSpectrumCovering`.
-/


namespace GaloisForLFunctions.HTGeometry

open Polynomial Matrix

/-- **Independence of the powers of a separating element.**  If `n` algebra maps to a field take
pairwise distinct values on `θ`, then `1, θ, …, θ^(n-1)` are linearly independent. -/
theorem linearIndependent_pow_of_separating {K C : Type*} [Field K] [CommRing C] [Algebra K C]
    {n : ℕ} (χ : Fin n → C →ₐ[K] K) {θ : C} (hsep : Function.Injective fun i => χ i θ) :
    LinearIndependent K fun j : Fin n => θ ^ (j : ℕ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hV : (Matrix.vandermonde fun i => χ i θ).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hsep
  have hmul : (Matrix.vandermonde fun i => χ i θ).mulVec c = 0 := by
    funext k
    have h := congrArg (fun x => χ k x) hc
    simp only [map_sum, map_zero, Algebra.smul_def] at h
    simp only [Matrix.mulVec, Matrix.vandermonde_apply, Pi.zero_apply, dotProduct]
    simpa [mul_comm] using h
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hV hmul) i

end GaloisForLFunctions.HTGeometry
