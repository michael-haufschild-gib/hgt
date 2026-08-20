import GaloisForLFunctions.HTGeometry.IsomonodromyGaugeInvariance

/-!
# A fundamental matrix carries the connection of its system

If `Y` is an invertible fundamental matrix for `σ Y = A Y` and the derivation commutes with the
shift, then the logarithmic derivative `ℓδ Y` solves the isomonodromy equation
`σ(B) A = δA + A B`.  Differentiating the system and cancelling `Y` is the whole proof.

When `A` and `ℓδ Y` have entries in the base field, the equation descends there: this is the step
that turns a constant Galois group into isomonodromy over the base.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {R : Type*} [CommRing R] [Differential R]

/-- **A fundamental matrix carries the connection of its system.**  The logarithmic derivative of a
fundamental matrix solves the isomonodromy equation of the system. -/
theorem isomonodromy_of_fundamentalMatrix (σ : R →+* R)
    (hσδ : ∀ x : R, σ (Differential.deriv x) = Differential.deriv (σ x))
    {n : Type*} [Fintype n] [DecidableEq n]
    (A Y : Matrix n n R) [Invertible Y] (hsys : Y.map σ = A * Y) :
    (logDerivMatrix Y).map σ * A = matrixDeriv A + A * logDerivMatrix Y := by
  have hmapmul : ((logDerivMatrix Y) * Y).map σ
      = (logDerivMatrix Y).map σ * Y.map σ := Matrix.map_mul
  have hkey : (logDerivMatrix Y).map σ * A * Y = (matrixDeriv A + A * logDerivMatrix Y) * Y := by
    calc (logDerivMatrix Y).map σ * A * Y
        = (logDerivMatrix Y).map σ * (A * Y) := by rw [mul_assoc]
      _ = (logDerivMatrix Y).map σ * Y.map σ := by rw [hsys]
      _ = ((logDerivMatrix Y) * Y).map σ := hmapmul.symm
      _ = (matrixDeriv Y).map σ := by rw [← matrixDeriv_eq_logDerivMatrix_mul]
      _ = matrixDeriv (Y.map σ) := (matrixDeriv_map σ hσδ Y).symm
      _ = matrixDeriv (A * Y) := by rw [hsys]
      _ = matrixDeriv A * Y + A * matrixDeriv Y := matrixDeriv_mul A Y
      _ = matrixDeriv A * Y + A * (logDerivMatrix Y * Y) := by
          rw [← matrixDeriv_eq_logDerivMatrix_mul]
      _ = (matrixDeriv A + A * logDerivMatrix Y) * Y := by
          rw [add_mul, mul_assoc]
  have hcancel := congrArg (fun M => M * ⅟Y) hkey
  simpa only [mul_assoc, mul_invOf_self, mul_one] using hcancel

/-- The isomonodromy equation descends along an injective differential algebra map. -/
theorem isomonodromy_descend {K : Type*} [Field K] [Differential K] [Algebra K R] [Nontrivial R]
    [DifferentialAlgebra K R] {n : Type*} [Fintype n] [DecidableEq n]
    (σK : K →+* K) (σR : R →+* R)
    (hcompat : ∀ a : K, σR (algebraMap K R a) = algebraMap K R (σK a))
    (A₀ B₀ : Matrix n n K)
    (h : (B₀.map (algebraMap K R)).map σR * A₀.map (algebraMap K R)
      = matrixDeriv (A₀.map (algebraMap K R))
        + A₀.map (algebraMap K R) * B₀.map (algebraMap K R)) :
    B₀.map σK * A₀ = matrixDeriv A₀ + A₀ * B₀ := by
  have hmapσ : (B₀.map (algebraMap K R)).map σR = (B₀.map σK).map (algebraMap K R) := by
    ext i j
    simp only [Matrix.map_apply]
    exact hcompat (B₀ i j)
  have hmapderiv : matrixDeriv (A₀.map (algebraMap K R)) = (matrixDeriv A₀).map (algebraMap K R) := by
    ext i j
    simp only [matrixDeriv_apply, Matrix.map_apply]
    exact deriv_algebraMap (A₀ i j)
  rw [hmapσ, hmapderiv] at h
  have hleft : (B₀.map σK).map (algebraMap K R) * A₀.map (algebraMap K R)
      = ((B₀.map σK) * A₀).map (algebraMap K R) := Matrix.map_mul.symm
  have hright : A₀.map (algebraMap K R) * B₀.map (algebraMap K R)
      = (A₀ * B₀).map (algebraMap K R) := Matrix.map_mul.symm
  rw [hleft, hright, ← Matrix.map_add _ (fun a c => map_add (algebraMap K R) a c)] at h
  ext i j
  have hentry := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at hentry
  exact (algebraMap K R).injective hentry

end

end GaloisForLFunctions.HTGeometry
