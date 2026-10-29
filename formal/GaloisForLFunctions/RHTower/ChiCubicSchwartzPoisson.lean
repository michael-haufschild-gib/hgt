import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicFourierLattice
import GaloisForLFunctions.RHTower.ChiCompactLatticePoisson
import GaloisForLFunctions.HTGeometry.SchwartzPoissonSummation

/-!
# Three-dimensional Schwartz Poisson summation

The physical integer-triple lattice is the three-dimensional specialization of
twisted Schwartz Poisson summation, with every Fourier lift retained.
-/

noncomputable section
open scoped FourierTransform

namespace RHTower.BAGTrace.FullPoisson

private def triples : Z ≃ ℤ × ℤ × ℤ where
  toFun n := (n 0,n 1,n 2)
  invFun n := ![n.1,n.2.1,n.2.2]
  left_inv n := by ext i; fin_cases i <;> rfl
  right_inv n := rfl

private lemma triples_point (n : Z) :
    GaloisForLFunctions.HTGeometry.IntegerLatticePoisson.euclideanIntegerPoint n =
      bagIntegerTriple (triples n) := by
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;> rfl

/-- Twisted Poisson summation for every physical Schwartz input and real frequency. -/
theorem full_schwartz_poisson (f : SchwartzMap BAGPhysicalSpace ℂ) (a : BAGPhysicalSpace) :
    (∑' k : ℤ × ℤ × ℤ, (𝓕 f) (bagIntegerTriple k - a)) =
      ∑' n : ℤ × ℤ × ℤ,
        Complex.exp ((2 * Real.pi * inner ℝ (bagIntegerTriple n) a : ℝ) * Complex.I) *
          f (bagIntegerTriple n) := by
  have h := GaloisForLFunctions.HTGeometry.IntegerLatticePoisson.schwartz_poisson_twisted f a
  calc
    _ = ∑' k : Z, (𝓕 f) (bagIntegerTriple (triples k) - a) :=
      (triples.tsum_eq (fun k => (𝓕 f) (bagIntegerTriple k - a))).symm
    _ = ∑' n : Z,
        Complex.exp ((2 * Real.pi * inner ℝ (bagIntegerTriple (triples n)) a : ℝ) * Complex.I) *
          f (bagIntegerTriple (triples n)) := by
      simpa only [triples_point] using h
    _ = _ := triples.tsum_eq (fun n : ℤ × ℤ × ℤ =>
      Complex.exp ((2 * Real.pi * inner ℝ (bagIntegerTriple n) a : ℝ) * Complex.I) *
        f (bagIntegerTriple n))

end RHTower.BAGTrace.FullPoisson
