import GaloisForLFunctions.SelbergClass.Primon.SemicircleMoments
import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircleCoordinateLaw

/-!
# Free Fock realization of the limiting prime moments

The one-letter, one-coordinate free Fock operator is creation plus
annihilation on the half-line. Its Dyson recursion is the Catalan recursion.
Its vacuum moments therefore equal the actual limiting phase integrals,
and the prime Hecke moments converge to this concrete operator model.
-/

open Filter Topology Matrix
open scoped Matrix
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- A single scalar generator: the resulting Fock action is creation plus annihilation. -/
def scalarFockGenerator : Unit → Matrix Unit Unit ℂ := fun _ => 1

private theorem scalarFockGenerator_hermitian :
    ∀ k, (scalarFockGenerator k)ᴴ = scalarFockGenerator k := by
  intro k
  simp [scalarFockGenerator]

private theorem scalarFockGenerator_trivialKernel : HasTrivialCommonKernel scalarFockGenerator := by
  intro x hx
  funext i
  simpa [scalarFockGenerator] using hx () i

/-- The scalar Dyson branch has exactly the Catalan coefficients. -/
theorem scalarDysonCoefficient_catalan (n : ℕ) :
    matrixDysonFormalCoeff scalarFockGenerator n () () = (catalan n : ℂ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [matrixDysonFormalCoeff]
    | succ n =>
      rw [matrixDysonFormalCoeff, catalan_succ]
      simp only [Matrix.sum_apply, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp [matrixSemicircleCovariance, scalarFockGenerator, Matrix.mul_apply,
        ih k k.isLt, ih (n - k) (by omega)]

/-- Even vacuum moments of scalar creation plus annihilation are Catalan numbers. -/
theorem scalarFockMoment_even (n : ℕ) :
    freeFockCoordinateMoment scalarFockGenerator () (2 * n) = (catalan n : ℝ) := by
  have h := coeff_matrixDysonFormalSeries_eq_coordinateMoment_even
    scalarFockGenerator scalarFockGenerator_hermitian () n
  rw [coeff_matrixDysonFormalSeries, scalarDysonCoefficient_catalan] at h
  exact_mod_cast h.symm

/-- The scalar Fock vacuum has no odd moments. -/
theorem scalarFockMoment_odd (n : ℕ) :
    freeFockCoordinateMoment scalarFockGenerator () (2 * n + 1) = 0 := by
  unfold freeFockCoordinateMoment
  rw [freeFockPower_vacuumCoefficient scalarFockGenerator scalarFockGenerator_hermitian,
    if_neg (by omega : ¬2 ∣ 2 * n + 1)]
  rfl

/-- Actual semicircle phase integrals equal the scalar free Fock vacuum moments. -/
theorem semicircleMoment_eq_scalarFockMoment (n : ℕ) :
    semicircleMoment n = freeFockCoordinateMoment scalarFockGenerator () n := by
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn, semicircleMoment_even, scalarFockMoment_even]
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, semicircleMoment_odd, scalarFockMoment_odd]

/-- Prime Hecke moments converge to the concrete scalar free-Fock vacuum moments. -/
theorem tendsto_kestenMoment_scalarFock (n : ℕ) :
    Tendsto (fun p => kestenMoment p n) cofinite
      (𝓝 (freeFockCoordinateMoment scalarFockGenerator () n)) := by
  rw [← semicircleMoment_eq_scalarFockMoment]
  exact tendsto_kestenMoment n

/-- The limiting moment form remains strictly positive, by its explicit Fock realization. -/
theorem semicircleMoment_positiveMomentForm :
    _root_.HTGeometry.PositiveMomentForm semicircleMoment := by
  have he : semicircleMoment = freeFockCoordinateMoment scalarFockGenerator () :=
    funext semicircleMoment_eq_scalarFockMoment
  rw [he]
  exact freeFockCoordinateMoment_positiveMomentForm scalarFockGenerator
    scalarFockGenerator_hermitian scalarFockGenerator_trivialKernel ()

/-- Probability law of the scalar free Fock vacuum. -/
def scalarFockSpectralLaw : MeasureTheory.ProbabilityMeasure ℝ :=
  freeFockCoordinateSpectralLaw scalarFockGenerator scalarFockGenerator_hermitian
    scalarFockGenerator_trivialKernel ()

/-- The scalar Fock probability law represents the actual semicircle phase moments. -/
theorem scalarFockSpectralLaw_hasMoments :
    HasHamburgerMoments semicircleMoment
      (scalarFockSpectralLaw : MeasureTheory.Measure ℝ) := by
  intro n
  have h := freeFockCoordinateSpectralLaw_hasMoments scalarFockGenerator
    scalarFockGenerator_hermitian scalarFockGenerator_trivialKernel () n
  simpa only [scalarFockSpectralLaw, ← semicircleMoment_eq_scalarFockMoment] using h

end
end GaloisForLFunctions.SelbergClass.Primon
