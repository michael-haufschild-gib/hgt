import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolDifferentialHorizon
import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolSpectralHolography

/-!
# Spectral detection of the differential principal-symbol horizon

Flat matrix principal symbols previously gave two separate conclusions: the differential
dependence locus collapses to the first determinant horizon, and every normalized characteristic
polynomial is constant across filtration depth.  Together they show that the complete
differential-algebraic phase boundary is detected by the zero root of one first-layer spectral
polynomial, while the full normalized spectrum is conserved at every later layer.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {K L g ι : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
  [Fintype ι] [DecidableEq ι]

/-- **Spectral differential-horizon universality law.**  For a flat realized matrix principal
law with one regular direction, every normalized characteristic polynomial is already visible at
the first filtration layer, and differential dependence occurs exactly when zero is a root of
that one first-layer polynomial. -/
theorem matrixPrincipalLowerLaw_spectralDifferentialHorizon
    (source : ι → L) (target : g → ι → L)
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw
      (fun n i ↦ differentialJet n (source i))
      (fun n i ↦ differentialJet n (target A i))
      (fun n ↦ symbol n A))
    (hsource : DifferentialIndependent K source) :
    (∀ n A,
      matrixPrincipalSpectralPolynomial symbol A₀ n A =
        matrixPrincipalSpectralPolynomial symbol A₀ 0 A) ∧
      (∀ A,
        A ∈ matrixDifferentialDependentSet (K := K) target ↔
          (matrixPrincipalSpectralPolynomial symbol A₀ 0 A).IsRoot 0) := by
  refine ⟨matrixPrincipalSpectralPolynomial_eq_first symbol hflat A₀ hA₀, ?_⟩
  intro A
  rw [matrixDifferentialDependentSet_eq_firstSingularSet_of_flat
    source target symbol hflat A₀ hA₀ hlaw hsource]
  change (symbol 0 A).det = 0 ↔ _
  rw [Polynomial.IsRoot]
  simp only [matrixPrincipalSpectralPolynomial, normalizedMatrixPrincipalSymbol,
    Matrix.eval_charpoly]
  simp only [map_zero, zero_sub]
  rw [Matrix.det_neg, Matrix.det_mul]
  simp [hA₀ 0]

end


end GaloisForLFunctions.HTGeometry
