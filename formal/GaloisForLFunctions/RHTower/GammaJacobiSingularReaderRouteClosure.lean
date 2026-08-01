import GaloisForLFunctions.RHTower.GammaJacobiEulerTailCyclicReaderNoGo
import GaloisForLFunctions.RHTower.VonMangoldtCounterreaderBarycentricAggregation
import GaloisForLFunctions.RHTower.VonMangoldtCyclicReaderFluxNoGo

/-!
# Route M Gamma--Jacobi singular-reader closure

Capstone for Route M's finite source class.  The literal Euler clock and Szegő aperture loss
saturate every finite prime matrix algebra; the actual accumulated Toeplitz counterreader is
noncyclic even on two jet coordinates; and edgewise symbol multiplication fails for the first two
literal von Mangoldt edges already at the first nonconstant coefficient.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Route M's saturated finite carrier cannot support a positively normalized,
inclusion-compatible cyclic reader with one fixed value on consecutive actual source sections. -/
theorem gammaJacobiSingularReader_positiveCyclicReaderFluxNoGo
    (M N : ℕ) (hM : 0 < M) :
    ¬ ∃ (Φ0 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ →ₗ[ℝ] ℝ)
        (Φ1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ →ₗ[ℝ] ℝ),
      HTGeometry.MatrixCyclicReader Φ0 ∧
      HTGeometry.MatrixCyclicReader Φ1 ∧
      0 < Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) ∧
      Φ0 (Matrix.single (0 : Fin (N + 1)) 0 1) =
        Φ1 (Matrix.single (0 : Fin (N + 2)) 0 1) ∧
      Φ0 (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 1)) =
        Φ1 (finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (N + 2)) :=
  not_exists_fixedValue_inclusionCompatible_cyclicReaders_finiteVonMangoldtSuccessor M N hM

/-- **Route M finite-carrier closure.**  The three unconditional obstructions hold simultaneously
for every injective finite prime packet and every Gamma--Jacobi tail aperture. -/
theorem gammaJacobiSingularReaderRouteClosure
    {I : Type*} [Fintype I] [DecidableEq I]
    (prime : I → Nat.Primes) (hprime : Function.Injective prime) (K : ℕ) :
    Algebra.adjoin ℝ
          {gammaJacobiPrimeEulerClock prime,
            gammaJacobiPrimeTailApertureLoss prime K} = ⊤ ∧
      (¬ HTGeometry.MatrixDensityClockCyclic
        (finiteVonMangoldtJetDensity
          vonMangoldtHankelToeplitzCounterDensity 2)
        (fun i : Fin 2 => (i : ℝ))) ∧
      counterreaderFirstSymbolCoefficient
          (finiteVonMangoldtSuccessorRelativeMoment 2) ≠
        counterreaderFirstSymbolCoefficient
            (fun q => vonMangoldtSuccessorRelativeMomentTerm q 2) +
          counterreaderFirstSymbolCoefficient
            (fun q => vonMangoldtSuccessorRelativeMomentTerm q 3) := by
  exact ⟨gammaJacobiTail_euler_generatedSubalgebra_eq_top prime hprime K,
    vonMangoldtCounterreader_not_clockCyclic,
    vonMangoldt_twoEdgeCounterreaderFirstCoefficient_ne_product⟩

end

end RHTower
