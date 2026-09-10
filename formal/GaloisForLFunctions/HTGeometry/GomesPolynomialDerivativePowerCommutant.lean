import GaloisForLFunctions.HTGeometry.GomesPolynomialDerivativePowerConjugacy
import GaloisForLFunctions.HTGeometry.GomesPolynomialDerivativeCommutant

/-!
# Full centralizers of all polynomial derivative powers

Every positive derivative power has a matrix algebra of formal-series symmetries.
The zeroth power is the identity and has the entire endomorphism algebra as centralizer.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]

/-- The full centralizer of an arbitrary polynomial derivative power. -/
def gomesPolynomialDerivativePowerCommutantAlgebra (m : ℕ) : Subalgebra K (Module.End K K[X]) :=
  Subalgebra.centralizer K {(Polynomial.derivative ^ m : Module.End K K[X])}

/-- Actual linear symmetries of an arbitrary polynomial derivative power. -/
abbrev GomesPolynomialDerivativePowerCommutant (m : ℕ) :=
  ↥(gomesPolynomialDerivativePowerCommutantAlgebra K m)

/-- Repeated polynomial differentiation has arbitrary formal-series matrices as its full symmetry algebra. -/
def gomesRepeatedPolynomialDerivativeCommutantEquiv
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (Subalgebra.centralizer K {gomesRepeatedEndomorphism K ι (Polynomial.derivative : Module.End K K[X])}) ≃ₐ[K]
      Matrix ι ι (PowerSeries K) :=
  (gomesRepeatedEndomorphismCommutantEquiv K ι (Polynomial.derivative : Module.End K K[X])).trans
    (gomesPolynomialDerivativeCommutantEquiv K).mapMatrix

/-- The complete commutant of the m-th derivative is the m-by-m formal power-series matrix algebra. -/
def gomesPolynomialDerivativePowerCommutantEquiv (m : ℕ) [NeZero m] :
    GomesPolynomialDerivativePowerCommutant K m ≃ₐ[K] Matrix (Fin m) (Fin m) (PowerSeries K) :=
  (gomesCentralizerTransportEquiv K ((gomesPolynomialResidueChainEquiv K m).conjAlgEquiv K)
    (Polynomial.derivative ^ m : Module.End K K[X])).trans
      ((Subalgebra.equivOfEq _ _ (congrArg
        (fun U : Module.End K (Fin m → K[X]) => Subalgebra.centralizer K {U})
          (gomesPolynomialResidueChainEquiv_conjugacy K m))).trans
            (gomesRepeatedPolynomialDerivativeCommutantEquiv K (Fin m)))

omit [CharZero K] in
/-- The zeroth derivative power admits every polynomial endomorphism as a symmetry. -/
theorem gomesPolynomialDerivativePowerCommutant_zero :
    gomesPolynomialDerivativePowerCommutantAlgebra K 0 = ⊤ := by
  ext E
  change E ∈ Subalgebra.centralizer K {(Polynomial.derivative ^ 0 : Module.End K K[X])} ↔ True
  simp [gomesCentralizerSingleton_mem_iff]

/-- Every positive derivative order has its full formal matrix classification with no extra premise. -/
theorem gomesPolynomialDerivativePowerCommutant_succ_classification (m : ℕ) :
    Nonempty (GomesPolynomialDerivativePowerCommutant K (m + 1) ≃ₐ[K]
      Matrix (Fin (m + 1)) (Fin (m + 1)) (PowerSeries K)) :=
  ⟨gomesPolynomialDerivativePowerCommutantEquiv K (m + 1)⟩

/-- Exhaustive classification includes the identity case instead of assuming a positive order. -/
theorem gomesPolynomialDerivativePowerCommutant_classification (m : ℕ) :
    (m = 0 ∧ gomesPolynomialDerivativePowerCommutantAlgebra K m = ⊤) ∨
      ∃ n : ℕ, m = n + 1 ∧
        Nonempty (GomesPolynomialDerivativePowerCommutant K m ≃ₐ[K]
          Matrix (Fin m) (Fin m) (PowerSeries K)) := by
  cases m with
  | zero => exact Or.inl ⟨rfl, gomesPolynomialDerivativePowerCommutant_zero K⟩
  | succ n => exact Or.inr ⟨n, rfl, gomesPolynomialDerivativePowerCommutant_succ_classification K n⟩

/-- Inverse classification acts by the full formal-series matrix on chain coordinates. -/
theorem gomesRepeatedPolynomialDerivativeCommutantEquiv_symm_apply
    (ι : Type*) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (PowerSeries K))
    (P : ι → K[X]) (i : ι) :
    ((gomesRepeatedPolynomialDerivativeCommutantEquiv K ι).symm M).val P i =
      ∑ j, gomesFormalSeriesPolynomialOperator K (M i j) (P j) := rfl

/-- Every formal matrix reconstructs an actual polynomial symmetry by residue-chain conjugation. -/
theorem gomesPolynomialDerivativePowerCommutantEquiv_symm_apply
    (m : ℕ) [NeZero m] (M : Matrix (Fin m) (Fin m) (PowerSeries K)) (P : K[X]) :
    ((gomesPolynomialDerivativePowerCommutantEquiv K m).symm M).val P =
      (gomesPolynomialResidueChainEquiv K m).symm
        (fun i => ∑ j, gomesFormalSeriesPolynomialOperator K (M i j)
          (gomesPolynomialResidueChainEquiv K m P j)) := rfl

end GaloisForLFunctions.HTGeometry
