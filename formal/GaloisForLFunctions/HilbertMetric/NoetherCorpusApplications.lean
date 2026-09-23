import GaloisForLFunctions.HilbertMetric.HilbertLineCommutatorCurvature
import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow

/-!
# Noether applications in Hilbert and symmetric-Fock geometry

Reflection and translation preserve compressed annihilation curvature energy.  Symmetric-Fock
lowering and raising operators carry exact number-operator charges.
-/

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

/-- Reflection of every line coordinate preserves compressed annihilation curvature energy. -/
theorem noetherFirst_hilbertLineReflectionEnergy
    {n : ℕ} (ξ : Fin n → ℝ) (t : ℝ) :
    matrixHilbertSchmidtEnergy
        (matrixSelfCommutator (hilbertLineAnnihilationCompression (fun i => -ξ i) t)) =
      matrixHilbertSchmidtEnergy
        (matrixSelfCommutator (hilbertLineAnnihilationCompression ξ t)) :=
  hilbertLineAnnihilationEnergy_reflection_invariant ξ t

/-- Translating the canonical distinct line configuration preserves its curvature energy. -/
theorem noetherFirst_hilbertLineTranslationEnergy
    {n : ℕ} (c : ℝ) :
    matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (hilbertLineAnnihilationCompression (fun i : Fin n => (i : ℝ) + c) 1)) =
      matrixHilbertSchmidtEnergy
        (matrixSelfCommutator
          (hilbertLineAnnihilationCompression (fun i : Fin n => (i : ℝ)) 1)) := by
  exact hilbertLineAnnihilationEnergy_translation_invariant
    (ξ := fun i : Fin n => (i : ℝ))
    (fun i j h => by
      apply Fin.ext
      exact Nat.cast_inj.mp h) c zero_lt_one

/-- Total symmetric-Fock lowering energy is the exact degree charge `n+1`. -/
theorem noetherFirst_symmetricFockLoweringCharge
    {I : Type*} [Fintype I] [DecidableEq I]
    (n : ℕ) (x : EuclideanSpace ℝ (Sym I (n + 1))) :
    ∑ i, ‖(symmetricFockAnnihilation n i) x‖ ^ (2 : ℕ) =
      ((n : ℝ) + 1) * ‖x‖ ^ (2 : ℕ) :=
  symmetricFockAnnihilation_energy n x

/-- Total adjoint-raising energy is degree plus mode-count charge. -/
theorem noetherFirst_symmetricFockRaisingCharge
    {I : Type*} [Fintype I] [DecidableEq I]
    (n : ℕ) (y : EuclideanSpace ℝ (Sym I n)) :
    ∑ i, ‖(symmetricFockAnnihilation n i).adjoint y‖ ^ (2 : ℕ) =
      ((n : ℝ) + Fintype.card I) * ‖y‖ ^ (2 : ℕ) :=
  symmetricFockAnnihilation_adjoint_energy n y

end GaloisForLFunctions.HilbertMetric
