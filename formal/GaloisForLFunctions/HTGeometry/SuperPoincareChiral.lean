import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection

namespace SuperPoincare

/-- Chiral basis of the one-dimensional `N = 2` supertranslation algebra. -/
structure D1N2Chiral (R : Type*) [Ring R] where
  supercharge : R
  conjugateSupercharge : R
  momentum : R
  supercharge_sq_zero : supercharge * supercharge = 0
  conjugateSupercharge_sq_zero : conjugateSupercharge * conjugateSupercharge = 0
  mixed_anticommutator :
    supercharge * conjugateSupercharge +
      conjugateSupercharge * supercharge = momentum

namespace D1N2Chiral

variable {R : Type*} [Ring R] (S : D1N2Chiral R)

/-- Chiral supertranslation momentum commutes with the first odd charge. -/
theorem momentum_commutes_supercharge :
    S.momentum * S.supercharge = S.supercharge * S.momentum := by
  have hzero :
      S.supercharge * (S.supercharge * S.conjugateSupercharge) = 0 := by
    rw [← mul_assoc, S.supercharge_sq_zero, zero_mul]
  rw [← S.mixed_anticommutator]
  calc
    (S.supercharge * S.conjugateSupercharge +
        S.conjugateSupercharge * S.supercharge) * S.supercharge =
      S.supercharge * (S.conjugateSupercharge * S.supercharge) +
        S.conjugateSupercharge * (S.supercharge * S.supercharge) := by
          simp only [add_mul, mul_assoc]
    _ = S.supercharge * (S.conjugateSupercharge * S.supercharge) := by
      rw [S.supercharge_sq_zero]
      simp
    _ = S.supercharge * (S.supercharge * S.conjugateSupercharge) +
        S.supercharge * (S.conjugateSupercharge * S.supercharge) := by
      rw [hzero, zero_add]
    _ = S.supercharge *
        (S.supercharge * S.conjugateSupercharge +
          S.conjugateSupercharge * S.supercharge) := by rw [mul_add]

/-- Chiral supertranslation momentum commutes with the conjugate odd charge. -/
theorem momentum_commutes_conjugateSupercharge :
    S.momentum * S.conjugateSupercharge =
      S.conjugateSupercharge * S.momentum := by
  have hzero :
      S.conjugateSupercharge *
        (S.conjugateSupercharge * S.supercharge) = 0 := by
    rw [← mul_assoc, S.conjugateSupercharge_sq_zero, zero_mul]
  rw [← S.mixed_anticommutator]
  calc
    (S.supercharge * S.conjugateSupercharge +
        S.conjugateSupercharge * S.supercharge) * S.conjugateSupercharge =
      S.supercharge * (S.conjugateSupercharge * S.conjugateSupercharge) +
        S.conjugateSupercharge * (S.supercharge * S.conjugateSupercharge) := by
          simp only [add_mul, mul_assoc]
    _ = S.conjugateSupercharge *
        (S.supercharge * S.conjugateSupercharge) := by
      rw [S.conjugateSupercharge_sq_zero]
      simp
    _ = S.conjugateSupercharge *
          (S.supercharge * S.conjugateSupercharge) +
        S.conjugateSupercharge *
          (S.conjugateSupercharge * S.supercharge) := by
      rw [hzero, add_zero]
    _ = S.conjugateSupercharge *
        (S.supercharge * S.conjugateSupercharge +
          S.conjugateSupercharge * S.supercharge) := by rw [mul_add]

end D1N2Chiral

end SuperPoincare

namespace HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection

/-- Differential and contracting homotopy of the exact two-term complex are chiral supercharges. -/
def exactModelChiralD1N2 :
    SuperPoincare.D1N2Chiral (Module.End ℝ (ℝ × ℝ)) where
  supercharge := exactModelDifferential
  conjugateSupercharge := exactModelHomotopy
  momentum := 1
  supercharge_sq_zero := exactModelDifferential_sq
  conjugateSupercharge_sq_zero := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp [exactModelHomotopy]
  mixed_anticommutator := exactModel_contraction

end HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection
