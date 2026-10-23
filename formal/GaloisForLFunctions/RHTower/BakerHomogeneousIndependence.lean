import GaloisForLFunctions.RHTower.BakerGeneralStatement
import GaloisForLFunctions.RHTower.BakerGeneralProof.BakerGeneralCapstone

/-!
# Homogeneous Baker independence, unconditionally

`BakerTheorem.homogeneous` restricts the inhomogeneous family `{1} ∪ {λᵢ}` of Baker's theorem to
the logarithms themselves; `bakerTheorem_holds` proves the inhomogeneous theorem.
-/

namespace GaloisForLFunctions.RHTower

/-- **Baker.** `ℚ`-linearly independent logarithms of algebraic numbers are linearly independent
over the algebraic numbers. -/
theorem baker_homogeneous_linearIndependent
    (n : ℕ) (lambda : Fin n → ℂ)
    (halg : ∀ i, IsLogarithmOfAlgebraic (lambda i))
    (hind : LinearIndependent ℚ lambda) :
    LinearIndependent (algebraicClosure ℚ ℂ) lambda :=
  bakerTheorem_holds.homogeneous n lambda halg hind

end GaloisForLFunctions.RHTower
