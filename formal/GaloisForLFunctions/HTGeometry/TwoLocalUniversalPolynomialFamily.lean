import GaloisForLFunctions.HTGeometry.PolynomialMatrixSimpleSpectrumTransport
import GaloisForLFunctions.HTGeometry.TwoLocalFullStarSpectrum
import Mathlib.Tactic

/-!
# One universal polynomial family for every selected star edge

All explicit selected-edge loops with a fixed distinguished Boolean
coordinate are placed in a single polynomial two-local matrix family.  Its
coordinates are precisely the constant, longitudinal, transverse, onsite,
and distinguished-star interaction coefficients.

Any two selected-edge basepoints can therefore be joined in the
nonvanishing characteristic-resultant locus.  This is the exact
common-family and common-component theorem required before conjugating the
local sheet swaps to one spectral basepoint.
-/

open scoped BigOperators

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

/-- Coefficient coordinates of the distinguished-star two-local family. -/
inductive DistinguishedStarTwoLocalParameter (m : ℕ)
  | constant
  | longitudinal
  | transverse
  | onsite (i : Fin m)
  | interaction (i : Fin m)
  deriving DecidableEq, Fintype

/-- Universal polynomial matrix with one variable for each allowed
distinguished-star two-local coefficient. -/
noncomputable def universalDistinguishedStarTwoLocalPolynomialMatrix
    (m : ℕ) :
    Matrix (Bool × (Fin m → Bool))
      (Bool × (Fin m → Bool))
      (MvPolynomial (DistinguishedStarTwoLocalParameter m) ℂ) :=
  fun x y =>
    if x = y then
      MvPolynomial.X .constant +
        MvPolynomial.X .longitudinal *
          MvPolynomial.C (boolOccupation x.1 : ℂ) +
        ∑ i, MvPolynomial.X (.onsite i) *
          MvPolynomial.C (boolOccupation (x.2 i) : ℂ) +
        ∑ i, MvPolynomial.X (.interaction i) *
          MvPolynomial.C (boolOccupation x.1 : ℂ) *
          MvPolynomial.C (boolOccupation (x.2 i) : ℂ)
    else if x.2 = y.2 then
      MvPolynomial.X .transverse
    else 0

/-- Evaluation of the polynomial family is exactly the standard
two-local coefficient model. -/
theorem eval_universalDistinguishedStarTwoLocalPolynomialMatrix
    (m : ℕ)
    (p : DistinguishedStarTwoLocalParameter m → ℂ) :
    (universalDistinguishedStarTwoLocalPolynomialMatrix m).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) p) =
      distinguishedStarTwoLocalHamiltonian
        (p .constant) (p .longitudinal) (p .transverse)
        (fun i => p (.onsite i))
        (fun i => p (.interaction i)) := by
  ext x y
  simp only [Matrix.map_apply,
    universalDistinguishedStarTwoLocalPolynomialMatrix,
    distinguishedStarTwoLocalHamiltonian]
  split_ifs <;> simp

/-- Every explicitly two-local distinguished-star matrix is an evaluation
of the one universal polynomial family. -/
theorem exists_universalDistinguishedStarTwoLocal_coordinates {m : ℕ}
    (H : Matrix (Bool × (Fin m → Bool))
      (Bool × (Fin m → Bool)) ℂ)
    (hH : IsComplexDistinguishedStarTwoLocalHamiltonian H) :
    ∃ p : DistinguishedStarTwoLocalParameter m → ℂ,
      (universalDistinguishedStarTwoLocalPolynomialMatrix m).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) p) = H := by
  rcases hH with
    ⟨constant, longitudinal, transverse, onsite,
      interaction, rfl⟩
  let p : DistinguishedStarTwoLocalParameter m → ℂ
    | .constant => constant
    | .longitudinal => longitudinal
    | .transverse => transverse
    | .onsite i => onsite i
    | .interaction i => interaction i
  refine ⟨p, ?_⟩
  rw [eval_universalDistinguishedStarTwoLocalPolynomialMatrix]

/-- Every selected-edge full Hamiltonian, at every complex continuation
parameter, belongs to the same universal polynomial family. -/
theorem exists_twoLocalSelectedEdge_universal_coordinates {m : ℕ}
    (z₀ : Fin m → Bool) (w : ℂ) :
    ∃ p : DistinguishedStarTwoLocalParameter m → ℂ,
      (universalDistinguishedStarTwoLocalPolynomialMatrix m).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) p) =
        twoLocalStarHamiltonianMatrix z₀ w :=
  exists_universalDistinguishedStarTwoLocal_coordinates _
    (twoLocalStarHamiltonian_is_complex_twoLocal z₀ w)

/-- Any two selected-edge loop basepoints lie in the same path component
of the simple-spectrum locus of one polynomial two-local family. -/
theorem exists_twoLocalSelectedEdges_commonBaseTransport {m : ℕ}
    (z₀ z₁ : Fin m → Bool) :
    ∃ (p₀ p₁ : DistinguishedStarTwoLocalParameter m → ℂ),
      (universalDistinguishedStarTwoLocalPolynomialMatrix m).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) p₀) =
        twoLocalStarHamiltonianMatrix z₀
          (twoLocalSelectedEdgeParameter 0) ∧
      (universalDistinguishedStarTwoLocalPolynomialMatrix m).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) p₁) =
        twoLocalStarHamiltonianMatrix z₁
          (twoLocalSelectedEdgeParameter 0) ∧
      ∃ path : Path p₀ p₁,
        ∀ s : I,
          MvPolynomial.eval (path s)
            (matrixCharacteristicResultantPolynomial
              (universalDistinguishedStarTwoLocalPolynomialMatrix m)) ≠ 0 := by
  obtain ⟨p₀, hp₀⟩ :=
    exists_twoLocalSelectedEdge_universal_coordinates z₀
      (twoLocalSelectedEdgeParameter 0)
  obtain ⟨p₁, hp₁⟩ :=
    exists_twoLocalSelectedEdge_universal_coordinates z₁
      (twoLocalSelectedEdgeParameter 0)
  refine ⟨p₀, p₁, hp₀, hp₁, ?_⟩
  apply exists_parameterPath_of_complete_injective_rootPackets
    (universalDistinguishedStarTwoLocalPolynomialMatrix m) p₀ p₁
    (fun x => twoLocalGlobalEigenvalueLift z₀ x 0)
    (fun x => twoLocalGlobalEigenvalueLift z₁ x 0)
    (twoLocalGlobalEigenvalueLift_injective z₀ 0)
    (twoLocalGlobalEigenvalueLift_injective z₁ 0)
  · intro x
    rw [hp₀]
    exact twoLocalGlobalEigenvalueLift_fullMatrix_root z₀ x 0
  · intro x
    rw [hp₁]
    exact twoLocalGlobalEigenvalueLift_fullMatrix_root z₁ x 0

end GaloisForLFunctions.HTGeometry
