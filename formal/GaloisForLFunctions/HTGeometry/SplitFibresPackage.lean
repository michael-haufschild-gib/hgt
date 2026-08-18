import GaloisForLFunctions.HTGeometry.AlgebraSpectrumCovering
import GaloisForLFunctions.HTGeometry.AlgebraCharpoly
import GaloisForLFunctions.HTGeometry.PowerMatrixCramer
import GaloisForLFunctions.HTGeometry.PowerDeterminantNonvanishing
import GaloisForLFunctions.HTGeometry.SplitAlgebraSeparation
import GaloisForLFunctions.HTGeometry.SplitParameterSeparability
import GaloisForLFunctions.HTGeometry.SplitFibrePointsDistinct

/-!
# Packaged splitness of the fibres, and the fibre cardinality it supplies

`SplitFibres B n` says that over every parameter the complex points of `B` form a jointly
surjective family of `n` points exhausting the fibre.  This is the étale/split hypothesis in the
form the chart data of `AlgebraSpectrumCovering` consumes; the cardinality condition follows at
once.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- Packaged splitness of every fibre of the complex-point space. -/
def SplitFibres (B : Type*) [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B]
    [IsScalarTower ℂ ℂ[X] B] (n : ℕ) : Prop :=
  ∀ s : ℂ, ∃ χ : Fin n → AlgSpec B,
    (∀ i, AlgSpec.proj B (χ i) = s) ∧
    (Function.Surjective fun b : B => fun i => χ i b) ∧
    {χ' : AlgSpec B | AlgSpec.proj B χ' = s} = Set.range χ

/-- The fibre cardinality supplied by splitness. -/
theorem ncard_fibre_of_splitFibres {n : ℕ} (h : SplitFibres B n) (s : ℂ) :
    {χ' : AlgSpec B | AlgSpec.proj B χ' = s}.ncard = n := by
  obtain ⟨χ, -, hsurj, hrange⟩ := h s
  have hinj := injective_of_surjective_family χ hsurj
  rw [hrange, Set.ncard_range_of_injective (f := χ) hinj]
  simp

end

end GaloisForLFunctions.HTGeometry
