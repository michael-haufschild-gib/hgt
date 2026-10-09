import GaloisForLFunctions.HTGeometry.LocallyNilpotentDerivationSlice
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
The native rational slice theorem, retaining the complex algebra structure.
This bridge supports the locally nilpotent clocks obtained from the proven
stable-coordinate construction in OpenAI/math.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ B] [Algebra ℚ B]
  [IsScalarTower ℚ ℂ B]

/-- Constants of a complex-linear derivation, with their complex algebra structure. -/
def complexDerivationKernel (D : Derivation ℂ B B) : Subalgebra ℂ B :=
  { (derivationKernel (D.restrictScalars ℚ)).toSubsemiring with
    algebraMap_mem' := D.map_algebraMap }

@[simp] theorem mem_complexDerivationKernel (D : Derivation ℂ B B) {b : B} :
    b ∈ complexDerivationKernel D ↔ D b = 0 := Iff.rfl

/-- A slice has unique polynomial expressions over the complex constants. -/
theorem complexSlice_aeval_injective (D : Derivation ℂ B B) {s : B} (hs : D s = 1) :
    Function.Injective (Polynomial.aeval s :
      Polynomial (complexDerivationKernel D) →ₐ[complexDerivationKernel D] B) :=
  aeval_slice_injective (D.restrictScalars ℚ) hs

theorem complexSlice_aeval_bijective (D : Derivation ℂ B B) {s : B} (hs : D s = 1)
    (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) :
    Function.Bijective ((Polynomial.aeval s :
      Polynomial (complexDerivationKernel D) →ₐ[complexDerivationKernel D] B).restrictScalars ℂ) :=
  bijective_aeval_of_locallyNilpotent (D.restrictScalars ℚ) hs hnil

/-- Polynomial splitting over constants, as a complex algebra equivalence. -/
def complexSliceAlgEquiv (D : Derivation ℂ B B) {s : B} (hs : D s = 1)
    (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) :
    Polynomial (complexDerivationKernel D) ≃ₐ[ℂ] B :=
  AlgEquiv.ofBijective ((Polynomial.aeval s :
    Polynomial (complexDerivationKernel D) →ₐ[complexDerivationKernel D] B).restrictScalars ℂ)
      (complexSlice_aeval_bijective D hs hnil)

@[simp] theorem complexSliceAlgEquiv_X (D : Derivation ℂ B B) {s : B} (hs : D s = 1)
    (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) :
    complexSliceAlgEquiv D hs hnil Polynomial.X = s := by
  exact Polynomial.aeval_X s

theorem complexSlice_unique_polynomial (D : Derivation ℂ B B) {s : B} (hs : D s = 1)
    (hnil : ∀ b : B, ∃ n : ℕ, (D^[n]) b = 0) (b : B) :
    ∃! p : Polynomial (complexDerivationKernel D), Polynomial.aeval s p = b := by
  obtain ⟨p, hp⟩ := (complexSlice_aeval_bijective D hs hnil).surjective b
  exact ⟨p, hp, fun q hq => complexSlice_aeval_injective D hs (hq.trans hp.symm)⟩

end
end GaloisForLFunctions.HTGeometry
