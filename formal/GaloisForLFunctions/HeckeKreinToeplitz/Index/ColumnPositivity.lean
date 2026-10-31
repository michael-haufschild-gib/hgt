import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnForm
import GaloisForLFunctions.HTGeometry.AppellHumbertGaussianBound

/-!
# Cauchy–Schwarz on nonnegative column subspaces

An indefinite kernel pairing restricts to a positive semidefinite Hermitian form
on each nonnegative subspace. Its mixed pairings obey Cauchy–Schwarz.
-/

open Complex Module
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G : Type*} [Group G]

/-- Cauchy–Schwarz holds on each nonnegative subspace of an indefinite column form. -/
theorem kernelColumnPairing_normSq_le_on_subspace {k : G → ℂ} (hk : IsHermKernel k)
    (W : Submodule ℂ (kernelColumnSpan k))
    (hW : ∀ x ∈ W, 0 ≤ (kernelColumnPairing k x x).re)
    (v w : kernelColumnSpan k) (hv : v ∈ W) (hw : w ∈ W) :
    normSq (kernelColumnPairing k v w) ≤
      (kernelColumnPairing k v v).re * (kernelColumnPairing k w w).re := by
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  let H : W → W → ℂ := fun x y => kernelColumnPairing k y x
  have hH : IsHermitianForm H :=
    { add_left := fun x y z => by
        change kernelColumnPairing k z ((x : kernelColumnSpan k) + y) = _
        exact map_add (kernelColumnPairing k (z : kernelColumnSpan k))
          (x : kernelColumnSpan k) (y : kernelColumnSpan k)
      smul_left := fun a x y => by
        change kernelColumnPairing k y (a • (x : kernelColumnSpan k)) = _
        rw [map_smul, smul_eq_mul]
      symm := fun x y => kernelColumnPairing_conj_symm hk x y }
  have hb := hH.norm_sq_le (fun x => hW x x.property) ⟨w, hw⟩ ⟨v, hv⟩
  simpa only [H, normSq_eq_norm_sq, mul_comm] using hb

#print axioms kernelColumnPairing_normSq_le_on_subspace
end GaloisForLFunctions.HeckeKreinToeplitz
