import GaloisForLFunctions.EffectiveScalingGeometry.PrimeAugmentedHomology
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor coordinates for actual prime-cutoff homology

Surviving odd faces form a basis of actual augmented homology in every degree.
Base-changing the integral basis gives a coefficient-ring linear equivalence
from the tensor product of integral homology to coefficient-ring homology.
On pure tensors its surviving coefficients are the integral coefficients times
the scalar. Agreement with the map induced by canonical chain extension, and
height naturality of that agreement, are separate compatibility statements.
-/

noncomputable section
open CategoryTheory RHTower
open scoped TensorProduct
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Actual augmented homology expressed in its surviving odd-face coefficients. -/
def primeHomologyCoordinateEquiv (k N : ℕ) :
    (primeCutoffHomology R (primeChainAugmentation R) k).obj N ≃ₗ[R]
      (primeCriticalFaces k N →₀ R) :=
  ((primeHomologyCriticalIso R k).app N).toLinearEquiv.trans
    (Finsupp.supportedEquivFinsupp (R := R) (primeCriticalFaces k N))

/-- The surviving faces index a basis of the actual homology module. -/
def primeHomologyCriticalBasis (k N : ℕ) :
    Module.Basis (primeCriticalFaces k N) R
      ((primeCutoffHomology R (primeChainAugmentation R) k).obj N) :=
  ⟨primeHomologyCoordinateEquiv R k N⟩

theorem primeHomologyCoordinateEquiv_basis (k N : ℕ) (s : primeCriticalFaces k N) :
    primeHomologyCoordinateEquiv R k N (primeHomologyCriticalBasis R k N s) = Finsupp.single s 1 :=
  (primeHomologyCriticalBasis R k N).repr_self s

/-- Base-changing the integral coordinate basis gives the same coefficient-ring basis. -/
def primeHomologyCoordinateBaseChange (k N : ℕ) :
    (R ⊗[ℤ] ((primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).obj N)) ≃ₗ[R]
      ((primeCutoffHomology R (primeChainAugmentation R) k).obj N) :=
  ((primeHomologyCriticalBasis ℤ k N).baseChange R).repr.trans
    (primeHomologyCriticalBasis R k N).repr.symm

theorem primeHomologyCoordinateBaseChange_basis (k N : ℕ) (s : primeCriticalFaces k N) :
    primeHomologyCoordinateBaseChange R k N
      ((1 : R) ⊗ₜ[ℤ] primeHomologyCriticalBasis ℤ k N s) = primeHomologyCriticalBasis R k N s := by
  rw [← Module.Basis.baseChange_apply]
  change (primeHomologyCriticalBasis R k N).repr.symm
    (((primeHomologyCriticalBasis ℤ k N).baseChange R).repr
      ((primeHomologyCriticalBasis ℤ k N).baseChange R s)) = _
  simp only [Module.Basis.repr_self,Module.Basis.repr_symm_single,one_smul]

/-- The tensor comparison multiplies each integral coefficient by the scalar. -/
theorem primeHomologyCoordinateBaseChange_tmul (k N : ℕ) (r : R)
    (x : (primeCutoffHomology ℤ (primeChainAugmentation ℤ) k).obj N)
    (s : primeCriticalFaces k N) :
    primeHomologyCoordinateEquiv R k N (primeHomologyCoordinateBaseChange R k N (r ⊗ₜ[ℤ] x)) s =
      primeHomologyCoordinateEquiv ℤ k N x s • r := by
  change (primeHomologyCriticalBasis R k N).repr
    ((primeHomologyCriticalBasis R k N).repr.symm
      (((primeHomologyCriticalBasis ℤ k N).baseChange R).repr (r ⊗ₜ[ℤ] x))) s = _
  rw [LinearEquiv.apply_symm_apply]
  exact Module.Basis.baseChange_repr_tmul R (primeHomologyCriticalBasis ℤ k N) r x s

#print axioms primeHomologyCriticalBasis
#print axioms primeHomologyCoordinateBaseChange
#print axioms primeHomologyCoordinateBaseChange_tmul
end GaloisForLFunctions.EffectiveScalingGeometry
