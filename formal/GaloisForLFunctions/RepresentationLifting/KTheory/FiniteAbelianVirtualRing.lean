import GaloisForLFunctions.RepresentationLifting.KTheory.VirtualCharacterK0
import GaloisForLFunctions.RHTower.Artin.ArtinFiniteAbelianFourier
import GaloisForLFunctions.HTGeometry.GroupAlgebras.FirstJet

/-!
# The integral group algebra of finite abelian characters

Integral Fourier decomposition identifies the concrete virtual-character ring
of a finite abelian group with the integral group algebra of its character
group. Under this ring isomorphism, dimension is coefficient summation.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open scoped BigOperators
open HTGeometry.GroupAlgebraFirstJet
variable (G : Type*) [CommGroup G] [Fintype G]

local instance : Finite (LinearCharacter G) := RHTower.deningerCharacterGroup_finite
local instance : Fintype (LinearCharacter G) := Fintype.ofFinite _

/-- A linear character as an element of the concrete virtual-character ring. -/
def linearCharacterVirtualHom : LinearCharacter G →* VirtualRepresentationRing G where
  toFun χ := ⟨(linearVirtualCharacter G χ).val, (linearVirtualCharacter G χ).property⟩
  map_one' := by
    ext g
    change (linearVirtualCharacter G (1 : LinearCharacter G)).val g = 1
    simp only [linearVirtualCharacter_apply, MonoidHom.one_apply, Units.val_one]
  map_mul' χ ψ := by
    ext g
    change (linearVirtualCharacter G (χ * ψ)).val g =
      (linearVirtualCharacter G χ).val g * (linearVirtualCharacter G ψ).val g
    simp only [linearVirtualCharacter_apply, MonoidHom.mul_apply, Units.val_mul]

/-- Integral character combinations with convolution multiplication. -/
def finiteAbelianCharacterAlgebraHom :
    MonoidAlgebra ℤ (LinearCharacter G) →ₐ[ℤ] VirtualRepresentationRing G :=
  MonoidAlgebra.lift ℤ _ _ (linearCharacterVirtualHom G)

theorem finiteAbelianCharacterAlgebraHom_single (χ : LinearCharacter G) (z : ℤ) :
    finiteAbelianCharacterAlgebraHom G (MonoidAlgebra.single χ z) =
      z • linearCharacterVirtualHom G χ :=
  MonoidAlgebra.lift_single _ _ _

theorem finiteAbelianCharacterAlgebraHom_coeff (f : MonoidAlgebra ℤ (LinearCharacter G)) :
    (finiteAbelianCharacterAlgebraHom G f).val =
      Finsupp.linearCombination ℤ RHTower.deningerCharacterFn f.coeff := by
  rw [finiteAbelianCharacterAlgebraHom, MonoidAlgebra.lift_apply]
  change (virtualRepresentationSubring G).subtype.toAddMonoidHom
    (f.coeff.sum (fun χ z => z • linearCharacterVirtualHom G χ)) = _
  rw [map_finsuppSum]
  simp only [map_zsmul, Finsupp.linearCombination_apply]
  congr 1
  funext χ z
  congr 1
  ext g
  exact linearVirtualCharacter_apply G χ g

theorem finiteAbelianCharacterAlgebraHom_injective :
    Function.Injective (finiteAbelianCharacterAlgebraHom G) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  have h := congrArg Subtype.val hf
  rw [finiteAbelianCharacterAlgebraHom_coeff] at h
  have hli : LinearIndependent ℤ (RHTower.deningerCharacterFn : LinearCharacter G → G → ℂ) :=
    RHTower.deningerCharacter_linearIndependent.restrict_scalars' ℤ
  have hc : f.coeff = 0 := (linearIndependent_iff.mp hli) _ h
  ext χ
  exact congrArg (fun a => a χ) hc

theorem finiteAbelianCharacterAlgebraHom_surjective :
    Function.Surjective (finiteAbelianCharacterAlgebraHom G) := by
  classical
  intro θ
  let v : VirtualCharacter G := ⟨θ.val, θ.property⟩
  refine ⟨∑ χ : LinearCharacter G, MonoidAlgebra.single χ
    (virtualMultiplicity G (linearVirtualCharacter G χ) v), ?_⟩
  rw [map_sum]
  simp only [finiteAbelianCharacterAlgebraHom_single]
  apply Subtype.ext
  have h := congrArg (fun w : VirtualCharacter G => w.val)
    (finiteAbelian_virtual_fourier_integral_subtype (G := G) v).symm
  simpa [linearCharacterVirtualHom, v] using h

/-- The representation-character ring is the integral group algebra of the character group. -/
def finiteAbelianCharacterAlgebraEquiv :
    MonoidAlgebra ℤ (LinearCharacter G) ≃ₐ[ℤ] VirtualRepresentationRing G :=
  AlgEquiv.ofBijective (finiteAbelianCharacterAlgebraHom G)
    ⟨finiteAbelianCharacterAlgebraHom_injective G, finiteAbelianCharacterAlgebraHom_surjective G⟩

/-- The dimension augmentation becomes ordinary group-algebra coefficient summation. -/
theorem finiteAbelianCharacterAlgebraHom_augmentation (f : MonoidAlgebra ℤ (LinearCharacter G)) :
    virtualRepresentationAugmentation G (finiteAbelianCharacterAlgebraHom G f) =
      augmentation ℤ (LinearCharacter G) f := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add f h hf hh => rw [map_add, map_add, map_add, hf, hh]
  | single χ z =>
    rw [finiteAbelianCharacterAlgebraHom_single, map_zsmul]
    have hd : virtualRepresentationAugmentation G (linearCharacterVirtualHom G χ) = 1 := by
      apply Int.cast_injective (α := ℂ)
      change (virtualRepresentationDegree G (linearCharacterVirtualHom G χ) : ℂ) = _
      rw [virtualRepresentationDegree_cast, Int.cast_one]
      exact (linearVirtualCharacter_apply G χ 1).trans (by simp)
    rw [hd]
    simp only [augmentation, MonoidAlgebra.lift_single, MonoidHom.one_apply, zsmul_eq_mul, mul_one]

end GaloisForLFunctions.RepresentationLifting
