import GaloisForLFunctions.RHTower.DeningerBaumslagEquivariance

/-!
# The packet at a Galois action

The equivariance of the packet, instantiated at the action of a Galois group on the field it is an
extension of, with the rational permutation module of that action as coefficients.  This is the
coherent Galois functoriality of the packet in a concrete case rather than in the abstract.

* `DeningerPermModule` : the rational permutation module of a group action.
* `deningerPacket_equivariant` : equivariance for the permutation module.
* `deningerPacket_galois` : equivariance at a Galois action.
-/

namespace RHTower

open scoped Classical

section PermModule

variable (Γ : Type*) [Group Γ] (ι : Type*) [MulAction Γ ι]

/-- The rational permutation module of a group action. -/
def DeningerPermModule (Γ : Type*) [Group Γ] (ι : Type*) [MulAction Γ ι] : Type _ := ι →₀ ℚ

noncomputable instance : AddCommGroup (DeningerPermModule Γ ι) := inferInstanceAs (AddCommGroup (ι →₀ ℚ))

noncomputable instance : Module ℚ (DeningerPermModule Γ ι) := inferInstanceAs (Module ℚ (ι →₀ ℚ))

noncomputable instance : DistribMulAction Γ (DeningerPermModule Γ ι) where
  smul γ f := Finsupp.mapDomain (fun i : ι => γ • i) f
  one_smul f := by
    show Finsupp.mapDomain (fun i : ι => (1 : Γ) • i) f = f
    simp only [one_smul]
    exact Finsupp.mapDomain_id
  mul_smul γ₁ γ₂ f := by
    show Finsupp.mapDomain (fun i : ι => (γ₁ * γ₂) • i) f =
      Finsupp.mapDomain (fun i : ι => γ₁ • i) (Finsupp.mapDomain (fun i : ι => γ₂ • i) f)
    rw [← Finsupp.mapDomain_comp]
    simp only [mul_smul, Function.comp_def]
  smul_zero γ := by
    show Finsupp.mapDomain (fun i : ι => γ • i) (0 : ι →₀ ℚ) = 0
    simp
  smul_add γ f g := by
    show Finsupp.mapDomain (fun i : ι => γ • i) (f + g) =
      Finsupp.mapDomain (fun i : ι => γ • i) f + Finsupp.mapDomain (fun i : ι => γ • i) g
    exact Finsupp.mapDomain_add

/-- The basis of the permutation module. -/
noncomputable def deningerPermBasis (Γ : Type*) [Group Γ] (ι : Type*) [MulAction Γ ι] (i : ι) :
    DeningerPermModule Γ ι := Finsupp.single i (1 : ℚ)

theorem deningerPermBasis_equivariant (γ : Γ) (i : ι) :
    deningerPermBasis Γ ι (γ • i) = γ • deningerPermBasis Γ ι i := by
  show Finsupp.single (γ • i) (1 : ℚ) =
    Finsupp.mapDomain (fun j : ι => γ • j) (Finsupp.single i (1 : ℚ))
  rw [Finsupp.mapDomain_single]

/-- **Equivariance of the packet for the permutation module.** -/
theorem deningerPacket_equivariant (γ : Γ) :
    (AddMonoidHom.toMultiplicative
        (DistribSMul.toAddMonoidHom (DeningerPermModule Γ ι) γ)).comp
        (deningerBauFreeMap (deningerPermBasis Γ ι)) =
      (deningerBauFreeMap (deningerPermBasis Γ ι)).comp (deningerBauFreeAut (ι := ι) γ) :=
  deningerBauFreeMap_equivariant _ γ (deningerPermBasis_equivariant Γ ι γ)

end PermModule

section Galois

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- **Equivariance of the packet at a Galois action.**  The Galois group of a field extension acts
on the field, hence on the free group it indexes and on its rationalization, and the packet
intertwines that action with the action on the rational permutation module. -/
theorem deningerPacket_galois (γ : L ≃ₐ[K] L) :
    (AddMonoidHom.toMultiplicative
        (DistribSMul.toAddMonoidHom (DeningerPermModule (L ≃ₐ[K] L) L) γ)).comp
        (deningerBauFreeMap (deningerPermBasis (L ≃ₐ[K] L) L)) =
      (deningerBauFreeMap (deningerPermBasis (L ≃ₐ[K] L) L)).comp
        (deningerBauFreeAut (ι := L) γ) :=
  deningerPacket_equivariant (L ≃ₐ[K] L) L γ

end Galois

end RHTower
