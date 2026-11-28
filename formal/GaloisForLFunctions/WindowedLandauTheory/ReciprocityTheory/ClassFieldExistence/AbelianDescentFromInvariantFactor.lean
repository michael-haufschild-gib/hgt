import Mathlib.FieldTheory.Galois.Abelian
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CyclicInvariantCharacter

/-! A faithful character of the relative Galois group descends abelianity
through a cyclic tower once its pullback to a Galois overfield is invariant. -/

noncomputable section

open IntermediateField

namespace GlobalTheory.Reciprocity

variable (K E T : Type) [Field K] [Field E] [Field T]
  [Algebra K E] [Algebra E T] [Algebra K T] [IsScalarTower K E T] [Normal K E]

local notation "res" => (AlgEquiv.restrictNormalHom E : (T ≃ₐ[K] T) →* (E ≃ₐ[K] E))

/-- The kernel of restriction to the middle field consists of its linear automorphisms. -/
def restrictionKernelEquiv : (res).ker ≃* (T ≃ₐ[E] T) where
  toFun t :=
    { t.val.toRingEquiv with
      commutes' := fun x =>
        (t.val.restrictNormal_commutes E x).symm.trans
          (congrArg (fun g : E ≃ₐ[K] E => algebraMap E T (g x)) (MonoidHom.mem_ker.mp t.2)) }
  invFun t := ⟨t.restrictScalars K, MonoidHom.mem_ker.mpr (AlgEquiv.ext fun x =>
    (algebraMap E T).injective ((AlgEquiv.restrictNormal_commutes (t.restrictScalars K) E x).trans
      (t.commutes x)))⟩
  left_inv _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  right_inv _ := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

section

variable [FiniteDimensional K T] [IsGalois K T] [IsCyclic (E ≃ₐ[K] E)]
  {M A : Type*} [Field M] [Group A]
  [Algebra K M] [Algebra E M] [Algebra M T] [IsScalarTower K M T] [IsScalarTower E M T]
  [Normal E M]

theorem isAbelianGalois_of_invariant_factor (ψ : (M ≃ₐ[E] M) →* A) (hψ : Function.Injective ψ)
    (h : ∀ (t : T ≃ₐ[K] T) (s : (res).ker),
      ψ (AlgEquiv.restrictNormalHom M (restrictionKernelEquiv K E T (conjugateIn (res).ker t s))) =
      ψ (AlgEquiv.restrictNormalHom M (restrictionKernelEquiv K E T s))) :
    IsAbelianGalois K M := by
  let rM := (AlgEquiv.restrictNormalHom M).comp (restrictionKernelEquiv K E T).toMonoidHom
  let ρ := ψ.comp rM
  let H := (res).ker
  haveI : IsCyclic ((T ≃ₐ[K] T) ⧸ H) :=
    (QuotientGroup.quotientKerEquivOfSurjective res
      (AlgEquiv.restrictNormalHom_surjective T)).symm.isCyclic.mp inferInstance
  let N := ρ.ker.map H.subtype
  letI : N.Normal := normal_map_ker_of_conjugation_invariant H ρ h
  letI : IsMulCommutative ((T ≃ₐ[K] T) ⧸ N) :=
    quotient_isMulCommutative_of_conjugation_invariant H ρ h
  let P := fixedField N
  let g := IsGalois.normalAutEquivQuotient N
  letI : IsAbelianGalois K P :=
    { (inferInstance : IsGalois K P) with
      is_comm.comm := fun x y => by
        obtain ⟨x, rfl⟩ := g.surjective x
        obtain ⟨y, rfl⟩ := g.surjective y
        rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm x y] }
  have hm (x : M) : algebraMap M T x ∈ P := by
    intro t
    obtain ⟨s, hs, he⟩ := t.2
    have hr : rM s = 1 := hψ ((MonoidHom.mem_ker.mp hs).trans (map_one ψ).symm)
    have hc := (restrictionKernelEquiv K E T s).restrictNormal_commutes M x
    change algebraMap M T (rM s x) = s.val (algebraMap M T x) at hc
    rw [hr] at hc
    change t.val (algebraMap M T x) = algebraMap M T x
    exact (congrArg (fun z : T ≃ₐ[K] T => z (algebraMap M T x)) he.symm).trans hc.symm
  let j : M →ₐ[K] P := (IsScalarTower.toAlgHom K M T).codRestrict P.toSubalgebra hm
  exact IsAbelianGalois.of_algHom j

end

end GlobalTheory.Reciprocity
