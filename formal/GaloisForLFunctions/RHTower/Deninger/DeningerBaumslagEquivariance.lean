import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagH1

/-!
# Equivariance of the packet under a group acting on the chosen family

The packet depends on a chosen family in `A`.  Whenever a group `Γ` acts on the index set and on
`A`, and the family is equivariant, the packet is equivariant too: the surjection `a_U` intertwines
the action induced on the rationalization by functoriality with the action on `A`.

Applied to a Galois group acting on `A` and permuting a chosen family, this is the coherent Galois
functoriality of the packet.

* `deningerBauFreeAut` : the induced action on the rationalization.
* `deningerBauFreeAut_one`, `deningerBauFreeAut_mul` : it is an action.
* `deningerBauFreeMap_equivariant` : the packet intertwines the two actions.
-/

namespace RHTower

section BaumslagEquivariance

universe u v w

variable {ι : Type u} {A : Type v} [AddCommGroup A] [Module ℚ A]
variable {Γ : Type w} [Group Γ] [MulAction Γ ι]

/-- The action induced on the rationalization of the free group by an action on the index set. -/
noncomputable def deningerBauFreeAut (γ : Γ) :
    DeningerBau (FreeGroup ι) →* DeningerBau (FreeGroup ι) :=
  deningerBauMap (FreeGroup.map (fun i : ι => γ • i))

theorem deningerBauFreeAut_one :
    deningerBauFreeAut (ι := ι) (1 : Γ) = MonoidHom.id (DeningerBau (FreeGroup ι)) := by
  have h : FreeGroup.map (fun i : ι => (1 : Γ) • i) = MonoidHom.id (FreeGroup ι) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    rw [FreeGroup.map.of, one_smul]
    rfl
  rw [deningerBauFreeAut, h, deningerBauMap_id]

theorem deningerBauFreeAut_mul (γ₁ γ₂ : Γ) :
    deningerBauFreeAut (ι := ι) (γ₁ * γ₂) =
      (deningerBauFreeAut (ι := ι) γ₁).comp (deningerBauFreeAut (ι := ι) γ₂) := by
  have h : FreeGroup.map (fun i : ι => (γ₁ * γ₂) • i) =
      (FreeGroup.map (fun i : ι => γ₁ • i)).comp (FreeGroup.map (fun i : ι => γ₂ • i)) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    rw [FreeGroup.map.of, MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.map.of, mul_smul]
  rw [deningerBauFreeAut, h, deningerBauMap_comp]
  rfl

variable [DistribMulAction Γ A]

/-- **Equivariance of the packet.**  If the chosen family is `Γ`-equivariant, then `a_U`
intertwines the induced action on the rationalization with the action on `A`. -/
theorem deningerBauFreeMap_equivariant (b : ι → A) (γ : Γ) (hb : ∀ i, b (γ • i) = γ • b i) :
    (AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom A γ)).comp
        (deningerBauFreeMap b) =
      (deningerBauFreeMap b).comp (deningerBauFreeAut (ι := ι) γ) := by
  have hgen : ((AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom A γ)).comp
        (deningerBauFreeMap b)).comp
        (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)) =
      ((deningerBauFreeMap b).comp (deningerBauFreeAut (ι := ι) γ)).comp
        (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    show (AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom A γ))
        (deningerBauFreeMap b (DeningerBau.of (FreeGroup.of i))) =
      deningerBauFreeMap b (deningerBauFreeAut (ι := ι) γ (DeningerBau.of (FreeGroup.of i)))
    simp only [deningerBauFreeAut, deningerBauMap_of, FreeGroup.map.of, deningerBauFreeMap,
      deningerBauLift_of, FreeGroup.lift_apply_of]
    exact congrArg Multiplicative.ofAdd (hb i).symm
  have h1 := deningerBauLift_unique (deningerMultiplicative_uniquelyDivisible (A := A))
    (((AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom A γ)).comp
        (deningerBauFreeMap b)).comp
      (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)))
    ((AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom A γ)).comp
      (deningerBauFreeMap b)) (fun _ => rfl)
  have h2 := deningerBauLift_unique (deningerMultiplicative_uniquelyDivisible (A := A))
    (((AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom A γ)).comp
        (deningerBauFreeMap b)).comp
      (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)))
    ((deningerBauFreeMap b).comp (deningerBauFreeAut (ι := ι) γ))
    (fun a => by exact (DFunLike.congr_fun hgen a).symm)
  exact h1.trans h2.symm

end BaumslagEquivariance

end RHTower
