import GaloisForLFunctions.RHTower.DeningerBaumslagPullback

/-!
# Functoriality of the rationalization, and equivariance of the packet

The Baumslag rationalization is a functor: a homomorphism of groups extends over the
rationalizations, uniquely, because the target has unique roots.  Identity and composition are
matched, so isomorphic groups have isomorphic rationalizations.

The packet's surjection is equivariant for that functoriality on the target side: replacing the
chosen family `b` by its image under an additive endomorphism of `A` replaces `a_U` by its
composite with that endomorphism.  Specializing to invertible maps gives the `GL(U)`-equivariance
the packet was missing, and to multiplication by a nonzero rational the power-map equivariance.

* `deningerBauMap`, `deningerBauMap_id`, `deningerBauMap_comp` : the functor.
* `deningerBauMapEquiv` : isomorphic groups have isomorphic rationalizations.
* `deningerBauFreeMap_comp` : equivariance of the packet on the target.
* `deningerBauFreeMap_linear`, `deningerBauFreeMap_smul` : the `GL` and power-map cases.
-/

namespace RHTower

section BaumslagFunctorial

universe u v w

variable {G : Type u} {K : Type v} {L : Type w} [Group G] [Group K] [Group L]

/-- **The rationalization of a homomorphism.** -/
noncomputable def deningerBauMap (f : G →* K) : DeningerBau G →* DeningerBau K :=
  deningerBauLift DeningerBau.uniquelyDivisible
    ((DeningerBau.of : K →* DeningerBau K).comp f)

@[simp]
theorem deningerBauMap_of (f : G →* K) (g : G) :
    deningerBauMap f (DeningerBau.of g) = DeningerBau.of (f g) := rfl

theorem deningerBauMap_id : deningerBauMap (MonoidHom.id G) = MonoidHom.id (DeningerBau G) := by
  have h1 : deningerBauMap (MonoidHom.id G) =
      deningerBauLift DeningerBau.uniquelyDivisible
        (DeningerBau.of : G →* DeningerBau G) := by
    rw [deningerBauMap, MonoidHom.comp_id]
  have h2 := deningerBauLift_unique DeningerBau.uniquelyDivisible
    (DeningerBau.of : G →* DeningerBau G) (MonoidHom.id (DeningerBau G)) (fun _ => rfl)
  rw [h1, ← h2]

theorem deningerBauMap_comp (f : G →* K) (g : K →* L) :
    deningerBauMap (g.comp f) = (deningerBauMap g).comp (deningerBauMap f) := by
  refine (deningerBauLift_unique DeningerBau.uniquelyDivisible
    ((DeningerBau.of : L →* DeningerBau L).comp (g.comp f))
    ((deningerBauMap g).comp (deningerBauMap f)) (fun a => rfl)).symm

/-- **Isomorphic groups have isomorphic rationalizations.** -/
noncomputable def deningerBauMapEquiv (e : G ≃* K) : DeningerBau G ≃* DeningerBau K where
  toFun := deningerBauMap (e : G →* K)
  invFun := deningerBauMap (e.symm : K →* G)
  left_inv := fun x => by
    have h : (deningerBauMap (e.symm : K →* G)).comp (deningerBauMap (e : G →* K)) =
        MonoidHom.id (DeningerBau G) := by
      rw [← deningerBauMap_comp]
      have : ((e.symm : K →* G).comp (e : G →* K)) = MonoidHom.id G := by
        ext a
        exact e.symm_apply_apply a
      rw [this, deningerBauMap_id]
    exact DFunLike.congr_fun h x
  right_inv := fun x => by
    have h : (deningerBauMap (e : G →* K)).comp (deningerBauMap (e.symm : K →* G)) =
        MonoidHom.id (DeningerBau K) := by
      rw [← deningerBauMap_comp]
      have : ((e : G →* K).comp (e.symm : K →* G)) = MonoidHom.id K := by
        ext a
        exact e.apply_symm_apply a
      rw [this, deningerBauMap_id]
    exact DFunLike.congr_fun h x
  map_mul' := map_mul _

end BaumslagFunctorial

section PacketEquivariance

universe u v

variable {ι : Type u} {A : Type v} [AddCommGroup A] [Module ℚ A]

/-- **The packet is equivariant on the target.**  Pushing the chosen family through an additive
endomorphism of `A` composes `a_U` with that endomorphism. -/
theorem deningerBauFreeMap_comp (b : ι → A) (g : A →+ A) :
    (AddMonoidHom.toMultiplicative g).comp (deningerBauFreeMap b) =
      deningerBauFreeMap (fun i => g (b i)) := by
  refine (deningerBauLift_unique (deningerMultiplicative_uniquelyDivisible (A := A))
    ((AddMonoidHom.toMultiplicative g).comp (deningerBauFreeMap b) |>.comp
      (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)))
    ((AddMonoidHom.toMultiplicative g).comp (deningerBauFreeMap b)) (fun _ => rfl)).trans ?_
  refine (deningerBauLift_unique (deningerMultiplicative_uniquelyDivisible (A := A))
    ((AddMonoidHom.toMultiplicative g).comp (deningerBauFreeMap b) |>.comp
      (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)))
    (deningerBauFreeMap (fun i => g (b i))) ?_).symm
  intro a
  have hgen : ((AddMonoidHom.toMultiplicative g).comp (deningerBauFreeMap b)).comp
      (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)) =
      (deningerBauFreeMap (fun i => g (b i))).comp
        (DeningerBau.of : FreeGroup ι →* DeningerBau (FreeGroup ι)) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    show (AddMonoidHom.toMultiplicative g) (deningerBauFreeMap b
        (DeningerBau.of (FreeGroup.of i))) =
      deningerBauFreeMap (fun i => g (b i)) (DeningerBau.of (FreeGroup.of i))
    simp only [deningerBauFreeMap, deningerBauLift_of, FreeGroup.lift_apply_of]
    rfl
  exact (DFunLike.congr_fun hgen a).symm

/-- **`GL`-equivariance**: the packet built from `g ∘ b` is the packet built from `b`, followed by
the linear map `g`. -/
theorem deningerBauFreeMap_linear (b : ι → A) (g : A →ₗ[ℚ] A) :
    (AddMonoidHom.toMultiplicative (g : A →+ A)).comp (deningerBauFreeMap b) =
      deningerBauFreeMap (fun i => g (b i)) :=
  deningerBauFreeMap_comp b (g : A →+ A)

/-- **Power-map equivariance**: scaling the chosen family by a rational scales `a_U`. -/
theorem deningerBauFreeMap_smul (b : ι → A) (q : ℚ) :
    (AddMonoidHom.toMultiplicative ((q • (LinearMap.id : A →ₗ[ℚ] A) : A →ₗ[ℚ] A) :
        A →+ A)).comp (deningerBauFreeMap b) =
      deningerBauFreeMap (fun i => q • b i) :=
  deningerBauFreeMap_comp b _

end PacketEquivariance

end RHTower
