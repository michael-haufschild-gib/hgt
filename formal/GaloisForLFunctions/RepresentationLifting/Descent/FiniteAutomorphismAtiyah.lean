import GaloisForLFunctions.RepresentationLifting.Descent.SemilinearAveraging
import GaloisForLFunctions.HTGeometry.DirectionalMultiplierAtiyahClass

/-!
# Finite automorphism actions have no multiplier Atiyah obstruction

Trace-one averaging makes every additive cocycle of a finite group of field
automorphisms a coboundary. Consequently the existing directional multiplier
Atiyah-class map vanishes for every multiplicative multiplier cocycle. The
field need not be algebraic over the constants, so equivariant derivations
can be nonzero.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry
variable (k L : Type*) [Field k] [Field L] [Algebra k L]
  (H : Subgroup (L ≃ₐ[k] L))

/-- A subgroup of algebra automorphisms acting through its underlying ring automorphisms. -/
def finiteAutomorphismRingAction : H →* (L ≃+* L) where
  toFun g := g.val.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem finiteAutomorphismRingAction_fix (g : H) (c : k) :
    finiteAutomorphismRingAction k L H g (algebraMap k L c) = algebraMap k L c :=
  g.val.commutes c

variable [Finite H]

/-- Every actual additive cocycle of the finite automorphism group has a primitive in the field. -/
theorem finiteAutomorphism_additiveCoboundary_surjective :
    Function.Surjective (additiveCoboundaryMap (finiteAutomorphismRingAction k L H)
      (finiteAutomorphismRingAction_fix k L H)) := by
  letI : Fintype H := Fintype.ofFinite H
  letI : FaithfulSMul H L :=
    ⟨fun {g h} e => Subtype.ext (AlgEquiv.ext e)⟩
  letI : SMulDistribClass H L L := ⟨fun g x y => map_mul g.val x y⟩
  intro c
  obtain ⟨b, hb⟩ := semilinear_oneCocycle_principal H L L c.val (fun g h => by
    rw [c.property g h]
    exact add_comm _ _)
  refine ⟨b, ?_⟩
  ext g
  exact hb g

/-- The existing additive-action first cohomology vanishes for every finite automorphism subgroup. -/
theorem finiteAutomorphism_additiveH1_subsingleton :
    Subsingleton (AdditiveActionH1 (finiteAutomorphismRingAction k L H)
      (finiteAutomorphismRingAction_fix k L H)) := by
  change Subsingleton (_ ⧸ LinearMap.range
    (additiveCoboundaryMap (finiteAutomorphismRingAction k L H)
      (finiteAutomorphismRingAction_fix k L H)))
  rw [LinearMap.range_eq_top.mpr (finiteAutomorphism_additiveCoboundary_surjective k L H)]
  infer_instance

/-- Finite automorphism groups have no directional multiplier Atiyah obstruction. -/
theorem finiteAutomorphism_multiplierAtiyahClassMap_eq_zero
    (a : H → Lˣ)
    (ha : ∀ g h, (a (g * h) : L) =
      finiteAutomorphismRingAction k L H g (a h : L) * (a g : L)) :
    multiplierAtiyahClassMap (finiteAutomorphismRingAction k L H)
      (finiteAutomorphismRingAction_fix k L H) a ha = 0 := by
  letI := finiteAutomorphism_additiveH1_subsingleton k L H
  exact Subsingleton.elim _ _

/-- Every equivariant derivation admits a field-valued primitive for its logarithmic multiplier cocycle. -/
theorem finiteAutomorphism_multiplierLogCocycle_primitive
    (a : H → Lˣ)
    (ha : ∀ g h, (a (g * h) : L) =
      finiteAutomorphismRingAction k L H g (a h : L) * (a g : L))
    (D : equivariantDerivations (finiteAutomorphismRingAction k L H)
      (finiteAutomorphismRingAction_fix k L H)) :
    ∃ b : L, ∀ g, multiplierLogCocycle D.val a g =
      finiteAutomorphismRingAction k L H g b - b := by
  apply (multiplierAtiyahClassMap_eq_zero_iff _ _ a ha D).mp
  simp only [finiteAutomorphism_multiplierAtiyahClassMap_eq_zero, LinearMap.zero_apply]

end GaloisForLFunctions.RepresentationLifting
