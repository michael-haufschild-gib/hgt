import GaloisForLFunctions.RepresentationLifting.QuadraticRepresentations
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Quadratic obstruction classes in group cohomology

Splicing the two equivariant quadratic sequences gives a degree-two connecting
map in every degree. In degree zero it assigns an actual H² class to every
invariant quadratic tensor. Tensor-valued lifts annihilate this map, and its
kernel is characterized by a second cohomological lifting problem. In dimension
at most one all these classes vanish because the pure-square inclusion splits.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace GaloisForLFunctions.RepresentationLifting
universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- An equivariantly split injection has zero connecting map in every degree. -/
theorem cohomologyConnecting_eq_zero_of_retraction
    (S : ShortComplex (Rep k G)) (hS : S.ShortExact)
    (r : S.X₂ ⟶ S.X₁) (hr : S.f ≫ r = 𝟙 _) (n : ℕ) :
    groupCohomology.δ hS n (n + 1) rfl = 0 := by
  have hz : groupCohomology.δ hS n (n + 1) rfl ≫
      (groupCohomology.functor k G (n + 1)).map S.f = 0 :=
    (groupCohomology.mapShortComplex₁ hS rfl).zero
  have hi : (groupCohomology.functor k G (n + 1)).map S.f ≫
      (groupCohomology.functor k G (n + 1)).map r = 𝟙 _ :=
    ((groupCohomology.functor k G (n + 1)).map_comp S.f r).symm.trans
      ((congrArg (groupCohomology.functor k G (n + 1)).map hr).trans
        ((groupCohomology.functor k G (n + 1)).map_id S.X₁))
  calc
    groupCohomology.δ hS n (n + 1) rfl =
        groupCohomology.δ hS n (n + 1) rfl ≫
          ((groupCohomology.functor k G (n + 1)).map S.f ≫
            (groupCohomology.functor k G (n + 1)).map r) :=
      (Category.comp_id _).symm.trans (congrArg
        (fun f => groupCohomology.δ hS n (n + 1) rfl ≫ f) hi.symm)
    _ = (groupCohomology.δ hS n (n + 1) rfl ≫
          (groupCohomology.functor k G (n + 1)).map S.f) ≫
          (groupCohomology.functor k G (n + 1)).map r := (Category.assoc _ _ _).symm
    _ = 0 := (congrArg (fun f => f ≫ (groupCohomology.functor k G (n + 1)).map r) hz).trans
      (zero_comp)

variable {ι : Type u} [CharP k 2] [Fintype ι] [LinearOrder ι]

/-- The double connecting homomorphism of the quadratic two-extension. -/
def quadraticConnecting (ρ : G →* Matrix ι ι k) (n : ℕ) :
    groupCohomology (Rep.of (quadraticSymmetricRepresentation ρ)) n ⟶
      groupCohomology (Rep.of (quadraticFrobeniusRepresentation ρ)) (n + 2) :=
  groupCohomology.δ (quadraticSecondSequence_shortExact ρ) n (n + 1) rfl ≫
    groupCohomology.δ (quadraticFirstSequence_shortExact ρ) (n + 1) (n + 2) rfl

/-- The class κ associated linearly to an invariant quadratic tensor. -/
def quadraticCohomologyClass (ρ : G →* Matrix ι ι k) :
    (quadraticSymmetricRepresentation ρ).invariants →ₗ[k]
      groupCohomology (Rep.of (quadraticFrobeniusRepresentation ρ)) 2 :=
  (quadraticConnecting ρ 0).hom.comp
    (groupCohomology.H0Iso (Rep.of (quadraticSymmetricRepresentation ρ))).inv.hom

/-- Every cohomology class lifted from the tensor square has zero quadratic obstruction. -/
theorem tensorProjection_quadraticConnecting (ρ : G →* Matrix ι ι k) (n : ℕ) :
    (groupCohomology.functor k G n).map (quadraticTensorProjection ρ) ≫
      quadraticConnecting ρ n = 0 := by
  have hz : (groupCohomology.functor k G n).map (quadraticTensorProjection ρ) ≫
      groupCohomology.δ (quadraticSecondSequence_shortExact ρ) n (n + 1) rfl = 0 :=
    (groupCohomology.mapShortComplex₃ (quadraticSecondSequence_shortExact ρ) rfl).zero
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ groupCohomology.δ (quadraticFirstSequence_shortExact ρ)
      (n + 1) (n + 2) rfl) hz).trans zero_comp)

/-- The quadratic connecting map vanishes in dimension at most one, in every degree. -/
theorem quadraticConnecting_rankOne_zero [Subsingleton ι]
    (ρ : G →* Matrix ι ι k) (n : ℕ) : quadraticConnecting ρ n = 0 := by
  have hz := cohomologyConnecting_eq_zero_of_retraction
    (quadraticFirstSequence ρ) (quadraticFirstSequence_shortExact ρ)
    (quadraticRankOneRetraction ρ) (quadraticRankOneRetraction_inclusion ρ) (n + 1)
  exact (congrArg (fun f => groupCohomology.δ (quadraticSecondSequence_shortExact ρ)
    n (n + 1) rfl ≫ f) hz).trans comp_zero

/-- Every invariant rank-one quadratic tensor has zero obstruction class. -/
theorem quadraticCohomologyClass_rankOne_zero [Subsingleton ι]
    (ρ : G →* Matrix ι ι k) : quadraticCohomologyClass ρ = 0 := by
  unfold quadraticCohomologyClass
  rw [quadraticConnecting_rankOne_zero]
  rfl

/-- Vanishing is equivalent to lifting the first boundary through polarization in cohomology. -/
theorem quadraticConnecting_zero_iff_lift (ρ : G →* Matrix ι ι k) (n : ℕ)
    (c : groupCohomology (Rep.of (quadraticSymmetricRepresentation ρ)) n) :
    (quadraticConnecting ρ n).hom c = 0 ↔
      ∃ b : groupCohomology (Rep.of (quadraticSymmetricRepresentation ρ)) (n + 1),
        ((groupCohomology.functor k G (n + 1)).map (quadraticNormHom ρ)).hom b =
          (groupCohomology.δ (quadraticSecondSequence_shortExact ρ) n (n + 1) rfl).hom c := by
  have he := (groupCohomology.mapShortComplex₃_exact
    (quadraticFirstSequence_shortExact ρ) (show (n + 1) + 1 = n + 2 from rfl)).moduleCat_range_eq_ker
  change LinearMap.range ((groupCohomology.functor k G (n + 1)).map (quadraticNormHom ρ)).hom =
    LinearMap.ker (groupCohomology.δ (quadraticFirstSequence_shortExact ρ)
      (n + 1) (n + 2) rfl).hom at he
  change ((groupCohomology.δ (quadraticSecondSequence_shortExact ρ) n (n + 1) rfl).hom c ∈
    LinearMap.ker (groupCohomology.δ (quadraticFirstSequence_shortExact ρ)
      (n + 1) (n + 2) rfl).hom) ↔ _
  rw [← he]
  rfl

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cohomologyConnecting_eq_zero_of_retraction
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticConnecting
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticCohomologyClass_rankOne_zero
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticConnecting_zero_iff_lift
