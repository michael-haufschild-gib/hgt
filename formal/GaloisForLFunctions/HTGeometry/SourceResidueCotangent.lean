import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Cotangent injectivity over the source residue field

The local Jacobian criterion is usually stated over the residue field of the quotient local
ring.  For lifting a basis back through a localization, the residue field of the source local
ring is the useful one: Nakayama's lemma then applies without any residue-field transport.

For a surjective local algebra map, the two residue fields agree.  This file makes the useful
source-residue formulation explicit and extracts a finite family which generates the kernel and
whose cotangent images are linearly independent.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

/-- The cotangent map of `P → S`, base-changed to the residue field of the source local ring
`P`.  The kernel containment is precisely what is needed for this base change. -/
noncomputable def sourceResidueCotangentMap
    (R P S : Type*) [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra P S] [IsLocalRing P]
    (hker : RingHom.ker (algebraMap P S) ≤
      IsLocalRing.maximalIdeal P) :
    IsLocalRing.ResidueField P ⊗[P] RingHom.ker (algebraMap P S) →ₗ[IsLocalRing.ResidueField P]
      IsLocalRing.ResidueField P ⊗[P] Ω[P⁄R] :=
  LinearMap.liftBaseChange _
    (KaehlerDifferential.kerToTensor R P (IsLocalRing.ResidueField P) ∘ₗ
      Submodule.inclusion (by
        change RingHom.ker (algebraMap P S) ≤
          RingHom.ker (IsLocalRing.residue P)
        rw [IsLocalRing.ker_residue]
        exact hker))

set_option maxHeartbeats 800000

/-- Formal smoothness makes the source-residue cotangent map injective.  The proof factors the
source residue map through the surjective local quotient and then invokes mathlib's local
Jacobian criterion over that field. -/
theorem sourceResidueCotangentMap_injective
    (R P S : Type*) [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]
    [IsLocalRing P] [IsLocalRing S] [Nontrivial S]
    [Algebra.FormallySmooth R P]
    [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (hsurj : Function.Surjective (algebraMap P S))
    (hfg : (RingHom.ker (algebraMap P S)).FG)
    (hsmooth : Algebra.FormallySmooth R S) :
    Function.Injective
      (sourceResidueCotangentMap R P S (by
        intro a ha
        rw [IsLocalRing.mem_maximalIdeal]
        intro hua
        have hu : IsUnit (algebraMap P S a) := hua.map (algebraMap P S)
        rw [RingHom.mem_ker.mp ha] at hu
        exact not_isUnit_zero hu)) := by
  let K := IsLocalRing.ResidueField P
  have hker : RingHom.ker (algebraMap P S) ≤
      RingHom.ker (algebraMap P K) := by
    change RingHom.ker (algebraMap P S) ≤
      RingHom.ker (IsLocalRing.residue P)
    rw [IsLocalRing.ker_residue]
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal]
    intro hua
    have hu : IsUnit (algebraMap P S a) := hua.map (algebraMap P S)
    rw [RingHom.mem_ker.mp ha] at hu
    exact not_isUnit_zero hu
  let g : S →ₐ[R] K :=
    AlgHom.liftOfSurjective
      (IsScalarTower.toAlgHom R P S) hsurj
      (IsScalarTower.toAlgHom R P K) hker
  letI : Algebra S K := g.toRingHom.toAlgebra
  have hcomp : (algebraMap S K).comp (algebraMap P S) =
      algebraMap P K := by
    ext x
    exact AlgHom.congr_fun
      (AlgHom.liftOfSurjective_comp
        (IsScalarTower.toAlgHom R P S) hsurj
        (IsScalarTower.toAlgHom R P K) hker) x
  letI : IsScalarTower P S K :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hmax : IsLocalRing.maximalIdeal S ≤
      RingHom.ker (algebraMap S K) := by
    intro a ha
    obtain ⟨b, rfl⟩ := hsurj a
    rw [RingHom.mem_ker]
    change ((algebraMap S K).comp (algebraMap P S)) b = 0
    rw [hcomp]
    change IsLocalRing.residue P b = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal]
    intro hb
    apply ha
    exact hb.map (algebraMap P S)
  have hinj : Function.Injective
      (KaehlerDifferential.cotangentComplexBaseChange R S P K) :=
    (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange
      P K hsurj hfg hmax).mp hsmooth
  simpa only [sourceResidueCotangentMap] using hinj

/-- An injective source-residue cotangent map supplies finitely many elements of the presentation
kernel which generate it over the local source ring and have linearly independent cotangent
images.  The finite indexing by `Fin m` is convenient for Jacobian matrices. -/
theorem exists_finite_sourceResidue_basis_lifts
    (R P S : Type*) [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra P S] [IsLocalRing P]
    (hker : RingHom.ker (algebraMap P S) ≤
      IsLocalRing.maximalIdeal P)
    (hfg : (RingHom.ker (algebraMap P S)).FG)
    (hinj : Function.Injective (sourceResidueCotangentMap R P S hker)) :
    ∃ (m : ℕ) (v : Fin m → RingHom.ker (algebraMap P S)),
      Submodule.span P (Set.range v) = ⊤ ∧
      LinearIndependent (IsLocalRing.ResidueField P)
        (fun i ↦ sourceResidueCotangentMap R P S hker
          (1 ⊗ₜ[P] v i)) := by
  let J := RingHom.ker (algebraMap P S)
  let K := IsLocalRing.ResidueField P
  let W := K ⊗[P] J
  letI : Module.Finite P J := Module.Finite.of_fg hfg
  letI : Module.Finite K W := inferInstance
  let b := Module.Free.chooseBasis K W
  letI : Finite (Module.Free.ChooseBasisIndex K W) :=
    Module.Finite.finite_basis b
  obtain ⟨v, hv⟩ :=
    (TensorProduct.mk_surjective P J K IsLocalRing.residue_surjective).comp_left b
  letI : Fintype (Module.Free.ChooseBasisIndex K W) := Fintype.ofFinite _
  let e : Fin (Fintype.card (Module.Free.ChooseBasisIndex K W)) ≃
      Module.Free.ChooseBasisIndex K W :=
    (Fintype.equivFin _).symm
  let v' := v ∘ e
  refine ⟨Fintype.card (Module.Free.ChooseBasisIndex K W), v', ?_, ?_⟩
  · have hspan := IsLocalRing.span_eq_top_of_tmul_eq_basis v b
      (fun i ↦ congr_fun hv i)
    have hrange : Set.range v' = Set.range v := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, by simp [v']⟩
    rw [hrange]
    exact hspan
  · have hli : LinearIndependent K
        (fun i ↦ sourceResidueCotangentMap R P S hker
          (1 ⊗ₜ[P] v i)) := by
      have hli' := b.linearIndependent.map'
        (sourceResidueCotangentMap R P S hker)
        (LinearMap.ker_eq_bot.mpr hinj)
      have hfun :
          (fun i ↦ sourceResidueCotangentMap R P S hker
            (1 ⊗ₜ[P] v i)) =
          (sourceResidueCotangentMap R P S hker) ∘ b := by
        funext i
        exact congrArg (sourceResidueCotangentMap R P S hker)
          (congr_fun hv i)
      rw [hfun]
      exact hli'
    exact hli.comp e e.injective

end

end GaloisForLFunctions.HTGeometry
