import GaloisForLFunctions.HTGeometry.PrimeWalshTailConstraint
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Category.Profinite.Nobeling.Basic
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Prime-Walsh Stone reconstruction

This file closes the algebraic reconstruction statement for a Boolean prime-tail constraint.
The source cylinder algebra is the algebra of locally constant functions on the full Boolean
cube.  Profinite finite-stage factorization shows that restriction onto a closed tail constraint
is onto every locally constant observable there.  Its kernel is exactly eventual zero along the
prime sequence, so the first isomorphism theorem gives the claimed quotient algebra.

The last theorem identifies idempotents with characteristic functions of clopen subsets.  Thus
the quotient recovers the Boolean algebra of clopens of the tail constraint without choosing a
tail representative.
-/

open CategoryTheory Limits

namespace Profinite.NobelingProof

/-- Every locally constant observable on a closed Boolean constraint factors through one finite
coordinate projection.  This is the codomain-generic form of the finite-stage factorization used
in the profinite Nöbeling development. -/
theorem locallyConstant_factors_finiteProjection
    {I α : Type*} [DecidableEq I] {C : Set (I → Bool)} (hC : IsClosed C)
    (f : LocallyConstant C α) :
    ∃ (s : Finset I)
      (g : LocallyConstant (π C (fun i => i ∈ (s : Set I))) α),
      f = g.comap
        ⟨ProjRestrict C (fun i => i ∈ (s : Set I)), continuous_projRestrict _ _⟩ := by
  classical
  obtain ⟨J, g, h⟩ := @Profinite.exists_locallyConstant (Finset I)ᵒᵖ _ _ _
    (spanCone hC.isCompact) α (spanCone_isLimit hC.isCompact) f
  exact ⟨Opposite.unop J, g, h⟩

end Profinite.NobelingProof

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology
open Profinite.NobelingProof

noncomputable section

private theorem isLocallyConstant_finiteProj
    {I : Type*} [DecidableEq I] (s : Finset I) :
    IsLocallyConstant (Proj (fun i => i ∈ s) : (I → Bool) → (I → Bool)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨orientationCylinder s (orientationRestriction s x),
    (isClopen_orientationCylinder s _).2, ?_, ?_⟩
  · exact (mem_orientationCylinder_iff s _ x).2 fun _ => rfl
  · intro y hy
    ext i
    simp only [Proj]
    split_ifs with hi
    · have hxy := (mem_orientationCylinder_iff s _ y).1 hy ⟨i, hi⟩
      exact hxy
    · rfl

/-- Extend a function on one finite projection of a closed Boolean constraint to a cylinder
function on the full Boolean cube. -/
def finiteProjectionExtension
    {I : Type*} [DecidableEq I] (C : Set (I → Bool)) (s : Finset I)
    (g : LocallyConstant (π C (fun i => i ∈ s)) ℂ) :
    LocallyConstant (I → Bool) ℂ := by
  classical
  exact
    { toFun := fun x =>
        if hx : Proj (fun i => i ∈ s) x ∈ π C (fun i => i ∈ s) then
          g ⟨Proj (fun i => i ∈ s) x, hx⟩ else 0
      isLocallyConstant := (isLocallyConstant_finiteProj s).comp fun x =>
        if hx : x ∈ π C (fun i => i ∈ s) then g ⟨x, hx⟩ else 0 }

theorem finiteProjectionExtension_projRestrict
    {I : Type*} [DecidableEq I] (C : Set (I → Bool)) (s : Finset I)
    (g : LocallyConstant (π C (fun i => i ∈ s)) ℂ) (x : C) :
    finiteProjectionExtension C s g x =
      g (ProjRestrict C (fun i => i ∈ s) x) := by
  classical
  have hmem : Proj (fun i => i ∈ s) (x : I → Bool) ∈
      π C (fun i => i ∈ s) := ⟨x.1, x.2, rfl⟩
  simp only [finiteProjectionExtension, LocallyConstant.coe_mk, dif_pos hmem]
  rfl

/-- Restriction of cylinder functions to the compact prime-tail constraint. -/
def primeTailRestrictionAlgHom
    {J : Type*} (θ : ℕ → (J → Bool)) :
    LocallyConstant (J → Bool) ℂ →ₐ[ℂ]
      LocallyConstant (primeOrientationTailClusterSet θ) ℂ :=
  LocallyConstant.comapₐ ℂ ⟨((↑) : primeOrientationTailClusterSet θ → (J → Bool)),
    continuous_subtype_val⟩

/-- Every locally constant observable of the compact tail constraint is the restriction of a
finite-cylinder observable on the full Boolean cube. -/
theorem primeTailRestrictionAlgHom_surjective
    {J : Type*} [DecidableEq J] (θ : ℕ → (J → Bool)) :
    Function.Surjective (primeTailRestrictionAlgHom θ) := by
  intro f
  obtain ⟨s, g, hfg⟩ := locallyConstant_factors_finiteProjection
    (isClosed_primeOrientationTailClusterSet θ) f
  refine ⟨finiteProjectionExtension (primeOrientationTailClusterSet θ) s g, ?_⟩
  ext x
  change finiteProjectionExtension (primeOrientationTailClusterSet θ) s g x = f x
  rw [finiteProjectionExtension_projRestrict]
  exact (LocallyConstant.congr_fun hfg x).symm

/-- The exact vanishing ideal of the compact prime-tail constraint. -/
def primeTailVanishingIdeal {J : Type*} (θ : ℕ → (J → Bool)) :
    Ideal (LocallyConstant (J → Bool) ℂ) :=
  RingHom.ker (primeTailRestrictionAlgHom θ)

/-- Prime-Walsh Stone reconstruction: cylinder observables modulo eventual tail-vanishing are
canonically the full locally constant algebra of the compact tail constraint. -/
def primeTailLocallyConstantQuotientEquiv
    {J : Type*} [DecidableEq J] (θ : ℕ → (J → Bool)) :
    (LocallyConstant (J → Bool) ℂ ⧸ primeTailVanishingIdeal θ) ≃ₐ[ℂ]
      LocallyConstant (primeOrientationTailClusterSet θ) ℂ :=
  Ideal.quotientKerAlgEquivOfSurjective (primeTailRestrictionAlgHom_surjective θ)

/-- A locally constant observable is eventually zero along a sequence exactly when it vanishes
on the sequence's complete tail-cluster constraint. -/
theorem locallyConstant_eventuallyZero_iff_vanishes_tailCluster
    {J : Type*} (θ : ℕ → (J → Bool)) (f : LocallyConstant (J → Bool) ℂ) :
    {n | f (θ n) ≠ 0}.Finite ↔
      ∀ x ∈ primeOrientationTailClusterSet θ, f x = 0 := by
  let U : Set (J → Bool) := {x | f x ≠ 0}
  have hU : IsClopen U := by
    have hzero := f.isLocallyConstant.isClopen_fiber 0
    change IsClopen {x | ¬f.toFun x = 0}
    exact hzero.compl
  constructor
  · intro hfinite x hx
    by_contra hfx
    have hfreq : ∃ᶠ n in atTop, θ n ∈ U := hx.frequently (hU.2.mem_nhds hfx)
    rw [Nat.frequently_atTop_iff_infinite] at hfreq
    exact hfreq hfinite
  · intro hvanish
    by_contra hfinite
    have hinf : {n | f (θ n) ≠ 0}.Infinite := hfinite
    have hfreq : ∃ᶠ n in atTop, θ n ∈ U := by
      rw [Nat.frequently_atTop_iff_infinite]
      exact hinf
    obtain ⟨x, hxU, hxcluster⟩ := hU.1.isCompact.exists_mapClusterPt_of_frequently hfreq
    exact hxU (hvanish x hxcluster)

theorem mem_primeTailVanishingIdeal_iff
    {J : Type*} (θ : ℕ → (J → Bool)) (f : LocallyConstant (J → Bool) ℂ) :
    f ∈ primeTailVanishingIdeal θ ↔
      ∀ x ∈ primeOrientationTailClusterSet θ, f x = 0 := by
  change primeTailRestrictionAlgHom θ f = 0 ↔ _
  constructor
  · intro hf x hx
    have h := LocallyConstant.congr_fun hf ⟨x, hx⟩
    exact h
  · intro hf
    ext x
    exact hf x.1 x.2

/-- The quotient kernel is literally eventual equality modulo finitely many prime coordinates. -/
theorem mem_primeTailVanishingIdeal_iff_eventuallyZero
    {J : Type*} (θ : ℕ → (J → Bool)) (f : LocallyConstant (J → Bool) ℂ) :
    f ∈ primeTailVanishingIdeal θ ↔ {n | f (θ n) ≠ 0}.Finite := by
  rw [mem_primeTailVanishingIdeal_iff,
    locallyConstant_eventuallyZero_iff_vanishes_tailCluster]

/-- Idempotents of a complex locally constant algebra are exactly characteristic functions of
clopen subsets. -/
theorem locallyConstant_idempotent_iff_clopen
    {X : Type*} [TopologicalSpace X] (f : LocallyConstant X ℂ) :
    f * f = f ↔ ∃ (U : Set X) (hU : IsClopen U), f = LocallyConstant.charFn ℂ hU := by
  constructor
  · intro hf
    let U : Set X := {x | f x = 1}
    have hU : IsClopen U := f.isLocallyConstant.isClopen_fiber 1
    refine ⟨U, hU, ?_⟩
    ext x
    have hpoint := LocallyConstant.congr_fun hf x
    simp only [LocallyConstant.mul_apply] at hpoint
    have hfac : f x * (f x - 1) = 0 := by
      calc
        f x * (f x - 1) = f x * f x - f x := by ring
        _ = 0 := sub_eq_zero.mpr hpoint
    rcases mul_eq_zero.mp hfac with hx | hx
    · rw [hx]
      exact ((LocallyConstant.charFn_eq_zero ℂ x hU).2 (by simp [U, hx])).symm
    · have hx' : f x = 1 := sub_eq_zero.mp hx
      rw [hx']
      exact ((LocallyConstant.charFn_eq_one ℂ x hU).2 (by exact hx')).symm
  · rintro ⟨U, hU, rfl⟩
    ext x
    by_cases hx : x ∈ U
    · simp [(LocallyConstant.charFn_eq_one ℂ x hU).2 hx]
    · simp [(LocallyConstant.charFn_eq_zero ℂ x hU).2 hx]

end

end GaloisForLFunctions.HTGeometry
