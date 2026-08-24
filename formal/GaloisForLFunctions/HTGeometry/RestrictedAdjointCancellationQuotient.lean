import GaloisForLFunctions.HTGeometry.GeneralizedSchurKernelRankProfile

/-!
# Common-factor cancellation as a quotient of a Hardy model space

For a generalized-Schur numerator `F` and denominator model space `K_B`, common inner directions
are exactly the kernel of the restricted numerator adjoint.  Quotienting by that kernel gives the
uncancelled divisor space, canonically equivalent to the restricted-adjoint range.  Consequently,
the arbitrary finite-rank profile used by generalized-Schur inertia is exactly the finite-dimension
profile of this quotient, with no finite-dimensionality assumption.
-/

open Complex
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A module contains an independent family of prescribed finite size. -/
def HasIndependentDimensionAtLeast (V : Type*) [AddCommGroup V] [Module ℂ V]
    (r : ℕ) : Prop :=
  ∃ v : Fin r → V, LinearIndependent ℂ v

/-- An independent family contains independent subfamilies of every smaller finite size. -/
theorem hasIndependentDimensionAtLeast_of_le
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {r s : ℕ} (hrs : r ≤ s)
    (h : HasIndependentDimensionAtLeast V s) :
    HasIndependentDimensionAtLeast V r := by
  obtain ⟨v, hv⟩ := h
  let e : Fin r ↪ Fin s := Fin.castLEEmb hrs
  exact ⟨fun i => v (e i), hv.comp e e.injective⟩

/-- Adjoint restricted to the candidate denominator model space. -/
def restrictedAdjointLinearMap (K : Submodule ℂ H) (C : H →L[ℂ] H) :
    K →ₗ[ℂ] H :=
  C.adjoint.toLinearMap.domRestrict K

/-- Exact common-factor cancellation space. -/
def restrictedAdjointCancellationSpace (K : Submodule ℂ H) (C : H →L[ℂ] H) :
    Submodule ℂ K :=
  LinearMap.ker (restrictedAdjointLinearMap K C)

/-- Denominator model space after deleting every common numerator direction. -/
abbrev RestrictedAdjointUncancelledQuotient
    (K : Submodule ℂ H) (C : H →L[ℂ] H) :=
  K ⧸ restrictedAdjointCancellationSpace K C

/-- First-isomorphism identification of uncancelled divisor quotient with surviving adjoint
range. -/
noncomputable def restrictedAdjointUncancelledQuotientEquivRange
    (K : Submodule ℂ H) (C : H →L[ℂ] H) :
    RestrictedAdjointUncancelledQuotient K C ≃ₗ[ℂ]
      LinearMap.range (restrictedAdjointLinearMap K C) :=
  LinearMap.quotKerEquivRange (restrictedAdjointLinearMap K C)

theorem restrictedAdjointRankAtLeast_iff_range
    (K : Submodule ℂ H) (C : H →L[ℂ] H) (r : ℕ) :
    RestrictedAdjointRankAtLeast K C r ↔
      HasIndependentDimensionAtLeast
        (LinearMap.range (restrictedAdjointLinearMap K C)) r := by
  constructor
  · rintro ⟨v, hv⟩
    let w : Fin r → LinearMap.range (restrictedAdjointLinearMap K C) :=
      fun i => ⟨restrictedAdjointLinearMap K C (v i), ⟨v i, rfl⟩⟩
    refine ⟨w, ?_⟩
    apply LinearIndependent.of_comp
      (LinearMap.range (restrictedAdjointLinearMap K C)).subtype
    change LinearIndependent ℂ
      (fun i => restrictedAdjointLinearMap K C (v i))
    change LinearIndependent ℂ
      (fun i => restrictedAdjointLinearMap K C (v i)) at hv
    exact hv
  · rintro ⟨w, hw⟩
    let v : Fin r → K := fun i => Classical.choose (w i).property
    have hv : ∀ i, restrictedAdjointLinearMap K C (v i) = w i :=
      fun i => Classical.choose_spec (w i).property
    refine ⟨v, ?_⟩
    change LinearIndependent ℂ
      (fun i => restrictedAdjointLinearMap K C (v i))
    have hwH := hw.map'
      (LinearMap.range (restrictedAdjointLinearMap K C)).subtype
      (by simp)
    change LinearIndependent ℂ (fun i => (w i : H)) at hwH
    simpa only [hv] using hwH

/-- Independent finite-dimension profiles are invariant under linear equivalence. -/
theorem hasIndependentDimensionAtLeast_equiv
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (r : ℕ) :
    HasIndependentDimensionAtLeast V r ↔ HasIndependentDimensionAtLeast W r := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun i => e (v i), ?_⟩
    exact hv.map' e.toLinearMap e.ker
  · rintro ⟨w, hw⟩
    refine ⟨fun i => e.symm (w i), ?_⟩
    exact hw.map' e.symm.toLinearMap e.symm.ker

/-- Restricted-adjoint rank is exactly dimension of the uncancelled quotient, in every finite
rank and without a finiteness premise. -/
theorem restrictedAdjointRankAtLeast_iff_uncancelledQuotient
    (K : Submodule ℂ H) (C : H →L[ℂ] H) (r : ℕ) :
    RestrictedAdjointRankAtLeast K C r ↔
      HasIndependentDimensionAtLeast (RestrictedAdjointUncancelledQuotient K C) r := by
  rw [restrictedAdjointRankAtLeast_iff_range]
  exact (hasIndependentDimensionAtLeast_equiv
    (restrictedAdjointUncancelledQuotientEquivRange K C) r).symm

/-- Szegő-kernel direction attached to a common disk zero of denominator and numerator. -/
def commonZeroCancellationVector
    (B : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) (hBa : B.fn a = 0) :
    hardyMultiplierModelSpace B :=
  ⟨hardyKernel ha, hardyKernel_mem_hardyMultiplierModelSpace B ha hBa⟩

theorem commonZeroCancellationVector_ne_zero
    (B : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) (hBa : B.fn a = 0) :
    commonZeroCancellationVector B ha hBa ≠ 0 := by
  intro hzero
  have hval := congrArg Subtype.val hzero
  exact hardyKernel_ne_zero ha hval

/-- A literal common numerator/denominator zero contributes a nonzero direction to the exact
cancellation space. -/
theorem commonZeroCancellationVector_mem
    (F B : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1)
    (hFa : F.fn a = 0) (hBa : B.fn a = 0) :
    commonZeroCancellationVector B ha hBa ∈
      restrictedAdjointCancellationSpace
        (hardyMultiplierModelSpace B) (hardyMul F) := by
  change (hardyMul F).adjoint (hardyKernel ha) = 0
  rw [adjoint_hardyMul_hardyKernel F ha, hFa, map_zero, zero_smul]

end GaloisForLFunctions.HTGeometry
