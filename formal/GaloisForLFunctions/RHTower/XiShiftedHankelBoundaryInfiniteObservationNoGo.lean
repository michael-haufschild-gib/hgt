import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryExtensionClass

/-!
# Infinite observation boundary at a shifted Xi Hankel face

The finite shifted-Xi Hankel face is an observation, not a locally finite carrier.  Its first
unseen moment gives an injective real family of complete extensions, and the canonical monic
remainder maps that face fibre onto the whole real line.

Kernel/death profiles of linear response families have a separate exact blindness: `x` and `-x`
have identical profiles, while every linear normal observation changes sign.  Consequently an
exact Gamma persistence lifetime cannot orient the shifted-Hankel normal without an additional
source coorientation.  No Gamma-corona theorem, Xi divisor premise, or computation enters this
route-local no-go.
-/

open Matrix Polynomial Set

namespace RHTower

noncomputable section

/-- Kernel/death profile of a family of same-carrier linear responses. -/
def linearResponseKernelProfile
    {ι V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : ι → V →ₗ[ℝ] V) (x : V) : ι → Prop :=
  fun i => T i x = 0

/-- A linear response kernel profile forgets the sign of its input. -/
theorem linearResponseKernelProfile_neg
    {ι V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : ι → V →ₗ[ℝ] V) (x : V) :
    linearResponseKernelProfile T (-x) =
      linearResponseKernelProfile T x := by
  funext i
  simp [linearResponseKernelProfile]

/-- **Persistence-sign no-go.**  No predicate depending only on a linear response kernel profile
can classify the strict sign of a nonzero linear normal observation on every input. -/
theorem no_linearResponseKernelProfile_strictSignClassifier
    {ι V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : ι → V →ₗ[ℝ] V) (L : V →ₗ[ℝ] ℝ) (x : V)
    (hx : L x ≠ 0) :
    ¬ ∃ orient : (ι → Prop) → Prop,
      ∀ z : V, orient (linearResponseKernelProfile T z) ↔ 0 < L z := by
  rintro ⟨orient, horient⟩
  have hxiff := horient x
  have hnegiff := horient (-x)
  rw [linearResponseKernelProfile_neg T x] at hnegiff
  simp only [map_neg] at hnegiff
  by_cases hpos : 0 < L x
  · have ho : orient (linearResponseKernelProfile T x) := hxiff.mpr hpos
    have hnegpos : 0 < -L x := hnegiff.mp ho
    linarith
  · have hlt : L x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
    have hnegpos : 0 < -L x := neg_pos.mpr hlt
    have ho : orient (linearResponseKernelProfile T x) := hnegiff.mpr hnegpos
    exact hpos (hxiff.mp ho)

/-- Complete moment sequences inducing one fixed shifted-Xi Hankel face. -/
def xiShiftedHankelMomentFaceFiber (y : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {t | HTGeometry.momentHankelMatrix t (n + 1) =
    HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)}

/-- Every shifted-Xi finite Hankel face has an infinite complete-moment fibre. -/
theorem xiShiftedHankelMomentFaceFiber_infinite (y : ℝ) (n : ℕ) :
    (xiShiftedHankelMomentFaceFiber y n).Infinite := by
  exact HTGeometry.sameMomentHankelFace_infinite
    (fun k => (xiShiftedReciprocalMoment y k).re) n

/-- The route's intrinsic first extension coordinate is surjective on the complete-moment fibre of
every fixed face.  In particular that finite face supports every outgoing orientation. -/
theorem xiShiftedHankelMomentFaceFiber_monicRemainder_surjective
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    Function.Surjective (fun t : xiShiftedHankelMomentFaceFiber y n =>
      HTGeometry.finiteHankelBoundaryMonicRemainder t.1 c) := by
  intro r
  obtain ⟨t, htface, htrem⟩ :=
    HTGeometry.exists_momentSequence_same_face_monicRemainder_eq
      (fun k => (xiShiftedReciprocalMoment y k).re) c hlast r
  exact ⟨⟨t, htface⟩, htrem⟩

end

end RHTower
