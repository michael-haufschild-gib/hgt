import GaloisForLFunctions.RHTower.FZZCigarPunctureTwoChannelPluckerClassification
import GaloisForLFunctions.RHTower.Suzuki.SuzukiExteriorFeshbachPruning

/-!
# FZZ puncture Gram-dark self-energy classification

A positive Gram/Feshbach return self-energy `K†K` cannot generate a mode in its
own dark sector.  Its kernel is exactly the kernel of the coupling `K`, and on
that kernel the effective equation `(A-K†K)x=0` reduces to the bare interior
equation `Ax=0`.

For a two-channel affine FZZ puncture whose on-shell source row is the same
coupling row that defines darkness, the on-shell node is automatic.  Point-mode
occurrence is then equivalent only to transverse slope, independently of target
energy.  Thus positive Gram return plus coupling-sourced nodality supplies no
zeta selectivity; any selectivity must enter through the bare interior kernel on
the dark sector or through dynamics not captured by positive Gram return.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- FZZ-facing name for the positive Gram/Feshbach return self-energy. -/
abbrev fzzPunctureGramSelfEnergy
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (K : X →L[ℂ] Y) : X →L[ℂ] X :=
  GaloisForLFunctions.RHTower.feshbachGramSelfEnergy K

/-- The dark sector of a positive Gram return is exactly the coupling kernel. -/
theorem fzzPunctureGramSelfEnergy_apply_eq_zero_iff
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (K : X →L[ℂ] Y) (x : X) :
    fzzPunctureGramSelfEnergy K x = 0 ↔ K x = 0 := by
  constructor
  · intro hG
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    calc
      inner ℂ (K x) (K x) = inner ℂ ((ContinuousLinearMap.adjoint K) (K x)) x :=
        (ContinuousLinearMap.adjoint_inner_left K x (K x)).symm
      _ = inner ℂ (fzzPunctureGramSelfEnergy K x) x := by
        rfl
      _ = 0 := by rw [hG]; simp
  · intro hK
    simp [fzzPunctureGramSelfEnergy,
      GaloisForLFunctions.RHTower.feshbachGramSelfEnergy, hK]

/-- On the coupling-dark sector, positive Gram return cannot create or remove a kernel vector. -/
theorem fzzPunctureGramDarkEffectiveKernel_iff
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (A : X →L[ℂ] X) (K : X →L[ℂ] Y) (x : X) :
    ((A - fzzPunctureGramSelfEnergy K) x = 0 ∧ K x = 0) ↔
      (A x = 0 ∧ K x = 0) := by
  constructor
  · rintro ⟨heff, hK⟩
    have hG : fzzPunctureGramSelfEnergy K x = 0 :=
      (fzzPunctureGramSelfEnergy_apply_eq_zero_iff K x).2 hK
    refine ⟨?_, hK⟩
    simpa [hG] using heff
  · rintro ⟨hA, hK⟩
    have hG : fzzPunctureGramSelfEnergy K x = 0 :=
      (fzzPunctureGramSelfEnergy_apply_eq_zero_iff K x).2 hK
    refine ⟨?_, hK⟩
    simp [hA, hG]

/-- When the coupling row also supplies the source, only transverse slope remains. -/
theorem fzzPunctureCouplingSourcedTwoChannelPointMode_iff
    (E : ℝ) (p q d0 d1 : ℂ) :
    FZZPunctureTwoChannelInternalRowPointMode E p q p q d0 d1 ↔
      (p ≠ 0 ∨ q ≠ 0) ∧ q * d0 - p * d1 ≠ 0 := by
  rw [fzzPunctureTwoChannelInternalRowPointMode_iff]
  constructor
  · rintro ⟨hpq, _, hslope⟩
    exact ⟨hpq, hslope⟩
  · rintro ⟨hpq, hslope⟩
    refine ⟨hpq, ?_, hslope⟩
    ring

/-- Fixed nonzero coupling and transverse slope produce a point mode at every target energy. -/
theorem fzzPunctureCouplingSourcedTwoChannelPointMode_allEnergy
    (p q d0 d1 : ℂ)
    (hpq : p ≠ 0 ∨ q ≠ 0)
    (htransverse : q * d0 - p * d1 ≠ 0) :
    ∀ E : ℝ,
      FZZPunctureTwoChannelInternalRowPointMode E p q p q d0 d1 := by
  intro E
  rw [fzzPunctureCouplingSourcedTwoChannelPointMode_iff]
  exact ⟨hpq, htransverse⟩

end

end RHTower
