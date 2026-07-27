import GaloisForLFunctions.HTGeometry.FiniteUnipotentTranslationDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaTerminalFace
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaTelescope
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaUnitPeriod
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaHypertranscendence

/-!
# Common-step nilpotence of the multiple elliptic-Gamma hierarchy

If one upper-half-plane step is, modulo the unit period, a positive integral multiple of every
structural period, repeated differencing by that step descends the intrinsic face hierarchy and
terminates at the constant zero-nome logarithmic derivative.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Arithmetic data saying that `β` is a positive integral multiple of every period modulo the
unit period. -/
structure MultipleEllipticGammaCommonStep (τ : ι → ℂ) (β : ℂ) where
  multiple : ι → ℕ
  multiple_pos : ∀ i, 0 < multiple i
  offset : ι → ℤ
  step_eq : ∀ i, β = (multiple i : ℂ) * τ i + (offset i : ℂ)

theorem addTranslationMeroEquiv_natCast_of_one_fixed
    {x : meroField (Set.univ : Set ℂ)}
    (hone : addTranslationMeroEquiv 1 x = x) :
    ∀ n : ℕ, addTranslationMeroEquiv (n : ℂ) x = x := by
  intro n
  induction n with
  | zero => simp [addTranslationMeroEquiv_zero_apply]
  | succ n ih =>
      rw [Nat.cast_succ, ← addTranslationMeroEquiv_add, hone, ih]

theorem addTranslationMeroEquiv_neg_natCast_of_one_fixed
    {x : meroField (Set.univ : Set ℂ)}
    (hone : addTranslationMeroEquiv 1 x = x) (n : ℕ) :
    addTranslationMeroEquiv (-(n : ℂ)) x = x := by
  apply (addTranslationMeroEquiv (n : ℂ)).injective
  rw [addTranslationMeroEquiv_add, add_neg_cancel,
    addTranslationMeroEquiv_zero_apply,
    addTranslationMeroEquiv_natCast_of_one_fixed hone]

theorem addTranslationMeroEquiv_intCast_of_one_fixed
    {x : meroField (Set.univ : Set ℂ)}
    (hone : addTranslationMeroEquiv 1 x = x) (k : ℤ) :
    addTranslationMeroEquiv (k : ℂ) x = x := by
  cases k with
  | ofNat n =>
      exact addTranslationMeroEquiv_natCast_of_one_fixed hone n
  | negSucc n =>
      rw [Int.cast_negSucc]
      exact addTranslationMeroEquiv_neg_natCast_of_one_fixed hone (n + 1)

theorem iteratedMeroTranslationDefect_add
    (β : ℂ) (n : ℕ) (x y : meroField (Set.univ : Set ℂ)) :
    iteratedMeroTranslationDefect β n (x + y) =
      iteratedMeroTranslationDefect β n x +
        iteratedMeroTranslationDefect β n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedMeroTranslationDefect_succ,
        iteratedMeroTranslationDefect_succ,
        iteratedMeroTranslationDefect_succ, ih, map_add]
      ring

@[simp]
theorem iteratedMeroTranslationDefect_zero_value
    (β : ℂ) (n : ℕ) :
    iteratedMeroTranslationDefect β n
      (0 : meroField (Set.univ : Set ℂ)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedMeroTranslationDefect_succ, ih, map_zero, sub_zero]

theorem iteratedMeroTranslationDefect_sum
    {κ : Type} [DecidableEq κ] (β : ℂ) (n : ℕ) (s : Finset κ)
    (f : κ → meroField (Set.univ : Set ℂ)) :
    iteratedMeroTranslationDefect β n (∑ k ∈ s, f k) =
      ∑ k ∈ s, iteratedMeroTranslationDefect β n (f k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        iteratedMeroTranslationDefect_add, ih]

theorem iteratedMeroTranslationDefect_add_right
    (β : ℂ) (m n : ℕ) (x : meroField (Set.univ : Set ℂ)) :
    iteratedMeroTranslationDefect β (m + n) x =
      iteratedMeroTranslationDefect β m
        (iteratedMeroTranslationDefect β n x) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, iteratedMeroTranslationDefect_succ,
        iteratedMeroTranslationDefect_succ, ih]

theorem iteratedMeroTranslationDefect_sum_translates
    {κ : Type} [DecidableEq κ] (β : ℂ) (n : ℕ) (s : Finset κ) (g : κ → ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    iteratedMeroTranslationDefect β n
        (∑ k ∈ s, addTranslationMeroEquiv (g k) x) =
      ∑ k ∈ s, addTranslationMeroEquiv (g k)
        (iteratedMeroTranslationDefect β n x) := by
  rw [iteratedMeroTranslationDefect_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact (addTranslationMeroEquiv_iteratedMeroTranslationDefect_comm
    (g k) β n x).symm

/-- One common-step defect is a finite sum of translates of a coface. -/
theorem multipleEllipticGammaLogDerivFaceMero_commonStep_defect
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (β : ℂ) (hcommon : MultipleEllipticGammaCommonStep τ β)
    (J : Finset ι) (q : ι) (hq : q ∉ J) :
    addTranslationMeroEquiv β
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) -
      multipleEllipticGammaLogDerivFaceMero τ hτ J =
      ∑ j ∈ Finset.range (hcommon.multiple q),
        addTranslationMeroEquiv ((j : ℂ) * τ q)
          (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) := by
  let F := multipleEllipticGammaLogDerivFaceMero τ hτ J
  have hone : addTranslationMeroEquiv 1 F = F :=
    addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivFaceMero τ hτ J
  calc
    addTranslationMeroEquiv β F - F =
        addTranslationMeroEquiv
            ((hcommon.multiple q : ℂ) * τ q + (hcommon.offset q : ℂ)) F - F := by
          rw [← hcommon.step_eq q]
    _ = addTranslationMeroEquiv ((hcommon.multiple q : ℂ) * τ q)
          (addTranslationMeroEquiv (hcommon.offset q : ℂ) F) - F := by
          rw [addTranslationMeroEquiv_add]
    _ = addTranslationMeroEquiv ((hcommon.multiple q : ℂ) * τ q) F - F := by
          rw [addTranslationMeroEquiv_intCast_of_one_fixed hone]
    _ = ∑ j ∈ Finset.range (hcommon.multiple q),
          addTranslationMeroEquiv ((j : ℂ) * τ q)
            (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) :=
      multipleEllipticGammaLogDerivFaceMero_translate_sub_eq_sum
        τ hτ J hq (hcommon.multiple q)

/-- **Facewise common-step nilpotence.** On a face with `d` surviving periods, the `(d+1)`-st
common-step defect vanishes. -/
theorem multipleEllipticGammaLogDerivFaceMero_commonStep_nilpotent
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (β : ℂ) (hcommon : MultipleEllipticGammaCommonStep τ β)
    (J : Finset ι) :
    iteratedMeroTranslationDefect β ((Jᶜ).card + 1)
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) = 0 := by
  suffices h :
      ∀ S : Finset ι,
        iteratedMeroTranslationDefect β (S.card + 1)
          (multipleEllipticGammaLogDerivFaceMero τ hτ Sᶜ) = 0 by
    simpa using h Jᶜ
  intro S
  induction S using Finset.induction_on with
  | empty =>
      have hcomp : (∅ : Finset ι)ᶜ = Finset.univ := by simp
      rw [Finset.card_empty, zero_add, hcomp,
        iteratedMeroTranslationDefect_succ,
        iteratedMeroTranslationDefect_zero]
      letI : IsEmpty (MultipleEllipticGammaFaceIndex (Finset.univ : Finset ι)) :=
        ⟨fun i => by simpa using i.2⟩
      have hfix :
          addTranslationMeroEquiv β
              (multipleEllipticGammaLogDerivFaceMero τ hτ Finset.univ) =
            multipleEllipticGammaLogDerivFaceMero τ hτ Finset.univ := by
        exact addTranslationMeroEquiv_multipleEllipticGammaLogDerivMero_isEmpty
          (multipleEllipticGammaFaceParameters τ Finset.univ)
          (fun i => hτ i) β
      rw [hfix, sub_self]
  | @insert q S hq ih =>
      have hqface : q ∉ (insert q S)ᶜ := by simp
      have hface : insert q ((insert q S)ᶜ) = Sᶜ := by
        ext i
        by_cases hiq : i = q
        · subst i
          simp [hq]
        · simp [hiq]
      have hdefect :=
        multipleEllipticGammaLogDerivFaceMero_commonStep_defect
          τ hτ β hcommon ((insert q S)ᶜ) q hqface
      rw [Finset.card_insert_of_notMem hq,
        iteratedMeroTranslationDefect_add_right β (S.card + 1) 1]
      change iteratedMeroTranslationDefect β (S.card + 1)
        (addTranslationMeroEquiv β
            (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q S)ᶜ) -
          multipleEllipticGammaLogDerivFaceMero τ hτ (insert q S)ᶜ) = 0
      rw [hdefect, hface,
        iteratedMeroTranslationDefect_sum_translates]
      rw [ih]
      simp

/-- The original logarithmic derivative has nilpotence order at most `card ι + 1`. -/
theorem multipleEllipticGammaLogDerivMero_commonStep_nilpotent
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (β : ℂ) (hcommon : MultipleEllipticGammaCommonStep τ β) :
    iteratedMeroTranslationDefect β (Fintype.card ι + 1)
      (multipleEllipticGammaLogDerivMero τ hτ) = 0 := by
  have h := multipleEllipticGammaLogDerivFaceMero_commonStep_nilpotent
    τ hτ β hcommon (∅ : Finset ι)
  rw [multipleEllipticGammaLogDerivFaceMero_empty] at h
  simpa using h

/-- A positive common step makes the logarithmic derivative differentially algebraic. -/
theorem differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_of_commonStep
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (β : ℂ) (hβ : 0 < β.im)
    (hcommon : MultipleEllipticGammaCommonStep τ β) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivMero τ hτ) := by
  apply differentialAlgebraicOver_of_iteratedMeroTranslationDefect_eq_zero hβ
  · exact addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivMero τ hτ
  · exact multipleEllipticGammaLogDerivMero_commonStep_nilpotent
      τ hτ β hcommon

/-- A positive common step makes the genuine raw multiple elliptic Gamma differentially
algebraic. -/
theorem differentialAlgebraicOver_multipleEllipticGammaMero_of_commonStep
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (β : ℂ) (hβ : 0 < β.im)
    (hcommon : MultipleEllipticGammaCommonStep τ β) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaMero τ hτ) := by
  apply (differentialAlgebraicOver_deriv_div_self_iff
    (K := RatFunc ℂ) (multipleEllipticGammaMero τ hτ)).mp
  simpa [multipleEllipticGammaLogDerivMero, Differential.logDeriv] using
    differentialAlgebraicOver_multipleEllipticGammaLogDerivMero_of_commonStep
      τ hτ β hβ hcommon

end

end GaloisForLFunctions
