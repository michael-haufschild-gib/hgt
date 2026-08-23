import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionCompletedTameReciprocity
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldContinuousH2Exhaustion
import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Landing completed tame reciprocity profiles in finite unramified continuous `H²`

A global `K₂ᴹ(F(t))` class has completed finite-place norm-tame `ℚ/ℤ` invariants and an
invariant at infinity.  This file packages those values as one literal finite-support all-place
profile, proves its zero-sum and product-one laws, and realizes the whole profile inside one
finite unramified continuous local `H²` layer.

This is a target-side bridge: Milnor reciprocity and finite local Galois cohomology now use the
same `ℚ/ℤ` coordinates and the same circle phases.  It does not assert a norm-residue comparison,
or identify the realizing cohomology classes with Brauer classes at the original global places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial WithZero WithZeroMulInt ValuativeRel

universe u

noncomputable section

local instance completedTameH2ProfileDecidableEqMonicIrred
    {F : Type*} [Field F] : DecidableEq (MonicIrred F) := Classical.decEq _

local instance completedTameH2ProfileDecidableEqResidueMilnorKDeg
    {F : Type*} [Field F] (q : MonicIrred F) (n : ℕ) :
    DecidableEq (MilnorKDeg (polyResidueField q.2.1) n) := Classical.decEq _

/-- Finite-place `ℚ/ℤ` profile obtained from completed norm-tame Milnor invariants. -/
noncomputable def rationalFunctionCompletedTameRatModIntFiniteProfile
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    MonicIrred F →₀ RatModInt :=
  DFinsupp.toFinsupp
    (DFinsupp.mapRange.addMonoidHom (fun q ↦
      (finiteMilnorKOneStdRatModIntInvariant F).comp (milnorNormAt q 1))
      (milnorPolynomialTotalResidue (F := F) 1 y))

/-- Evaluation of the finite completed norm-tame invariant profile. -/
theorem rationalFunctionCompletedTameRatModIntFiniteProfile_apply
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2)
    (q : MonicIrred F) :
    rationalFunctionCompletedTameRatModIntFiniteProfile F y q =
      finiteMilnorKOneStdRatModIntInvariant F
        (milnorNormAt q 1 (milnorPolynomialTotalResidue (F := F) 1 y q)) := by
  rfl

/-- Sum of the finite-place profile is the DFinsupp sum of normalized residue invariants. -/
theorem rationalFunctionCompletedTameRatModIntFiniteProfile_sum
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    finsuppRatModIntSumAddHom (MonicIrred F)
        (rationalFunctionCompletedTameRatModIntFiniteProfile F y) =
      (milnorPolynomialTotalResidue (F := F) 1 y).sum
        (fun q x ↦ finiteMilnorKOneStdRatModIntInvariant F (milnorNormAt q 1 x)) := by
  let p : Π₀ _q : MonicIrred F, RatModInt :=
    DFinsupp.mapRange.addMonoidHom (fun q ↦
      (finiteMilnorKOneStdRatModIntInvariant F).comp (milnorNormAt q 1))
      (milnorPolynomialTotalResidue (F := F) 1 y)
  change p.toFinsupp.sum (fun _ q ↦ q) = _
  change p.sum (fun _ q ↦ q) = _
  change (DFinsupp.mapRange
      (fun q x ↦ finiteMilnorKOneStdRatModIntInvariant F (milnorNormAt q 1 x))
      (fun q ↦ ((finiteMilnorKOneStdRatModIntInvariant F).comp
        (milnorNormAt q 1)).map_zero)
      (milnorPolynomialTotalResidue (F := F) 1 y)).sum (fun _ q ↦ q) = _
  rw [DFinsupp.sum_mapRange_index]
  intro q
  rfl

/-- All-place profile: finite completed tame invariants plus the invariant at infinity. -/
noncomputable def rationalFunctionCompletedTameRatModIntAllPlaceProfile
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    Option (MonicIrred F) →₀ RatModInt :=
  Finsupp.embDomain Function.Embedding.some
      (rationalFunctionCompletedTameRatModIntFiniteProfile F y) +
    Finsupp.single none
      (finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y))

/-- A finite-place coordinate of the all-place profile. -/
@[simp] theorem rationalFunctionCompletedTameRatModIntAllPlaceProfile_apply_some
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2)
    (q : MonicIrred F) :
    rationalFunctionCompletedTameRatModIntAllPlaceProfile F y (some q) =
      rationalFunctionCompletedTameRatModIntFiniteProfile F y q := by
  simp [rationalFunctionCompletedTameRatModIntAllPlaceProfile]

/-- Infinity coordinate of the all-place profile. -/
@[simp] theorem rationalFunctionCompletedTameRatModIntAllPlaceProfile_apply_none
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    rationalFunctionCompletedTameRatModIntAllPlaceProfile F y none =
      finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y) := by
  simp [rationalFunctionCompletedTameRatModIntAllPlaceProfile]

/-- The literal all-place completed tame profile has global invariant sum zero. -/
theorem rationalFunctionCompletedTameRatModIntAllPlaceProfile_sum_eq_zero
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    finsuppRatModIntSumAddHom (Option (MonicIrred F))
      (rationalFunctionCompletedTameRatModIntAllPlaceProfile F y) = 0 := by
  rw [rationalFunctionCompletedTameRatModIntAllPlaceProfile, map_add]
  change (Finsupp.embDomain Function.Embedding.some
      (rationalFunctionCompletedTameRatModIntFiniteProfile F y)).sum (fun _ q ↦ q) +
    (Finsupp.single none
      (finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y))).sum
        (fun _ q ↦ q) = 0
  rw [Finsupp.sum_embDomain,
    Finsupp.sum_single_index (h := fun (_ : Option (MonicIrred F)) q ↦ q) rfl]
  change finsuppRatModIntSumAddHom (MonicIrred F)
      (rationalFunctionCompletedTameRatModIntFiniteProfile F y) +
    finiteMilnorKOneStdRatModIntInvariant F (milnorResidueInfty 1 y) = 0
  rw [rationalFunctionCompletedTameRatModIntFiniteProfile_sum]
  simpa only [rationalFunctionFiniteAdicNormTameRatModIntInvariant_section] using
    milnorPolynomialKTwo_completedFiniteTameRatModIntInvariant_sum_eq_zero F y

/-- Standard phases of the literal all-place completed tame profile multiply to one. -/
theorem rationalFunctionCompletedTameRatModIntAllPlaceProfile_character_product_eq_one
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    (rationalFunctionCompletedTameRatModIntAllPlaceProfile F y).prod
      (fun _ q ↦ ratModIntStdAddChar q) = 1 := by
  rw [finsuppRatModIntStdAddChar_product_eq_one_iff_sum_eq_zero]
  exact rationalFunctionCompletedTameRatModIntAllPlaceProfile_sum_eq_zero F y

/-- **Target-side Milnor-to-local-`H²` landing.**  The all-place completed tame invariant profile
of a global rational-function Milnor class is realized in one finite unramified continuous `H²`
layer over any nonarchimedean local field, with the same product-one phase law. -/
theorem rationalFunctionCompletedTameRatModIntAllPlaceProfile_realized_by_finiteUnramifiedContinuousH2
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (F : Type u) [Field F] [Finite F] (y : MilnorKDeg (RatFunc F) 2) :
    NonarchimedeanLocalFiniteUnramifiedContinuousH2RealizesReciprocalProfile K
      (rationalFunctionCompletedTameRatModIntAllPlaceProfile F y) := by
  apply nonarchimedeanLocalField_zeroSum_finsuppRatModInt_realized_with_phase_product_one
  exact rationalFunctionCompletedTameRatModIntAllPlaceProfile_sum_eq_zero F y

end

end GaloisForLFunctions.HTGeometry.ABHN
