import GaloisForLFunctions.HTGeometry.ABHN.RestrictedBrauerGroup
import GaloisForLFunctions.HTGeometry.ABHN.Specification

/-!
# Summing local invariants on restricted Brauer families

For any supplied family of additive local invariants, a restricted local Brauer family has a
finitely supported family of values in `ℚ/ℤ`.  Its finite sum is therefore an additive map.  This
is the global-reciprocity target of ABHN; the missing local class-field-theory results are only
needed to supply the local invariant family and to factor the global localization map through the
restricted carrier.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Sum a finitely supported family of elements of `ℚ/ℤ`. -/
noncomputable def finsuppRatModIntSumAddHom (ι : Type u) :
    (ι →₀ RatModInt) →+ RatModInt := by
  classical
  exact
    { toFun := fun f ↦ f.sum fun _ q ↦ q
      map_zero' := Finsupp.sum_zero_index
      map_add' := fun f g ↦ Finsupp.sum_add_index (by intros; rfl) (by intros; rfl) }

/-- Evaluate a number-field restricted local Brauer family under local invariant maps and retain
the resulting finite support. -/
noncomputable def numberFieldLocalInvariantFinsupp
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (x : RestrictedLocalBrauerClasses K) : NumberFieldPlace K →₀ RatModInt :=
  Finsupp.onFinset x.finite_nonSplit_support.toFinset
    (fun v ↦ invariant v (x.toLocalBrauerClasses v)) (by
      intro v hv
      exact (Set.Finite.mem_toFinset x.finite_nonSplit_support).mpr (by
        intro hx
        apply hv
        rw [hx]
        change invariant v 0 = 0
        exact (invariant v).map_zero))

/-- Pointwise characterization of the finitely supported local-invariant family. -/
theorem numberFieldLocalInvariantFinsupp_apply
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt)
    (x : RestrictedLocalBrauerClasses K) (v : NumberFieldPlace K) :
    numberFieldLocalInvariantFinsupp K invariant x v = invariant v (x.toLocalBrauerClasses v) :=
  Finsupp.onFinset_apply

/-- Evaluation by a family of number-field local invariants is additive on restricted families. -/
noncomputable def numberFieldLocalInvariantFinsuppAddHom
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt) :
    RestrictedLocalBrauerClasses K →+ (NumberFieldPlace K →₀ RatModInt) where
  toFun := numberFieldLocalInvariantFinsupp K invariant
  map_zero' := by
    ext v
    rw [numberFieldLocalInvariantFinsupp_apply]
    change invariant v 0 = 0
    exact (invariant v).map_zero
  map_add' x y := by
    ext v
    change invariant v (x.toLocalBrauerClasses v + y.toLocalBrauerClasses v) =
      numberFieldLocalInvariantFinsupp K invariant x v +
        numberFieldLocalInvariantFinsupp K invariant y v
    rw [numberFieldLocalInvariantFinsupp_apply, numberFieldLocalInvariantFinsupp_apply]
    exact (invariant v).map_add _ _

/-- The finite sum of local invariants on a number-field restricted Brauer family. -/
noncomputable def numberFieldRestrictedInvariantSum
    (K : Type u) [Field K] [NumberField K]
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt) :
    RestrictedLocalBrauerClasses K →+ RatModInt :=
  (finsuppRatModIntSumAddHom (NumberFieldPlace K)).comp
    (numberFieldLocalInvariantFinsuppAddHom K invariant)

/-- The genuine global-reciprocity assertion once a localization map and all local invariants are
available. -/
def NumberFieldGlobalReciprocity
    (K : Type u) [Field K] [NumberField K]
    (globalToLocal : BrauerGroup.{u, u} K →+ RestrictedLocalBrauerClasses K)
    (invariant : ∀ v : NumberFieldPlace K, BrauerGroup (completion K v) →+ RatModInt) : Prop :=
  ∀ x, numberFieldRestrictedInvariantSum K invariant (globalToLocal x) = 0

/-- Evaluate a rational-function-field restricted local Brauer family under local invariants and
retain the resulting finite support. -/
noncomputable def rationalFunctionLocalInvariantFinsupp
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (x : RationalFunctionRestrictedLocalBrauerClasses F) : RationalFunctionPlace F →₀ RatModInt :=
  Finsupp.onFinset x.finite_nonSplit_support.toFinset
    (fun v ↦ invariant v (x.toLocalBrauerClasses v)) (by
      intro v hv
      exact (Set.Finite.mem_toFinset x.finite_nonSplit_support).mpr (by
        intro hx
        apply hv
        rw [hx]
        change invariant v 0 = 0
        exact (invariant v).map_zero))

/-- Pointwise characterization of the rational-function local-invariant family. -/
theorem rationalFunctionLocalInvariantFinsupp_apply
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt)
    (x : RationalFunctionRestrictedLocalBrauerClasses F) (v : RationalFunctionPlace F) :
    rationalFunctionLocalInvariantFinsupp F invariant x v = invariant v (x.toLocalBrauerClasses v) :=
  Finsupp.onFinset_apply

/-- Evaluation by rational-function-field local invariants is additive on restricted families. -/
noncomputable def rationalFunctionLocalInvariantFinsuppAddHom
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt) :
    RationalFunctionRestrictedLocalBrauerClasses F →+ (RationalFunctionPlace F →₀ RatModInt) where
  toFun := rationalFunctionLocalInvariantFinsupp F invariant
  map_zero' := by
    ext v
    rw [rationalFunctionLocalInvariantFinsupp_apply]
    change invariant v 0 = 0
    exact (invariant v).map_zero
  map_add' x y := by
    ext v
    change invariant v (x.toLocalBrauerClasses v + y.toLocalBrauerClasses v) =
      rationalFunctionLocalInvariantFinsupp F invariant x v +
        rationalFunctionLocalInvariantFinsupp F invariant y v
    rw [rationalFunctionLocalInvariantFinsupp_apply, rationalFunctionLocalInvariantFinsupp_apply]
    exact (invariant v).map_add _ _

/-- The finite sum of local invariants on a rational-function-field restricted Brauer family. -/
noncomputable def rationalFunctionRestrictedInvariantSum
    (F : Type u) [Field F] [Finite F]
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt) :
    RationalFunctionRestrictedLocalBrauerClasses F →+ RatModInt :=
  (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).comp
    (rationalFunctionLocalInvariantFinsuppAddHom F invariant)

/-- The genuine function-field global-reciprocity assertion once a localization map and all
local invariants are available. -/
def RationalFunctionGlobalReciprocity
    (F : Type u) [Field F] [Finite F]
    (globalToLocal : BrauerGroup.{u, u} (RatFunc F) →+
      RationalFunctionRestrictedLocalBrauerClasses F)
    (invariant : ∀ v : RationalFunctionPlace F,
      BrauerGroup (rationalFunctionCompletion F v) →+ RatModInt) : Prop :=
  ∀ x, rationalFunctionRestrictedInvariantSum F invariant (globalToLocal x) = 0

end GaloisForLFunctions.HTGeometry.ABHN
