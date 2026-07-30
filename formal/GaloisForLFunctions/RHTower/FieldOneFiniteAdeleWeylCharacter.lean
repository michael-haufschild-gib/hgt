import GaloisForLFunctions.RHTower.FieldOnePadicStandardWeylCharacter
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Canonical standard character of the rational finite adeles

The compatible standard characters of all `p`-adic completions vanish on
integral inputs. Hence, on a restricted finite adele, their values have finite
support and can be summed canonically in `ℝ / ℤ`.

This file constructs that global finite-adele character and proves additivity,
local constancy, nontriviality through a one-place principal part, and the
corresponding Weyl-multiplier representation law. Compatibility with diagonal
rationals and an archimedean character is deliberately a separate theorem.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Filter Function IsDedekindDomain
open scoped RestrictedProduct

/-- Finite adeles of `ℚ`, indexed by the height-one primes of `ℤ`. -/
abbrev FieldOneFiniteAdele :=
  IsDedekindDomain.FiniteAdeleRing ℤ ℚ

/-- Standard additive-circle character at the finite place `v`. -/
noncomputable def fieldOneFiniteAdeleLocalUnitCharacter
    (v : HeightOneSpectrum ℤ) :
    v.adicCompletion ℚ →+ UnitAddCircle := by
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  exact
    { toFun := fun x =>
        fieldOnePadicStandardUnitAddCircleCharacter
          (Rat.HeightOneSpectrum.primesEquiv v)
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x)
      map_zero' := by simp
      map_add' := by simp }

theorem fieldOneFiniteAdeleLocalUnitCharacter_vanishes_on_integers
    (v : HeightOneSpectrum ℤ) {x : v.adicCompletion ℚ}
    (hx : x ∈ v.adicCompletionIntegers ℚ) :
    fieldOneFiniteAdeleLocalUnitCharacter v x = 0 := by
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  apply
    fieldOnePadicStandardUnitAddCircleCharacter_vanishes_on_integers
      (Rat.HeightOneSpectrum.primesEquiv v)
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hx

/-- Local character values of a finite adele have finite support. -/
theorem fieldOneFiniteAdeleLocalUnitCharacter_hasFiniteSupport
    (x : FieldOneFiniteAdele) :
    HasFiniteSupport
      (fun v => fieldOneFiniteAdeleLocalUnitCharacter v (x v)) := by
  change
    {v | ¬fieldOneFiniteAdeleLocalUnitCharacter v (x v) = 0}.Finite
  rw [← Filter.eventually_cofinite]
  filter_upwards [x.2] with v hv
  exact
    fieldOneFiniteAdeleLocalUnitCharacter_vanishes_on_integers v hv

/-- Raw global finite-adele character, as the finite sum of local standard
characters in `ℝ / ℤ`. -/
noncomputable def fieldOneFiniteAdeleStandardUnitAddCircleRaw
    (x : FieldOneFiniteAdele) : UnitAddCircle :=
  ∑ᶠ v, fieldOneFiniteAdeleLocalUnitCharacter v (x v)

@[simp]
theorem fieldOneFiniteAdeleStandardUnitAddCircleRaw_zero :
    fieldOneFiniteAdeleStandardUnitAddCircleRaw 0 = 0 := by
  change
    (∑ᶠ v, fieldOneFiniteAdeleLocalUnitCharacter v 0) = 0
  simp

theorem fieldOneFiniteAdeleStandardUnitAddCircleRaw_add
    (x y : FieldOneFiniteAdele) :
    fieldOneFiniteAdeleStandardUnitAddCircleRaw (x + y) =
      fieldOneFiniteAdeleStandardUnitAddCircleRaw x +
        fieldOneFiniteAdeleStandardUnitAddCircleRaw y := by
  change
    (∑ᶠ v, fieldOneFiniteAdeleLocalUnitCharacter v ((x + y) v)) =
      (∑ᶠ v, fieldOneFiniteAdeleLocalUnitCharacter v (x v)) +
        ∑ᶠ v, fieldOneFiniteAdeleLocalUnitCharacter v (y v)
  rw [show
    (fun v => fieldOneFiniteAdeleLocalUnitCharacter v ((x + y) v)) =
      (fun v =>
        fieldOneFiniteAdeleLocalUnitCharacter v (x v) +
          fieldOneFiniteAdeleLocalUnitCharacter v (y v)) by
      funext v
      exact map_add (fieldOneFiniteAdeleLocalUnitCharacter v) (x v) (y v)]
  exact finsum_add_distrib
    (fieldOneFiniteAdeleLocalUnitCharacter_hasFiniteSupport x)
    (fieldOneFiniteAdeleLocalUnitCharacter_hasFiniteSupport y)

/-- Canonical additive-circle-valued character of the finite adeles. -/
noncomputable def fieldOneFiniteAdeleStandardUnitAddCircleCharacter :
    FieldOneFiniteAdele →+ UnitAddCircle where
  toFun := fieldOneFiniteAdeleStandardUnitAddCircleRaw
  map_zero' := fieldOneFiniteAdeleStandardUnitAddCircleRaw_zero
  map_add' := fieldOneFiniteAdeleStandardUnitAddCircleRaw_add

/-- Integral finite adeles, viewed as an additive subgroup. -/
def fieldOneFiniteAdeleIntegralAddSubgroup :
    AddSubgroup FieldOneFiniteAdele where
  carrier := {x | ∀ v, x v ∈ v.adicCompletionIntegers ℚ}
  zero_mem' := fun _ => zero_mem _
  add_mem' hx hy v := add_mem (hx v) (hy v)
  neg_mem' hx v := neg_mem (hx v)

theorem fieldOneFiniteAdeleIntegralAddSubgroup_isOpen :
    IsOpen
      (fieldOneFiniteAdeleIntegralAddSubgroup :
        Set FieldOneFiniteAdele) := by
  apply RestrictedProduct.isOpen_forall_mem
  intro v
  exact Valued.isOpen_valuationSubring
    (HeightOneSpectrum.adicCompletion ℚ v)

theorem fieldOneFiniteAdeleStandardUnitAddCircleCharacter_vanishes_on_integers
    {x : FieldOneFiniteAdele}
    (hx : x ∈ fieldOneFiniteAdeleIntegralAddSubgroup) :
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter x = 0 := by
  change
    (∑ᶠ v, fieldOneFiniteAdeleLocalUnitCharacter v (x v)) = 0
  change ∀ v, x v ∈ v.adicCompletionIntegers ℚ at hx
  rw [← finsum_zero]
  apply finsum_congr
  intro v
  exact
    fieldOneFiniteAdeleLocalUnitCharacter_vanishes_on_integers v (hx v)

theorem fieldOneFiniteAdeleStandardUnitAddCircleCharacter_isLocallyConstant :
    IsLocallyConstant
      fieldOneFiniteAdeleStandardUnitAddCircleCharacter := by
  apply AddMonoidHom.isLocallyConstant_of_open_addSubgroup_le_ker
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter
    fieldOneFiniteAdeleIntegralAddSubgroup
    fieldOneFiniteAdeleIntegralAddSubgroup_isOpen
  intro x hx
  exact
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter_vanishes_on_integers hx

/-- Principal-part witness at a finite place, transported from `p_v⁻¹`. -/
noncomputable def fieldOneFiniteAdeleLocalPrincipalPart
    (v : HeightOneSpectrum ℤ) : v.adicCompletion ℚ := by
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
      ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) :
        ℚ_[Rat.HeightOneSpectrum.primesEquiv v])⁻¹

theorem fieldOneFiniteAdeleLocalUnitCharacter_principalPart_ne_zero
    (v : HeightOneSpectrum ℤ) :
    fieldOneFiniteAdeleLocalUnitCharacter v
      (fieldOneFiniteAdeleLocalPrincipalPart v) ≠ 0 := by
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  change
    fieldOnePadicStandardUnitAddCircleCharacter
      (Rat.HeightOneSpectrum.primesEquiv v)
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
        (fieldOneFiniteAdeleLocalPrincipalPart v)) ≠ 0
  rw [show
    fieldOneFiniteAdeleLocalPrincipalPart v =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) :
          ℚ_[Rat.HeightOneSpectrum.primesEquiv v])⁻¹ by rfl,
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply]
  exact
    fieldOnePadicStandardUnitAddCircleCharacter_inv_p_ne_zero
      (Rat.HeightOneSpectrum.primesEquiv v)

/-- A finite adele supported at one place. -/
noncomputable def fieldOneFiniteAdeleSingle
    (v : HeightOneSpectrum ℤ) (a : v.adicCompletion ℚ) :
    FieldOneFiniteAdele := by
  classical
  exact
    ⟨fun w =>
        if h : w = v then h.symm ▸ a else 0,
      by
        filter_upwards [Filter.eventually_cofinite_ne v] with w hw
        simp [hw]⟩

@[simp]
theorem fieldOneFiniteAdeleSingle_apply_same
    (v : HeightOneSpectrum ℤ) (a : v.adicCompletion ℚ) :
    fieldOneFiniteAdeleSingle v a v = a := by
  classical
  change (if h : v = v then h.symm ▸ a else 0) = a
  simp

theorem fieldOneFiniteAdeleSingle_apply_of_ne
    {v w : HeightOneSpectrum ℤ} (h : w ≠ v)
    (a : v.adicCompletion ℚ) :
    fieldOneFiniteAdeleSingle v a w = 0 := by
  classical
  change (if h' : w = v then h'.symm ▸ a else 0) = 0
  rw [dif_neg h]

theorem fieldOneFiniteAdeleStandardUnitAddCircleCharacter_single
    (v : HeightOneSpectrum ℤ) (a : v.adicCompletion ℚ) :
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter
        (fieldOneFiniteAdeleSingle v a) =
      fieldOneFiniteAdeleLocalUnitCharacter v a := by
  change
    (∑ᶠ w, fieldOneFiniteAdeleLocalUnitCharacter w
      (fieldOneFiniteAdeleSingle v a w)) =
      fieldOneFiniteAdeleLocalUnitCharacter v a
  calc
    (∑ᶠ w, fieldOneFiniteAdeleLocalUnitCharacter w
        (fieldOneFiniteAdeleSingle v a w)) =
        fieldOneFiniteAdeleLocalUnitCharacter v
          (fieldOneFiniteAdeleSingle v a v) :=
      finsum_eq_single
        (fun w : HeightOneSpectrum ℤ =>
          fieldOneFiniteAdeleLocalUnitCharacter w
            (fieldOneFiniteAdeleSingle v a w))
        v
        (fun w hw => by
          change
            fieldOneFiniteAdeleLocalUnitCharacter w
              (fieldOneFiniteAdeleSingle v a w) = 0
          rw [fieldOneFiniteAdeleSingle_apply_of_ne hw]
          exact map_zero _)
    _ = fieldOneFiniteAdeleLocalUnitCharacter v a := by
      rw [fieldOneFiniteAdeleSingle_apply_same]

theorem fieldOneFiniteAdeleStandardUnitAddCircleCharacter_ne_zero :
    fieldOneFiniteAdeleStandardUnitAddCircleCharacter ≠ 0 := by
  intro h
  let v : HeightOneSpectrum ℤ :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
      ⟨2, Nat.prime_two⟩
  have hz :
      fieldOneFiniteAdeleStandardUnitAddCircleCharacter
        (fieldOneFiniteAdeleSingle v
          (fieldOneFiniteAdeleLocalPrincipalPart v)) = 0 := by
    simpa only [Pi.zero_apply] using!
      DFunLike.congr_fun h
        (fieldOneFiniteAdeleSingle v
          (fieldOneFiniteAdeleLocalPrincipalPart v))
  rw [fieldOneFiniteAdeleStandardUnitAddCircleCharacter_single] at hz
  exact
    fieldOneFiniteAdeleLocalUnitCharacter_principalPart_ne_zero v hz

noncomputable def fieldOneFiniteAdeleStandardAddChar :
    AddChar FieldOneFiniteAdele ℂ :=
  Circle.coeHom.compAddChar <|
    AddCircle.toCircle_addChar.compAddMonoidHom <|
      fieldOneFiniteAdeleStandardUnitAddCircleCharacter

theorem fieldOneFiniteAdeleStandardAddChar_isLocallyConstant :
    IsLocallyConstant fieldOneFiniteAdeleStandardAddChar := by
  simpa only [fieldOneFiniteAdeleStandardAddChar,
    AddChar.compAddMonoidHom_apply,
    MonoidHom.compAddChar_apply] using!
      fieldOneFiniteAdeleStandardUnitAddCircleCharacter_isLocallyConstant.comp
        (fun z : UnitAddCircle => (AddCircle.toCircle z : ℂ))

theorem fieldOneFiniteAdeleStandardAddChar_ne_one :
    fieldOneFiniteAdeleStandardAddChar ≠ 1 := by
  intro h
  apply fieldOneFiniteAdeleStandardUnitAddCircleCharacter_ne_zero
  ext x
  change fieldOneFiniteAdeleStandardUnitAddCircleCharacter x = 0
  have hcomplex :
      (AddCircle.toCircle
        (fieldOneFiniteAdeleStandardUnitAddCircleCharacter x) : ℂ) = 1 := by
    simpa only [fieldOneFiniteAdeleStandardAddChar, Pi.one_apply,
      AddChar.compAddMonoidHom_apply, MonoidHom.compAddChar_apply] using!
        DFunLike.congr_fun h x
  have hcircle :
      AddCircle.toCircle
        (fieldOneFiniteAdeleStandardUnitAddCircleCharacter x) =
          (1 : Circle) :=
    Subtype.ext hcomplex
  apply AddCircle.injective_toCircle one_ne_zero
  simpa only [AddCircle.toCircle_zero] using hcircle

/-- Standard finite-adele character packaged for the generic Weyl multiplier. -/
noncomputable def fieldOneFiniteAdeleStandardLocallyConstantAddChar :
    LocallyConstantAddChar (R := FieldOneFiniteAdele) :=
  ⟨fieldOneFiniteAdeleStandardAddChar,
    fieldOneFiniteAdeleStandardAddChar_isLocallyConstant⟩

/-- Weyl multiplier on finite-adele compactly supported locally constant
functions. -/
noncomputable def fieldOneFiniteAdeleStandardWeylMultiplier
    (r : FieldOneFiniteAdele) :
    compactlySupportedLocallyConstant FieldOneFiniteAdele →ₗ[ℂ]
      compactlySupportedLocallyConstant FieldOneFiniteAdele :=
  locallyConstantWeylMultiplier
    fieldOneFiniteAdeleStandardLocallyConstantAddChar r

theorem fieldOneFiniteAdeleStandardWeylMultiplier_add
    (r s : FieldOneFiniteAdele) :
    (fieldOneFiniteAdeleStandardWeylMultiplier r).comp
        (fieldOneFiniteAdeleStandardWeylMultiplier s) =
      fieldOneFiniteAdeleStandardWeylMultiplier (r + s) :=
  locallyConstantWeylMultiplier_add
    fieldOneFiniteAdeleStandardLocallyConstantAddChar r s

end

end GaloisForLFunctions.RHTower
