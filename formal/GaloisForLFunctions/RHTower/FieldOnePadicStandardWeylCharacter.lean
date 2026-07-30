import GaloisForLFunctions.RHTower.FieldOnePadicWeylCharacter
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Canonical all-depth `p`-adic Weyl character

This file removes the arbitrary injective-extension choice from the depth-one
construction.  The standard additive character on `ℚ_[p]` is assembled from
the compatible denominator stages `p⁻ⁿ ℤ_[p]`, using reduction modulo `pⁿ`.

The construction proves:

* compatibility under increasing denominator depth;
* exact normalization on every `p⁻ⁿ`;
* kernel exactly `ℤ_[p]`;
* local constancy and nontriviality;
* the corresponding Weyl multiplier representation law.

No global finite-adele character or restricted-product assembly is claimed
here.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

theorem zmodPow_toAddCircle_mul_transition
    {m n : ℕ} (hmn : m ≤ n) (a : ZMod (p ^ n)) :
    ZMod.toAddCircle
        ((p ^ (n - m) : ZMod (p ^ n)) * a) =
      ZMod.toAddCircle
        (ZMod.cast a : ZMod (p ^ m)) := by
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective a
  have hmul :
      (p ^ (n - m) : ZMod (p ^ n)) * (j : ZMod (p ^ n)) =
        (((p ^ (n - m) : ℕ) : ℤ) * j : ℤ) := by
    norm_cast
  rw [hmul, ZMod.toAddCircle_intCast,
    ZMod.cast_intCast (pow_dvd_pow p hmn) j,
    ZMod.toAddCircle_intCast]
  congr 1
  norm_cast
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  apply (Rat.divInt_eq_divInt_iff
    (pow_ne_zero n hp0)
    (pow_ne_zero m hp0)).2
  calc
    (p ^ (n - m) : ℤ) * j * (p ^ m : ℤ) =
        j * ((p ^ (n - m) : ℤ) * (p ^ m : ℤ)) := by ring
    _ = j * (p ^ (n - m + m) : ℤ) := by rw [pow_add]
    _ = j * (p ^ n : ℤ) := by rw [Nat.sub_add_cancel hmn]

/-- The additive subgroup `p⁻ⁿ ℤ_p` of elements whose product with `pⁿ`
is integral. -/
def fieldOnePadicDenominatorStage (n : ℕ) : AddSubgroup ℚ_[p] where
  carrier := {x | ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1}
  zero_mem' := by simp
  add_mem' hx hy := by
    change ‖(p : ℚ_[p]) ^ n * (_ + _)‖ ≤ 1
    change ‖(p : ℚ_[p]) ^ n * _‖ ≤ 1 at hx hy
    rw [mul_add]
    exact (Padic.nonarchimedean _ _).trans
      (max_le hx hy)
  neg_mem' hx := by
    change ‖(p : ℚ_[p]) ^ n * (-_)‖ ≤ 1
    change ‖(p : ℚ_[p]) ^ n * _‖ ≤ 1 at hx
    simpa only [mul_neg, norm_neg] using hx

/-- Scaling a stage element by `pⁿ` as a bundled `p`-adic integer. -/
def fieldOnePadicDenominatorStageIntegral
    (n : ℕ) (x : fieldOnePadicDenominatorStage p n) : ℤ_[p] :=
  ⟨(p : ℚ_[p]) ^ n * x.1, x.2⟩

/-- Canonical stage character obtained by reduction modulo `pⁿ` followed
by `a ↦ a / pⁿ mod ℤ`. -/
noncomputable def fieldOnePadicDenominatorStageCharacter (n : ℕ) :
    fieldOnePadicDenominatorStage p n →+ UnitAddCircle where
  toFun x :=
    ZMod.toAddCircle
      (PadicInt.toZModPow n
        (fieldOnePadicDenominatorStageIntegral p n x))
  map_zero' := by
    change ZMod.toAddCircle
      (PadicInt.toZModPow n
        (fieldOnePadicDenominatorStageIntegral p n 0)) = 0
    rw [show fieldOnePadicDenominatorStageIntegral p n 0 = 0 by
      apply PadicInt.ext
      simp [fieldOnePadicDenominatorStageIntegral]]
    simp
  map_add' x y := by
    have hint :
        fieldOnePadicDenominatorStageIntegral p n (x + y) =
          fieldOnePadicDenominatorStageIntegral p n x +
            fieldOnePadicDenominatorStageIntegral p n y := by
      apply PadicInt.ext
      simp [fieldOnePadicDenominatorStageIntegral, mul_add]
    change ZMod.toAddCircle
        (PadicInt.toZModPow n
          (fieldOnePadicDenominatorStageIntegral p n (x + y))) =
      ZMod.toAddCircle
          (PadicInt.toZModPow n
            (fieldOnePadicDenominatorStageIntegral p n x)) +
        ZMod.toAddCircle
          (PadicInt.toZModPow n
            (fieldOnePadicDenominatorStageIntegral p n y))
    rw [hint, map_add, map_add]

theorem fieldOnePadicDenominatorStage_mono
    {m n : ℕ} (hmn : m ≤ n) :
    fieldOnePadicDenominatorStage p m ≤
      fieldOnePadicDenominatorStage p n := by
  intro x hx
  change (p : ℚ_[p]) ^ n * x ∈
    fieldOnePadicIntegralAddSubgroup p
  have hpow :
      (p : ℚ_[p]) ^ n * x =
        (p : ℚ_[p]) ^ (n - m) *
          ((p : ℚ_[p]) ^ m * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
  change ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1
  change ‖(p : ℚ_[p]) ^ m * x‖ ≤ 1 at hx
  rw [hpow]
  rw [norm_mul]
  exact mul_le_one₀
    ((norm_pow_le _ _).trans
      (pow_le_one₀ (norm_nonneg _)
        (Padic.norm_p_lt_one (p := p)).le))
    (norm_nonneg _)
    hx

theorem fieldOnePadicDenominatorStageIntegral_transition
    {m n : ℕ} (hmn : m ≤ n)
    (x : fieldOnePadicDenominatorStage p m) :
    fieldOnePadicDenominatorStageIntegral p n
        ⟨x, fieldOnePadicDenominatorStage_mono p hmn x.2⟩ =
      (p : ℤ_[p]) ^ (n - m) *
        fieldOnePadicDenominatorStageIntegral p m x := by
  apply PadicInt.ext
  simp only [fieldOnePadicDenominatorStageIntegral,
    PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]

theorem fieldOnePadicDenominatorStageCharacter_transition
    {m n : ℕ} (hmn : m ≤ n)
    (x : fieldOnePadicDenominatorStage p m) :
    fieldOnePadicDenominatorStageCharacter p n
        ⟨x, fieldOnePadicDenominatorStage_mono p hmn x.2⟩ =
      fieldOnePadicDenominatorStageCharacter p m x := by
  change ZMod.toAddCircle
      (PadicInt.toZModPow n
        (fieldOnePadicDenominatorStageIntegral p n
          ⟨x, fieldOnePadicDenominatorStage_mono p hmn x.2⟩)) =
    ZMod.toAddCircle
      (PadicInt.toZModPow m
        (fieldOnePadicDenominatorStageIntegral p m x))
  rw [fieldOnePadicDenominatorStageIntegral_transition p hmn,
    map_mul, map_pow, map_natCast,
    zmodPow_toAddCircle_mul_transition p hmn,
    PadicInt.cast_toZModPow m n hmn]

/-- Every `p`-adic number belongs to some finite denominator stage. -/
theorem fieldOnePadic_exists_denominatorStage (x : ℚ_[p]) :
    ∃ n : ℕ, x ∈ fieldOnePadicDenominatorStage p n := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx, fieldOnePadicDenominatorStage]⟩
  by_cases hv : 0 ≤ x.valuation
  · refine ⟨0, ?_⟩
    change ‖(p : ℚ_[p]) ^ 0 * x‖ ≤ 1
    simpa only [pow_zero, one_mul] using
      (Padic.norm_le_one_iff_val_nonneg x).2 hv
  · let n := Int.toNat (-x.valuation)
    refine ⟨n, ?_⟩
    change ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1
    rw [Padic.norm_le_one_iff_val_nonneg]
    have hp0 : (p : ℚ_[p]) ≠ 0 := by
      exact_mod_cast hp.out.ne_zero
    rw [Padic.valuation_mul (pow_ne_zero n hp0) hx,
      Padic.valuation_pow, Padic.valuation_p]
    have hn : (n : ℤ) = -x.valuation := by
      change ((Int.toNat (-x.valuation) : ℕ) : ℤ) =
        -x.valuation
      rw [Int.toNat_of_nonneg
        (neg_nonneg.mpr (le_of_not_ge hv))]
    rw [hn]
    simp

/-- Chosen denominator depth. The resulting global character will be
independent of this choice by stage compatibility. -/
noncomputable def fieldOnePadicDenominatorDepth (x : ℚ_[p]) : ℕ :=
  Classical.choose (fieldOnePadic_exists_denominatorStage p x)

theorem fieldOnePadicDenominatorDepth_spec (x : ℚ_[p]) :
    x ∈ fieldOnePadicDenominatorStage p
      (fieldOnePadicDenominatorDepth p x) :=
  Classical.choose_spec (fieldOnePadic_exists_denominatorStage p x)

/-- Raw all-depth character obtained by evaluating at a chosen denominator
stage. -/
noncomputable def fieldOnePadicStandardUnitAddCircleRaw (x : ℚ_[p]) :
    UnitAddCircle :=
  fieldOnePadicDenominatorStageCharacter p
      (fieldOnePadicDenominatorDepth p x)
    ⟨x, fieldOnePadicDenominatorDepth_spec p x⟩

/-- The raw value can be computed at every valid denominator stage. -/
theorem fieldOnePadicStandardUnitAddCircleRaw_eq_stage
    {x : ℚ_[p]} {n : ℕ}
    (hx : x ∈ fieldOnePadicDenominatorStage p n) :
    fieldOnePadicStandardUnitAddCircleRaw p x =
      fieldOnePadicDenominatorStageCharacter p n ⟨x, hx⟩ := by
  let k := fieldOnePadicDenominatorDepth p x
  let N := max k n
  have hkN : k ≤ N := Nat.le_max_left _ _
  have hnN : n ≤ N := Nat.le_max_right _ _
  have hk := fieldOnePadicDenominatorDepth_spec p x
  calc
    fieldOnePadicStandardUnitAddCircleRaw p x =
        fieldOnePadicDenominatorStageCharacter p N
          ⟨x, fieldOnePadicDenominatorStage_mono p hkN hk⟩ := by
      simpa only [fieldOnePadicStandardUnitAddCircleRaw, k, N] using
        (fieldOnePadicDenominatorStageCharacter_transition p hkN
          ⟨x, hk⟩).symm
    _ = fieldOnePadicDenominatorStageCharacter p n ⟨x, hx⟩ := by
      simpa only [N] using
        fieldOnePadicDenominatorStageCharacter_transition p hnN
          ⟨x, hx⟩

@[simp]
theorem fieldOnePadicStandardUnitAddCircleRaw_zero :
    fieldOnePadicStandardUnitAddCircleRaw p 0 = 0 := by
  have h0 : (0 : ℚ_[p]) ∈ fieldOnePadicDenominatorStage p 0 := by
    simp [fieldOnePadicDenominatorStage]
  rw [fieldOnePadicStandardUnitAddCircleRaw_eq_stage p h0]
  exact map_zero _

theorem fieldOnePadicStandardUnitAddCircleRaw_add (x y : ℚ_[p]) :
    fieldOnePadicStandardUnitAddCircleRaw p (x + y) =
      fieldOnePadicStandardUnitAddCircleRaw p x +
        fieldOnePadicStandardUnitAddCircleRaw p y := by
  let m := fieldOnePadicDenominatorDepth p x
  let n := fieldOnePadicDenominatorDepth p y
  let N := max m n
  have hmN : m ≤ N := Nat.le_max_left _ _
  have hnN : n ≤ N := Nat.le_max_right _ _
  let xN : fieldOnePadicDenominatorStage p N :=
    ⟨x, fieldOnePadicDenominatorStage_mono p hmN
      (fieldOnePadicDenominatorDepth_spec p x)⟩
  let yN : fieldOnePadicDenominatorStage p N :=
    ⟨y, fieldOnePadicDenominatorStage_mono p hnN
      (fieldOnePadicDenominatorDepth_spec p y)⟩
  rw [fieldOnePadicStandardUnitAddCircleRaw_eq_stage p
      (show x + y ∈ fieldOnePadicDenominatorStage p N from (xN + yN).2),
    fieldOnePadicStandardUnitAddCircleRaw_eq_stage p xN.2,
    fieldOnePadicStandardUnitAddCircleRaw_eq_stage p yN.2]
  exact map_add _ xN yN

/-- Canonical all-depth additive-circle-valued character. -/
noncomputable def fieldOnePadicStandardUnitAddCircleCharacter :
    ℚ_[p] →+ UnitAddCircle where
  toFun := fieldOnePadicStandardUnitAddCircleRaw p
  map_zero' := fieldOnePadicStandardUnitAddCircleRaw_zero p
  map_add' := fieldOnePadicStandardUnitAddCircleRaw_add p

theorem fieldOnePadicStandardUnitAddCircleCharacter_eq_stage
    {x : ℚ_[p]} {n : ℕ}
    (hx : x ∈ fieldOnePadicDenominatorStage p n) :
    fieldOnePadicStandardUnitAddCircleCharacter p x =
      fieldOnePadicDenominatorStageCharacter p n ⟨x, hx⟩ :=
  fieldOnePadicStandardUnitAddCircleRaw_eq_stage p hx

/-- Exact normalization at every principal depth. -/
theorem fieldOnePadicStandardUnitAddCircleCharacter_inv_pow
    (n : ℕ) :
    fieldOnePadicStandardUnitAddCircleCharacter p
        ((p : ℚ_[p]) ^ n)⁻¹ =
      ZMod.toAddCircle (1 : ZMod (p ^ n)) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  have hstage :
      ((p : ℚ_[p]) ^ n)⁻¹ ∈
        fieldOnePadicDenominatorStage p n := by
    change ‖(p : ℚ_[p]) ^ n * ((p : ℚ_[p]) ^ n)⁻¹‖ ≤ 1
    rw [mul_inv_cancel₀ (pow_ne_zero n hp0), norm_one]
  rw [fieldOnePadicStandardUnitAddCircleCharacter_eq_stage p hstage]
  change ZMod.toAddCircle
      (PadicInt.toZModPow n
        ⟨(p : ℚ_[p]) ^ n * ((p : ℚ_[p]) ^ n)⁻¹, hstage⟩) =
    ZMod.toAddCircle (1 : ZMod (p ^ n))
  congr 1
  let oneZp : ℤ_[p] := ⟨(1 : ℚ_[p]), by simp⟩
  rw [show (⟨(p : ℚ_[p]) ^ n * ((p : ℚ_[p]) ^ n)⁻¹,
      hstage⟩ : ℤ_[p]) = oneZp by
        apply PadicInt.ext
        change (p : ℚ_[p]) ^ n * ((p : ℚ_[p]) ^ n)⁻¹ = 1
        rw [mul_inv_cancel₀ (pow_ne_zero n hp0)]]
  change PadicInt.toZModPow n oneZp = 1
  have hone : oneZp = (1 : ℤ_[p]) := by
    apply PadicInt.ext
    rfl
  rw [hone]
  exact map_one _

theorem fieldOnePadicStandardUnitAddCircleCharacter_vanishes_on_integers
    {x : ℚ_[p]} (hx : x ∈ fieldOnePadicIntegralAddSubgroup p) :
    fieldOnePadicStandardUnitAddCircleCharacter p x = 0 := by
  have hstage : x ∈ fieldOnePadicDenominatorStage p 0 := by
    simpa [fieldOnePadicDenominatorStage] using hx
  rw [fieldOnePadicStandardUnitAddCircleCharacter_eq_stage p hstage]
  letI : Subsingleton (ZMod (p ^ 0)) :=
    ZMod.subsingleton_iff.mpr (by simp)
  change ZMod.toAddCircle
      (PadicInt.toZModPow 0
        (fieldOnePadicDenominatorStageIntegral p 0 ⟨x, hstage⟩)) = 0
  have hz :
      PadicInt.toZModPow 0
        (fieldOnePadicDenominatorStageIntegral p 0 ⟨x, hstage⟩) = 0 :=
    Subsingleton.elim _ _
  rw [hz]
  exact map_zero _

theorem fieldOnePadicStandardUnitAddCircleCharacter_isLocallyConstant :
    IsLocallyConstant (fieldOnePadicStandardUnitAddCircleCharacter p) := by
  apply AddMonoidHom.isLocallyConstant_of_open_addSubgroup_le_ker
    (fieldOnePadicStandardUnitAddCircleCharacter p)
    (fieldOnePadicIntegralAddSubgroup p)
    (fieldOnePadicIntegralAddSubgroup_isOpen p)
  intro x hx
  exact
    fieldOnePadicStandardUnitAddCircleCharacter_vanishes_on_integers p hx

/-- Exact kernel of the standard additive-circle character. -/
theorem fieldOnePadicStandardUnitAddCircleCharacter_eq_zero_iff
    (x : ℚ_[p]) :
    fieldOnePadicStandardUnitAddCircleCharacter p x = 0 ↔
      x ∈ fieldOnePadicIntegralAddSubgroup p := by
  refine ⟨?_, fieldOnePadicStandardUnitAddCircleCharacter_vanishes_on_integers p⟩
  intro hx
  let n := fieldOnePadicDenominatorDepth p x
  let u : ℤ_[p] :=
    fieldOnePadicDenominatorStageIntegral p n
      ⟨x, fieldOnePadicDenominatorDepth_spec p x⟩
  have hstage :
      fieldOnePadicDenominatorStageCharacter p n
        ⟨x, fieldOnePadicDenominatorDepth_spec p x⟩ = 0 := by
    rw [← fieldOnePadicStandardUnitAddCircleCharacter_eq_stage p
      (fieldOnePadicDenominatorDepth_spec p x)]
    exact hx
  change ZMod.toAddCircle (PadicInt.toZModPow n u) = 0 at hstage
  have hzmod : PadicInt.toZModPow n u = 0 :=
    ZMod.toAddCircle_eq_zero.mp hstage
  have hker :
      u ∈ RingHom.ker (PadicInt.toZModPow n) := hzmod
  rw [PadicInt.ker_toZModPow] at hker
  rcases Ideal.mem_span_singleton.mp hker with ⟨z, hz⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  have hux :
      (u : ℚ_[p]) = (p : ℚ_[p]) ^ n * x := rfl
  have huz :
      (u : ℚ_[p]) = (p : ℚ_[p]) ^ n * (z : ℚ_[p]) := by
    rw [hz]
    simp only [PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast]
  have hxz : x = (z : ℚ_[p]) := by
    apply (mul_left_cancel₀ (pow_ne_zero n hp0))
    rw [← hux, huz]
  change ‖x‖ ≤ 1
  rw [hxz]
  exact z.2

noncomputable def fieldOnePadicStandardAddChar : AddChar ℚ_[p] ℂ :=
  Circle.coeHom.compAddChar <|
    AddCircle.toCircle_addChar.compAddMonoidHom <|
      fieldOnePadicStandardUnitAddCircleCharacter p

theorem fieldOnePadicStandardAddChar_isLocallyConstant :
    IsLocallyConstant (fieldOnePadicStandardAddChar p) := by
  simpa only [fieldOnePadicStandardAddChar,
    AddChar.compAddMonoidHom_apply,
    MonoidHom.compAddChar_apply] using!
      (fieldOnePadicStandardUnitAddCircleCharacter_isLocallyConstant p).comp
        (fun z : UnitAddCircle => (AddCircle.toCircle z : ℂ))

theorem fieldOnePadicStandardUnitAddCircleCharacter_inv_p_ne_zero :
    fieldOnePadicStandardUnitAddCircleCharacter p
      (p : ℚ_[p])⁻¹ ≠ 0 := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  letI : NeZero (p ^ 1) := ⟨pow_ne_zero 1 (Fact.out : Nat.Prime p).ne_zero⟩
  letI : Fact (1 < p ^ 1) := ⟨by
    simpa using (Fact.out : Nat.Prime p).one_lt⟩
  rw [show (p : ℚ_[p])⁻¹ = ((p : ℚ_[p]) ^ 1)⁻¹ by simp,
    fieldOnePadicStandardUnitAddCircleCharacter_inv_pow]
  intro h
  apply (one_ne_zero : (1 : ZMod (p ^ 1)) ≠ 0)
  apply ZMod.toAddCircle_injective (p ^ 1)
  simpa only [map_zero] using h

theorem fieldOnePadicStandardAddChar_inv_p_ne_one :
    fieldOnePadicStandardAddChar p (p : ℚ_[p])⁻¹ ≠ 1 := by
  intro h
  have hcircle :
      AddCircle.toCircle
          (fieldOnePadicStandardUnitAddCircleCharacter p
            (p : ℚ_[p])⁻¹) = (1 : Circle) :=
    Subtype.ext h
  have hzero :
      fieldOnePadicStandardUnitAddCircleCharacter p
        (p : ℚ_[p])⁻¹ = 0 :=
    AddCircle.injective_toCircle one_ne_zero <| by
      simpa only [AddCircle.toCircle_zero] using hcircle
  exact
    fieldOnePadicStandardUnitAddCircleCharacter_inv_p_ne_zero p hzero

theorem fieldOnePadicStandardAddChar_ne_one :
    fieldOnePadicStandardAddChar p ≠ 1 := by
  intro h
  exact fieldOnePadicStandardAddChar_inv_p_ne_one p <| by
    simpa only [Pi.one_apply] using!
      DFunLike.congr_fun h (p : ℚ_[p])⁻¹

/-- Standard locally constant additive character packaged for the generic
finite-place Weyl multiplier. -/
noncomputable def fieldOnePadicStandardLocallyConstantAddChar :
    LocallyConstantAddChar (R := ℚ_[p]) :=
  ⟨fieldOnePadicStandardAddChar p,
    fieldOnePadicStandardAddChar_isLocallyConstant p⟩

/-- Standard all-depth Weyl multiplier on `p`-adic Bruhat functions. -/
noncomputable def fieldOnePadicStandardWeylMultiplier (r : ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] →ₗ[ℂ]
      compactlySupportedLocallyConstant ℚ_[p] :=
  locallyConstantWeylMultiplier
    (fieldOnePadicStandardLocallyConstantAddChar p) r

theorem fieldOnePadicStandardWeylMultiplier_add (r s : ℚ_[p]) :
    (fieldOnePadicStandardWeylMultiplier p r).comp
        (fieldOnePadicStandardWeylMultiplier p s) =
      fieldOnePadicStandardWeylMultiplier p (r + s) :=
  locallyConstantWeylMultiplier_add
    (fieldOnePadicStandardLocallyConstantAddChar p) r s

end

end GaloisForLFunctions.RHTower
