import GaloisForLFunctions.HeckeLFunctions.HeckePrimitiveGaussConstantsHaveExactNorm
import GaloisForLFunctions.HeckeLFunctions.HeckeFourierCoefficientsScaleByRayResidues
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaWeightsArePrincipalIdealCharacters

/-!
# Primitive Fourier coefficients are inverse Hecke values

The integral ideal attached to a trace-dual frequency changes by its
principal multiplier. On coprime frequencies, the finite residue factor
and real sign combine into the actual ray-class value. This makes the
sign-corrected coefficient times the ideal character constant. Transfer
to the unit base determines that constant for every coprime base ideal;
the unsupported frequencies vanish on both sides of the final identity.
-/

noncomputable section
open NumberField
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
  {b : Ideal (𝓞 K)} (hb0 : b ≠ ⊥)
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
local notation "Jdual" => FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)

/-- Multiplication of frequencies is multiplication of their associated ideals by a principal ideal. -/
theorem heckeDualFrequencyIdeal_principal_mul (α : Kˣ) (a a' : Jdual)
    (hα : (a' : K) = (α : K) * (a : K)) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (α : K) *
      (heckeDualFrequencyIdeal 𝔪 hb0 a : FI) = (heckeDualFrequencyIdeal 𝔪 hb0 a' : FI) := by
  apply mul_right_cancel₀ (heckeDualProductIdeal_ne_zero 𝔪 hb0)
  rw [mul_assoc, heckeDualFrequencyIdeal_mul_dual, heckeDualFrequencyIdeal_mul_dual,
    FractionalIdeal.spanSingleton_mul_spanSingleton, ← hα]

theorem heckeDualFrequencyIdeal_principal_mul_unit (α : Kˣ) (a a' : Jdual)
    (ha : (a : K) ≠ 0) (ha' : (a' : K) ≠ 0)
    (hα : (a' : K) = (α : K) * (a : K)) :
    _root_.toPrincipalIdeal (𝓞 K) K α *
        idealUnit ((heckeDualFrequencyIdeal_eq_bot_iff 𝔪 hb0 a).not.mpr ha) =
      idealUnit ((heckeDualFrequencyIdeal_eq_bot_iff 𝔪 hb0 a').not.mpr ha') := by
  apply Units.ext
  rw [Units.val_mul, _root_.coe_toPrincipalIdeal, coe_idealUnit, coe_idealUnit]
  exact heckeDualFrequencyIdeal_principal_mul 𝔪 hb0 α a a' hα

/-- A multiplier between two supported nonzero frequencies is automatically prime to the modulus. -/
theorem heckeDualFrequencyMultiplier_mem_primeTo (α : Kˣ) (a a' : Jdual)
    (ha : (a : K) ≠ 0) (ha' : (a' : K) ≠ 0)
    (hα : (a' : K) = (α : K) * (a : K))
    (hc : heckeDualFrequencyIdeal 𝔪 hb0 a ⊔ 𝔪.fin = ⊤)
    (hc' : heckeDualFrequencyIdeal 𝔪 hb0 a' ⊔ 𝔪.fin = ⊤) :
    α ∈ primeToUnits 𝔪 := by
  apply (toPrincipalIdeal_mem_idealGroup_iff 𝔪 α).mp
  have h := heckeDualFrequencyIdeal_principal_mul_unit 𝔪 hb0 α a a' ha ha' hα
  rw [← eq_mul_inv_iff_mul_eq] at h
  rw [h]
  exact (idealGroup 𝔪).mul_mem ((idealUnit_mem_idealGroup_iff 𝔪 _).mpr hc')
    ((idealGroup 𝔪).inv_mem ((idealUnit_mem_idealGroup_iff 𝔪 _).mpr hc))

/-- The actual ray character of a frequency multiplier is the ratio of its ideal coefficients. -/
theorem heckeValue_dualFrequencyIdeal_mul_principal (ψ : HeckeCharacter 𝔪)
    (α : primeToUnits 𝔪) (a a' : Jdual) (ha : (a : K) ≠ 0) (ha' : (a' : K) ≠ 0)
    (hα : (a' : K) = (α : Kˣ) * (a : K))
    (hc : heckeDualFrequencyIdeal 𝔪 hb0 a ⊔ 𝔪.fin = ⊤)
    (hc' : heckeDualFrequencyIdeal 𝔪 hb0 a' ⊔ 𝔪.fin = ⊤) :
    (ψ (rayClassOfElt 𝔪 α) : ℂ) * heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a) =
      heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a') := by
  have hI0 := (heckeDualFrequencyIdeal_eq_bot_iff 𝔪 hb0 a).not.mpr ha
  have hI'0 := (heckeDualFrequencyIdeal_eq_bot_iff 𝔪 hb0 a').not.mpr ha'
  let A : idealGroup 𝔪 := ⟨idealUnit hI0, (idealUnit_mem_idealGroup_iff 𝔪 _).mpr hc⟩
  let A' : idealGroup 𝔪 := ⟨idealUnit hI'0, (idealUnit_mem_idealGroup_iff 𝔪 _).mpr hc'⟩
  let P : idealGroup 𝔪 := ⟨_root_.toPrincipalIdeal (𝓞 K) K (α : Kˣ),
    (toPrincipalIdeal_mem_idealGroup_iff 𝔪 _).mpr α.2⟩
  have hprod : P * A = A' := Subtype.ext
    (heckeDualFrequencyIdeal_principal_mul_unit 𝔪 hb0 (α : Kˣ) a a' ha ha' hα)
  rw [heckeValue_of_mem 𝔪 ψ hI0 A.2, heckeValue_of_mem 𝔪 ψ hI'0 A'.2]
  change (ψ (rayClass 𝔪 P) : ℂ) * (ψ (rayClass 𝔪 A) : ℂ) = (ψ (rayClass 𝔪 A') : ℂ)
  rw [← Units.val_mul, ← map_mul, ← map_mul, hprod]

/-- Every infinite sign character has square one. -/
theorem infiniteSignCharacter_sq (ψ : HeckeCharacter 𝔪) (σ : 𝔪.inf → ℤˣ) :
    (infiniteSignCharacter 𝔪 ψ σ : ℂ) ^ 2 = 1 := by
  have hσ : σ ^ 2 = 1 := by
    funext w
    change σ w ^ 2 = 1
    rcases Int.units_eq_one_or (σ w) with h | h <;> rw [h] <;> norm_num
  rw [← Units.val_pow_eq_pow_val, ← map_pow, hσ, map_one, Units.val_one]

variable (hb : b ⊔ 𝔪.fin = ⊤)

/-- Finite Gauss scaling and principal ray values make the sign-corrected coefficient invariant. -/
theorem finiteHeckeFourierCoefficient_sign_character_invariant (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (α : primeToUnits 𝔪)
    (a a' : Jdual) (ha : (a : K) ≠ 0) (ha' : (a' : K) ≠ 0)
    (hα : (a' : K) = (α : Kˣ) * (a : K))
    (hc : heckeDualFrequencyIdeal 𝔪 hb0 a ⊔ 𝔪.fin = ⊤)
    (hc' : heckeDualFrequencyIdeal 𝔪 hb0 a' ⊔ 𝔪.fin = ⊤) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ (a' : K) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha')) : ℂ) *
        heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a') =
      finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) *
        heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a) := by
  have hu : Units.mk0 (a' : K) ha' = (α : Kˣ) * Units.mk0 (a : K) ha := Units.ext hα
  have hs : (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha')) : ℂ) =
      (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (α : Kˣ)) : ℂ) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) := by
    rw [hu, map_mul, map_mul, Units.val_mul]
  have hv := heckeValue_dualFrequencyIdeal_mul_principal 𝔪 hb0 ψ α a a' ha ha' hα hc hc'
  have hchar := congrArg (fun z : ℂˣ => (z : ℂ)) (character_rayClassOfElt_eq 𝔪 ψ α)
  simp only [Units.val_mul] at hchar
  rw [hchar] at hv
  rw [finiteHeckeFourierCoefficient_mul_primeTo 𝔪 hb hb0 ψ hψ α a a' hα, hs, ← hv]
  calc
    _ = ((finiteResidueCharacter 𝔪 ψ (reduce 𝔪 α) : ℂ)⁻¹ *
          (finiteResidueCharacter 𝔪 ψ (reduce 𝔪 α) : ℂ)) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (α : Kˣ)) : ℂ) ^ 2 *
        (finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
          (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) *
          heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (Units.ne_zero _), infiniteSignCharacter_sq, one_mul, one_mul]

/-- Every supported unit-base frequency gives the same arithmetic Gauss constant. -/
theorem finiteHeckeFourierCoefficient_unitBase_invariant (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin)
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * ⊤ : Ideal (𝓞 K)) : FI)) (ha : (a : K) ≠ 0)
    (hc : heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) a ⊔ 𝔪.fin = ⊤) :
    finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ (a : K) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) *
        heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) a) =
      heckeGaussConstant 𝔪 ψ := by
  let α₀ : Kˣ := Units.mk0 ((a : K) / (heckeReferenceFrequency 𝔪 : K))
    (div_ne_zero ha (heckeReferenceFrequency_ne_zero 𝔪))
  have hα : (a : K) = (α₀ : K) * (heckeReferenceFrequency 𝔪 : K) :=
    (div_mul_cancel₀ _ (heckeReferenceFrequency_ne_zero 𝔪)).symm
  have hp : α₀ ∈ primeToUnits 𝔪 :=
    heckeDualFrequencyMultiplier_mem_primeTo 𝔪 (b := ⊤) (by simp) α₀
      (heckeReferenceFrequency 𝔪) a (heckeReferenceFrequency_ne_zero 𝔪) ha hα
      (heckeReferenceIdeal_coprime 𝔪) hc
  let α : primeToUnits 𝔪 := ⟨α₀, hp⟩
  exact finiteHeckeFourierCoefficient_sign_character_invariant 𝔪 (b := ⊤) (by simp)
    (by simp) ψ hψ α (heckeReferenceFrequency 𝔪) a (heckeReferenceFrequency_ne_zero 𝔪)
    ha hα (heckeReferenceIdeal_coprime 𝔪) hc

/-- The unit-base Fourier coefficient is the inverse actual ideal character with its sign and Gauss factor. -/
theorem finiteHeckeFourierCoefficient_unitBase_eq_inverse_heckeValue (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin)
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * ⊤ : Ideal (𝓞 K)) : FI)) (ha : (a : K) ≠ 0) :
    finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ (a : K) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) =
      heckeGaussConstant 𝔪 ψ *
        (heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) a))⁻¹ := by
  by_cases hc : heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) a ⊔ 𝔪.fin = ⊤
  · have hI0 := (heckeDualFrequencyIdeal_eq_bot_iff 𝔪 (b := ⊤) (by simp) a).not.mpr ha
    have hV : heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) a) ≠ 0 := by
      rw [heckeValue_of_mem 𝔪 ψ hI0 ((idealUnit_mem_idealGroup_iff 𝔪 _).mpr hc)]
      exact Units.ne_zero _
    have h := finiteHeckeFourierCoefficient_unitBase_invariant 𝔪 ψ hψ a ha hc
    calc
      _ = (finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ (a : K) *
            (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) *
            heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) a)) *
          (heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) a))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hV, mul_one]
      _ = _ := by rw [h]
  · have hF : finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ (a : K) = 0 := by
      by_contra hF
      exact hc ((finiteHeckeFourierCoefficient_ne_zero_iff_coprime 𝔪 (b := ⊤)
        (by simp) (by simp) ψ hψ a).mp hF)
    have hV : heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) a) = 0 := by
      apply heckeValue_of_not_mem
      rintro ⟨hI0, hI⟩
      exact hc ((idealUnit_mem_idealGroup_iff 𝔪 hI0).mp hI)
    rw [hF, hV, zero_mul, inv_zero, mul_zero]

include hb0 in
/-- Multiplication by the base ideal converts the modulus-product dual into the unit-base dual. -/
theorem heckeDualProductIdeal_mul_base :
    Jdual * (b : FI) = FractionalIdeal.dual ℤ ℚ ((𝔪.fin * ⊤ : Ideal (𝓞 K)) : FI) := by
  have hbF : (b : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hb0
  rw [Ideal.mul_top, FractionalIdeal.dual_eq_mul_inv ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI),
    FractionalIdeal.dual_eq_mul_inv ℤ ℚ (𝔪.fin : FI), FractionalIdeal.coeIdeal_mul, mul_inv_rev]
  calc
    _ = FractionalIdeal.dual ℤ ℚ (1 : FI) * (𝔪.fin : FI)⁻¹ * ((b : FI)⁻¹ * (b : FI)) := by
      ac_rfl
    _ = _ := by rw [inv_mul_cancel₀ hbF, mul_one]

/-- Transfer to the unit base changes the associated ideal by the exact principal/base ratio. -/
theorem heckeDualFrequencyIdeal_toUnitBase_mul_base (a : Jdual) (x : 𝓞 K) (hx : x ∈ b) :
    heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp)
        (heckeTraceFrequencyToUnitBase 𝔪 hb0 a x hx) * b =
      Ideal.span {x} * heckeDualFrequencyIdeal 𝔪 hb0 a := by
  have hF :
      (heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp)
        (heckeTraceFrequencyToUnitBase 𝔪 hb0 a x hx) : FI) * (b : FI) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) *
        (heckeDualFrequencyIdeal 𝔪 hb0 a : FI) := by
    apply mul_right_cancel₀ (heckeDualProductIdeal_ne_zero 𝔪 hb0)
    calc
      _ = (heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp)
          (heckeTraceFrequencyToUnitBase 𝔪 hb0 a x hx) : FI) * (Jdual * (b : FI)) := by
        ac_rfl
      _ = _ := by
        rw [heckeDualProductIdeal_mul_base 𝔪 hb0, heckeDualFrequencyIdeal_mul_dual,
          mul_assoc, heckeDualFrequencyIdeal_mul_dual,
          FractionalIdeal.spanSingleton_mul_spanSingleton]
        rfl
  apply FractionalIdeal.coeIdeal_injective (K := K)
  change ((heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp)
    (heckeTraceFrequencyToUnitBase 𝔪 hb0 a x hx) * b : Ideal (𝓞 K)) : FI) =
      ((Ideal.span {x} * heckeDualFrequencyIdeal 𝔪 hb0 a : Ideal (𝓞 K)) : FI)
  rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_span_singleton, ← RingOfIntegers.coe_eq_algebraMap]
  exact hF

omit [NumberField K] in
include hb0 hb in
/-- A nonzero coprime ideal contains a nonzero element invertible modulo the modulus. -/
theorem exists_nonzero_unitResidue_mem_coprimeIdeal :
    ∃ x : 𝓞 K, x ∈ b ∧ x ≠ 0 ∧ IsUnit (Ideal.Quotient.mk 𝔪.fin x) := by
  by_cases hm : 𝔪.fin = ⊤
  · obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff b).mp hb0
    refine ⟨x, hx, hx0, ?_⟩
    have hq : Ideal.Quotient.mk 𝔪.fin x = 1 := by
      rw [← map_one (Ideal.Quotient.mk 𝔪.fin)]
      apply Ideal.Quotient.eq.mpr
      rw [hm]
      exact Submodule.mem_top
    rw [hq]
    exact isUnit_one
  · let x := residueRep 𝔪 hb 1
    have hq : Ideal.Quotient.mk 𝔪.fin x = 1 := mk_residueRep hb 1
    have hx0 : x ≠ 0 := by
      intro hx0
      apply hm
      apply (Ideal.eq_top_iff_one _).mpr
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_one, ← hq, hx0, map_zero]
    refine ⟨x, residueRep_mem hb 1, hx0, ?_⟩
    rw [hq]
    exact isUnit_one

/-- The common Gauss constant acquires exactly the base ideal's Hecke value. -/
theorem finiteHeckeFourierCoefficient_base_invariant (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (a : Jdual) (ha : (a : K) ≠ 0)
    (hc : heckeDualFrequencyIdeal 𝔪 hb0 a ⊔ 𝔪.fin = ⊤) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) *
        heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a) =
      heckeGaussConstant 𝔪 ψ * heckeValue 𝔪 ψ b := by
  obtain ⟨x, hx, hx0, hxu⟩ := exists_nonzero_unitResidue_mem_coprimeIdeal 𝔪 hb0 hb
  obtain ⟨u, hu⟩ := hxu
  have hxK : (x : K) ≠ 0 := by simpa using hx0
  have hw : finiteHeckeWeight 𝔪 ψ (Ideal.Quotient.mk 𝔪.fin x) =
      (finiteResidueCharacter 𝔪 ψ u : ℂ) := by
    rw [← hu, finiteHeckeWeight_unit]
  let a₁ := heckeTraceFrequencyToUnitBase 𝔪 hb0 a x hx
  have ha₁ : (a₁ : K) ≠ 0 := mul_ne_zero hxK ha
  have ht : finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ (a₁ : K) =
      (finiteResidueCharacter 𝔪 ψ u : ℂ)⁻¹ * finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) := by
    change finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ ((x : K) * (a : K)) = _
    simpa only [MulChar.inv_apply_eq_inv', hw] using
      finiteHeckeFourierCoefficient_toUnitBase 𝔪 hb hb0 ψ hψ a x hx
  have hF₁ : finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ (a₁ : K) ≠ 0 := by
    rw [ht]
    exact mul_ne_zero (inv_ne_zero (Units.ne_zero _))
      ((finiteHeckeFourierCoefficient_ne_zero_iff_coprime 𝔪 hb0 hb ψ hψ a).mpr hc)
  have hc₁ := (finiteHeckeFourierCoefficient_ne_zero_iff_coprime 𝔪 (b := ⊤)
    (by simp) (by simp) ψ hψ a₁).mp hF₁
  have hC := finiteHeckeFourierCoefficient_unitBase_invariant 𝔪 ψ hψ a₁ ha₁ hc₁
  have hval := congrArg (heckeValue 𝔪 ψ)
    (heckeDualFrequencyIdeal_toUnitBase_mul_base 𝔪 hb0 a x hx)
  rw [heckeValue_mul, heckeValue_mul] at hval
  have hp := integralHeckeWeight_mul_infiniteSign_eq_heckeValue 𝔪 ψ x hxK
  change finiteHeckeWeight 𝔪 ψ (Ideal.Quotient.mk 𝔪.fin x) *
    (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ hxK)) : ℂ) =
      heckeValue 𝔪 ψ (Ideal.span {x}) at hp
  rw [hw] at hp
  have hs : (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha₁)) : ℂ) =
      (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ hxK)) : ℂ) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) := by
    have hunit : Units.mk0 (a₁ : K) ha₁ = Units.mk0 (x : K) hxK * Units.mk0 (a : K) ha :=
      Units.ext rfl
    rw [hunit, map_mul, map_mul, Units.val_mul]
  symm
  calc
    _ = (finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ (a₁ : K) *
          (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha₁)) : ℂ) *
          heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) a₁)) *
        heckeValue 𝔪 ψ b := by rw [hC]
    _ = finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ (a₁ : K) *
          (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha₁)) : ℂ) *
          (heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 (b := ⊤) (by simp) a₁) *
            heckeValue 𝔪 ψ b) := by rw [mul_assoc]
    _ = ((finiteResidueCharacter 𝔪 ψ u : ℂ)⁻¹ *
          finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K)) *
        ((infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ hxK)) : ℂ) *
          (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ)) *
        (((finiteResidueCharacter 𝔪 ψ u : ℂ) *
          (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ hxK)) : ℂ)) *
          heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a)) := by
      rw [hval, ← hp, ht, hs]
    _ = ((finiteResidueCharacter 𝔪 ψ u : ℂ)⁻¹ * (finiteResidueCharacter 𝔪 ψ u : ℂ)) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ hxK)) : ℂ) ^ 2 *
        (finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
          (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) *
          heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (Units.ne_zero _), infiniteSignCharacter_sq, one_mul, one_mul]

/-- Actual primitive dual-theta coefficients are inverse Hecke ideal values with exact class and sign factors. -/
theorem finiteHeckeFourierCoefficient_eq_inverse_heckeValue (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (a : Jdual) (ha : (a : K) ≠ 0) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) =
      heckeGaussConstant 𝔪 ψ * heckeValue 𝔪 ψ b *
        (heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a))⁻¹ := by
  by_cases hc : heckeDualFrequencyIdeal 𝔪 hb0 a ⊔ 𝔪.fin = ⊤
  · have hI0 := (heckeDualFrequencyIdeal_eq_bot_iff 𝔪 hb0 a).not.mpr ha
    have hV : heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a) ≠ 0 := by
      rw [heckeValue_of_mem 𝔪 ψ hI0 ((idealUnit_mem_idealGroup_iff 𝔪 _).mpr hc)]
      exact Units.ne_zero _
    have h := finiteHeckeFourierCoefficient_base_invariant 𝔪 hb0 hb ψ hψ a ha hc
    calc
      _ = (finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
            (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) *
            heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a)) *
          (heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hV, mul_one]
      _ = _ := by rw [h]
  · have hF : finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) = 0 := by
      by_contra hF
      exact hc ((finiteHeckeFourierCoefficient_ne_zero_iff_coprime 𝔪 hb0 hb ψ hψ a).mp hF)
    have hV : heckeValue 𝔪 ψ (heckeDualFrequencyIdeal 𝔪 hb0 a) = 0 := by
      apply heckeValue_of_not_mem
      rintro ⟨hI0, hI⟩
      exact hc ((idealUnit_mem_idealGroup_iff 𝔪 hI0).mp hI)
    rw [hF, hV, zero_mul, inv_zero, mul_zero]

/-- Inverting a Hecke character inverts every ideal coefficient, including the zero extension. -/
theorem heckeValue_inv (ψ : HeckeCharacter 𝔪) (I : Ideal (𝓞 K)) :
    heckeValue 𝔪 ψ⁻¹ I = (heckeValue 𝔪 ψ I)⁻¹ := by
  by_cases h : ∃ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪
  · obtain ⟨hI, hm⟩ := h
    rw [heckeValue_of_mem 𝔪 ψ⁻¹ hI hm, heckeValue_of_mem 𝔪 ψ hI hm]
    exact Units.val_inv_eq_inv_val _
  · rw [heckeValue_of_not_mem 𝔪 ψ⁻¹ h, heckeValue_of_not_mem 𝔪 ψ h, inv_zero]

/-- The actual dual-theta coefficient is the inverse Hecke character with its exact arithmetic factor. -/
theorem finiteHeckeFourierCoefficient_eq_dualHeckeValue (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (a : Jdual) (ha : (a : K) ≠ 0) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) *
        (infiniteSignCharacter 𝔪 ψ (signAtInf 𝔪 (Units.mk0 _ ha)) : ℂ) =
      heckeGaussConstant 𝔪 ψ * heckeValue 𝔪 ψ b *
        heckeValue 𝔪 ψ⁻¹ (heckeDualFrequencyIdeal 𝔪 hb0 a) := by
  rw [heckeValue_inv]
  exact finiteHeckeFourierCoefficient_eq_inverse_heckeValue 𝔪 hb0 hb ψ hψ a ha

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.heckeDualFrequencyMultiplier_mem_primeTo
#print axioms GaloisForLFunctions.HeckeLFunctions.finiteHeckeFourierCoefficient_sign_character_invariant
#print axioms GaloisForLFunctions.HeckeLFunctions.finiteHeckeFourierCoefficient_unitBase_eq_inverse_heckeValue
#print axioms GaloisForLFunctions.HeckeLFunctions.finiteHeckeFourierCoefficient_eq_inverse_heckeValue
#print axioms GaloisForLFunctions.HeckeLFunctions.finiteHeckeFourierCoefficient_eq_dualHeckeValue
