import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateProjection
import GaloisForLFunctions.RHTower.FieldOneLocalHaarModule

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology
open scoped BigOperators NNReal ENNReal

variable (p : ℕ) [Fact p.Prime]

theorem fieldOnePadicUnit_sub_eq_primePow_mul_of_reduction_eq
    (q : ℕ) {u v : ℤ_[p]ˣ}
    (h : fieldOnePadicUnitReduction p q u =
      fieldOnePadicUnitReduction p q v) :
    ∃ z : ℤ_[p],
      (u : ℤ_[p]) - (v : ℤ_[p]) = (p : ℤ_[p]) ^ q * z := by
  have hval := congrArg Units.val h
  change PadicInt.toZModPow q (u : ℤ_[p]) =
    PadicInt.toZModPow q (v : ℤ_[p]) at hval
  have hker : (u : ℤ_[p]) - (v : ℤ_[p]) ∈
      RingHom.ker (PadicInt.toZModPow (p := p) q) := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hval
  rw [PadicInt.ker_toZModPow] at hker
  exact Ideal.mem_span_singleton.mp hker

theorem fieldOnePadicUnitReduction_eq_of_deeperReduction_eq
    (n t : ℕ) {u v : ℤ_[p]ˣ}
    (h : fieldOnePadicUnitReduction p (n + t) u =
      fieldOnePadicUnitReduction p (n + t) v) :
    fieldOnePadicUnitReduction p n u =
      fieldOnePadicUnitReduction p n v := by
  obtain ⟨z, hz⟩ :=
    fieldOnePadicUnit_sub_eq_primePow_mul_of_reduction_eq p (n + t) h
  apply Units.ext
  change PadicInt.toZModPow n (u : ℤ_[p]) =
    PadicInt.toZModPow n (v : ℤ_[p])
  rw [← sub_eq_zero, ← map_sub, hz, map_mul, map_pow, map_natCast]
  rw [pow_add]
  have hp : ((p : ZMod (p ^ n)) ^ n) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hp, zero_mul, zero_mul]

theorem fieldOnePadicBruhat_unit_action_eq_of_deeperReduction_eq
    (n N L : ℕ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p N)
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p])) = f.1 x)
    {u v : ℤ_[p]ˣ}
    (hred : fieldOnePadicUnitReduction p (n + N + L) u =
      fieldOnePadicUnitReduction p (n + N + L) v)
    (x : ℚ_[p]) :
    f.1 (((u : ℤ_[p]) : ℚ_[p]) * x) =
      f.1 (((v : ℤ_[p]) : ℚ_[p]) * x) := by
  by_cases hx : x ∈ fieldOnePadicDenominatorStage p N
  · obtain ⟨z, hz⟩ :=
      fieldOnePadicUnit_sub_eq_primePow_mul_of_reduction_eq
        p (n + N + L) hred
    let w : ℤ_[p] := fieldOnePadicDenominatorStageIntegral p N ⟨x, hx⟩
    let z' : ℤ_[p] := (p : ℤ_[p]) ^ n * z * w
    have hw : (w : ℚ_[p]) = (p : ℚ_[p]) ^ N * x := rfl
    have harg : (((u : ℤ_[p]) : ℚ_[p])) * x =
        (((v : ℤ_[p]) : ℚ_[p])) * x +
          (p : ℚ_[p]) ^ L * (z' : ℚ_[p]) := by
      have hzq : (((u : ℤ_[p]) : ℚ_[p])) -
          (((v : ℤ_[p]) : ℚ_[p])) =
            (p : ℚ_[p]) ^ (n + N + L) * (z : ℚ_[p]) := by
        have hz' := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz
        simpa only [PadicInt.coe_sub, PadicInt.coe_mul,
          PadicInt.coe_pow, PadicInt.coe_natCast] using hz'
      have huq : (((u : ℤ_[p]) : ℚ_[p])) =
          (((v : ℤ_[p]) : ℚ_[p])) +
            (p : ℚ_[p]) ^ (n + N + L) * (z : ℚ_[p]) := by
        calc
          (((u : ℤ_[p]) : ℚ_[p])) =
              ((((u : ℤ_[p]) : ℚ_[p])) -
                (((v : ℤ_[p]) : ℚ_[p]))) +
                (((v : ℤ_[p]) : ℚ_[p])) := by ring
          _ = (p : ℚ_[p]) ^ (n + N + L) * (z : ℚ_[p]) +
                (((v : ℤ_[p]) : ℚ_[p])) := by rw [hzq]
          _ = _ := by ring
      rw [huq]
      dsimp only [z']
      rw [PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_natCast, hw]
      rw [show n + N + L = L + n + N by omega,
        pow_add, pow_add]
      ring
    rw [harg]
    exact hperiod _ z'
  · have huout : (((u : ℤ_[p]) : ℚ_[p])) * x ∉
        tsupport (f.1 : ℚ_[p] → ℂ) := by
      intro hmem
      apply hx
      exact (fieldOnePadicDenominatorStage_unit_mul_iff p N u x).mp
        (hsupport hmem)
    have hvout : (((v : ℤ_[p]) : ℚ_[p])) * x ∉
        tsupport (f.1 : ℚ_[p] → ℂ) := by
      intro hmem
      apply hx
      exact (fieldOnePadicDenominatorStage_unit_mul_iff p N v x).mp
        (hsupport hmem)
    rw [image_eq_zero_of_notMem_tsupport huout,
      image_eq_zero_of_notMem_tsupport hvout]

theorem fieldOnePadicPrimitiveAngularProjection_integrand_classInvariant
    (n N L : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p N)
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p])) = f.1 x)
    (x : ℚ_[p]) {u v : ℤ_[p]ˣ}
    (hred : fieldOnePadicUnitReduction p (n + N + L) u =
      fieldOnePadicUnitReduction p (n + N + L) v) :
    fieldOnePadicPrimitiveUnitCharacter p n χ u *
        f.1 (((u : ℤ_[p]) : ℚ_[p]) * x) =
      fieldOnePadicPrimitiveUnitCharacter p n χ v *
        f.1 (((v : ℤ_[p]) : ℚ_[p]) * x) := by
  rw [fieldOnePadicBruhat_unit_action_eq_of_deeperReduction_eq
    p n N L f hsupport hperiod hred x]
  congr 1
  unfold fieldOnePadicPrimitiveUnitCharacter
  rw [fieldOnePadicUnitReduction_eq_of_deeperReduction_eq p n (N + L)]
  have hred' := hred
  rw [Nat.add_assoc] at hred'
  exact hred'

theorem fieldOnePadicPrimitiveAngularProjectionValue_eq_finiteAverage
    (n N L : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p N)
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p])) = f.1 x)
    (x : ℚ_[p]) :
    fieldOnePadicPrimitiveAngularProjectionValue p n χ f x =
      ((Fintype.card (ZMod (p ^ (n + N + L)))ˣ : ℕ) : ℂ)⁻¹ *
        ∑ r : (ZMod (p ^ (n + N + L)))ˣ,
          fieldOnePadicPrimitiveUnitCharacter p n χ
              (fieldOnePadicUnitResidueRep p (n + N + L) r) *
            f.1 ((((fieldOnePadicUnitResidueRep p (n + N + L) r :
              ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * x) := by
  let g : ℤ_[p]ˣ → ℂ := fun u =>
    fieldOnePadicPrimitiveUnitCharacter p n χ u *
      f.1 (((u : ℤ_[p]) : ℚ_[p]) * x)
  have hg := integrable_fieldOnePadicPrimitiveAngularProjectionValue_integrand
    p n χ f x
  have hclass : ∀ {u v : ℤ_[p]ˣ},
      fieldOnePadicUnitReduction p (n + N + L) u =
        fieldOnePadicUnitReduction p (n + N + L) v → g u = g v := by
    intro u v huv
    exact fieldOnePadicPrimitiveAngularProjection_integrand_classInvariant
      p n N L χ f hsupport hperiod x huv
  have hquad := fieldOnePadicUnit_sampleSum_eq_nsmul_integral
    p (n + N + L) g hg hclass
  change (∫ u, g u ∂fieldOnePadicUnitNormalizedHaar p) = _
  change (∑ r : (ZMod (p ^ (n + N + L)))ˣ,
      g (fieldOnePadicUnitResidueRep p (n + N + L) r)) =
    Fintype.card (ZMod (p ^ (n + N + L)))ˣ •
      (∫ u, g u ∂fieldOnePadicUnitNormalizedHaar p) at hquad
  rw [hquad]
  simp only [nsmul_eq_mul]
  have hcard :
      ((Fintype.card (ZMod (p ^ (n + N + L)))ˣ : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

def fieldOnePadicPrimitiveAngularFiniteAverage
    (n N L : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  ∑ r : (ZMod (p ^ (n + N + L)))ˣ,
    (((Fintype.card (ZMod (p ^ (n + N + L)))ˣ : ℕ) : ℂ)⁻¹ *
      fieldOnePadicPrimitiveUnitCharacter p n χ
        (fieldOnePadicUnitResidueRep p (n + N + L) r)) •
      fieldOnePadicBruhatDilation p
        (fieldOnePadicUnitEmbedding p
          (fieldOnePadicUnitResidueRep p (n + N + L) r)) f

theorem fieldOnePadicPrimitiveAngularProjection_eq_finiteAverage_of_finiteLevel
    (n N L : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p N)
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p])) = f.1 x) :
    fieldOnePadicPrimitiveAngularProjection p n χ f =
      fieldOnePadicPrimitiveAngularFiniteAverage p n N L χ f := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rw [fieldOnePadicPrimitiveAngularProjection_apply,
    fieldOnePadicPrimitiveAngularProjectionValue_eq_finiteAverage
      p n N L χ f hsupport hperiod x]
  change _ = fieldOnePadicBruhatEvalLinear p x
    (∑ r : (ZMod (p ^ (n + N + L)))ˣ,
      (((Fintype.card (ZMod (p ^ (n + N + L)))ˣ : ℕ) : ℂ)⁻¹ *
        fieldOnePadicPrimitiveUnitCharacter p n χ
          (fieldOnePadicUnitResidueRep p (n + N + L) r)) •
        fieldOnePadicBruhatDilation p
          (fieldOnePadicUnitEmbedding p
            (fieldOnePadicUnitResidueRep p (n + N + L) r)) f)
  rw [map_sum]
  simp only [map_smul, fieldOnePadicBruhatEvalLinear_apply,
    fieldOnePadicBruhatDilation_apply, fieldOnePadicUnitEmbedding_val,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem fieldOnePadicUnitEmbedding_mul_coordinates
    (u v : ℤ_[p]ˣ) (k : ℤ) :
    fieldOnePadicUnitEmbedding p u *
        fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd k, v) =
      fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd k, u * v) := by
  change fieldOnePadicValuationUnitContinuousMulEquiv p
      (Multiplicative.ofAdd 0, u) *
        fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd k, v) = _
  rw [← map_mul]
  congr 1
  simp

theorem fieldOnePadicRamifiedCriticalCharacter_unit_mul
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (u : ℤ_[p]ˣ) (a : ℚ_[p]ˣ) :
    fieldOnePadicRamifiedCriticalCharacter p n χ ρ
        (fieldOnePadicUnitEmbedding p u * a) =
      fieldOnePadicPrimitiveUnitCharacter p n χ u *
        fieldOnePadicRamifiedCriticalCharacter p n χ ρ a := by
  let z : Multiplicative ℤ × ℤ_[p]ˣ :=
    (fieldOnePadicValuationUnitContinuousMulEquiv p).symm a
  let k : ℤ := Multiplicative.toAdd z.1
  let v : ℤ_[p]ˣ := z.2
  have ha : fieldOnePadicValuationUnitContinuousMulEquiv p
      (Multiplicative.ofAdd k, v) = a := by
    simp [k, v, z]
  rw [← ha, fieldOnePadicUnitEmbedding_mul_coordinates,
    fieldOnePadicRamifiedCriticalCharacter_coordinates,
    fieldOnePadicRamifiedCriticalCharacter_coordinates]
  change ((ρ : ℂ) ^ k) *
      fieldOnePadicPrimitiveUnitCharacter p n χ (u * v) =
    fieldOnePadicPrimitiveUnitCharacter p n χ u *
      (((ρ : ℂ) ^ k) *
        fieldOnePadicPrimitiveUnitCharacter p n χ v)
  rw [fieldOnePadicPrimitiveUnitCharacter_mul]
  ring

theorem fieldOnePadicCriticalHalfDensity_unit_mul
    (u : ℤ_[p]ˣ) (a : ℚ_[p]ˣ) :
    fieldOnePadicCriticalHalfDensity p
        (fieldOnePadicUnitEmbedding p u * a) =
      fieldOnePadicCriticalHalfDensity p a := by
  let z : Multiplicative ℤ × ℤ_[p]ˣ :=
    (fieldOnePadicValuationUnitContinuousMulEquiv p).symm a
  let k : ℤ := Multiplicative.toAdd z.1
  let v : ℤ_[p]ˣ := z.2
  have ha : fieldOnePadicValuationUnitContinuousMulEquiv p
      (Multiplicative.ofAdd k, v) = a := by
    simp [k, v, z]
  rw [← ha, fieldOnePadicUnitEmbedding_mul_coordinates,
    fieldOnePadicCriticalHalfDensity_coordinates,
    fieldOnePadicCriticalHalfDensity_coordinates]

theorem fieldOnePadicUnitEmbedding_distribHaarChar
    (u : ℤ_[p]ˣ) :
    distribHaarChar ℚ_[p] (fieldOnePadicUnitEmbedding p u) = 1 := by
  rw [fieldOnePadicUnits_distribHaarChar_eq_nnnorm]
  apply NNReal.eq
  simp only [NNReal.coe_one, coe_nnnorm,
    fieldOnePadicUnitEmbedding_val]
  exact PadicInt.norm_units u

theorem fieldOnePadicCriticalTateLinear_dilation_unit
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (u : ℤ_[p]ˣ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicCriticalTateLinear p n χ ρ
        (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f) =
      (fieldOnePadicPrimitiveUnitCharacter p n χ u)⁻¹ *
        fieldOnePadicCriticalTateLinear p n χ ρ f := by
  let b := fieldOnePadicUnitEmbedding p u
  let c := fieldOnePadicPrimitiveUnitCharacter p n χ u
  let G : ℚ_[p]ˣ → ℂ := fieldOnePadicCriticalTateIntegrand p n χ ρ f
  have hc : c ≠ 0 :=
    fieldOnePadicPrimitiveUnitCharacter_ne_zero p n χ u
  have hpoint : (fun a : ℚ_[p]ˣ =>
      fieldOnePadicCriticalTateIntegrand p n χ ρ
        (fieldOnePadicBruhatDilation p b f) a) =
      fun a => c⁻¹ * G (b * a) := by
    funext a
    unfold G fieldOnePadicCriticalTateIntegrand
    rw [fieldOnePadicBruhatDilation_apply,
      fieldOnePadicRamifiedCriticalCharacter_unit_mul,
      fieldOnePadicCriticalHalfDensity_unit_mul]
    dsimp only [b, c]
    rw [Units.val_mul]
    calc
      f.1 (((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p]) *
            (a : ℚ_[p])) *
            fieldOnePadicRamifiedCriticalCharacter p n χ ρ a *
            fieldOnePadicCriticalHalfDensity p a =
          c⁻¹ * c *
            (f.1 (((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p]) *
              (a : ℚ_[p])) *
              fieldOnePadicRamifiedCriticalCharacter p n χ ρ a *
              fieldOnePadicCriticalHalfDensity p a) := by
                rw [inv_mul_cancel₀ hc, one_mul]
      _ = _ := by ring
  change (∫ a, fieldOnePadicCriticalTateIntegrand p n χ ρ
      (fieldOnePadicBruhatDilation p b f) a
      ∂fieldOnePadicMultiplicativeHaar p) = _
  rw [hpoint, integral_const_mul,
    integral_mul_left_eq_self G b]
  rfl

theorem fieldOnePadicDualCriticalTateLinear_dilation_unit
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (u : ℤ_[p]ˣ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicDualCriticalTateLinear p n χ ρ
        (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f) =
      fieldOnePadicPrimitiveUnitCharacter p n χ u *
        fieldOnePadicDualCriticalTateLinear p n χ ρ f := by
  let b := fieldOnePadicUnitEmbedding p u
  let c := fieldOnePadicPrimitiveUnitCharacter p n χ u
  let G : ℚ_[p]ˣ → ℂ := fieldOnePadicDualCriticalTateIntegrand p n χ ρ f
  have hc : c ≠ 0 :=
    fieldOnePadicPrimitiveUnitCharacter_ne_zero p n χ u
  have hpoint : (fun a : ℚ_[p]ˣ =>
      fieldOnePadicDualCriticalTateIntegrand p n χ ρ
        (fieldOnePadicBruhatDilation p b f) a) =
      fun a => c * G (b * a) := by
    funext a
    unfold G fieldOnePadicDualCriticalTateIntegrand
    rw [fieldOnePadicBruhatDilation_apply,
      fieldOnePadicRamifiedCriticalCharacter_unit_mul,
      fieldOnePadicCriticalHalfDensity_unit_mul]
    dsimp only [b, c]
    rw [Units.val_mul]
    have hcinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
    calc
      f.1 (((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p]) *
            (a : ℚ_[p])) *
            (fieldOnePadicRamifiedCriticalCharacter p n χ ρ a)⁻¹ *
            fieldOnePadicCriticalHalfDensity p a =
          c * c⁻¹ *
            (f.1 (((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p]) *
              (a : ℚ_[p])) *
              (fieldOnePadicRamifiedCriticalCharacter p n χ ρ a)⁻¹ *
              fieldOnePadicCriticalHalfDensity p a) := by
                rw [mul_inv_cancel₀ hc, one_mul]
      _ = c *
          (f.1 (((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p]) *
              (a : ℚ_[p])) *
            (c * fieldOnePadicRamifiedCriticalCharacter p n χ ρ a)⁻¹ *
            fieldOnePadicCriticalHalfDensity p a) := by
              rw [mul_inv_rev]
              ring
  change (∫ a, fieldOnePadicDualCriticalTateIntegrand p n χ ρ
      (fieldOnePadicBruhatDilation p b f) a
      ∂fieldOnePadicMultiplicativeHaar p) = _
  rw [hpoint, integral_const_mul,
    integral_mul_left_eq_self G b]
  rfl

@[simp] theorem fieldOnePadicUnitEmbedding_inv (u : ℤ_[p]ˣ) :
    fieldOnePadicUnitEmbedding p u⁻¹ =
      (fieldOnePadicUnitEmbedding p u)⁻¹ := by
  change fieldOnePadicValuationUnitContinuousMulEquiv p
      (Multiplicative.ofAdd 0, u⁻¹) =
    (fieldOnePadicValuationUnitContinuousMulEquiv p
      (Multiplicative.ofAdd 0, u))⁻¹
  rw [← map_inv]
  congr 1

theorem fieldOnePadicBruhatFourierLinear_dilation_unit
    (u : ℤ_[p]ˣ) (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicBruhatFourierLinear p
        (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f) =
      fieldOnePadicBruhatDilation p
        (fieldOnePadicUnitEmbedding p u⁻¹)
        (fieldOnePadicBruhatFourierLinear p f) := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  change fieldOnePadicBruhatFourier p
      (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f) y =
    fieldOnePadicBruhatFourier p f
      (((fieldOnePadicUnitEmbedding p u⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * y)
  rw [fieldOnePadicBruhatFourier_dilation,
    fieldOnePadicUnitEmbedding_distribHaarChar,
    fieldOnePadicUnitEmbedding_inv]
  simp

theorem fieldOnePadicDualCriticalTateFourierLinear_dilation_unit
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (u : ℤ_[p]ˣ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicDualCriticalTateLinear p n χ ρ
        (fieldOnePadicBruhatFourierLinear p
          (fieldOnePadicBruhatDilation p
            (fieldOnePadicUnitEmbedding p u) f)) =
      (fieldOnePadicPrimitiveUnitCharacter p n χ u)⁻¹ *
        fieldOnePadicDualCriticalTateLinear p n χ ρ
          (fieldOnePadicBruhatFourierLinear p f) := by
  rw [fieldOnePadicBruhatFourierLinear_dilation_unit,
    fieldOnePadicDualCriticalTateLinear_dilation_unit,
    fieldOnePadicPrimitiveUnitCharacter_inv]

theorem fieldOnePadicRamifiedTateDefectLinear_dilation_unit
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (u : ℤ_[p]ˣ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicRamifiedTateDefectLinear p n χ ρ
        (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f) =
      (fieldOnePadicPrimitiveUnitCharacter p n χ u)⁻¹ *
        fieldOnePadicRamifiedTateDefectLinear p n χ ρ f := by
  unfold fieldOnePadicRamifiedTateDefectLinear
  change fieldOnePadicDualCriticalTateLinear p n χ ρ
        (fieldOnePadicBruhatFourierLinear p
          (fieldOnePadicBruhatDilation p
            (fieldOnePadicUnitEmbedding p u) f)) -
      fieldOnePadicRamifiedTatePhase p n χ ρ *
        fieldOnePadicCriticalTateLinear p n χ ρ
          (fieldOnePadicBruhatDilation p
            (fieldOnePadicUnitEmbedding p u) f) =
      (fieldOnePadicPrimitiveUnitCharacter p n χ u)⁻¹ *
        (fieldOnePadicDualCriticalTateLinear p n χ ρ
            (fieldOnePadicBruhatFourierLinear p f) -
          fieldOnePadicRamifiedTatePhase p n χ ρ *
            fieldOnePadicCriticalTateLinear p n χ ρ f)
  rw [fieldOnePadicDualCriticalTateFourierLinear_dilation_unit,
    fieldOnePadicCriticalTateLinear_dilation_unit]
  ring

theorem fieldOnePadicRamifiedTateDefectLinear_projection_eq
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (ρ : Circle) (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicRamifiedTateDefectLinear p n χ ρ
        (fieldOnePadicPrimitiveAngularProjection p n χ f) =
      fieldOnePadicRamifiedTateDefectLinear p n χ ρ f := by
  classical
  obtain ⟨N, L, hsupport, hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  rw [fieldOnePadicPrimitiveAngularProjection_eq_finiteAverage_of_finiteLevel
    p n N L χ f hsupport hperiod]
  unfold fieldOnePadicPrimitiveAngularFiniteAverage
  rw [map_sum]
  simp_rw [map_smul,
    fieldOnePadicRamifiedTateDefectLinear_dilation_unit]
  let C : ℂ :=
    ((Fintype.card (ZMod (p ^ (n + N + L)))ˣ : ℕ) : ℂ)
  have hC : C ≠ 0 := by
    dsimp only [C]
    exact_mod_cast Fintype.card_ne_zero
  have hterm : ∀ r : (ZMod (p ^ (n + N + L)))ˣ,
      (C⁻¹ * fieldOnePadicPrimitiveUnitCharacter p n χ
          (fieldOnePadicUnitResidueRep p (n + N + L) r)) *
        ((fieldOnePadicPrimitiveUnitCharacter p n χ
            (fieldOnePadicUnitResidueRep p (n + N + L) r))⁻¹ *
          fieldOnePadicRamifiedTateDefectLinear p n χ ρ f) =
      C⁻¹ * fieldOnePadicRamifiedTateDefectLinear p n χ ρ f := by
    intro r
    have hc := fieldOnePadicPrimitiveUnitCharacter_ne_zero p n χ
      (fieldOnePadicUnitResidueRep p (n + N + L) r)
    calc
      (C⁻¹ * fieldOnePadicPrimitiveUnitCharacter p n χ
          (fieldOnePadicUnitResidueRep p (n + N + L) r)) *
          ((fieldOnePadicPrimitiveUnitCharacter p n χ
              (fieldOnePadicUnitResidueRep p (n + N + L) r))⁻¹ *
            fieldOnePadicRamifiedTateDefectLinear p n χ ρ f) =
        C⁻¹ *
          (fieldOnePadicPrimitiveUnitCharacter p n χ
              (fieldOnePadicUnitResidueRep p (n + N + L) r) *
            (fieldOnePadicPrimitiveUnitCharacter p n χ
              (fieldOnePadicUnitResidueRep p (n + N + L) r))⁻¹) *
          fieldOnePadicRamifiedTateDefectLinear p n χ ρ f := by ring
      _ = _ := by rw [mul_inv_cancel₀ hc, mul_one]
  change (∑ r : (ZMod (p ^ (n + N + L)))ˣ,
      (C⁻¹ * fieldOnePadicPrimitiveUnitCharacter p n χ
          (fieldOnePadicUnitResidueRep p (n + N + L) r)) *
        ((fieldOnePadicPrimitiveUnitCharacter p n χ
            (fieldOnePadicUnitResidueRep p (n + N + L) r))⁻¹ *
          fieldOnePadicRamifiedTateDefectLinear p n χ ρ f)) = _
  simp_rw [hterm]
  rw [Finset.sum_const, nsmul_eq_mul]
  change C * (C⁻¹ *
    fieldOnePadicRamifiedTateDefectLinear p n χ ρ f) = _
  rw [← mul_assoc, mul_inv_cancel₀ hC, one_mul]

theorem fieldOnePadicRamifiedTateDefectLinear_eq_zero
    (n : ℕ+) (χ : FieldOnePadicPrimitiveAngularCharacter p (n : ℕ))
    (ρ : Circle) (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicRamifiedTateDefectLinear p (n : ℕ) χ ρ f = 0 := by
  obtain ⟨c, hc⟩ :=
    fieldOnePadicPrimitiveAngularProjection_exists_radialPacketInvSynthesis
      p n χ f
  rw [← fieldOnePadicRamifiedTateDefectLinear_projection_eq
    p (n : ℕ) χ ρ f, hc]
  exact fieldOnePadicRamifiedTateDefectLinear_synthesis p n χ ρ c

/-- Literal positive-conductor local Tate equation (2.258) for every p-adic
Bruhat test. Positive conductor and primitivity are encoded in the input
types; no local functional equation is assumed. -/
theorem fieldOnePadicRamifiedTateEquation258
    (n : ℕ+) (χ : FieldOnePadicPrimitiveAngularCharacter p (n : ℕ))
    (ρ : Circle) (f : compactlySupportedLocallyConstant ℚ_[p]) :
    (∫ a : ℚ_[p]ˣ,
        fieldOnePadicBruhatFourier p f (a : ℚ_[p]) *
          (fieldOnePadicRamifiedCriticalCharacter p (n : ℕ) χ ρ a)⁻¹ *
          (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)
        ∂fieldOnePadicMultiplicativeHaar p) =
      fieldOnePadicRamifiedTatePhase p (n : ℕ) χ ρ *
        (∫ a : ℚ_[p]ˣ,
          f.1 (a : ℚ_[p]) *
            fieldOnePadicRamifiedCriticalCharacter p (n : ℕ) χ ρ a *
            (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)
          ∂fieldOnePadicMultiplicativeHaar p) := by
  have hzero := fieldOnePadicRamifiedTateDefectLinear_eq_zero p n χ ρ f
  unfold fieldOnePadicRamifiedTateDefectLinear at hzero
  change fieldOnePadicDualCriticalTateLinear p (n : ℕ) χ ρ
        (fieldOnePadicBruhatFourierLinear p f) -
      fieldOnePadicRamifiedTatePhase p (n : ℕ) χ ρ *
        fieldOnePadicCriticalTateLinear p (n : ℕ) χ ρ f = 0 at hzero
  have heq := sub_eq_zero.mp hzero
  have hdual : (fun a : ℚ_[p]ˣ =>
        fieldOnePadicBruhatFourier p f (a : ℚ_[p]) *
          (fieldOnePadicRamifiedCriticalCharacter p (n : ℕ) χ ρ a)⁻¹ *
          (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)) =
      fieldOnePadicDualCriticalTateIntegrand p (n : ℕ) χ ρ
        (fieldOnePadicBruhatFourier p f) := by
    funext a
    unfold fieldOnePadicDualCriticalTateIntegrand
    rw [fieldOnePadicCriticalHalfDensity_eq_sqrt_norm]
  have hprimal : (fun a : ℚ_[p]ˣ =>
        f.1 (a : ℚ_[p]) *
          fieldOnePadicRamifiedCriticalCharacter p (n : ℕ) χ ρ a *
          (Real.sqrt ‖(a : ℚ_[p])‖ : ℂ)) =
      fieldOnePadicCriticalTateIntegrand p (n : ℕ) χ ρ f := by
    funext a
    unfold fieldOnePadicCriticalTateIntegrand
    rw [fieldOnePadicCriticalHalfDensity_eq_sqrt_norm]
  rw [hdual, hprimal]
  exact heq

end
end GaloisForLFunctions.RHTower
