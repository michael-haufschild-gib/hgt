import GaloisForLFunctions.HTGeometry.PaperRealMultiplierResolvent
import GaloisForLFunctions.RHTower.WeightOneCliffordSpectralNoGo

/-!
# Squared Clifford mass is visible modulo compact operators

The actual maximal Clifford-square resolvent belongs to the modulation commutant.
Its resolvent identity makes squared mass recoverable from the operator, hence also from
its compact quotient. The TraceCone compact-ideal cost of a difference is zero exactly
when the squared masses agree, and infinite otherwise.
-/

namespace RHTower

noncomputable section
open MeasureTheory Complex Classical
open GaloisForLFunctions.HTGeometry
open scoped ENNReal

/-- The native maximal Clifford-square resolvent at `i`. -/
def paperWeightOneResolvent (a : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  resolventCLM (weightOneSpectralSquare_isSelfAdjoint a) (z := I) (by simp)

theorem paperWeightOneResolvent_apply_ae (a : ℝ) (f : SoninL2) :
    (paperWeightOneResolvent a f : ℝ → ℂ) =ᵐ[volume]
      fun x => ((weightOneSpectralSquareEnergy a x : ℂ) - I)⁻¹ * f x :=
  maximalRealL2Mul_resolvent_apply_ae volume
    (measurable_weightOneSpectralSquareEnergy a) (by simp) f

theorem paperWeightOneResolvent_mem_commutant (a : ℝ) :
    paperWeightOneResolvent a ∈ paperModulationCommutant :=
  maximalRealL2Mul_resolvent_mem_commutant
    (measurable_weightOneSpectralSquareEnergy a) (by simp)

/-- The full native resolvent norm survives in the compact quotient. -/
theorem paperWeightOneResolvent_compactIdealDistance (a : ℝ) :
    compactIdealDistance (paperWeightOneResolvent a) = ‖paperWeightOneResolvent a‖ :=
  paperModulationCommutant_compactIdealDistance
    ⟨_, paperWeightOneResolvent_mem_commutant a⟩

/-- Every distance between two actual Clifford-square resolvents survives unchanged. -/
theorem paperWeightOneResolvent_compactIdealDistance_sub (a b : ℝ) :
    compactIdealDistance (paperWeightOneResolvent a - paperWeightOneResolvent b) =
      ‖paperWeightOneResolvent a - paperWeightOneResolvent b‖ := by
  let A : paperModulationCommutant := ⟨_, paperWeightOneResolvent_mem_commutant a⟩
  let B : paperModulationCommutant := ⟨_, paperWeightOneResolvent_mem_commutant b⟩
  exact paperModulationCommutant_compactIdealDistance (A - B)

theorem paperWeightOneResolvent_injective (a : ℝ) :
    Function.Injective (paperWeightOneResolvent a) :=
  resolventCLM_injective (weightOneSpectralSquare_isSelfAdjoint a) (by simp)

/-- The exact second resolvent identity for the native squared-mass shift. -/
theorem paperWeightOneResolvent_sub (a b : ℝ) :
    paperWeightOneResolvent a - paperWeightOneResolvent b =
      ((b^2 - a^2 : ℝ) : ℂ) • (paperWeightOneResolvent a * paperWeightOneResolvent b) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (paperWeightOneResolvent a f) (paperWeightOneResolvent b f),
    paperWeightOneResolvent_apply_ae a f, paperWeightOneResolvent_apply_ae b f,
    Lp.coeFn_smul ((b^2 - a^2 : ℝ) : ℂ)
      (paperWeightOneResolvent a (paperWeightOneResolvent b f)),
    paperWeightOneResolvent_apply_ae a (paperWeightOneResolvent b f)]
    with x hsub ha hb hsmul hab
  change (paperWeightOneResolvent a f - paperWeightOneResolvent b f) x =
    (((b^2 - a^2 : ℝ) : ℂ) •
      (paperWeightOneResolvent a (paperWeightOneResolvent b f))) x
  rw [hsub, hsmul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha, hb, hab, hb]
  have hEa := realEnergy_sub_nonreal_ne_zero (weightOneSpectralSquareEnergy a x)
    (z := I) (by simp)
  have hEb := realEnergy_sub_nonreal_ne_zero (weightOneSpectralSquareEnergy b x)
    (z := I) (by simp)
  have he : ((weightOneSpectralSquareEnergy b x : ℂ) - I) -
      ((weightOneSpectralSquareEnergy a x : ℂ) - I) = ((b^2-a^2 : ℝ) : ℂ) := by
    simp only [weightOneSpectralSquareEnergy]
    push_cast
    ring
  rw [← sub_mul, inv_sub_inv hEa hEb, he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Two resolvents coincide precisely when their squared masses coincide. -/
theorem paperWeightOneResolvent_eq_iff (a b : ℝ) :
    paperWeightOneResolvent a = paperWeightOneResolvent b ↔ a^2 = b^2 := by
  have hprod : paperWeightOneResolvent a * paperWeightOneResolvent b ≠ 0 := by
    intro h
    obtain ⟨f, hf⟩ := exists_ne (0 : SoninL2)
    apply hf
    apply paperWeightOneResolvent_injective b
    apply paperWeightOneResolvent_injective a
    have he := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f) h
    simpa only [mul_apply_eq_comp, map_zero, zero_apply] using he
  rw [← sub_eq_zero, paperWeightOneResolvent_sub, smul_eq_zero]
  simp only [hprod, or_false, Complex.ofReal_eq_zero, sub_eq_zero]
  exact eq_comm

/-- Compact equivalence recovers the exact squared mass. -/
theorem paperWeightOneResolvent_compact_sub_iff (a b : ℝ) :
    IsCompactOperator (paperWeightOneResolvent a - paperWeightOneResolvent b) ↔ a^2 = b^2 := by
  have h : IsCompactOperator (paperWeightOneResolvent a - paperWeightOneResolvent b) ↔
      paperWeightOneResolvent a = paperWeightOneResolvent b :=
    (paperModulationCommutant_compact_sub_iff_eq
      ⟨_, paperWeightOneResolvent_mem_commutant a⟩
      ⟨_, paperWeightOneResolvent_mem_commutant b⟩).trans Subtype.ext_iff
  exact h.trans (paperWeightOneResolvent_eq_iff a b)

/-- The paper's extended ideal cost distinguishes all unequal squared masses. -/
theorem paperWeightOneResolvent_difference_traceCost (a b : ℝ) :
    compactOperatorTraceCost SoninL2 (paperWeightOneResolvent a - paperWeightOneResolvent b) =
      if a^2 = b^2 then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperWeightOneResolvent_compact_sub_iff]

/-- Finite paper ideal cost forces exact squared-mass agreement. -/
theorem paperWeightOneResolvent_difference_traceCost_lt_top_iff (a b : ℝ) :
    compactOperatorTraceCost SoninL2
      (paperWeightOneResolvent a - paperWeightOneResolvent b) < ∞ ↔ a^2 = b^2 := by
  rw [compactOperatorTraceCost_lt_top_iff, paperWeightOneResolvent_compact_sub_iff]

/-- Every actual resolvent has infinite compact-ideal cost. -/
theorem paperWeightOneResolvent_traceCost (a : ℝ) :
    compactOperatorTraceCost SoninL2 (paperWeightOneResolvent a) = ∞ :=
  (compactOperatorTraceCost_eq_top_iff _).mpr (weightOneSpectralSquare_not_compactResolvent a)

/-- Arbitrary compact corrections preserve the squared-mass classification. -/
theorem paperWeightOneResolvent_difference_traceCost_add_compact (a b : ℝ)
    (K : compactOperatorStarAlgebra SoninL2) :
    compactOperatorTraceCost SoninL2
      (paperWeightOneResolvent a - paperWeightOneResolvent b + K.1) =
      if a^2 = b^2 then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperWeightOneResolvent_difference_traceCost]

end
end RHTower
