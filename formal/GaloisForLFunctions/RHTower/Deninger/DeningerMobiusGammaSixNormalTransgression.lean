import GaloisForLFunctions.RHTower.Deninger.DeningerSteinbergKummerSuccessorNormalTransgression

/-!
# Deninger--Möbius Gamma-six normal transgression

Constructs the finite-corrected ordinary-integer source whose first surviving label is six,
the exact spectral-normalized half-density transport at clock `6^m`, and an honest complementary
rational Steinberg cell.  A normalized cubic in the existing Kummer derivation extracts both
orientations `[6^m] - 1` and `[6^(-m)] - 1`.  Their difference has regulator `2m log 6`, admits
two strict Tate interval primitives, maps to the physical Gamma-six transport under the canonical
rational-adelic representation, and defines a non-boundary multiplier K1 class.

The complete analytic source statements begin at the unconditional summability depth `m ≥ 3`;
all algebraic statements hold at every positive depth.  No Xi zero, RH predicate, quotient
annihilation, or additional axiom is used.
-/

open Complex
open GaloisForLFunctions.RHTower
open Filter MeasureTheory

namespace RHTower

noncomputable section

def deningerGammaSixBaseScaling : CCMRationalAdelicScaling :=
  deningerScalingOfPositiveRational 6 (by norm_num)

def deningerGammaSixScaling (m : DeningerSteinbergDepth) :
    CCMRationalAdelicScaling := deningerGammaSixBaseScaling ^ (m : ℕ)

theorem deningerScalingAbsoluteValue_gammaSix
    (m : DeningerSteinbergDepth) :
    deningerScalingAbsoluteValue (deningerGammaSixScaling m) =
      (6 : ℝ) ^ (m : ℕ) := by
  rw [deningerGammaSixScaling]
  induction (m : ℕ) with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, deningerScalingAbsoluteValue_mul, ih]
      congr 1
      norm_num [deningerGammaSixBaseScaling,
        deningerScalingAbsoluteValue, deningerScalingOfPositiveRational]

def deningerGammaSixNormalCLM (m : DeningerSteinbergDepth) :
    MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2 :=
  deningerHalfDensityRepresentation
    (deningerSteinbergBasis (deningerGammaSixScaling m))

def deningerGammaSixNormalInvCLM (m : DeningerSteinbergDepth) :
    MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2 :=
  deningerHalfDensityRepresentation
    (deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹)

theorem deningerGammaSixNormal_mul_inv (m : DeningerSteinbergDepth) :
    deningerGammaSixNormalCLM m * deningerGammaSixNormalInvCLM m =
      ContinuousLinearMap.id ℂ MobiusThetaSourceL2 := by
  rw [deningerGammaSixNormalCLM, deningerGammaSixNormalInvCLM]
  rw [← map_mul, ← deningerSteinbergBasis_mul, mul_inv_cancel,
    deningerSteinbergBasis_one, map_one]
  rfl

theorem deningerGammaSixNormal_inv_mul (m : DeningerSteinbergDepth) :
    deningerGammaSixNormalInvCLM m * deningerGammaSixNormalCLM m =
      ContinuousLinearMap.id ℂ MobiusThetaSourceL2 := by
  rw [deningerGammaSixNormalCLM, deningerGammaSixNormalInvCLM]
  rw [← map_mul, ← deningerSteinbergBasis_mul, inv_mul_cancel,
    deningerSteinbergBasis_one, map_one]
  rfl

@[simp] theorem deningerGammaSixNormalCLM_apply
    (m : DeningerSteinbergDepth) (f : MobiusThetaSourceL2) :
    deningerGammaSixNormalCLM m f =
      (((6 : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) •
        MellinL2.additiveTranslationUnitary
          (((m : ℝ) * Real.log 6) * MellinL2.spectralNormalization) f := by
  rw [deningerGammaSixNormalCLM,
    deningerHalfDensityRepresentation_basis,
    deningerHalfDensityScalingCLM_apply,
    deningerScalingAbsoluteValue_gammaSix]
  have hamp : (((6 : ℝ) ^ (m : ℕ)) ^ ((1 : ℝ) / 2)) =
      (6 : ℝ) ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 6)]
    congr 1
    ring
  have htime : Real.log ((6 : ℝ) ^ (m : ℕ)) * MellinL2.spectralNormalization =
      ((m : ℝ) * Real.log 6) * MellinL2.spectralNormalization := by
    rw [Real.log_pow]
  rw [hamp, htime]

def deningerGammaSixCompleteSource (m : MobiusHonestDepth) :
    MobiusThetaSourceL2 :=
  deningerGammaSixNormalInvCLM ⟨m, by omega⟩
    (mobiusThetaPrimeNormalResidual 6 m)

theorem deningerGammaSixNormal_completeSource (m : MobiusHonestDepth) :
    deningerGammaSixNormalCLM ⟨m, by omega⟩
        (deningerGammaSixCompleteSource m) =
      mobiusThetaPrimeNormalResidual 6 m := by
  rw [deningerGammaSixCompleteSource, ← mul_apply_eq_comp,
    deningerGammaSixNormal_mul_inv]
  rfl

theorem moebius_six : ArithmeticFunction.moebius 6 = 1 := by
  rw [show 6 = 2 * 3 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  norm_num

theorem tendsto_mobiusThetaPrimeNormalResidual_six :
    Tendsto (mobiusThetaPrimeNormalResidual 6) atTop (nhds xiThetaSourceL2) := by
  simpa [moebius_six] using
    (tendsto_mobiusThetaPrimeNormalResidual (p := 6) (by omega))

theorem norm_deningerGammaSixNormalInvCLM_apply
    (m : DeningerSteinbergDepth) (f : MobiusThetaSourceL2) :
    ‖deningerGammaSixNormalInvCLM m f‖ =
      (6 : ℝ) ^ (-((m : ℝ) / 2)) * ‖f‖ := by
  rw [deningerGammaSixNormalInvCLM,
    deningerHalfDensityRepresentation_basis,
    deningerHalfDensityScalingCLM_apply, norm_smul,
    LinearIsometryEquiv.norm_map, Complex.norm_real, Real.norm_eq_abs]
  have habs_inv : deningerScalingAbsoluteValue (deningerGammaSixScaling m)⁻¹ =
      ((6 : ℝ) ^ (m : ℕ))⁻¹ := by
    rw [deningerScalingAbsoluteValue]
    rw [ccmRationalAdelicScaling_inv_val]
    push_cast
    rw [abs_inv, ← deningerScalingAbsoluteValue,
      deningerScalingAbsoluteValue_gammaSix]
  rw [habs_inv, abs_of_pos (Real.rpow_pos_of_pos (inv_pos.mpr (by positivity)) _)]
  rw [← Real.rpow_neg_eq_inv_rpow]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
  congr 2
  ring

theorem tendsto_deningerGammaSixCompleteSource_zero :
    Tendsto (fun n : ℕ => deningerGammaSixCompleteSource ⟨n + 3, by omega⟩)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbdd : ∃ C : ℝ, ∀ m : ℕ, ‖mobiusThetaPrimeNormalResidual 6 (m + 3)‖ ≤ C := by
    obtain ⟨C, hC⟩ := tendsto_mobiusThetaPrimeNormalResidual_six.norm.bddAbove_range
    exact ⟨C, fun m => hC ⟨m + 3, rfl⟩⟩
  obtain ⟨C, hC⟩ := hbdd
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine squeeze_zero (g := fun m : ℕ =>
      (6 : ℝ) ^ (-(((m + 3 : ℕ) : ℝ) / 2)) * C)
    (fun m => norm_nonneg _) (fun m => ?_) ?_
  · rw [deningerGammaSixCompleteSource,
      norm_deningerGammaSixNormalInvCLM_apply]
    exact mul_le_mul_of_nonneg_left (hC m)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) _)
  · have hpow : Tendsto
        (fun m : ℕ => (6 : ℝ) ^ (-(((m + 3 : ℕ) : ℝ) / 2))) atTop (nhds 0) := by
      have hexp : Tendsto (fun m : ℕ => (((m + 3 : ℕ) : ℝ) / 2)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)).atTop_div_const
          (by norm_num)
      have hb := tendsto_rpow_atTop_of_base_lt_one ((6 : ℝ)⁻¹)
        (by norm_num) (by norm_num)
      convert hb.comp hexp using 1
      funext m
      change (6 : ℝ) ^ (-(((m + 3 : ℕ) : ℝ) / 2)) =
        (6 : ℝ)⁻¹ ^ (((m + 3 : ℕ) : ℝ) / 2)
      exact Real.rpow_neg_eq_inv_rpow _ _
    simpa using hpow.mul_const C

theorem tendsto_deningerGammaSixNormal_completeSource :
    Tendsto (fun m : ℕ => deningerGammaSixNormalCLM ⟨m + 3, by omega⟩
      (deningerGammaSixCompleteSource ⟨m + 3, by omega⟩)) atTop
      (nhds xiThetaSourceL2) := by
  have h := tendsto_mobiusThetaPrimeNormalResidual_six.comp (tendsto_add_atTop_nat 3)
  exact h.congr' (Filter.Eventually.of_forall fun m =>
    (deningerGammaSixNormal_completeSource ⟨m + 3, by omega⟩).symm)

theorem moebius_four : ArithmeticFunction.moebius 4 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  norm_num [Squarefree]
  exact ⟨2, by norm_num, by norm_num⟩

theorem mobiusThetaDirectDirichletTerm_four (m : ℕ) :
    mobiusThetaDirectDirichletTerm m 4 = 0 := by
  rw [mobiusThetaDirectDirichletTerm,
    LSeries.term_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0), moebius_four]
  simp

/-- Literal finite correction of the direct Möbius source through ordinary labels `2,3,5`. -/
def deningerGammaSixFiniteCorrectedSource (m : MobiusHonestDepth) :
    MobiusThetaSourceL2 :=
  mobiusThetaPrimeNormalResidual 1 m - xiThetaSourceL2 -
    mobiusThetaDirectDirichletTerm m 2 -
    mobiusThetaDirectDirichletTerm m 3 -
    mobiusThetaDirectDirichletTerm m 5

/-- Finite correction leaves exactly the complete ordinary-integer tail starting at six. -/
theorem deningerGammaSixFiniteCorrectedSource_eq_tail
    (m : MobiusHonestDepth) :
    deningerGammaSixFiniteCorrectedSource m =
      ∑' k : ℕ, mobiusThetaDirectDirichletTerm m (k + 6) := by
  rw [deningerGammaSixFiniteCorrectedSource,
    ← mobiusThetaDirectPhysicalRung,
    mobiusThetaDirectPhysicalRung_eq_tsum m.2]
  have hsplit := (summable_mobiusThetaDirectDirichletTerm m.2).sum_add_tsum_nat_add 6
  rw [← hsplit]
  have hfin :
      ∑ i ∈ Finset.range 6, mobiusThetaDirectDirichletTerm m i =
        xiThetaSourceL2 + mobiusThetaDirectDirichletTerm m 2 +
          mobiusThetaDirectDirichletTerm m 3 +
          mobiusThetaDirectDirichletTerm m 5 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, mobiusThetaDirectDirichletTerm_zero,
      mobiusThetaDirectDirichletTerm_one,
      mobiusThetaDirectDirichletTerm_four]
    abel
  rw [hfin]
  abel

theorem deningerGammaSixNormal_tail_head (m : DeningerSteinbergDepth) :
    deningerGammaSixNormalCLM m
        (mobiusThetaPrimeNormalTailTerm 1 m 4) = xiThetaSourceL2 := by
  rw [deningerGammaSixNormalCLM_apply,
    mobiusThetaPrimeNormalTailTerm, map_smul, smul_smul,
    additiveTranslationUnitary_add_apply]
  have htranslate :
      (m : ℝ) * Real.log 6 * MellinL2.spectralNormalization +
          -((m : ℝ) * Real.log (((1 + 4 + 1 : ℕ) : ℝ) / 1)) *
            MellinL2.spectralNormalization = 0 := by
    norm_num
  norm_num only [Nat.cast_ofNat, Nat.cast_one] at htranslate ⊢
  rw [htranslate, additiveTranslationUnitary_zero_apply]
  rw [mobiusThetaPrimeNormalWeight, moebius_six]
  norm_num only [Nat.cast_one, one_div]
  have hreal : (6 : ℝ) ^ ((m : ℝ) / 2) *
      (6 : ℝ)⁻¹ ^ ((m : ℝ) / 2) = 1 := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6)
      (by positivity : (0 : ℝ) ≤ (6 : ℝ)⁻¹)]
    norm_num
  push_cast
  norm_num only [one_mul]
  have hscalar :
      (↑((6 : ℝ) ^ ((m : ℝ) / 2)) : ℂ) *
          ↑(((1 : ℝ) / 6) ^ ((m : ℝ) / 2)) = 1 := by
    have hreal' : (6 : ℝ) ^ ((m : ℝ) / 2) *
        ((1 : ℝ) / 6) ^ ((m : ℝ) / 2) = 1 := by
      rw [one_div]
      exact hreal
    exact_mod_cast hreal'
  rw [hscalar, one_smul]

theorem deningerGammaSixNormal_tail_succ
    (m : DeningerSteinbergDepth) (k : ℕ) :
    deningerGammaSixNormalCLM m
        (mobiusThetaPrimeNormalTailTerm 1 m (k + 5)) =
      mobiusThetaPrimeNormalTailTerm 6 m k := by
  rw [deningerGammaSixNormalCLM_apply,
    mobiusThetaPrimeNormalTailTerm, map_smul, smul_smul,
    additiveTranslationUnitary_add_apply]
  have hindex : 1 + (k + 5) + 1 = 6 + k + 1 := by omega
  rw [hindex]
  have hn : (0 : ℝ) < (6 + k + 1 : ℕ) := by positivity
  have hcoeff :
      (6 : ℝ) ^ ((m : ℝ) / 2) *
          mobiusThetaPrimeNormalWeight 1 m (k + 5) =
        mobiusThetaPrimeNormalWeight 6 m k := by
    rw [mobiusThetaPrimeNormalWeight, mobiusThetaPrimeNormalWeight, hindex]
    norm_num only [Nat.cast_one, Nat.cast_ofNat]
    rw [show (6 : ℝ) / (6 + k + 1 : ℕ) =
        6 * ((1 : ℝ) / (6 + k + 1 : ℕ)) by field_simp]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by positivity)]
    ring
  have htranslate :
      (m : ℝ) * Real.log 6 * MellinL2.spectralNormalization +
          -((m : ℝ) * Real.log (((6 + k + 1 : ℕ) : ℝ) / 1)) *
            MellinL2.spectralNormalization =
        -((m : ℝ) * Real.log (((6 + k + 1 : ℕ) : ℝ) / 6)) *
          MellinL2.spectralNormalization := by
    rw [Real.log_div (ne_of_gt hn) (by norm_num : (1 : ℝ) ≠ 0),
      Real.log_div (ne_of_gt hn) (by norm_num : (6 : ℝ) ≠ 0)]
    norm_num
    ring
  congr 1
  · exact_mod_cast hcoeff
  · apply congrArg
      (fun t => MellinL2.additiveTranslationUnitary t xiThetaSourceL2)
    convert htranslate using 1 <;> norm_num

theorem deningerGammaSixNormal_direct_head (m : DeningerSteinbergDepth) :
    deningerGammaSixNormalCLM m
        (mobiusThetaDirectDirichletTerm m 6) = xiThetaSourceL2 := by
  rw [mobiusThetaDirectDirichletTerm_add_two m 4]
  exact deningerGammaSixNormal_tail_head m

theorem deningerGammaSixNormal_direct_succ
    (m : DeningerSteinbergDepth) (k : ℕ) :
    deningerGammaSixNormalCLM m
        (mobiusThetaDirectDirichletTerm m (k + 7)) =
      mobiusThetaPrimeNormalTailTerm 6 m k := by
  rw [show k + 7 = (k + 5) + 2 by omega,
    mobiusThetaDirectDirichletTerm_add_two]
  exact deningerGammaSixNormal_tail_succ m k

/-- The literal finite-corrected source is the inverse image of the complete six packet. -/
theorem deningerGammaSixFiniteCorrectedSource_eq_completeSource
    (m : MobiusHonestDepth) :
    deningerGammaSixFiniteCorrectedSource m = deningerGammaSixCompleteSource m := by
  have htransport : deningerGammaSixNormalCLM ⟨m, by omega⟩
        (deningerGammaSixFiniteCorrectedSource m) =
      mobiusThetaPrimeNormalResidual 6 m := by
    rw [
      deningerGammaSixFiniteCorrectedSource_eq_tail]
    have hs : Summable
        (fun k : ℕ => mobiusThetaDirectDirichletTerm m (k + 6)) :=
      (summable_mobiusThetaDirectDirichletTerm m.2).comp_injective
        (fun _ _ h => by omega)
    rw [ContinuousLinearMap.map_tsum _ hs]
    have hsmap := hs.mapL (deningerGammaSixNormalCLM ⟨m, by omega⟩)
    have hsplit := hsmap.sum_add_tsum_nat_add 1
    rw [← hsplit]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      deningerGammaSixNormal_direct_head,
      deningerGammaSixNormal_direct_succ]
    rw [mobiusThetaPrimeNormalResidual, moebius_six]
    norm_num
  calc
    deningerGammaSixFiniteCorrectedSource m =
        deningerGammaSixNormalInvCLM ⟨m, by omega⟩
          (deningerGammaSixNormalCLM ⟨m, by omega⟩
            (deningerGammaSixFiniteCorrectedSource m)) := by
          rw [← mul_apply_eq_comp, deningerGammaSixNormal_inv_mul]
          rfl
    _ = deningerGammaSixNormalInvCLM ⟨m, by omega⟩
          (mobiusThetaPrimeNormalResidual 6 m) := congrArg _ htransport
    _ = deningerGammaSixCompleteSource m := rfl

/-- Exact finite-corrected complete-tail transport at the physical Gamma clock. -/
theorem deningerGammaSixNormal_finiteCorrectedSource (m : MobiusHonestDepth) :
    deningerGammaSixNormalCLM ⟨m, by omega⟩
        (deningerGammaSixFiniteCorrectedSource m) =
      mobiusThetaPrimeNormalResidual 6 m := by
  rw [deningerGammaSixFiniteCorrectedSource_eq_completeSource,
    deningerGammaSixNormal_completeSource]

/-! ## Honest Gamma-six Steinberg cell and cubic Kummer selector -/

def deningerGammaSixCoefficient (m : DeningerSteinbergDepth) : ℚ :=
  6 ^ (m : ℕ)

def deningerGammaSixDenominator (m : DeningerSteinbergDepth) : ℚ :=
  deningerGammaSixCoefficient m + 1

def deningerGammaSixX (m : DeningerSteinbergDepth) : ℚ :=
  deningerGammaSixCoefficient m / deningerGammaSixDenominator m

def deningerGammaSixY (m : DeningerSteinbergDepth) : ℚ :=
  1 / deningerGammaSixDenominator m

theorem deningerGammaSixCoefficient_one_lt (m : DeningerSteinbergDepth) :
    1 < deningerGammaSixCoefficient m := by
  unfold deningerGammaSixCoefficient
  exact_mod_cast Nat.one_lt_pow (by omega : (m : ℕ) ≠ 0) (by norm_num : 1 < 6)

theorem deningerGammaSixDenominator_pos (m : DeningerSteinbergDepth) :
    0 < deningerGammaSixDenominator m := by
  unfold deningerGammaSixDenominator deningerGammaSixCoefficient
  positivity

theorem deningerGammaSixX_pos (m : DeningerSteinbergDepth) :
    0 < deningerGammaSixX m := by
  exact div_pos (lt_trans (by norm_num) (deningerGammaSixCoefficient_one_lt m))
    (deningerGammaSixDenominator_pos m)

theorem deningerGammaSixY_pos (m : DeningerSteinbergDepth) :
    0 < deningerGammaSixY m := by
  exact div_pos (by norm_num) (deningerGammaSixDenominator_pos m)

theorem deningerGammaSixX_add_Y (m : DeningerSteinbergDepth) :
    deningerGammaSixX m + deningerGammaSixY m = 1 := by
  rw [deningerGammaSixX, deningerGammaSixY]
  field_simp [deningerGammaSixDenominator_pos m |>.ne']
  unfold deningerGammaSixDenominator
  ring

theorem deningerGammaSixY_lt_X (m : DeningerSteinbergDepth) :
    deningerGammaSixY m < deningerGammaSixX m := by
  rw [deningerGammaSixX, deningerGammaSixY]
  exact div_lt_div_of_pos_right (deningerGammaSixCoefficient_one_lt m)
    (deningerGammaSixDenominator_pos m)

theorem deningerGammaSixX_lt_one (m : DeningerSteinbergDepth) :
    deningerGammaSixX m < 1 := by
  nlinarith [deningerGammaSixY_pos m, deningerGammaSixX_add_Y m]

theorem deningerGammaSixY_lt_one (m : DeningerSteinbergDepth) :
    deningerGammaSixY m < 1 := by
  nlinarith [deningerGammaSixX_pos m, deningerGammaSixX_add_Y m]

theorem deningerGammaSixX_div_Y (m : DeningerSteinbergDepth) :
    deningerGammaSixX m / deningerGammaSixY m = deningerGammaSixCoefficient m := by
  rw [deningerGammaSixX, deningerGammaSixY]
  have hden : deningerGammaSixDenominator m ≠ 0 :=
    ne_of_gt (deningerGammaSixDenominator_pos m)
  field_simp [hden]

def deningerGammaSixXScaling (m : DeningerSteinbergDepth) :
    CCMRationalAdelicScaling :=
  deningerScalingOfPositiveRational (deningerGammaSixX m) (deningerGammaSixX_pos m)

def deningerGammaSixYScaling (m : DeningerSteinbergDepth) :
    CCMRationalAdelicScaling :=
  deningerScalingOfPositiveRational (deningerGammaSixY m) (deningerGammaSixY_pos m)

def deningerGammaSixSteinbergCell (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing :=
  (deningerSteinbergBasis (deningerGammaSixXScaling m) - 1) *
    (deningerSteinbergBasis (deningerGammaSixYScaling m) - 1)

def deningerGammaSixA (m : DeningerSteinbergDepth) : ℂ :=
  (Real.log (deningerGammaSixX m : ℝ) : ℂ)

def deningerGammaSixB (m : DeningerSteinbergDepth) : ℂ :=
  (Real.log (deningerGammaSixY m : ℝ) : ℂ)

def deningerGammaSixL (m : DeningerSteinbergDepth) : ℂ :=
  deningerGammaSixA m + deningerGammaSixB m

def deningerGammaSixSelectorDenominator (m : DeningerSteinbergDepth) : ℂ :=
  deningerGammaSixA m * deningerGammaSixB m *
    (deningerGammaSixA m - deningerGammaSixB m)

def deningerGammaSixSelectorScalar (m : DeningerSteinbergDepth) (t : ℂ) : ℂ :=
  t * (t - deningerGammaSixL m) * (2 * t - deningerGammaSixL m) /
    deningerGammaSixSelectorDenominator m

theorem deningerGammaSixA_ne_zero (m : DeningerSteinbergDepth) :
    deningerGammaSixA m ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast deningerGammaSixX_pos m)
      (by exact_mod_cast ne_of_lt (deningerGammaSixX_lt_one m)))

theorem deningerGammaSixB_ne_zero (m : DeningerSteinbergDepth) :
    deningerGammaSixB m ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast deningerGammaSixY_pos m)
      (by exact_mod_cast ne_of_lt (deningerGammaSixY_lt_one m)))

theorem deningerGammaSixA_sub_B_ne_zero (m : DeningerSteinbergDepth) :
    deningerGammaSixA m - deningerGammaSixB m ≠ 0 := by
  apply sub_ne_zero.mpr
  have hlt : Real.log (deningerGammaSixY m : ℝ) <
      Real.log (deningerGammaSixX m : ℝ) :=
    Real.strictMonoOn_log
      (by show (0 : ℝ) < (deningerGammaSixY m : ℝ)
          exact_mod_cast deningerGammaSixY_pos m)
      (by show (0 : ℝ) < (deningerGammaSixX m : ℝ)
          exact_mod_cast deningerGammaSixX_pos m)
      (by exact_mod_cast deningerGammaSixY_lt_X m)
  intro h
  apply hlt.ne
  exact Complex.ofReal_injective (by simpa [deningerGammaSixA,
    deningerGammaSixB] using h.symm)

theorem deningerGammaSixSelectorDenominator_ne_zero
    (m : DeningerSteinbergDepth) :
    deningerGammaSixSelectorDenominator m ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (deningerGammaSixA_ne_zero m)
    (deningerGammaSixB_ne_zero m)) (deningerGammaSixA_sub_B_ne_zero m)

@[simp] theorem deningerGammaSixSelectorScalar_zero (m : DeningerSteinbergDepth) :
    deningerGammaSixSelectorScalar m 0 = 0 := by
  simp [deningerGammaSixSelectorScalar]

@[simp] theorem deningerGammaSixSelectorScalar_L (m : DeningerSteinbergDepth) :
    deningerGammaSixSelectorScalar m (deningerGammaSixL m) = 0 := by
  simp [deningerGammaSixSelectorScalar]

@[simp] theorem deningerGammaSixSelectorScalar_A (m : DeningerSteinbergDepth) :
    deningerGammaSixSelectorScalar m (deningerGammaSixA m) = -1 := by
  rw [deningerGammaSixSelectorScalar, deningerGammaSixL]
  field_simp [deningerGammaSixSelectorDenominator_ne_zero m]
  unfold deningerGammaSixSelectorDenominator
  ring

@[simp] theorem deningerGammaSixSelectorScalar_B (m : DeningerSteinbergDepth) :
    deningerGammaSixSelectorScalar m (deningerGammaSixB m) = 1 := by
  rw [deningerGammaSixSelectorScalar, deningerGammaSixL]
  field_simp [deningerGammaSixSelectorDenominator_ne_zero m]
  unfold deningerGammaSixSelectorDenominator
  ring

theorem deningerGammaSixSelectorScalar_cubic
    (m : DeningerSteinbergDepth) (t : ℂ) :
    deningerGammaSixSelectorScalar m t =
      (deningerGammaSixSelectorDenominator m)⁻¹ *
        (2 * t ^ 3 - (3 * deningerGammaSixL m) * t ^ 2 +
          (deningerGammaSixL m) ^ 2 * t) := by
  rw [deningerGammaSixSelectorScalar]
  field_simp [deningerGammaSixSelectorDenominator_ne_zero m]
  ring

@[simp] theorem deningerGammaSixKummerWeight_X (m : DeningerSteinbergDepth) :
    ccmRationalAdelicKummerLogWeight (deningerGammaSixXScaling m) =
      deningerGammaSixA m :=
  deningerKummerLogWeight_positiveRational _ _

@[simp] theorem deningerGammaSixKummerWeight_Y (m : DeningerSteinbergDepth) :
    ccmRationalAdelicKummerLogWeight (deningerGammaSixYScaling m) =
      deningerGammaSixB m :=
  deningerKummerLogWeight_positiveRational _ _

def deningerGammaSixSelectorCoefficientMap (m : DeningerSteinbergDepth) :
    (CCMRationalAdelicScaling →₀ ℂ) →ₗ[ℂ] (CCMRationalAdelicScaling →₀ ℂ) :=
  Finsupp.lsum ℂ fun k => deningerGammaSixSelectorScalar m
    (ccmRationalAdelicKummerLogWeight k) • Finsupp.lsingle k

/-- Cubic Kummer selector attached to the honest Gamma-six complementary pair. -/
def deningerGammaSixSelector (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing →ₗ[ℂ]
      RouteRMultiplierKOne.KummerGroupRing :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap.comp
    ((deningerGammaSixSelectorCoefficientMap m).comp
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)

@[simp] theorem deningerGammaSixSelector_basis
    (m : DeningerSteinbergDepth) (k : CCMRationalAdelicScaling) :
    deningerGammaSixSelector m (deningerSteinbergBasis k) =
      deningerGammaSixSelectorScalar m
        (ccmRationalAdelicKummerLogWeight k) • deningerSteinbergBasis k := by
  simp [deningerGammaSixSelector, deningerGammaSixSelectorCoefficientMap,
    deningerSteinbergBasis, MonoidAlgebra.of_apply, smul_eq_mul]

/-- Gamma-six selector is exactly a normalized cubic in the Kummer derivation. -/
theorem deningerGammaSixSelector_eq_cubic
    (m : DeningerSteinbergDepth)
    (F : RouteRMultiplierKOne.KummerGroupRing) :
    deningerGammaSixSelector m F =
      (deningerGammaSixSelectorDenominator m)⁻¹ •
        (2 • RouteRMultiplierKOne.kummerGroupRingDerivation
              (RouteRMultiplierKOne.kummerGroupRingDerivation
                (RouteRMultiplierKOne.kummerGroupRingDerivation F)) -
          (3 * deningerGammaSixL m) •
            RouteRMultiplierKOne.kummerGroupRingDerivation
              (RouteRMultiplierKOne.kummerGroupRingDerivation F) +
          (deningerGammaSixL m) ^ 2 •
            RouteRMultiplierKOne.kummerGroupRingDerivation F) := by
  induction F using MonoidAlgebra.induction_on with
  | hM k =>
      change deningerGammaSixSelector m (deningerSteinbergBasis k) = _
      let w := ccmRationalAdelicKummerLogWeight k
      have hN1 : RouteRMultiplierKOne.kummerGroupRingDerivation
          (deningerSteinbergBasis k) = w • deningerSteinbergBasis k :=
        RouteRMultiplierKOne.kummerGroupRingDerivation_of k
      have hN2 : RouteRMultiplierKOne.kummerGroupRingDerivation
          (RouteRMultiplierKOne.kummerGroupRingDerivation
            (deningerSteinbergBasis k)) = w ^ 2 • deningerSteinbergBasis k := by
        rw [hN1, map_smul, hN1]
        module
      have hN3 : RouteRMultiplierKOne.kummerGroupRingDerivation
          (RouteRMultiplierKOne.kummerGroupRingDerivation
            (RouteRMultiplierKOne.kummerGroupRingDerivation
              (deningerSteinbergBasis k))) = w ^ 3 • deningerSteinbergBasis k := by
        rw [hN2, map_smul, hN1]
        module
      rw [deningerGammaSixSelector_basis]
      change deningerGammaSixSelectorScalar m w • deningerSteinbergBasis k =
        (deningerGammaSixSelectorDenominator m)⁻¹ •
          (2 • RouteRMultiplierKOne.kummerGroupRingDerivation
                (RouteRMultiplierKOne.kummerGroupRingDerivation
                  (RouteRMultiplierKOne.kummerGroupRingDerivation
                    (deningerSteinbergBasis k))) -
            (3 * deningerGammaSixL m) •
              RouteRMultiplierKOne.kummerGroupRingDerivation
                (RouteRMultiplierKOne.kummerGroupRingDerivation
                  (deningerSteinbergBasis k)) +
            deningerGammaSixL m ^ 2 •
              RouteRMultiplierKOne.kummerGroupRingDerivation
                (deningerSteinbergBasis k))
      rw [hN3, hN2, hN1, deningerGammaSixSelectorScalar_cubic]
      module
  | hadd F H hF hH =>
      simp only [map_add, hF, hH]
      module
  | hsmul c F hF =>
      simp only [map_smul, hF]
      module

theorem deningerGammaSixSteinbergCell_expand (m : DeningerSteinbergDepth) :
    deningerGammaSixSteinbergCell m =
      deningerSteinbergBasis
          (deningerGammaSixXScaling m * deningerGammaSixYScaling m) -
        deningerSteinbergBasis (deningerGammaSixXScaling m) -
        deningerSteinbergBasis (deningerGammaSixYScaling m) + 1 := by
  rw [deningerGammaSixSteinbergCell, deningerSteinbergBasis_mul]
  ring

/-- Exact extraction of the Gamma-six oriented edge from the honest Steinberg cell. -/
theorem deningerGammaSixSelector_cell (m : DeningerSteinbergDepth) :
    deningerGammaSixSelector m (deningerGammaSixSteinbergCell m) =
      deningerSteinbergBasis (deningerGammaSixXScaling m) -
        deningerSteinbergBasis (deningerGammaSixYScaling m) := by
  rw [deningerGammaSixSteinbergCell_expand]
  simp only [map_add, map_sub, deningerGammaSixSelector_basis,
    ccmRationalAdelicKummerLogWeight_mul,
    deningerGammaSixKummerWeight_X, deningerGammaSixKummerWeight_Y]
  have hone : ccmRationalAdelicKummerLogWeight
      (1 : CCMRationalAdelicScaling) = 0 := by
    simp [ccmRationalAdelicKummerLogWeight]
  rw [show (1 : RouteRMultiplierKOne.KummerGroupRing) =
      deningerSteinbergBasis 1 by rw [deningerSteinbergBasis_one],
    deningerGammaSixSelector_basis, hone,
    deningerGammaSixSelectorScalar_zero]
  rw [show deningerGammaSixSelectorScalar m
      (deningerGammaSixA m + deningerGammaSixB m) = 0 by
    simpa [deningerGammaSixL] using deningerGammaSixSelectorScalar_L m]
  simp

theorem deningerGammaSixY_inv_mul_X_scaling (m : DeningerSteinbergDepth) :
    (deningerGammaSixYScaling m)⁻¹ * deningerGammaSixXScaling m =
      deningerGammaSixScaling m := by
  apply ccmRationalAdelicScalingEquiv.injective
  apply Units.ext
  change (deningerGammaSixY m)⁻¹ * deningerGammaSixX m =
    (6 : ℚ) ^ (m : ℕ)
  rw [inv_mul_eq_div, deningerGammaSixX_div_Y]
  rfl

theorem deningerGammaSixX_inv_mul_Y_scaling (m : DeningerSteinbergDepth) :
    (deningerGammaSixXScaling m)⁻¹ * deningerGammaSixYScaling m =
      (deningerGammaSixScaling m)⁻¹ := by
  have h := congrArg (fun k : CCMRationalAdelicScaling => k⁻¹)
    (deningerGammaSixY_inv_mul_X_scaling m)
  simpa [mul_comm] using h

/-- Forward full-grade normal extracted from the honest Gamma-six cell. -/
def deningerGammaSixForwardEscape (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing :=
  deningerSteinbergBasis (deningerGammaSixYScaling m)⁻¹ *
    deningerGammaSixSelector m (deningerGammaSixSteinbergCell m)

/-- Counteroriented full-grade normal extracted from the same honest cell. -/
def deningerGammaSixReciprocalEscape (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing :=
  -deningerSteinbergBasis (deningerGammaSixXScaling m)⁻¹ *
    deningerGammaSixSelector m (deningerGammaSixSteinbergCell m)

theorem deningerGammaSixForwardEscape_eq (m : DeningerSteinbergDepth) :
    deningerGammaSixForwardEscape m =
      deningerSteinbergBasis (deningerGammaSixScaling m) - 1 := by
  rw [deningerGammaSixForwardEscape, deningerGammaSixSelector_cell, mul_sub,
    ← deningerSteinbergBasis_mul, ← deningerSteinbergBasis_mul,
    inv_mul_cancel, deningerSteinbergBasis_one,
    deningerGammaSixY_inv_mul_X_scaling]

theorem deningerGammaSixReciprocalEscape_eq (m : DeningerSteinbergDepth) :
    deningerGammaSixReciprocalEscape m =
      deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹ - 1 := by
  rw [deningerGammaSixReciprocalEscape, deningerGammaSixSelector_cell]
  calc
    -deningerSteinbergBasis (deningerGammaSixXScaling m)⁻¹ *
          (deningerSteinbergBasis (deningerGammaSixXScaling m) -
            deningerSteinbergBasis (deningerGammaSixYScaling m)) =
        deningerSteinbergBasis (deningerGammaSixXScaling m)⁻¹ *
          deningerSteinbergBasis (deningerGammaSixYScaling m) -
            deningerSteinbergBasis (deningerGammaSixXScaling m)⁻¹ *
              deningerSteinbergBasis (deningerGammaSixXScaling m) := by
            ring
    _ = deningerSteinbergBasis
          ((deningerGammaSixXScaling m)⁻¹ * deningerGammaSixYScaling m) - 1 := by
          rw [← deningerSteinbergBasis_mul, ← deningerSteinbergBasis_mul,
            inv_mul_cancel, deningerSteinbergBasis_one]
    _ = deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹ - 1 := by
          rw [deningerGammaSixX_inv_mul_Y_scaling]

/-- Two-sided Gamma-six orientation class. -/
def deningerGammaSixOrientedEscape (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing :=
  deningerGammaSixForwardEscape m - deningerGammaSixReciprocalEscape m

theorem deningerGammaSixOrientedEscape_eq (m : DeningerSteinbergDepth) :
    deningerGammaSixOrientedEscape m =
      deningerSteinbergBasis (deningerGammaSixScaling m) -
        deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹ := by
  rw [deningerGammaSixOrientedEscape, deningerGammaSixForwardEscape_eq,
    deningerGammaSixReciprocalEscape_eq]
  ring

def deningerGammaSixDepthPair (m : DeningerSteinbergDepth) :
    DeningerPositiveSteinbergPair where
  x := deningerGammaSixX m
  y := deningerGammaSixY m
  x_pos := deningerGammaSixX_pos m
  y_pos := deningerGammaSixY_pos m
  complementary := deningerGammaSixX_add_Y m

theorem deningerGammaSixSteinbergCell_mem_steinbergIdeal
    (m : DeningerSteinbergDepth) :
    deningerGammaSixSteinbergCell m ∈ deningerKummerSteinbergIdeal := by
  change deningerPositiveSteinbergCell (deningerGammaSixDepthPair m) ∈
    deningerKummerSteinbergIdeal
  exact Ideal.subset_span (Set.mem_range_self (deningerGammaSixDepthPair m))

theorem deningerGammaSixScaling_eq_positiveRational
    (m : DeningerSteinbergDepth) :
    deningerGammaSixScaling m =
      deningerScalingOfPositiveRational (deningerGammaSixCoefficient m)
        (lt_trans (by norm_num) (deningerGammaSixCoefficient_one_lt m)) := by
  apply ccmRationalAdelicScalingEquiv.injective
  apply Units.ext
  rfl

theorem deningerGammaSixScaling_weight (m : DeningerSteinbergDepth) :
    ccmRationalAdelicKummerLogWeight (deningerGammaSixScaling m) =
      (m : ℂ) * (Real.log 6 : ℂ) := by
  rw [deningerGammaSixScaling_eq_positiveRational,
    deningerKummerLogWeight_positiveRational]
  unfold deningerGammaSixCoefficient
  push_cast
  rw [Real.log_pow]
  push_cast
  rfl

theorem deningerKummerRegulator_gammaSixForwardEscape
    (m : DeningerSteinbergDepth) :
    deningerKummerRegulator (deningerGammaSixForwardEscape m) =
      (m : ℂ) * (Real.log 6 : ℂ) := by
  rw [deningerGammaSixForwardEscape_eq, map_sub,
    deningerKummerRegulator_basis, deningerGammaSixScaling_weight,
    deningerKummerRegulator_one, sub_zero]

theorem deningerKummerRegulator_gammaSixReciprocalEscape
    (m : DeningerSteinbergDepth) :
    deningerKummerRegulator (deningerGammaSixReciprocalEscape m) =
      -((m : ℂ) * (Real.log 6 : ℂ)) := by
  rw [deningerGammaSixReciprocalEscape_eq, map_sub,
    deningerKummerRegulator_basis, ccmRationalAdelicKummerLogWeight_inv,
    deningerGammaSixScaling_weight, deningerKummerRegulator_one, sub_zero]

/-- Oriented Kummer regulator sees twice the full Gamma-six depth. -/
theorem deningerKummerRegulator_gammaSixOrientedEscape
    (m : DeningerSteinbergDepth) :
    deningerKummerRegulator (deningerGammaSixOrientedEscape m) =
      2 * (m : ℂ) * (Real.log 6 : ℂ) := by
  rw [deningerGammaSixOrientedEscape, map_sub,
    deningerKummerRegulator_gammaSixForwardEscape,
    deningerKummerRegulator_gammaSixReciprocalEscape]
  ring

theorem deningerKummerRegulator_gammaSixOrientedEscape_ne_zero
    (m : DeningerSteinbergDepth) :
    deningerKummerRegulator (deningerGammaSixOrientedEscape m) ≠ 0 := by
  rw [deningerKummerRegulator_gammaSixOrientedEscape]
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast (show (m : ℕ) ≠ 0 by omega)))
    (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne')

/-- Two-sided Gamma-six normal cannot be ordinary Steinberg/Milnor incidence. -/
theorem deningerGammaSixOrientedEscape_not_mem_steinbergIdeal
    (m : DeningerSteinbergDepth) :
    deningerGammaSixOrientedEscape m ∉ deningerKummerSteinbergIdeal := by
  intro h
  exact deningerKummerRegulator_gammaSixOrientedEscape_ne_zero m
    (deningerKummerRegulator_eq_zero_of_mem_steinbergIdeal h)

def deningerGammaSixForwardTatePrimitive (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing :=
  deningerSteinbergBasis (deningerGammaSixScaling m) *
    GaloisForLFunctions.HTGeometry.tateIntervalCharacter
      (deningerSteinbergBasis deningerGammaSixBaseScaling⁻¹) (m : ℕ)

def deningerGammaSixReciprocalTatePrimitive (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.KummerGroupRing :=
  deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹ *
    GaloisForLFunctions.HTGeometry.tateIntervalCharacter
      (deningerSteinbergBasis deningerGammaSixBaseScaling) (m : ℕ)

theorem deningerGammaSixForwardTateTop_cancel (m : DeningerSteinbergDepth) :
    deningerSteinbergBasis (deningerGammaSixScaling m) *
        deningerSteinbergBasis deningerGammaSixBaseScaling⁻¹ ^ (m : ℕ) = 1 := by
  rw [← deningerSteinbergBasis_pow, ← deningerSteinbergBasis_mul,
    deningerGammaSixScaling]
  simp

theorem deningerGammaSixReciprocalTateTop_cancel (m : DeningerSteinbergDepth) :
    deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹ *
        deningerSteinbergBasis deningerGammaSixBaseScaling ^ (m : ℕ) = 1 := by
  rw [← deningerSteinbergBasis_pow, ← deningerSteinbergBasis_mul,
    ← deningerGammaSixScaling]
  simp

/-- Strict forward Tate boundary for the Gamma-six cell normal. -/
theorem deningerGammaSixForwardTateBoundary (m : DeningerSteinbergDepth) :
    (1 - deningerSteinbergBasis deningerGammaSixBaseScaling⁻¹) *
        deningerGammaSixForwardTatePrimitive m =
      deningerGammaSixForwardEscape m := by
  rw [deningerGammaSixForwardTatePrimitive, deningerGammaSixForwardEscape_eq]
  calc
    (1 - deningerSteinbergBasis deningerGammaSixBaseScaling⁻¹) *
          (deningerSteinbergBasis (deningerGammaSixScaling m) *
            GaloisForLFunctions.HTGeometry.tateIntervalCharacter
              (deningerSteinbergBasis deningerGammaSixBaseScaling⁻¹) (m : ℕ)) =
        deningerSteinbergBasis (deningerGammaSixScaling m) *
          ((1 - deningerSteinbergBasis deningerGammaSixBaseScaling⁻¹) *
            GaloisForLFunctions.HTGeometry.tateIntervalCharacter
              (deningerSteinbergBasis deningerGammaSixBaseScaling⁻¹) (m : ℕ)) := by ring
    _ = deningerSteinbergBasis (deningerGammaSixScaling m) *
          (1 - deningerSteinbergBasis deningerGammaSixBaseScaling⁻¹ ^ (m : ℕ)) := by
          rw [GaloisForLFunctions.HTGeometry.one_sub_mul_tateIntervalCharacter]
    _ = deningerSteinbergBasis (deningerGammaSixScaling m) - 1 := by
          rw [mul_sub, mul_one, deningerGammaSixForwardTateTop_cancel]

/-- Strict reciprocal Tate boundary for the Gamma-six cell normal. -/
theorem deningerGammaSixReciprocalTateBoundary (m : DeningerSteinbergDepth) :
    (1 - deningerSteinbergBasis deningerGammaSixBaseScaling) *
        deningerGammaSixReciprocalTatePrimitive m =
      deningerGammaSixReciprocalEscape m := by
  rw [deningerGammaSixReciprocalTatePrimitive,
    deningerGammaSixReciprocalEscape_eq]
  calc
    (1 - deningerSteinbergBasis deningerGammaSixBaseScaling) *
          (deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹ *
            GaloisForLFunctions.HTGeometry.tateIntervalCharacter
              (deningerSteinbergBasis deningerGammaSixBaseScaling) (m : ℕ)) =
        deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹ *
          ((1 - deningerSteinbergBasis deningerGammaSixBaseScaling) *
            GaloisForLFunctions.HTGeometry.tateIntervalCharacter
              (deningerSteinbergBasis deningerGammaSixBaseScaling) (m : ℕ)) := by ring
    _ = deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹ *
          (1 - deningerSteinbergBasis deningerGammaSixBaseScaling ^ (m : ℕ)) := by
          rw [GaloisForLFunctions.HTGeometry.one_sub_mul_tateIntervalCharacter]
    _ = deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹ - 1 := by
          rw [mul_sub, mul_one, deningerGammaSixReciprocalTateTop_cancel]

theorem deningerKummerCharacter_gammaSixBaseScaling (delta : ℂ) :
    deningerKummerCharacter delta
        (deningerSteinbergBasis deningerGammaSixBaseScaling) =
      (6 : ℂ) ^ delta := by
  rw [deningerKummerCharacter_basis]
  norm_num [deningerGammaSixBaseScaling,
    deningerScalingOfPositiveRational]

theorem deningerKummerCharacter_gammaSixScaling
    (m : DeningerSteinbergDepth) (delta : ℂ) :
    deningerKummerCharacter delta
        (deningerSteinbergBasis (deningerGammaSixScaling m)) =
      (6 : ℂ) ^ ((m : ℂ) * delta) := by
  rw [deningerGammaSixScaling, deningerSteinbergBasis_pow, map_pow,
    deningerKummerCharacter_gammaSixBaseScaling, ← Complex.cpow_nat_mul]

theorem deningerKummerCharacter_gammaSixInvScaling
    (m : DeningerSteinbergDepth) (delta : ℂ) :
    deningerKummerCharacter delta
        (deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹) =
      ((6 : ℂ) ^ ((m : ℂ) * delta))⁻¹ := by
  have hmul :
      deningerKummerCharacter delta
          (deningerSteinbergBasis (deningerGammaSixScaling m)⁻¹) *
        deningerKummerCharacter delta
          (deningerSteinbergBasis (deningerGammaSixScaling m)) = 1 := by
    rw [← map_mul, ← deningerSteinbergBasis_mul, inv_mul_cancel,
      deningerSteinbergBasis_one, map_one]
  rw [deningerKummerCharacter_gammaSixScaling] at hmul
  exact eq_inv_of_mul_eq_one_left hmul

theorem deningerKummerCharacter_gammaSixForwardEscape
    (m : DeningerSteinbergDepth) (delta : ℂ) :
    deningerKummerCharacter delta (deningerGammaSixForwardEscape m) =
      (6 : ℂ) ^ ((m : ℂ) * delta) - 1 := by
  rw [deningerGammaSixForwardEscape_eq, map_sub, map_one,
    deningerKummerCharacter_gammaSixScaling]

theorem deningerKummerCharacter_gammaSixReciprocalEscape
    (m : DeningerSteinbergDepth) (delta : ℂ) :
    deningerKummerCharacter delta (deningerGammaSixReciprocalEscape m) =
      (6 : ℂ) ^ (-((m : ℂ) * delta)) - 1 := by
  rw [deningerGammaSixReciprocalEscape_eq, map_sub, map_one,
    deningerKummerCharacter_gammaSixInvScaling, Complex.cpow_neg]

/-- Exact two-sided Gamma-six character curvature. -/
theorem deningerKummerCharacter_gammaSixOrientedEscape
    (m : DeningerSteinbergDepth) (delta : ℂ) :
    deningerKummerCharacter delta (deningerGammaSixOrientedEscape m) =
      (6 : ℂ) ^ ((m : ℂ) * delta) -
        (6 : ℂ) ^ (-((m : ℂ) * delta)) := by
  rw [deningerGammaSixOrientedEscape, map_sub,
    deningerKummerCharacter_gammaSixForwardEscape,
    deningerKummerCharacter_gammaSixReciprocalEscape]
  ring

def deningerGammaSixForwardPhysicalEscapeCLM (m : DeningerSteinbergDepth) :
    MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2 :=
  deningerGammaSixNormalCLM m - ContinuousLinearMap.id ℂ MobiusThetaSourceL2

def deningerGammaSixReciprocalPhysicalEscapeCLM (m : DeningerSteinbergDepth) :
    MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2 :=
  deningerGammaSixNormalInvCLM m - ContinuousLinearMap.id ℂ MobiusThetaSourceL2

def deningerGammaSixOrientedPhysicalEscapeCLM (m : DeningerSteinbergDepth) :
    MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2 :=
  deningerGammaSixNormalCLM m - deningerGammaSixNormalInvCLM m

/-- Half-density representation sends the algebraic forward edge to the exact Gamma normal. -/
theorem deningerHalfDensityRepresentation_gammaSixForwardEscape
    (m : DeningerSteinbergDepth) :
    deningerHalfDensityRepresentation (deningerGammaSixForwardEscape m) =
      deningerGammaSixForwardPhysicalEscapeCLM m := by
  rw [deningerGammaSixForwardEscape_eq, map_sub, map_one,
    deningerHalfDensityRepresentation_basis]
  rw [deningerGammaSixForwardPhysicalEscapeCLM,
    deningerGammaSixNormalCLM, deningerHalfDensityRepresentation_basis]
  change deningerHalfDensityScalingCLM (deningerGammaSixScaling m) -
      ContinuousLinearMap.id ℂ MobiusThetaSourceL2 = _
  rfl

/-- Half-density representation sends the reciprocal edge to exact inverse Gamma transport. -/
theorem deningerHalfDensityRepresentation_gammaSixReciprocalEscape
    (m : DeningerSteinbergDepth) :
    deningerHalfDensityRepresentation (deningerGammaSixReciprocalEscape m) =
      deningerGammaSixReciprocalPhysicalEscapeCLM m := by
  rw [deningerGammaSixReciprocalEscape_eq, map_sub, map_one,
    deningerHalfDensityRepresentation_basis]
  rw [deningerGammaSixReciprocalPhysicalEscapeCLM,
    deningerGammaSixNormalInvCLM, deningerHalfDensityRepresentation_basis]
  change deningerHalfDensityScalingCLM (deningerGammaSixScaling m)⁻¹ -
      ContinuousLinearMap.id ℂ MobiusThetaSourceL2 = _
  rfl

theorem deningerHalfDensityRepresentation_gammaSixOrientedEscape
    (m : DeningerSteinbergDepth) :
    deningerHalfDensityRepresentation (deningerGammaSixOrientedEscape m) =
      deningerGammaSixOrientedPhysicalEscapeCLM m := by
  rw [deningerGammaSixOrientedEscape, map_sub,
    deningerHalfDensityRepresentation_gammaSixForwardEscape,
    deningerHalfDensityRepresentation_gammaSixReciprocalEscape]
  rw [deningerGammaSixOrientedPhysicalEscapeCLM,
    deningerGammaSixForwardPhysicalEscapeCLM,
    deningerGammaSixReciprocalPhysicalEscapeCLM]
  module

theorem deningerHalfDensityRepresentation_gammaSixForwardTateBoundary
    (m : DeningerSteinbergDepth) :
    (ContinuousLinearMap.id ℂ MobiusThetaSourceL2 -
        deningerHalfDensityRepresentation
          (deningerSteinbergBasis deningerGammaSixBaseScaling⁻¹)) *
      deningerHalfDensityRepresentation (deningerGammaSixForwardTatePrimitive m) =
        deningerGammaSixForwardPhysicalEscapeCLM m := by
  change (1 - deningerHalfDensityRepresentation
      (deningerSteinbergBasis deningerGammaSixBaseScaling⁻¹)) *
      deningerHalfDensityRepresentation (deningerGammaSixForwardTatePrimitive m) = _
  have h := congrArg deningerHalfDensityRepresentation
    (deningerGammaSixForwardTateBoundary m)
  simpa only [map_mul, map_sub, map_one,
    deningerHalfDensityRepresentation_gammaSixForwardEscape] using h

theorem deningerHalfDensityRepresentation_gammaSixReciprocalTateBoundary
    (m : DeningerSteinbergDepth) :
    (ContinuousLinearMap.id ℂ MobiusThetaSourceL2 -
        deningerHalfDensityRepresentation
          (deningerSteinbergBasis deningerGammaSixBaseScaling)) *
      deningerHalfDensityRepresentation
          (deningerGammaSixReciprocalTatePrimitive m) =
        deningerGammaSixReciprocalPhysicalEscapeCLM m := by
  change (1 - deningerHalfDensityRepresentation
      (deningerSteinbergBasis deningerGammaSixBaseScaling)) *
      deningerHalfDensityRepresentation
          (deningerGammaSixReciprocalTatePrimitive m) = _
  have h := congrArg deningerHalfDensityRepresentation
    (deningerGammaSixReciprocalTateBoundary m)
  simpa only [map_mul, map_sub, map_one,
    deningerHalfDensityRepresentation_gammaSixReciprocalEscape] using h

@[simp] theorem deningerGammaSixForwardPhysicalEscapeCLM_apply
    (m : DeningerSteinbergDepth) (f : MobiusThetaSourceL2) :
    deningerGammaSixForwardPhysicalEscapeCLM m f =
      deningerGammaSixNormalCLM m f - f := rfl

@[simp] theorem deningerGammaSixReciprocalPhysicalEscapeCLM_apply
    (m : DeningerSteinbergDepth) (f : MobiusThetaSourceL2) :
    deningerGammaSixReciprocalPhysicalEscapeCLM m f =
      deningerGammaSixNormalInvCLM m f - f := rfl

/-- Strict source-to-physical forward chain-map descent for the finite corrected source. -/
theorem deningerGammaSixForwardPhysicalEscape_finiteCorrectedSource
    (m : MobiusHonestDepth) :
    deningerGammaSixForwardPhysicalEscapeCLM ⟨m, by omega⟩
        (deningerGammaSixFiniteCorrectedSource m) =
      mobiusThetaPrimeNormalResidual 6 m -
        deningerGammaSixFiniteCorrectedSource m := by
  rw [deningerGammaSixForwardPhysicalEscapeCLM_apply,
    deningerGammaSixNormal_finiteCorrectedSource]

theorem tendsto_deningerGammaSixForwardPhysicalEscape_finiteCorrectedSource :
    Tendsto (fun n : ℕ =>
      deningerGammaSixForwardPhysicalEscapeCLM ⟨n + 3, by omega⟩
        (deningerGammaSixFiniteCorrectedSource ⟨n + 3, by omega⟩))
      atTop (nhds xiThetaSourceL2) := by
  have h := (tendsto_mobiusThetaPrimeNormalResidual_six.comp
    (tendsto_add_atTop_nat 3)).sub tendsto_deningerGammaSixCompleteSource_zero
  have hevent : ∀ᶠ n : ℕ in atTop,
      mobiusThetaPrimeNormalResidual 6 (n + 3) -
          deningerGammaSixCompleteSource ⟨n + 3, by omega⟩ =
        deningerGammaSixForwardPhysicalEscapeCLM ⟨n + 3, by omega⟩
          (deningerGammaSixFiniteCorrectedSource ⟨n + 3, by omega⟩) :=
    Filter.Eventually.of_forall fun n => by
      rw [← deningerGammaSixFiniteCorrectedSource_eq_completeSource]
      simpa using (deningerGammaSixForwardPhysicalEscape_finiteCorrectedSource
        ⟨n + 3, by omega⟩).symm
  simpa using h.congr' hevent

/-- Reciprocal edge returns the transported six packet to its finite-corrected source. -/
theorem deningerGammaSixReciprocalPhysicalEscape_residual
    (m : MobiusHonestDepth) :
    deningerGammaSixReciprocalPhysicalEscapeCLM ⟨m, by omega⟩
        (mobiusThetaPrimeNormalResidual 6 m) =
      deningerGammaSixFiniteCorrectedSource m -
        mobiusThetaPrimeNormalResidual 6 m := by
  rw [deningerGammaSixReciprocalPhysicalEscapeCLM_apply,
    deningerGammaSixFiniteCorrectedSource_eq_completeSource,
    deningerGammaSixCompleteSource]

/-- Genuine multiplier K1 cycle of the forward Gamma-six normal. -/
def deningerGammaSixForwardKOneCycle
    (m : DeningerSteinbergDepth) : RouteRMultiplierKOne.MC1 :=
  let u := RouteRMultiplierKOne.dilUnit (deningerGammaSixScaling m)
  PiTensorProduct.tprod ℂ (fun i : Fin 2 =>
    Fin.cases (↑u⁻¹ : RouteRMultiplierKOne.Mult)
      (fun _ => (u : RouteRMultiplierKOne.Mult)) i)

def deningerGammaSixReciprocalKOneCycle
    (m : DeningerSteinbergDepth) : RouteRMultiplierKOne.MC1 :=
  let u := RouteRMultiplierKOne.dilUnit (deningerGammaSixScaling m)⁻¹
  PiTensorProduct.tprod ℂ (fun i : Fin 2 =>
    Fin.cases (↑u⁻¹ : RouteRMultiplierKOne.Mult)
      (fun _ => (u : RouteRMultiplierKOne.Mult)) i)

def deningerGammaSixOrientedKOneCycle
    (m : DeningerSteinbergDepth) : RouteRMultiplierKOne.MC1 :=
  deningerGammaSixForwardKOneCycle m - deningerGammaSixReciprocalKOneCycle m

theorem deningerGammaSixForwardKOneCycle_boundary
    (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.mBoundaryOne
      (deningerGammaSixForwardKOneCycle m) = 0 := by
  rw [deningerGammaSixForwardKOneCycle,
    RouteRMultiplierKOne.mBoundaryOne_tprod]
  simp

theorem deningerGammaSixReciprocalKOneCycle_boundary
    (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.mBoundaryOne
      (deningerGammaSixReciprocalKOneCycle m) = 0 := by
  rw [deningerGammaSixReciprocalKOneCycle,
    RouteRMultiplierKOne.mBoundaryOne_tprod]
  simp

theorem deningerGammaSixOrientedKOneCycle_boundary
    (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.mBoundaryOne
      (deningerGammaSixOrientedKOneCycle m) = 0 := by
  rw [deningerGammaSixOrientedKOneCycle, map_sub,
    deningerGammaSixForwardKOneCycle_boundary,
    deningerGammaSixReciprocalKOneCycle_boundary, sub_self]

theorem deningerGammaSixForwardKOneCycle_kummerValue
    (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle
        (deningerGammaSixForwardKOneCycle m) =
      (m : ℂ) * (Real.log 6 : ℂ) := by
  rw [deningerGammaSixForwardKOneCycle,
    RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle_tprod]
  change RouteRMultiplierKOne.kummerGroupRingTrace
      (RouteRMultiplierKOne.multiplierToKummerGroupRing
          (↑((RouteRMultiplierKOne.dilUnit
            (deningerGammaSixScaling m))⁻¹) : RouteRMultiplierKOne.Mult) *
        RouteRMultiplierKOne.kummerGroupRingDerivation
          (RouteRMultiplierKOne.multiplierToKummerGroupRing
            ((RouteRMultiplierKOne.dilUnit
              (deningerGammaSixScaling m) : RouteRMultiplierKOne.Multˣ) :
                RouteRMultiplierKOne.Mult))) = _
  rw [RouteRMultiplierKOne.multiplierToKummerGroupRing_dilUnit_inv,
    RouteRMultiplierKOne.multiplierToKummerGroupRing_dilUnit,
    RouteRMultiplierKOne.kummerGroupRingPair_inv_of,
    deningerGammaSixScaling_weight]

theorem deningerGammaSixReciprocalKOneCycle_kummerValue
    (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle
        (deningerGammaSixReciprocalKOneCycle m) =
      -((m : ℂ) * (Real.log 6 : ℂ)) := by
  rw [deningerGammaSixReciprocalKOneCycle,
    RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle_tprod]
  change RouteRMultiplierKOne.kummerGroupRingTrace
      (RouteRMultiplierKOne.multiplierToKummerGroupRing
          (↑((RouteRMultiplierKOne.dilUnit
            (deningerGammaSixScaling m)⁻¹)⁻¹) : RouteRMultiplierKOne.Mult) *
        RouteRMultiplierKOne.kummerGroupRingDerivation
          (RouteRMultiplierKOne.multiplierToKummerGroupRing
            ((RouteRMultiplierKOne.dilUnit
              (deningerGammaSixScaling m)⁻¹ : RouteRMultiplierKOne.Multˣ) :
                RouteRMultiplierKOne.Mult))) = _
  rw [RouteRMultiplierKOne.multiplierToKummerGroupRing_dilUnit_inv,
    RouteRMultiplierKOne.multiplierToKummerGroupRing_dilUnit,
    RouteRMultiplierKOne.kummerGroupRingPair_inv_of,
    ccmRationalAdelicKummerLogWeight_inv,
    deningerGammaSixScaling_weight]

theorem deningerGammaSixOrientedKOneCycle_kummerValue
    (m : DeningerSteinbergDepth) :
    RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle
        (deningerGammaSixOrientedKOneCycle m) =
      2 * (m : ℂ) * (Real.log 6 : ℂ) := by
  rw [deningerGammaSixOrientedKOneCycle, map_sub,
    deningerGammaSixForwardKOneCycle_kummerValue,
    deningerGammaSixReciprocalKOneCycle_kummerValue]
  ring

/-- Oriented Gamma-six K1 class is not a degree-two Hochschild boundary. -/
theorem deningerGammaSixOrientedKOneCycle_not_mem_boundaryTwo_range
    (m : DeningerSteinbergDepth) :
    deningerGammaSixOrientedKOneCycle m ∉
      LinearMap.range RouteRMultiplierKOne.multiplierHochschildBoundaryTwo := by
  rintro ⟨z, hz⟩
  have hzero : RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle
      (RouteRMultiplierKOne.multiplierHochschildBoundaryTwo z) = 0 := by
    have hcomp := congrArg
      (fun L : RouteRMultiplierKOne.MultiplierDegreeTwoCyclicSource →ₗ[ℂ] ℂ => L z)
      RouteRMultiplierKOne.multiplierKummerCyclicOneCocycle_comp_boundaryTwo
    simpa using hcomp
  rw [hz, deningerGammaSixOrientedKOneCycle_kummerValue] at hzero
  exact deningerKummerRegulator_gammaSixOrientedEscape_ne_zero m
    (by rw [deningerKummerRegulator_gammaSixOrientedEscape]; exact hzero)

/-! ## One-sided analytic orientation and singular norm growth -/

theorem norm_deningerGammaSixNormalInvCLM_sq
    (m : DeningerSteinbergDepth) (f : MobiusThetaSourceL2) :
    ‖deningerGammaSixNormalInvCLM m (deningerGammaSixNormalInvCLM m f)‖ =
      (6 : ℝ) ^ (-(m : ℝ)) * ‖f‖ := by
  rw [norm_deningerGammaSixNormalInvCLM_apply,
    norm_deningerGammaSixNormalInvCLM_apply, ← mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
  congr 2
  ring

theorem deningerGammaSixOrientedPhysicalEscape_completeSource
    (m : MobiusHonestDepth) :
    deningerGammaSixOrientedPhysicalEscapeCLM ⟨m, by omega⟩
        (deningerGammaSixCompleteSource m) =
      mobiusThetaPrimeNormalResidual 6 m -
        deningerGammaSixNormalInvCLM ⟨m, by omega⟩
          (deningerGammaSixNormalInvCLM ⟨m, by omega⟩
            (mobiusThetaPrimeNormalResidual 6 m)) := by
  rw [deningerGammaSixOrientedPhysicalEscapeCLM,
    sub_apply,
    deningerGammaSixNormal_completeSource,
    deningerGammaSixCompleteSource]

theorem tendsto_deningerGammaSixNormalInv_sq_residual_zero :
    Tendsto (fun n : ℕ =>
      deningerGammaSixNormalInvCLM ⟨n + 3, by omega⟩
        (deningerGammaSixNormalInvCLM ⟨n + 3, by omega⟩
          (mobiusThetaPrimeNormalResidual 6 (n + 3))))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hR := tendsto_mobiusThetaPrimeNormalResidual_six.comp
    (tendsto_add_atTop_nat 3)
  obtain ⟨C, hC⟩ := hR.norm.bddAbove_range
  have hbound : ∀ n : ℕ,
      ‖mobiusThetaPrimeNormalResidual 6 (n + 3)‖ ≤ C :=
    fun n => hC ⟨n, rfl⟩
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hbound 0)
  refine squeeze_zero (g := fun n : ℕ =>
      (6 : ℝ) ^ (-(((n + 3 : ℕ) : ℝ))) * C)
    (fun _ => norm_nonneg _) (fun n => ?_) ?_
  · rw [norm_deningerGammaSixNormalInvCLM_sq]
    exact mul_le_mul_of_nonneg_left (hbound n)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) _)
  · have hpow : Tendsto (fun n : ℕ =>
        (6 : ℝ) ^ (-(((n + 3 : ℕ) : ℝ))))
        atTop (nhds 0) := by
      have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 6⁻¹) (by norm_num : (6 : ℝ)⁻¹ < 1)
      convert (hbase.comp (tendsto_add_atTop_nat 3)) using 1
      funext n
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6),
        Real.rpow_natCast, ← inv_pow]
      rfl
    simpa using hpow.mul_const C

/-- The reciprocal physical face dies; the forward theta endpoint survives. -/
theorem tendsto_deningerGammaSixOrientedPhysicalEscape_completeSource :
    Tendsto (fun n : ℕ =>
      deningerGammaSixOrientedPhysicalEscapeCLM ⟨n + 3, by omega⟩
        (deningerGammaSixCompleteSource ⟨n + 3, by omega⟩))
      atTop (nhds xiThetaSourceL2) := by
  have hR := tendsto_mobiusThetaPrimeNormalResidual_six.comp
    (tendsto_add_atTop_nat 3)
  have h := hR.sub tendsto_deningerGammaSixNormalInv_sq_residual_zero
  have hevent : ∀ᶠ n : ℕ in atTop,
      mobiusThetaPrimeNormalResidual 6 (n + 3) -
          deningerGammaSixNormalInvCLM ⟨n + 3, by omega⟩
            (deningerGammaSixNormalInvCLM ⟨n + 3, by omega⟩
              (mobiusThetaPrimeNormalResidual 6 (n + 3))) =
        deningerGammaSixOrientedPhysicalEscapeCLM ⟨n + 3, by omega⟩
          (deningerGammaSixCompleteSource ⟨n + 3, by omega⟩) :=
    Filter.Eventually.of_forall fun n => by
      simpa using (deningerGammaSixOrientedPhysicalEscape_completeSource
        ⟨n + 3, by omega⟩).symm
  simpa using h.congr' hevent

theorem norm_deningerGammaSixNormalCLM (m : DeningerSteinbergDepth) :
    ‖deningerGammaSixNormalCLM m‖ = (6 : ℝ) ^ ((m : ℝ) / 2) := by
  rw [deningerGammaSixNormalCLM, deningerHalfDensityRepresentation_basis,
    deningerHalfDensityScalingCLM, norm_smul,
    LinearIsometry.norm_toContinuousLinearMap, mul_one,
    Complex.norm_real, Real.norm_eq_abs, deningerScalingAbsoluteValue_gammaSix]
  rw [abs_of_pos (Real.rpow_pos_of_pos (by positivity) _),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 6)]
  congr 1
  ring

theorem norm_deningerGammaSixForwardPhysicalEscapeCLM_lower
    (m : DeningerSteinbergDepth) :
    (6 : ℝ) ^ ((m : ℝ) / 2) - 1 ≤
      ‖deningerGammaSixForwardPhysicalEscapeCLM m‖ := by
  have h := norm_sub_norm_le (deningerGammaSixNormalCLM m)
    (ContinuousLinearMap.id ℂ MobiusThetaSourceL2)
  rw [norm_deningerGammaSixNormalCLM, ContinuousLinearMap.norm_id] at h
  exact h

theorem tendsto_norm_deningerGammaSixForwardPhysicalEscapeCLM_atTop :
    Tendsto (fun n : ℕ =>
      ‖deningerGammaSixForwardPhysicalEscapeCLM ⟨n + 3, by omega⟩‖)
      atTop atTop := by
  have hpow : Tendsto (fun n : ℕ =>
      (6 : ℝ) ^ (((n + 3 : ℕ) : ℝ) / 2)) atTop atTop := by
    have hbase : 1 < (6 : ℝ) ^ ((1 : ℝ) / 2) := by
      exact Real.one_lt_rpow (by norm_num) (by norm_num)
    convert (tendsto_pow_atTop_atTop_of_one_lt hbase).comp
      (tendsto_add_atTop_nat 3) using 1
    funext n
    change (6 : ℝ) ^ (((n + 3 : ℕ) : ℝ) / 2) =
      ((6 : ℝ) ^ ((1 : ℝ) / 2)) ^ (n + 3)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
    congr 1
    ring
  rw [tendsto_atTop] at hpow ⊢
  intro b
  filter_upwards [hpow (b + 1)] with n hn
  have hlower := norm_deningerGammaSixForwardPhysicalEscapeCLM_lower
    (⟨n + 3, by omega⟩ : DeningerSteinbergDepth)
  linarith

end
end RHTower

