import GaloisForLFunctions.RHTower.WallDatumRayBound
import GaloisForLFunctions.RHTower.WallInwardTailRemainder

/-!
# The four scalar inputs of the one-block estimate

Assembling the block estimate needs, besides the region estimates themselves, four elementary facts:
an indicator's squared mass is the squared mass on its region; on a unit block the squared `L¹` mass
of a profile is at most its `L²` mass; the propagated datum has finite squared mass on the whole
frequency line; and the vector accumulated at the threshold by the two boundary terms is bounded by
one power of the threshold times the block's `L¹` mass.

The last is where the coefficient `4 + π` comes from: the threshold operator is
`i·W·A + W·P` with `‖A‖ ≤ 1` and `‖P‖ ≤ (3+π)(1+|W|)^{-1} ≤ 3 + π` at floor one.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [InnerProductSpace ℂ X] [CompleteSpace X] in
/-- The squared mass of an indicator is the squared mass on the region. -/
theorem lintegral_sq_indicator_eq {A : Set ℝ} (hA : MeasurableSet A) (f : ℝ → X) :
    (∫⁻ x : ℝ, ‖A.indicator f x‖ₑ ^ 2) = ∫⁻ x in A, ‖f x‖ₑ ^ 2 := by
  rw [← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

omit [InnerProductSpace ℂ X] [CompleteSpace X] in
/-- **On a unit block the squared `L¹` mass is at most the `L²` mass.** -/
theorem sq_integral_norm_block_le {g : ℝ → X} {m : ℝ} (hg2 : MemLp g 2 (volume : Measure ℝ))
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    (∫ L in Icc m (m + 1), ‖g L‖) ^ 2 ≤ ∫ L : ℝ, ‖g L‖ ^ 2 := by
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  have hgI : IntegrableOn g (Icc m (m + 1)) := hg1.integrableOn
  have hL1 : (∫⁻ L in Icc m (m + 1), ‖g L‖ₑ) = ENNReal.ofReal (∫ L in Icc m (m + 1), ‖g L‖) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hgI]
  have hsqint : Integrable (fun L : ℝ => ‖g L‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hg2.aestronglyMeasurable).mp hg2
  have hL2 : (∫⁻ L : ℝ, ‖g L‖ₑ ^ 2) = ENNReal.ofReal (∫ L : ℝ, ‖g L‖ ^ 2) := by
    rw [← lintegral_enorm_sq_eq_ofReal_integral hsqint]
  have hCS := sq_lintegral_enorm_block_le (g := g) (m := m) hgI.aestronglyMeasurable.enorm
  rw [hL1] at hCS
  have hmono : (∫⁻ L in Icc m (m + 1), ‖g L‖ₑ ^ 2) ≤ ∫⁻ L : ℝ, ‖g L‖ₑ ^ 2 :=
    setLIntegral_le_lintegral _ _
  have hfin := hCS.trans (hmono.trans (le_of_eq hL2))
  rw [← ENNReal.ofReal_pow (integral_nonneg fun _ => norm_nonneg _)] at hfin
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => by positivity)).mp hfin

variable [Nontrivial X]

/-- **The whole-line squared mass of the propagated datum.** -/
theorem exists_bound_lintegral_sq_line_stripPropagator (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : X,
      (∫⁻ x : ℝ, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2)
        ≤ ENNReal.ofReal (C * ‖c‖ ^ 2) := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_stripPropagator_line hT hE hσ0 hσ1
  obtain ⟨w, hw0, hwe⟩ : ∃ w : ℝ, 0 ≤ w ∧
      ENNReal.ofReal w = ∫⁻ x : ℝ, oneAddAbsWeight (2 * (1 / 2 + σ)) x :=
    ⟨(∫⁻ x : ℝ, oneAddAbsWeight (2 * (1 / 2 + σ)) x).toReal, ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (lintegral_oneAddAbsWeight_ne_top (by linarith))⟩
  refine ⟨K ^ 2 * w, by positivity, fun c => ?_⟩
  have hpt : ∀ x : ℝ, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖
      ≤ (K * ‖c‖) * (1 + |x|) ^ (-(1 / 2 + σ)) := by
    intro x
    calc ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖
        ≤ ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖ * ‖c‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * (1 + |x|) ^ (-(1 / 2 + σ))) * ‖c‖ :=
          mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
      _ = (K * ‖c‖) * (1 + |x|) ^ (-(1 / 2 + σ)) := by ring
  refine (lintegral_sq_globalPowerTail_le hpt).trans (le_of_eq ?_)
  rw [← hwe, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

omit [Nontrivial X] in
/-- **The vector accumulated at the threshold by the two boundary terms.** -/
theorem norm_thresholdVector_le {σ K₂ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g : ℝ → X} {m W : ℝ} (hg : IntegrableOn g (Icc m (m + 1))) (hW : 1 ≤ |W|)
    (hfloor : ∀ L ∈ Icc m (m + 1), 1 ≤ wallFloor T σ W + L) :
    ‖thresholdVector E T g m σ W‖
      ≤ (K₂ * (1 + |W|) ^ (1 / 2 + σ)) * (4 + Real.pi)
        * ∫ L in Icc m (m + 1), ‖g L‖ := by
  have hW0 : (0 : ℝ) < 1 + |W| := by positivity
  have hinv : (1 + |W|)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    linarith [abs_nonneg W]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbase : ∀ L ∈ Icc m (m + 1), ‖thresholdOperator E T σ L W (g L)‖
      ≤ ((K₂ * (1 + |W|) ^ (1 / 2 + σ)) * (4 + Real.pi)) * ‖g L‖ := by
    intro L hL
    have hop := norm_thresholdOperator_le' (E := E) hσ0 hσ1 one_pos hb₂ hW (hfloor L hL)
    have hcoef : (1 : ℝ)⁻¹ + ((1 : ℝ)⁻¹) ^ 3 * (3 + Real.pi) * (1 + |W|)⁻¹ ≤ 4 + Real.pi := by
      have : (3 + Real.pi) * (1 + |W|)⁻¹ ≤ (3 + Real.pi) * 1 :=
        mul_le_mul_of_nonneg_left hinv (by linarith)
      simp only [inv_one, one_pow, one_mul] at *
      linarith
    have hnn : (0 : ℝ) ≤ K₂ * (1 + |W|) ^ (1 / 2 + σ) :=
      mul_nonneg hK₂ (Real.rpow_nonneg hW0.le _)
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact hop.trans (mul_le_mul_of_nonneg_left hcoef hnn)
  have hint : IntegrableOn
      (fun L => ((K₂ * (1 + |W|) ^ (1 / 2 + σ)) * (4 + Real.pi)) * ‖g L‖) (Icc m (m + 1)) :=
    hg.norm.const_mul _
  have hle := MeasureTheory.norm_integral_le_of_norm_le hint
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL using hbase L hL)
  rw [integral_const_mul] at hle
  rw [thresholdVector]
  exact hle

end GaloisForLFunctions.RHTower
