import GaloisForLFunctions.RHTower.BurnolBaseCoefficientCoordinates
import GaloisForLFunctions.RHTower.BurnolBaseFirstJetNoncompact

/-!
# Strong native differentiation at the Burnol formation boundary

Bounded diagonal averages identify the strong first derivative on the complete original source.
The derivative is noncompact, whereas every positive-step difference quotient is compact.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

local notation "Source" => lp (fun _ : RoutePPrimitiveIndex => ℂ) 2

/-- The scalar semigroup average; the value on nonpositive times is irrelevant to the right limit. -/
def burnolFirstJetAverageValue (c : ℝ) (pe : RoutePPrimitiveIndex) : ℝ :=
  if 0 < c then
    (1 - Real.exp (-c * xiGammaEulerPrimitiveLogFrequency pe)) /
      (c * xiGammaEulerPrimitiveLogFrequency pe)
  else 1

theorem burnolFirstJetAverageValue_mem_unitInterval (c : ℝ) (pe : RoutePPrimitiveIndex) :
    0 ≤ burnolFirstJetAverageValue c pe ∧ burnolFirstJetAverageValue c pe ≤ 1 := by
  by_cases hc : 0 < c
  · rw [burnolFirstJetAverageValue, if_pos hc]
    have hlam := xiGammaEulerPrimitiveLogFrequency_pos pe
    have hp : 0 < c * xiGammaEulerPrimitiveLogFrequency pe := mul_pos hc hlam
    have he : Real.exp (-c * xiGammaEulerPrimitiveLogFrequency pe) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    refine ⟨div_nonneg (sub_nonneg.mpr he) hp.le, ?_⟩
    rw [div_le_one hp]
    have h := Real.add_one_le_exp (-c * xiGammaEulerPrimitiveLogFrequency pe)
    linarith
  · simp [burnolFirstJetAverageValue, hc]

theorem norm_burnolFirstJetAverageValue_le (c : ℝ) (pe : RoutePPrimitiveIndex) :
    ‖(burnolFirstJetAverageValue c pe : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (burnolFirstJetAverageValue_mem_unitInterval c pe).1]
  exact (burnolFirstJetAverageValue_mem_unitInterval c pe).2

theorem tendsto_burnolFirstJetAverageValue (pe : RoutePPrimitiveIndex) :
    Tendsto (fun c => burnolFirstJetAverageValue c pe) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  let lam : ℝ := xiGammaEulerPrimitiveLogFrequency pe
  have hlam : 0 < lam := xiGammaEulerPrimitiveLogFrequency_pos pe
  have hlin : HasDerivAt (fun c : ℝ => -c * lam) (-lam) 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).neg.mul_const lam)
  have he : HasDerivAt (fun c : ℝ => Real.exp (-c * lam)) (-lam) 0 := by
    simpa [Function.comp_apply] using! (Real.hasDerivAt_exp (-0 * lam)).comp 0 hlin
  have hd : HasDerivAt (fun c : ℝ => 1 - Real.exp (-c * lam)) lam 0 := by
    simpa only [Pi.sub_apply, neg_neg, zero_add, sub_neg_eq_add] using!
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub he
  have hraw : Tendsto (fun c : ℝ => c⁻¹ * (1 - Real.exp (-c * lam)) * lam⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa [smul_eq_mul, hlam.ne'] using hd.tendsto_slope_zero_right.mul_const lam⁻¹
  apply hraw.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  change 0 < c at hc
  simp only [burnolFirstJetAverageValue, if_pos hc, div_eq_mul_inv, mul_inv_rev]
  dsimp [lam]
  ring

/-- Bounded native averages on all prime-depth coefficient vectors. -/
def burnolFirstJetAverage (c : ℝ) : Source →L[ℂ] Source :=
  LpDiagonal.lpDiag (fun pe => (burnolFirstJetAverageValue c pe : ℂ)) 1 zero_le_one
    (norm_burnolFirstJetAverageValue_le c)

theorem burnolFirstJetAverage_single (c : ℝ) (pe : RoutePPrimitiveIndex) :
    burnolFirstJetAverage c (lp.single 2 pe (1 : ℂ)) =
      (burnolFirstJetAverageValue c pe : ℂ) • lp.single 2 pe (1 : ℂ) :=
  LpDiagonal.lpDiag_single _ _ _ _ pe

/-- The averages converge strongly to the identity, with no uniform clock bound. -/
theorem tendsto_burnolFirstJetAverage (x : Source) :
    Tendsto (fun c => burnolFirstJetAverage c x) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
  let f : ℝ → RoutePPrimitiveIndex → ℝ := fun c pe =>
    ‖((burnolFirstJetAverageValue c pe : ℂ) - 1) * (x : RoutePPrimitiveIndex → ℂ) pe‖ ^ 2
  have hpoint (pe : RoutePPrimitiveIndex) : Tendsto (fun c => f c pe)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun c => (burnolFirstJetAverageValue c pe : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).comp (tendsto_burnolFirstJetAverageValue pe)
    simpa [f] using ((hc.sub_const 1).mul_const ((x : RoutePPrimitiveIndex → ℂ) pe)).norm.pow 2
  have hbound (c : ℝ) (pe : RoutePPrimitiveIndex) :
      ‖f c pe‖ ≤ ‖(x : RoutePPrimitiveIndex → ℂ) pe‖ ^ 2 := by
    have hm := burnolFirstJetAverageValue_mem_unitInterval c pe
    have hd : ‖(burnolFirstJetAverageValue c pe : ℂ) - 1‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hmul := mul_le_mul_of_nonneg_right hd (norm_nonneg ((x : RoutePPrimitiveIndex → ℂ) pe))
    simpa only [f, Real.norm_eq_abs, abs_sq, norm_mul, one_mul] using
      pow_le_pow_left₀ (by positivity) hmul 2
  have hsum : Tendsto (fun c => ∑' pe, f c pe) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence (summable_norm_sq_lp x)
      hpoint (Eventually.of_forall hbound)
  have hnorm (c : ℝ) : ‖burnolFirstJetAverage c x - x‖ ^ 2 = ∑' pe, f c pe := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    apply tsum_congr
    intro pe
    dsimp [f]
    congr 2
    change (burnolFirstJetAverageValue c pe : ℂ) * (x : RoutePPrimitiveIndex → ℂ) pe -
        (x : RoutePPrimitiveIndex → ℂ) pe = _
    ring
  have hnormsq : Tendsto (fun c => ‖burnolFirstJetAverage c x - x‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hsum.congr fun c => (hnorm c).symm
  have hnorm0 : Tendsto (fun c => ‖burnolFirstJetAverage c x - x‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hnormsq.sqrt
  have hz := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm0
  simpa using hz.add_const x

/-- Native positive-step difference quotient of the original synthesis in coefficient coordinates. -/
def burnolBaseNativeDifferenceQuotient (c : ℝ) : Source →L[ℂ] routePBurnolHalfLineL2 :=
  ((c⁻¹ : ℝ) : ℂ) •
    (burnolWeightedShift c.toNNReal ∘L burnolBaseCoefficientSynthesis -
      burnolBaseCoefficientSynthesis)

private theorem ext_source_single {T S : Source →L[ℂ] routePBurnolHalfLineL2}
    (h : ∀ pe, T (lp.single 2 pe (1 : ℂ)) = S (lp.single 2 pe (1 : ℂ))) : T = S := by
  apply ContinuousLinearMap.ext
  intro x
  have hsingle (pe : RoutePPrimitiveIndex) :
      T (lp.single 2 pe (x pe)) = S (lp.single 2 pe (x pe)) := by
    have he : (lp.single 2 pe (x pe) : Source) = (x pe) • lp.single 2 pe (1 : ℂ) := by
      simp [← lp.single_smul]
    rw [he, map_smul, map_smul, h pe]
  have hT := (lp.hasSum_single (by norm_num) x).mapL T
  have hS := (lp.hasSum_single (by norm_num) x).mapL S
  simp only [hsingle] at hT
  exact hT.unique hS

/-- Exact bounded-operator identity for every positive native step. -/
theorem burnolBaseNativeDifferenceQuotient_eq {c : ℝ} (hc : 0 < c) :
    burnolBaseNativeDifferenceQuotient c =
      -(burnolBaseFirstJetSynthesis ∘L burnolFirstJetAverage c) := by
  apply ext_source_single
  intro pe
  change ((c⁻¹ : ℝ) : ℂ) •
    (burnolWeightedShift c.toNNReal (burnolBaseCoefficientSynthesis (lp.single 2 pe 1)) -
      burnolBaseCoefficientSynthesis (lp.single 2 pe 1)) =
    -(burnolBaseFirstJetSynthesis (burnolFirstJetAverage c (lp.single 2 pe 1)))
  rw [burnolBaseCoefficientSynthesis_single, one_smul, burnolWeightedShift_baseField,
    Real.coe_toNNReal c hc.le, burnolFirstJetAverage_single, map_smul,
    burnolBaseFirstJetSynthesis_single, one_smul, burnolBaseFirstJetField]
  have hscalar : ((c⁻¹ : ℝ) : ℂ) *
      ((Real.exp (-c * xiGammaEulerPrimitiveLogFrequency pe) : ℂ) - 1) =
        -(burnolFirstJetAverageValue c pe : ℂ) * (xiGammaEulerPrimitiveLogFrequency pe : ℂ) := by
    rw [burnolFirstJetAverageValue, if_pos hc]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hlam' : (xiGammaEulerPrimitiveLogFrequency pe : ℂ) ≠ 0 := by
      exact_mod_cast (xiGammaEulerPrimitiveLogFrequency_pos pe).ne'
    push_cast
    field_simp [hc', hlam']
    ring
  simp only [neg_mul] at hscalar
  convert congrArg (fun z : ℂ => z • routePPrimitiveBurnolBaseField pe) hscalar using 1 <;> module

/-- Every original coefficient vector has a native strong right derivative. -/
theorem tendsto_burnolBaseNativeDifferenceQuotient (x : Source) :
    Tendsto (fun c => burnolBaseNativeDifferenceQuotient c x)
      (𝓝[>] (0 : ℝ)) (𝓝 (-burnolBaseFirstJetSynthesis x)) := by
  have h := ((burnolBaseFirstJetSynthesis.continuous.tendsto x).comp
    (tendsto_burnolFirstJetAverage x)).neg
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [burnolBaseNativeDifferenceQuotient_eq hc]
  rfl

theorem isCompactOperator_burnolBaseNativeDifferenceQuotient (c : ℝ) :
    IsCompactOperator (burnolBaseNativeDifferenceQuotient c) := by
  change IsCompactOperator (fun x : Source => ((c⁻¹ : ℝ) : ℂ) •
    (burnolWeightedShift c.toNNReal (burnolBaseCoefficientSynthesis x) - burnolBaseCoefficientSynthesis x))
  exact ((isCompactOperator_burnolBaseCoefficientSynthesis.clm_comp
    (burnolWeightedShift c.toNNReal)).sub isCompactOperator_burnolBaseCoefficientSynthesis).smul
      ((c⁻¹ : ℝ) : ℂ)

/-- The right derivative exists strongly but in no operator-norm limit. -/
theorem not_tendsto_burnolBaseNativeDifferenceQuotient (L : Source →L[ℂ] routePBurnolHalfLineL2) :
    ¬ Tendsto burnolBaseNativeDifferenceQuotient (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  intro hL
  have heq : L = -burnolBaseFirstJetSynthesis := by
    apply ContinuousLinearMap.ext
    intro x
    have happ : Continuous (fun T : Source →L[ℂ] routePBurnolHalfLineL2 => T x) := by fun_prop
    exact tendsto_nhds_unique ((happ.tendsto L).comp hL)
      (tendsto_burnolBaseNativeDifferenceQuotient x)
  have hc := isCompactOperator_of_tendsto hL
    (Eventually.of_forall isCompactOperator_burnolBaseNativeDifferenceQuotient)
  rw [heq] at hc
  apply not_isCompactOperator_burnolBaseFirstJetSynthesis
  have hneg : IsCompactOperator (fun x : Source => -(-burnolBaseFirstJetSynthesis x)) := hc.neg
  simpa only [neg_neg] using hneg

local instance : MeasurableSpace RoutePPrimitiveIndex := ⊤
local notation "CSource" => Lp ℂ 2 (Measure.count : Measure RoutePPrimitiveIndex)

/-- The admitted first jet on the literal counting-measure source. -/
def burnolBaseNativeFirstJet : CSource →L[ℂ] routePBurnolHalfLineL2 :=
  burnolBaseFirstJetSynthesis ∘L burnolBaseCountCoordinates.toLinearIsometry.toContinuousLinearMap

/-- The native difference quotient of the existing Bochner synthesis itself. -/
def burnolBaseOriginalDifferenceQuotient (c : ℝ) : CSource →L[ℂ] routePBurnolHalfLineL2 :=
  ((c⁻¹ : ℝ) : ℂ) •
    (burnolWeightedShift c.toNNReal ∘L routePPrimitiveBurnolBaseSynthesis -
      routePPrimitiveBurnolBaseSynthesis)

/-- Full original-source generator admission; no analytic domain hypothesis is assumed. -/
theorem tendsto_burnolBaseOriginalDifferenceQuotient (f : CSource) :
    Tendsto (fun c => burnolBaseOriginalDifferenceQuotient c f)
      (𝓝[>] (0 : ℝ)) (𝓝 (-burnolBaseNativeFirstJet f)) := by
  have h := tendsto_burnolBaseNativeDifferenceQuotient (burnolBaseCountCoordinates f)
  simpa [burnolBaseOriginalDifferenceQuotient, burnolBaseNativeDifferenceQuotient,
    burnolBaseCoefficientSynthesis_countCoordinates, burnolBaseNativeFirstJet] using h

theorem not_isCompactOperator_burnolBaseNativeFirstJet :
    ¬ IsCompactOperator burnolBaseNativeFirstJet := by
  intro h
  have hc := h.comp_clm burnolBaseCountCoordinates.symm.toLinearIsometry.toContinuousLinearMap
  have heq : burnolBaseNativeFirstJet ∘L
      burnolBaseCountCoordinates.symm.toLinearIsometry.toContinuousLinearMap =
        burnolBaseFirstJetSynthesis := by
    ext x
    simp [burnolBaseNativeFirstJet]
  change IsCompactOperator (burnolBaseNativeFirstJet ∘L
    burnolBaseCountCoordinates.symm.toLinearIsometry.toContinuousLinearMap) at hc
  rw [heq] at hc
  exact not_isCompactOperator_burnolBaseFirstJetSynthesis hc

/-- Operator-norm differentiation fails for the literal original source, not only its coordinates. -/
theorem not_tendsto_burnolBaseOriginalDifferenceQuotient
    (L : CSource →L[ℂ] routePBurnolHalfLineL2) :
    ¬ Tendsto burnolBaseOriginalDifferenceQuotient (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  intro hL
  have heq : L = -burnolBaseNativeFirstJet := by
    apply ContinuousLinearMap.ext
    intro f
    have happ : Continuous (fun T : CSource →L[ℂ] routePBurnolHalfLineL2 => T f) := by fun_prop
    exact tendsto_nhds_unique ((happ.tendsto L).comp hL)
      (tendsto_burnolBaseOriginalDifferenceQuotient f)
  have hA := routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt.isCompactOperator
  have hcompact (c : ℝ) : IsCompactOperator (burnolBaseOriginalDifferenceQuotient c) := by
    change IsCompactOperator (fun f : CSource => ((c⁻¹ : ℝ) : ℂ) •
      (burnolWeightedShift c.toNNReal (routePPrimitiveBurnolBaseSynthesis f) -
        routePPrimitiveBurnolBaseSynthesis f))
    exact ((hA.clm_comp (burnolWeightedShift c.toNNReal)).sub hA).smul ((c⁻¹ : ℝ) : ℂ)
  have hc := isCompactOperator_of_tendsto hL (Eventually.of_forall hcompact)
  rw [heq] at hc
  apply not_isCompactOperator_burnolBaseNativeFirstJet
  have hneg : IsCompactOperator (fun f : CSource => -(-burnolBaseNativeFirstJet f)) := hc.neg
  simpa only [neg_neg] using hneg

end
end RHTower
