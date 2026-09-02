import GaloisForLFunctions.RHTower.RouteECofactorParityBalance

/-!
# Exact dyadic-slice count for cofactor-amplified Route E

The cofactor-amplified card uses distinguished-prime exponents in the literal interval
`[1.1 - 10⁻⁴, 1.1]`.  Its dyadic slices are indexed by the integral powers of two lying between
`(log U)^1.0999` and `2 (log U)^1.1`.

This module keeps the ceiling and floor defining that finite index set and proves equation `(6a)`
with its exact leading constant: after division by `log log U`, the number of slices tends to
`1 / (10000 log 2)`.
-/

open Filter Topology

namespace RHTower.CofactorParity

noncomputable section

/-- Lower endpoint `(log U)^(1.1 - 10⁻⁴)` of the card's distinguished-prime band. -/
def cofactorAmplifiedSliceLower (U : ℝ) : ℝ :=
  (Real.log U) ^ ((10999 : ℝ) / 10000)

/-- Upper endpoint `2 (log U)^1.1` of the card's distinguished-prime band. -/
def cofactorAmplifiedSliceUpper (U : ℝ) : ℝ :=
  2 * (Real.log U) ^ ((11 : ℝ) / 10)

/-- Exact integer set of dyadic exponents whose powers of two lie in the card's band. -/
def cofactorAmplifiedDyadicSlices (U : ℝ) : Finset ℤ :=
  Finset.Icc
    ⌈Real.log (cofactorAmplifiedSliceLower U) / Real.log 2⌉
    ⌊Real.log (cofactorAmplifiedSliceUpper U) / Real.log 2⌋

private def cofactorAmplifiedSliceSpan (U : ℝ) : ℝ :=
  Real.log (cofactorAmplifiedSliceUpper U) / Real.log 2 -
    Real.log (cofactorAmplifiedSliceLower U) / Real.log 2

private theorem tendsto_cofactorAmplifiedSliceSpan_div_logLog :
    Tendsto (fun U : ℝ =>
      cofactorAmplifiedSliceSpan U / Real.log (Real.log U)) atTop
      (𝓝 (((1 : ℝ) / 10000) / Real.log 2)) := by
  have hLL : Tendsto (fun U : ℝ => Real.log (Real.log U)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hinv : Tendsto (fun U : ℝ => (1 : ℝ) / Real.log (Real.log U)) atTop (𝓝 0) :=
    hLL.const_div_atTop 1
  have hconst : Tendsto (fun _U : ℝ => ((1 : ℝ) / 10000) / Real.log 2) atTop
      (𝓝 (((1 : ℝ) / 10000) / Real.log 2)) := tendsto_const_nhds
  have hlim := hconst.add hinv
  simpa only [add_zero] using hlim.congr' (by
    filter_upwards [eventually_gt_atTop (Real.exp 1)] with U hU
    have hU1 : 1 < U := lt_trans (by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)) hU
    have hlogU : 0 < Real.log U := Real.log_pos hU1
    have hlogU1 : 1 < Real.log U := (Real.lt_log_iff_exp_lt (by positivity)).2 hU
    have hLL0 : 0 < Real.log (Real.log U) := Real.log_pos hlogU1
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    rw [cofactorAmplifiedSliceSpan, cofactorAmplifiedSliceUpper,
      cofactorAmplifiedSliceLower,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (ne_of_gt (Real.rpow_pos_of_pos hlogU ((11 : ℝ) / 10))),
      Real.log_rpow hlogU, Real.log_rpow hlogU]
    field_simp
    ring)

private theorem tendsto_cofactorAmplifiedSliceSpan_atTop :
    Tendsto cofactorAmplifiedSliceSpan atTop atTop := by
  have htarget : 0 < (((1 : ℝ) / 10000) / Real.log 2) := by positivity
  have hhalf : 0 < (((1 : ℝ) / 10000) / Real.log 2) / 2 := half_pos htarget
  have hratio :=
    tendsto_cofactorAmplifiedSliceSpan_div_logLog.eventually_const_lt (half_lt_self htarget)
  have hLL : Tendsto (fun U : ℝ => Real.log (Real.log U)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  rw [tendsto_atTop]
  intro b
  filter_upwards [hratio, hLL.eventually_ge_atTop 1,
    (hLL.const_mul_atTop hhalf).eventually_ge_atTop b] with U hratio hLL1 hbound
  have heq : cofactorAmplifiedSliceSpan U =
      (cofactorAmplifiedSliceSpan U / Real.log (Real.log U)) * Real.log (Real.log U) := by
    field_simp
  rw [heq]
  nlinarith

private theorem tendsto_cofactorAmplifiedSliceRoundingError :
    Tendsto (fun U : ℝ =>
      ((cofactorAmplifiedDyadicSlices U).card : ℝ) / Real.log (Real.log U) -
        cofactorAmplifiedSliceSpan U / Real.log (Real.log U)) atTop (𝓝 0) := by
  have hLL : Tendsto (fun U : ℝ => Real.log (Real.log U)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hupper : Tendsto (fun U : ℝ => (1 : ℝ) / Real.log (Real.log U)) atTop (𝓝 0) :=
    hLL.const_div_atTop 1
  refine squeeze_zero_norm' ?_ hupper
  filter_upwards [tendsto_cofactorAmplifiedSliceSpan_atTop.eventually_ge_atTop 2,
      hLL.eventually_ge_atTop 1] with U hspan hLL1
  let α : ℝ := Real.log (cofactorAmplifiedSliceLower U) / Real.log 2
  let β : ℝ := Real.log (cofactorAmplifiedSliceUpper U) / Real.log 2
  have hspanEq : cofactorAmplifiedSliceSpan U = β - α := by
    simp only [cofactorAmplifiedSliceSpan, α, β]
  have hfloorLo : β - 1 < (⌊β⌋ : ℝ) := Int.sub_one_lt_floor β
  have hfloorHi : (⌊β⌋ : ℝ) ≤ β := Int.floor_le β
  have hceilLo : α ≤ (⌈α⌉ : ℝ) := Int.le_ceil α
  have hceilHi : (⌈α⌉ : ℝ) < α + 1 := Int.ceil_lt_add_one α
  have horder : ⌈α⌉ ≤ ⌊β⌋ := by
    have : (⌈α⌉ : ℝ) < (⌊β⌋ : ℝ) := by rw [hspanEq] at hspan; linarith
    exact_mod_cast this.le
  have hcard : ((cofactorAmplifiedDyadicSlices U).card : ℝ) =
      (⌊β⌋ : ℝ) + 1 - (⌈α⌉ : ℝ) := by
    rw [cofactorAmplifiedDyadicSlices, Int.card_Icc]
    change (((⌊β⌋ + 1 - ⌈α⌉).toNat : ℕ) : ℝ) = _
    have hnonneg : 0 ≤ ⌊β⌋ + 1 - ⌈α⌉ := by omega
    have hz := Int.toNat_of_nonneg hnonneg
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) hz
  have herr :
      |((cofactorAmplifiedDyadicSlices U).card : ℝ) - cofactorAmplifiedSliceSpan U| ≤ 1 := by
    rw [hcard, hspanEq]
    rw [abs_le]
    constructor <;> linarith
  have hLL0 : 0 < Real.log (Real.log U) := by linarith
  rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hLL0]
  exact div_le_div_of_nonneg_right herr hLL0.le

/-- **Equation `(6a)` at the card's literal band.**  The exact floor-and-ceiling dyadic-slice
count is asymptotic to `(10⁻⁴ / log 2) log log U`. -/
theorem tendsto_card_cofactorAmplifiedDyadicSlices_div_logLog :
    Tendsto (fun U : ℝ =>
      ((cofactorAmplifiedDyadicSlices U).card : ℝ) / Real.log (Real.log U)) atTop
      (𝓝 (((1 : ℝ) / 10000) / Real.log 2)) := by
  have h := tendsto_cofactorAmplifiedSliceSpan_div_logLog.add
    tendsto_cofactorAmplifiedSliceRoundingError
  simpa only [add_zero] using h.congr' (Filter.Eventually.of_forall fun U => by ring)

end


end RHTower.CofactorParity
