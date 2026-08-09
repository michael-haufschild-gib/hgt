import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralFinitePart

/-!
# The finite-part primitive identity

The finite part

* `a > 0`:  `η_a(h) = c ∫₀¹ h(s) s^{a-1} ds`,
* `a ≤ 0`:  `η_a(h) = c (∫₀¹ (h(s) − h(0)) s^{a-1} ds + h(0)/a)`, the constant being dropped at
  `a = 0`,

is a primitive of the source cochain at every admissible observer:

`η_a(e^{-V·}h) − η_a(h) = c ∫₀¹ (e^{-Vs} − 1) h(s) s^{a-1} ds`.

The divergent constants cancel because the transported chart has the same value at the origin.
Above the cut the primitive is annihilated in the future: for `a > 0` the transported finite part
tends to zero.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

/-- The finite-part primitive `η_a`. -/
def finitePart (c a : ℝ) (h : ChartFun) : ℝ :=
  if 0 < a then c * ∫ s in Ioo (0 : ℝ) 1, h.toFun s * s ^ (a - 1)
  else c * ((∫ s in Ioo (0 : ℝ) 1, (h.toFun s - h.toFun 0) * s ^ (a - 1)) +
    (if a = 0 then 0 else h.toFun 0 / a))

/-- The pairing of the source cochain with a test vector in the chart. -/
def sourcePairing (c a V : ℝ) (h : ChartFun) : ℝ :=
  c * ∫ s in Ioo (0 : ℝ) 1, laplaceCochain V s * h.toFun s * s ^ (a - 1)

/-- **The finite part is a primitive of the source cochain.** -/
theorem finitePart_transport_sub (c : ℝ) {a V : ℝ} (ha : -1 < a) (hV : 0 ≤ V) (h : ChartFun) :
    finitePart c a (ChartFun.transport V hV h) - finitePart c a h = sourcePairing c a V h := by
  rcases lt_or_ge 0 a with hpos | hnonpos
  · have hEq : (∫ s in Ioo (0 : ℝ) 1, (ChartFun.transport V hV h).toFun s * s ^ (a - 1)) -
        (∫ s in Ioo (0 : ℝ) 1, h.toFun s * s ^ (a - 1)) =
        ∫ s in Ioo (0 : ℝ) 1, laplaceCochain V s * h.toFun s * s ^ (a - 1) := by
      rw [← integral_sub (integrableOn_chart_mul_rpow (ChartFun.transport V hV h) hpos)
        (integrableOn_chart_mul_rpow h hpos)]
      refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
      simp only [ChartFun.transport_toFun, laplaceCochain]
      ring
    rw [finitePart, finitePart, if_pos hpos, if_pos hpos, sourcePairing]
    linear_combination c * hEq
  · have hEq : (∫ s in Ioo (0 : ℝ) 1, ((ChartFun.transport V hV h).toFun s -
          (ChartFun.transport V hV h).toFun 0) * s ^ (a - 1)) -
        (∫ s in Ioo (0 : ℝ) 1, (h.toFun s - h.toFun 0) * s ^ (a - 1)) =
        ∫ s in Ioo (0 : ℝ) 1, laplaceCochain V s * h.toFun s * s ^ (a - 1) := by
      rw [← integral_sub (integrableOn_chart_sub_mul_rpow (ChartFun.transport V hV h) ha)
        (integrableOn_chart_sub_mul_rpow h ha)]
      refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
      simp only [ChartFun.transport_toFun, laplaceCochain, mul_zero, neg_zero, Real.exp_zero,
        one_mul]
      ring
    have hK : (if a = 0 then (0 : ℝ) else (ChartFun.transport V hV h).toFun 0 / a) =
        (if a = 0 then (0 : ℝ) else h.toFun 0 / a) := by
      rw [ChartFun.transport_zero]
    rw [finitePart, finitePart, if_neg (not_lt.2 hnonpos), if_neg (not_lt.2 hnonpos), hK,
      sourcePairing]
    linear_combination c * hEq

/-! ## Forward annihilation above the cut -/

/-- Above the cut the transported finite part is an ordinary integral. -/
theorem finitePart_transport_of_pos (c : ℝ) {a V : ℝ} (ha : 0 < a) (hV : 0 ≤ V) (h : ChartFun) :
    finitePart c a (ChartFun.transport V hV h) =
      c * ∫ s in Ioo (0 : ℝ) 1, Real.exp (-(V * s)) * h.toFun s * s ^ (a - 1) := by
  rw [finitePart, if_pos ha]
  congr 1

/-- **Forward stability above the cut.** -/
theorem tendsto_transported_finitePart (c : ℝ) {a : ℝ} (ha : 0 < a) (h : ChartFun) :
    Tendsto (fun V : ℝ =>
        c * ∫ s in Ioo (0 : ℝ) 1, Real.exp (-(V * s)) * h.toFun s * s ^ (a - 1))
      atTop (𝓝 0) := by
  obtain ⟨B, hB0, hBsize, -⟩ := h.exists_bound
  have hdom : IntegrableOn (fun s : ℝ => B * s ^ (a - 1)) (Ioo 0 1) :=
    (integrableOn_rpow_of_neg_one_lt (by linarith)).const_mul _
  have hmain : Tendsto
      (fun V : ℝ => ∫ s in Ioo (0 : ℝ) 1, Real.exp (-(V * s)) * h.toFun s * s ^ (a - 1))
      atTop (𝓝 (∫ _s in Ioo (0 : ℝ) 1, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => B * s ^ (a - 1)) ?_ ?_
      hdom ?_
    · refine Eventually.of_forall fun V => ?_
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ContinuousOn.mul (ContinuousOn.mul ?_ (h.continuousOn'.mono Ioo_subset_Icc_self)) ?_
      · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
      · exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx.1)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with V hV
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hs0 : (0 : ℝ) < s := hs.1
      have hw : (0 : ℝ) < s ^ (a - 1) := Real.rpow_pos_of_pos hs0 _
      have hexp0 : (0 : ℝ) < Real.exp (-(V * s)) := Real.exp_pos _
      have hexp1 : Real.exp (-(V * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hw, abs_of_pos hexp0]
      have hb := hBsize s ⟨hs0.le, hs.2.le⟩
      have : Real.exp (-(V * s)) * |h.toFun s| ≤ B := by
        nlinarith [abs_nonneg (h.toFun s)]
      exact mul_le_mul_of_nonneg_right this hw.le
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hs0 : (0 : ℝ) < s := hs.1
      have hneg : Tendsto (fun V : ℝ => -(V * s)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hs0)
      have hexp : Tendsto (fun V : ℝ => Real.exp (-(V * s))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hneg
      have := (hexp.mul_const (h.toFun s)).mul_const (s ^ (a - 1))
      simpa using this
  rw [integral_zero] at hmain
  simpa using hmain.const_mul c

end

end GaloisForLFunctions.HTGeometry.Interfinity
