import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralPrimitiveIdentity

/-!
# No stable primitive below the cut

Below the stability cut the finite-part primitive is not annihilated in the future.  Testing with
the constant chart, its transported value is

`c (∫₀¹ (e^{-Vs} − 1) s^{a-1} ds + 1/a)`,

whose integral diverges to `−∞`: on `(1/V, 1)` the source cochain is bounded above by `e^{-1} − 1`,
and there the weight dominates `s^{-1}`, whose integral is `log V`.  Since two primitives differ by
a fixed vector, no primitive is stable when `a ≤ 0`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

/-- The constant chart. -/
def ChartFun.const (r : ℝ) : ChartFun where
  toFun := fun _ => r
  continuousOn' := continuousOn_const
  exists_bound := ⟨|r|, abs_nonneg r, fun _ _ => le_refl _, fun s hs => by
    simp only [sub_self, abs_zero]
    exact mul_nonneg (abs_nonneg r) hs.1⟩

@[simp] theorem ChartFun.const_toFun (r s : ℝ) : (ChartFun.const r).toFun s = r := rfl

/-- The source pairing against the constant chart. -/
def cutIntegral (a V : ℝ) : ℝ := ∫ s in Ioo (0 : ℝ) 1, laplaceCochain V s * s ^ (a - 1)

theorem integrableOn_cutIntegrand {a V : ℝ} (ha : -1 < a) (hV : 0 ≤ V) :
    IntegrableOn (fun s : ℝ => laplaceCochain V s * s ^ (a - 1)) (Ioo 0 1) := by
  have := integrableOn_source_pairing (ChartFun.const 1) ha hV
  refine this.congr_fun (fun s _ => ?_) measurableSet_Ioo
  simp

theorem integrableOn_rpow_Ioo_of_pos {a c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => s ^ (a - 1)) (Ioo c 1) := by
  refine ContinuousOn.integrableOn_compact isCompact_Icc ?_ |>.mono_set Ioo_subset_Icc_self
  exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hc hx.1))

/-- On the tail interval the weight dominates the inverse. -/
theorem inv_le_rpow_of_nonpos {a s : ℝ} (ha : a ≤ 0) (hs : 0 < s) (hs1 : s ≤ 1) :
    s⁻¹ ≤ s ^ (a - 1) := by
  rw [← Real.rpow_neg_one s]
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)

theorem integral_inv_Ioo {c : ℝ} (hc : 0 < c) (h1 : c ≤ 1) :
    (∫ s in Ioo c 1, s⁻¹) = Real.log (1 / c) := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h1]
  exact integral_inv_of_pos hc zero_lt_one

/-- **The cut integral diverges below the cut.** -/
theorem cutIntegral_le {a : ℝ} (ha : -1 < a) (ha0 : a ≤ 0) {V : ℝ} (hV : 1 ≤ V) :
    cutIntegral a V ≤ (Real.exp (-1) - 1) * Real.log V := by
  have hV0 : (0 : ℝ) < V := lt_of_lt_of_le zero_lt_one hV
  set c : ℝ := 1 / V with hcdef
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hcdef, div_le_one hV0]
    exact hV
  have hint : IntegrableOn (fun s : ℝ => laplaceCochain V s * s ^ (a - 1)) (Ioo 0 1) :=
    integrableOn_cutIntegrand ha hV0.le
  have hneg : ∀ s ∈ Ioo (0 : ℝ) 1, laplaceCochain V s * s ^ (a - 1) ≤ 0 := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have hw : (0 : ℝ) < s ^ (a - 1) := Real.rpow_pos_of_pos hs0 _
    have hb : laplaceCochain V s ≤ 0 := by
      have : Real.exp (-(V * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      simp only [laplaceCochain]
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg hb hw.le
  -- restrict to the tail interval
  have hstep1 : cutIntegral a V ≤ ∫ s in Ioo c 1, laplaceCochain V s * s ^ (a - 1) := by
    have hsubLE : (Ioo c 1 : Set ℝ) ≤ Ioo (0 : ℝ) 1 := fun x hx => ⟨lt_trans hc0 hx.1, hx.2⟩
    have hmono := setIntegral_mono_set (f := fun s : ℝ => -(laplaceCochain V s * s ^ (a - 1)))
      hint.neg ?_ hsubLE.eventuallyLE
    · rw [integral_neg, integral_neg] at hmono
      show (∫ s in Ioo (0 : ℝ) 1, laplaceCochain V s * s ^ (a - 1)) ≤ _
      exact neg_le_neg_iff.1 hmono
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      simpa using hneg s hs
  -- bound the tail integrand
  have hstep2 : (∫ s in Ioo c 1, laplaceCochain V s * s ^ (a - 1)) ≤
      ∫ s in Ioo c 1, (Real.exp (-1) - 1) * s⁻¹ := by
    refine setIntegral_mono_on (hint.mono_set fun x hx => ⟨lt_trans hc0 hx.1, hx.2⟩) ?_
      measurableSet_Ioo ?_
    · have hI : IntegrableOn (fun s : ℝ => s⁻¹) (Ioo c 1) := by
        refine ContinuousOn.integrableOn_compact isCompact_Icc ?_ |>.mono_set Ioo_subset_Icc_self
        exact ContinuousOn.inv₀ continuousOn_id fun x hx => ne_of_gt (lt_of_lt_of_le hc0 hx.1)
      exact hI.const_mul _
    · intro s hs
      have hs0 : (0 : ℝ) < s := lt_trans hc0 hs.1
      have hs1 : s ≤ 1 := hs.2.le
      have hw : (0 : ℝ) < s ^ (a - 1) := Real.rpow_pos_of_pos hs0 _
      have hVs : (1 : ℝ) ≤ V * s := by
        rw [hcdef] at hs
        have := hs.1
        rw [div_lt_iff₀ hV0] at this
        nlinarith
      have hexp : Real.exp (-(V * s)) ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.2
        linarith
      have hbneg : laplaceCochain V s ≤ Real.exp (-1) - 1 := by
        simp only [laplaceCochain]
        linarith
      have hcneg : Real.exp (-1) - 1 < 0 := by
        have := Real.exp_lt_one_iff.2 (by norm_num : (-1 : ℝ) < 0)
        linarith
      have hinv : s⁻¹ ≤ s ^ (a - 1) := inv_le_rpow_of_nonpos ha0 hs0 hs1
      calc laplaceCochain V s * s ^ (a - 1) ≤ (Real.exp (-1) - 1) * s ^ (a - 1) :=
            mul_le_mul_of_nonneg_right hbneg hw.le
        _ ≤ (Real.exp (-1) - 1) * s⁻¹ := by
            have := mul_le_mul_of_nonpos_left hinv hcneg.le
            linarith
  have hval : (∫ s in Ioo c 1, (Real.exp (-1) - 1) * s⁻¹) = (Real.exp (-1) - 1) * Real.log V := by
    rw [integral_const_mul, integral_inv_Ioo hc0 hc1, hcdef]
    congr 1
    rw [one_div_one_div]
  linarith [hstep1, hstep2, hval.le, hval.ge]

/-- **No stable primitive below the cut.**  The transported finite part of the constant chart tends
to `−∞` for every `a ≤ 0`. -/
theorem tendsto_cutIntegral_atBot {a : ℝ} (ha : -1 < a) (ha0 : a ≤ 0) :
    Tendsto (fun V : ℝ => cutIntegral a V) atTop atBot := by
  have hcneg : Real.exp (-1) - 1 < 0 := by
    have := Real.exp_lt_one_iff.2 (by norm_num : (-1 : ℝ) < 0)
    linarith
  have hlog : Tendsto (fun V : ℝ => (Real.exp (-1) - 1) * Real.log V) atTop atBot := by
    have hpos : 0 < -(Real.exp (-1) - 1) := by linarith
    have h1 : Tendsto (fun V : ℝ => -(Real.exp (-1) - 1) * Real.log V) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hpos Real.tendsto_log_atTop
    have h2 := tendsto_neg_atTop_atBot.comp h1
    refine h2.congr fun V => ?_
    show -(-(Real.exp (-1) - 1) * Real.log V) = _
    ring
  refine tendsto_atBot_mono' _ ?_ hlog
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with V hV
  exact cutIntegral_le ha ha0 hV

/-- Below the cut the transported finite part of the constant chart is the cut integral shifted by
the fixed finite-part constant. -/
theorem finitePart_const_transport (c : ℝ) {a V : ℝ} (ha0 : a ≤ 0) (hV : 0 ≤ V) :
    finitePart c a (ChartFun.transport V hV (ChartFun.const 1)) =
      c * (cutIntegral a V + (if a = 0 then 0 else 1 / a)) := by
  rw [finitePart, if_neg (not_lt.2 ha0)]
  congr 2
  · refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
    simp only [ChartFun.transport_toFun, ChartFun.const_toFun, laplaceCochain, mul_one, mul_zero,
      neg_zero, Real.exp_zero]
  · rw [ChartFun.transport_zero, ChartFun.const_toFun]

/-- **No stable primitive below the cut.**  For a nonzero weight constant the transported finite
part of the constant chart has no limit at all, so it cannot tend to zero. -/
theorem not_tendsto_finitePart_of_nonpos {c : ℝ} (hc : c ≠ 0) {a : ℝ} (ha : -1 < a) (ha0 : a ≤ 0)
    (L : ℝ) :
    ¬ Tendsto (fun V : ℝ => c * (cutIntegral a V + (if a = 0 then 0 else 1 / a))) atTop (𝓝 L) := by
  have hAB : Tendsto (fun V : ℝ => cutIntegral a V + (if a = 0 then 0 else 1 / a)) atTop atBot :=
    Filter.tendsto_atBot_add_const_right _ _ (tendsto_cutIntegral_atBot ha ha0)
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have : Tendsto (fun V : ℝ => c * (cutIntegral a V + (if a = 0 then 0 else 1 / a))) atTop
        atTop := Filter.Tendsto.const_mul_atBot_of_neg hneg hAB
    exact not_tendsto_nhds_of_tendsto_atTop this L
  · have : Tendsto (fun V : ℝ => c * (cutIntegral a V + (if a = 0 then 0 else 1 / a))) atTop
        atBot := Filter.Tendsto.const_mul_atBot hpos hAB
    exact not_tendsto_nhds_of_tendsto_atBot this L

end

end GaloisForLFunctions.HTGeometry.Interfinity
