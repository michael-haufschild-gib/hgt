import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaIntervalRemainder

/-!
# Integrated Gamma interactions and endpoint losses

The actual interval kernel splits into a nonnegative averaging defect and its
far-end charge. Strictly separated rectangles admit endpoint bounds; touching
rectangles retain the averaging defect and a finite width-weighted boundary reading.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals

/-- The actual nonnegative Gamma interaction of two intervals. -/
def gammaIntervalKernel (a b c d : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, ENNReal.ofReal (archLevyDensity |y - x|)

/-- Loss from replacing an integrated interaction by its farthest-endpoint conductance. -/
def gammaIntervalPairDefect (a b c d : ℝ) : ℝ≥0∞ :=
  gammaIntervalKernel a b c d -
    ENNReal.ofReal ((b - a) * (d - c) * archLevyDensity (max (d - a) (b - c)))

/-- The integrated kernel is symmetric under exchanging the intervals. -/
theorem gammaIntervalKernel_comm (a b c d : ℝ) :
    gammaIntervalKernel a b c d = gammaIntervalKernel c d a b := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (archLevyDensity |p.2 - p.1|)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_archLevyDensity.comp (measurable_snd.sub measurable_fst).abs)
  unfold gammaIntervalKernel
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro x
  rw [abs_sub_comm x y]

/-- Farthest-endpoint replacement loses the same amount in both orientations. -/
theorem gammaIntervalPairDefect_comm (a b c d : ℝ) :
    gammaIntervalPairDefect a b c d = gammaIntervalPairDefect c d a b := by
  unfold gammaIntervalPairDefect
  rw [gammaIntervalKernel_comm a b c d, max_comm (d - a) (b - c)]
  congr 2
  ring

/-- A common logarithmic translation preserves the actual two-interval interaction. -/
theorem gammaIntervalKernel_translate (s a b c d : ℝ) :
    gammaIntervalKernel (s + a) (s + b) (s + c) (s + d) =
      gammaIntervalKernel a b c d := by
  have hpre (u v : ℝ) : (fun t : ℝ => s + t) ⁻¹' Ioo (s + u) (s + v) = Ioo u v := by
    ext t
    change (s + u < s + t ∧ s + t < s + v) ↔ (u < t ∧ t < v)
    simp only [add_lt_add_iff_left]
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (archLevyDensity |p.2 - p.1|)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_archLevyDensity.comp (measurable_snd.sub measurable_fst).abs)
  have houter := (measurePreserving_add_left (volume : Measure ℝ) s).setLIntegral_comp_preimage
    (s := Ioo (s + a) (s + b))
    (f := fun x : ℝ => ∫⁻ y in Ioo (s + c) (s + d),
      ENNReal.ofReal (archLevyDensity |y - x|)) measurableSet_Ioo hm.lintegral_prod_right'
  rw [hpre] at houter
  unfold gammaIntervalKernel
  rw [← houter]
  apply lintegral_congr
  intro x
  have hinner := (measurePreserving_add_left (volume : Measure ℝ) s).setLIntegral_comp_preimage
    (s := Ioo (s + c) (s + d))
    (f := fun y : ℝ => ENNReal.ofReal (archLevyDensity |y - (s + x)|)) measurableSet_Ioo
    (ENNReal.measurable_ofReal.comp
      (measurable_archLevyDensity.comp (measurable_id.sub measurable_const).abs))
  rw [hpre] at hinner
  rw [← hinner]
  apply lintegral_congr
  intro y
  rw [show s + y - (s + x) = y - x by ring]

/-- Endpoint replacement loss also survives common translation exactly. -/
theorem gammaIntervalPairDefect_translate (s a b c d : ℝ) :
    gammaIntervalPairDefect (s + a) (s + b) (s + c) (s + d) =
      gammaIntervalPairDefect a b c d := by
  unfold gammaIntervalPairDefect
  rw [gammaIntervalKernel_translate]
  simp only [add_sub_add_left_eq_sub]

/-- Exact averaging decomposition against any set, including the full exterior. -/
theorem gamma_interval_set_kernel_eq_defect_add_far (a b : ℝ) (F : Set ℝ) :
    (∫⁻ x in Ioo a b, ∫⁻ y in F, ENNReal.ofReal (archLevyDensity |y - x|)) =
      (∫⁻ x in Ioo a b, ∫⁻ y in F, gammaIntervalRowDefect a b x y) +
        ENNReal.ofReal (b - a) * (∫⁻ y in F, gammaFarCharge a b y) := by
  calc
    _ = ∫⁻ x in Ioo a b, ∫⁻ y in F,
        (gammaIntervalRowDefect a b x y + gammaFarCharge a b y) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      apply lintegral_congr
      intro y
      exact (tsub_add_cancel_of_le (gammaFarCharge_le_actual hx y)).symm
    _ = (∫⁻ x in Ioo a b, ∫⁻ y in F, gammaIntervalRowDefect a b x y) +
        (∫⁻ _x in Ioo a b, ∫⁻ y in F, gammaFarCharge a b y) := by
      simp_rw [lintegral_add_right _ (measurable_gammaFarCharge a b)]
      exact lintegral_add_right _ measurable_const
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, mul_comm]

/-- Exact averaging decomposition, without any gap assumption. -/
theorem gammaIntervalKernel_eq_defect_add_far (a b c d : ℝ) :
    gammaIntervalKernel a b c d =
      (∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, gammaIntervalRowDefect a b x y) +
        ENNReal.ofReal (b - a) * (∫⁻ y in Ioo c d, gammaFarCharge a b y) :=
  gamma_interval_set_kernel_eq_defect_add_far a b (Ioo c d)

/-- Across ordered disjoint intervals, the far charge is bounded by the source-width reading. -/
theorem gammaIntervalKernel_le_defect_add_width {a b c d : ℝ} (hab : a < b)
    (hsep : b ≤ c ∨ d ≤ a) :
    gammaIntervalKernel a b c d ≤
      (∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d, gammaIntervalRowDefect a b x y) +
        ENNReal.ofReal ((b - a) * (d - c) * archLevyDensity (b - a)) := by
  have hw : 0 < b - a := sub_pos.mpr hab
  have hk : 0 ≤ archLevyDensity (b - a) := (archLevyDensity_pos hw).le
  have hint : (∫⁻ y in Ioo c d, gammaFarCharge a b y) ≤
      ENNReal.ofReal ((d - c) * archLevyDensity (b - a)) := by
    calc
      _ ≤ ∫⁻ _y in Ioo c d, ENNReal.ofReal (archLevyDensity (b - a)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun y hy => ?_
        rcases hsep with hr | hl
        · have hyb : b < y := hr.trans_lt hy.1
          have hyn : y ∉ Ioo a b := fun h => (not_lt_of_ge hyb.le) h.2
          rw [gammaFarCharge, if_neg hyn, max_eq_left (by linarith only [hab, hyb])]
          exact ENNReal.ofReal_le_ofReal (strictAntiOn_archLevyDensity.antitoneOn hw
            (show 0 < y - a by linarith only [hab, hyb]) (by linarith only [hyb]))
        · have hya : y < a := hy.2.trans_le hl
          have hyn : y ∉ Ioo a b := fun h => (not_lt_of_ge hya.le) h.1
          rw [gammaFarCharge, if_neg hyn, max_eq_right (by linarith only [hab, hya])]
          exact ENNReal.ofReal_le_ofReal (strictAntiOn_archLevyDensity.antitoneOn hw
            (show 0 < b - y by linarith only [hab, hya]) (by linarith only [hya]))
      _ = _ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo,
          ← ENNReal.ofReal_mul hk]
        congr 1
        ring
  rw [gammaIntervalKernel_eq_defect_add_far]
  refine add_le_add le_rfl ((mul_le_mul_right hint (ENNReal.ofReal (b - a))).trans_eq ?_)
  rw [← ENNReal.ofReal_mul hw.le]
  congr 1
  ring

/-- A strictly separated rectangle is bounded by its nearest-endpoint kernel. -/
theorem gammaIntervalKernel_le_near {a b c d : ℝ} (hab : a < b) (hsep : b < c) (hcd : c < d) :
    gammaIntervalKernel a b c d ≤
      ENNReal.ofReal ((b - a) * (d - c) * archLevyDensity (c - b)) := by
  have hw : 0 < b - a := sub_pos.mpr hab
  have hv : 0 < d - c := sub_pos.mpr hcd
  have hg : 0 < c - b := sub_pos.mpr hsep
  unfold gammaIntervalKernel
  calc
    _ ≤ ∫⁻ _x in Ioo a b, ∫⁻ _y in Ioo c d, ENNReal.ofReal (archLevyDensity (c - b)) := by
      refine setLIntegral_mono' measurableSet_Ioo fun x hx => ?_
      refine setLIntegral_mono' measurableSet_Ioo fun y hy => ?_
      have hyx : 0 < y - x := by linarith only [hx.2, hy.1, hsep]
      rw [abs_of_pos hyx]
      exact ENNReal.ofReal_le_ofReal (strictAntiOn_archLevyDensity.antitoneOn hg hyx
        (by linarith only [hx.2, hy.1]))
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
      rw [ENNReal.ofReal_mul (mul_nonneg hw.le hv.le), ENNReal.ofReal_mul hw.le]
      ring

/-- The integrated replacement loss is bounded by the two endpoint readings. -/
theorem gammaIntervalPairDefect_le_endpoints {a b c d : ℝ}
    (hab : a < b) (hsep : b < c) (hcd : c < d) :
    gammaIntervalPairDefect a b c d ≤
      ENNReal.ofReal ((b - a) * (d - c) *
        (archLevyDensity (c - b) - archLevyDensity (d - a))) := by
  have hw : 0 < b - a := sub_pos.mpr hab
  have hv : 0 < d - c := sub_pos.mpr hcd
  have hg : 0 < c - b := sub_pos.mpr hsep
  have hf : 0 < d - a := by linarith only [hab, hsep, hcd]
  have hdiff : 0 ≤ archLevyDensity (c - b) - archLevyDensity (d - a) :=
    sub_nonneg.mpr (strictAntiOn_archLevyDensity.antitoneOn hg hf
      (by linarith only [hab, hcd]))
  have hfar : 0 ≤ (b - a) * (d - c) * archLevyDensity (d - a) :=
    mul_nonneg (mul_nonneg hw.le hv.le) (archLevyDensity_pos hf).le
  have hloss : 0 ≤ (b - a) * (d - c) *
      (archLevyDensity (c - b) - archLevyDensity (d - a)) :=
    mul_nonneg (mul_nonneg hw.le hv.le) hdiff
  unfold gammaIntervalPairDefect
  rw [max_eq_left (by linarith only [hab, hsep, hcd])]
  apply tsub_le_iff_right.mpr
  refine (gammaIntervalKernel_le_near hab hsep hcd).trans_eq ?_
  rw [← ENNReal.ofReal_add hloss hfar]
  congr 1
  ring

#print axioms gammaIntervalKernel_comm
#print axioms gammaIntervalPairDefect_comm
#print axioms gammaIntervalKernel_translate
#print axioms gammaIntervalPairDefect_translate
#print axioms gamma_interval_set_kernel_eq_defect_add_far
#print axioms gammaIntervalKernel_eq_defect_add_far
#print axioms gammaIntervalKernel_le_defect_add_width
#print axioms gammaIntervalKernel_le_near
#print axioms gammaIntervalPairDefect_le_endpoints

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
