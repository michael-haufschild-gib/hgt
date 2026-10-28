import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaMeanZeroEnergy
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-!
# Integrated Gamma rows and boundary moments

Translation and reflection reduce separated half-line rows to one integrable
Gamma tail. Tonelli turns triangular boundary windows into a finite first moment.
The full loss from interval averaging is exactly twice that moment.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals

/-- The actual Gamma mass above a positive separation. -/
def gammaTailMass (δ : ℝ) : ℝ := ∫ t in Ioi δ, archLevyDensity t

/-- A positive Gamma tail has nonnegative mass. -/
theorem gammaTailMass_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ gammaTailMass δ :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht => (archLevyDensity_pos (hδ.trans ht)).le

private theorem ofReal_gammaTailMass {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (gammaTailMass δ) =
      ∫⁻ t in Ioi δ, ENNReal.ofReal (archLevyDensity t) :=
  ofReal_integral_eq_lintegral_ofReal
    (_root_.RHTower.WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ)
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht =>
      (archLevyDensity_pos (hδ.trans ht)).le)

/-- Translation identifies the exact right half-line Gamma row. -/
theorem gamma_right_halfLine_row_eq {T x : ℝ} (hsep : x < T) :
    (∫⁻ y in Ioi T, ENNReal.ofReal (archLevyDensity |y - x|)) =
      ENNReal.ofReal (gammaTailMass (T - x)) := by
  have hm : Measurable (fun y : ℝ => ENNReal.ofReal (archLevyDensity |y - x|)) :=
    ENNReal.measurable_ofReal.comp (measurable_archLevyDensity.comp (measurable_id.sub measurable_const).abs)
  have hp : (fun t : ℝ => x + t) ⁻¹' Ioi T = Ioi (T - x) := by
    ext t
    change T < x + t ↔ T - x < t
    constructor <;> intro h <;> linarith only [h]
  have he := (measurePreserving_add_left (volume : Measure ℝ) x).setLIntegral_comp_preimage
    (s := Ioi T) measurableSet_Ioi hm
  rw [hp] at he
  calc
    _ = ∫⁻ t in Ioi (T - x), ENNReal.ofReal (archLevyDensity t) := by
      rw [← he]
      refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := by linarith only [hsep, show T - x < t from ht]
      simp only [add_sub_cancel_left, abs_of_pos ht0]
    _ = _ := (ofReal_gammaTailMass (sub_pos.mpr hsep)).symm

/-- An entire right half-line row is paid by its fixed separation tail. -/
theorem gamma_right_halfLine_row_le {δ T x : ℝ} (hδ : 0 < δ) (hsep : x + δ ≤ T) :
    (∫⁻ y in Ioi T, ENNReal.ofReal (archLevyDensity |y - x|)) ≤
      ENNReal.ofReal (gammaTailMass δ) := by
  rw [gamma_right_halfLine_row_eq (by linarith only [hδ, hsep]),
    ofReal_gammaTailMass (by linarith only [hδ, hsep]), ofReal_gammaTailMass hδ]
  exact lintegral_mono' (Measure.restrict_mono
    (fun t ht => show δ < t by linarith only [hsep, show T - x < t from ht]) le_rfl) le_rfl

/-- Reflection identifies the exact left half-line Gamma row. -/
theorem gamma_left_halfLine_row_eq {T x : ℝ} (hsep : T < x) :
    (∫⁻ y in Iio T, ENNReal.ofReal (archLevyDensity |y - x|)) =
      ENNReal.ofReal (gammaTailMass (x - T)) := by
  have hm : Measurable (fun y : ℝ => ENNReal.ofReal (archLevyDensity |y - x|)) :=
    ENNReal.measurable_ofReal.comp (measurable_archLevyDensity.comp (measurable_id.sub measurable_const).abs)
  have hp : (fun t : ℝ => x - t) ⁻¹' Iio T = Ioi (x - T) := by
    ext t
    change x - t < T ↔ x - T < t
    constructor <;> intro h <;> linarith only [h]
  have he := (Measure.measurePreserving_sub_left (volume : Measure ℝ) x).setLIntegral_comp_preimage
    (s := Iio T) measurableSet_Iio hm
  rw [hp] at he
  calc
    _ = ∫⁻ t in Ioi (x - T), ENNReal.ofReal (archLevyDensity t) := by
      rw [← he]
      refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := by linarith only [hsep, show x - T < t from ht]
      rw [show x - t - x = -t by ring, abs_neg, abs_of_pos ht0]
    _ = _ := (ofReal_gammaTailMass (sub_pos.mpr hsep)).symm

/-- Reflection gives the same uniform estimate on a left half-line row. -/
theorem gamma_left_halfLine_row_le {δ T x : ℝ} (hδ : 0 < δ) (hsep : T + δ ≤ x) :
    (∫⁻ y in Iio T, ENNReal.ofReal (archLevyDensity |y - x|)) ≤
      ENNReal.ofReal (gammaTailMass δ) := by
  rw [gamma_left_halfLine_row_eq (by linarith only [hδ, hsep]),
    ofReal_gammaTailMass (by linarith only [hδ, hsep]), ofReal_gammaTailMass hδ]
  exact lintegral_mono' (Measure.restrict_mono
    (fun t ht => show δ < t by linarith only [hsep, show x - T < t from ht]) le_rfl) le_rfl

/-- All interactions beyond two separated boundaries cost at most two tails per unit length. -/
theorem gamma_separated_interval_rows_le {δ a b T U : ℝ}
    (hδ : 0 < δ) (hab : a < b) (hleft : T + δ ≤ a) (hright : b + δ ≤ U) :
    (∫⁻ x in Ioo a b, ∫⁻ y in Iio T ∪ Ioi U,
      ENNReal.ofReal (archLevyDensity |y - x|)) ≤
      ENNReal.ofReal (2 * (b - a) * gammaTailMass δ) := by
  have hd : Disjoint (Iio T) (Ioi U) := by
    apply disjoint_left.mpr
    intro y hy hz
    change y < T at hy
    change U < y at hz
    linarith only [hδ, hab, hleft, hright, hy, hz]
  calc
    _ ≤ ∫⁻ _x in Ioo a b, (2 : ℝ≥0∞) * ENNReal.ofReal (gammaTailMass δ) := by
      refine setLIntegral_mono' measurableSet_Ioo fun x hx => ?_
      rw [lintegral_union measurableSet_Ioi hd, two_mul]
      exact add_le_add (gamma_left_halfLine_row_le hδ (by linarith only [hleft, hx.1]))
        (gamma_right_halfLine_row_le hδ (by linarith only [hright, hx.2]))
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (b - a)),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring


open SpacingScaleHarmonicAnalysis

private theorem triangle_lintegral {K : ℝ → ℝ≥0∞} (hK : Measurable K) (w : ℝ) :
    (∫⁻ x in Ioo 0 w, ∫⁻ t in Ioo x w, K t) =
      ∫⁻ t in Ioo 0 w, ENNReal.ofReal t * K t := by
  let B : ℝ → ℝ → ℝ≥0∞ := fun x t => if x < t then K t else 0
  have hB : Measurable (fun p : ℝ × ℝ => B p.1 p.2) := by
    change Measurable (fun p : ℝ × ℝ => if p.1 < p.2 then K p.2 else 0)
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (hK.comp measurable_snd) measurable_const
  have hx (x : ℝ) (hx : x ∈ Ioo 0 w) :
      (∫⁻ t in Ioo x w, K t) = ∫⁻ t in Ioo 0 w, B x t := by
    have hp : Ioi x ∩ Ioo (0 : ℝ) w = Ioo x w := by
      ext t
      change (x < t ∧ 0 < t ∧ t < w) ↔ (x < t ∧ t < w)
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, hx.1.trans h.1, h.2⟩
    change _ = ∫⁻ t in Ioo 0 w, (Ioi x).indicator K t
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hp]
  have ht (t : ℝ) (ht : t ∈ Ioo 0 w) :
      (∫⁻ x in Ioo 0 w, B x t) = ENNReal.ofReal t * K t := by
    have hp : Iio t ∩ Ioo (0 : ℝ) w = Ioo 0 t := by
      ext x
      change (x < t ∧ 0 < x ∧ x < w) ↔ (0 < x ∧ x < t)
      constructor
      · exact fun h => ⟨h.2.1, h.1⟩
      · exact fun h => ⟨h.2, h.1, h.2.trans ht.2⟩
    change (∫⁻ x in Ioo 0 w, (Iio t).indicator (fun _ => K t) x) = _
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      hp, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, mul_comm]
  calc
    _ = ∫⁻ x in Ioo 0 w, ∫⁻ t in Ioo 0 w, B x t :=
      setLIntegral_congr_fun measurableSet_Ioo hx
    _ = ∫⁻ t in Ioo 0 w, ∫⁻ x in Ioo 0 w, B x t :=
      lintegral_lintegral_swap hB.aemeasurable
    _ = _ := setLIntegral_congr_fun measurableSet_Ioo ht

/-- The nested Gamma boundary windows equal the first kernel moment. -/
theorem gamma_triangle_eq_first_moment (w : ℝ) :
    (∫⁻ x in Ioo 0 w, ∫⁻ t in Ioo x w, ENNReal.ofReal (archLevyDensity t)) =
      ∫⁻ t in Ioo 0 w, ENNReal.ofReal (t * archLevyDensity t) := by
  rw [triangle_lintegral (K := fun t : ℝ => ENNReal.ofReal (archLevyDensity t))
    (ENNReal.measurable_ofReal.comp measurable_archLevyDensity) w]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [ENNReal.ofReal_mul ht.1.le]

/-- A Gamma boundary triangle of width at most one costs a fixed constant per unit width. -/
theorem gamma_triangle_le {w : ℝ} (hw1 : w ≤ 1) :
    (∫⁻ x in Ioo 0 w, ∫⁻ t in Ioo x w, ENNReal.ofReal (archLevyDensity t)) ≤
      ENNReal.ofReal (Real.exp (1 / 2) * w / 2) := by
  rw [gamma_triangle_eq_first_moment w]
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 w) : t * archLevyDensity t ≤ Real.exp (1 / 2) / 2 := by
    have h := archLevyDensity_le_sqrt_e_div ht.1 (ht.2.le.trans hw1)
    have h' := (le_div_iff₀ (mul_pos (by norm_num) ht.1)).mp h
    nlinarith only [h']
  calc
    _ ≤ ∫⁻ _t in Ioo (0 : ℝ) w, ENNReal.ofReal (Real.exp (1 / 2) / 2) :=
      setLIntegral_mono' measurableSet_Ioo fun t ht => ENNReal.ofReal_le_ofReal (hpoint t ht)
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (1 / 2) / 2)]
      congr 1
      ring





private theorem gamma_tail_sub_eq_window {s w : ℝ} (hs : 0 < s) (hsw : s ≤ w) :
    ENNReal.ofReal (gammaTailMass s) - ENNReal.ofReal (gammaTailMass w) =
      ∫⁻ t in Ioo s w, ENNReal.ofReal (archLevyDensity t) := by
  have hw : 0 < w := hs.trans_le hsw
  symm
  apply ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top
  rw [ofReal_gammaTailMass hs, ofReal_gammaTailMass hw]
  have he : volume.restrict (Ioo s w) = volume.restrict (Ioc s w) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [he, ← lintegral_union measurableSet_Ioi (by
    apply disjoint_left.mpr
    intro t ht ht'
    exact (not_lt_of_ge ht.2) ht'), Ioc_union_Ioi_eq_Ioi hsw]

/-- The far-end charge is dominated by the actual kernel at every interior source point. -/
theorem gammaFarCharge_le_actual {a b x : ℝ} (hx : x ∈ Ioo a b) (y : ℝ) :
    gammaFarCharge a b y ≤ ENNReal.ofReal (archLevyDensity |y - x|) := by
  by_cases hy : y ∈ Ioo a b
  · simp only [gammaFarCharge, if_pos hy]
    exact bot_le
  rw [gammaFarCharge, if_neg hy]
  have hout : y ≤ a ∨ b ≤ y := by
    by_cases hya : a < y
    · exact Or.inr (le_of_not_gt (fun hyb => hy ⟨hya, hyb⟩))
    · exact Or.inl (le_of_not_gt hya)
  apply ENNReal.ofReal_le_ofReal
  rcases hout with hya | hby
  · have hdist : 0 < x - y := by linarith only [hx.1, hya]
    rw [abs_of_neg (by linarith only [hdist]), neg_sub,
      max_eq_right (by linarith only [hx.1, hx.2, hya])]
    exact strictAntiOn_archLevyDensity.antitoneOn hdist
      (show 0 < b - y by linarith only [hdist, hx.2]) (by linarith only [hx.2])
  · have hdist : 0 < y - x := by linarith only [hx.2, hby]
    rw [abs_of_pos hdist, max_eq_left (by linarith only [hx.1, hx.2, hby])]
    exact strictAntiOn_archLevyDensity.antitoneOn hdist
      (show 0 < y - a by linarith only [hdist, hx.1]) (by linarith only [hx.1])

private theorem gammaFarCharge_right {a b y : ℝ} (hab : a < b) (hy : b < y) :
    gammaFarCharge a b y = ENNReal.ofReal (archLevyDensity |y - a|) := by
  have hn : y ∉ Ioo a b := fun h => (not_lt_of_ge hy.le) h.2
  rw [gammaFarCharge, if_neg hn, max_eq_left (by linarith only [hab, hy]),
    abs_of_pos (by linarith only [hab, hy])]

private theorem gammaFarCharge_left {a b y : ℝ} (hab : a < b) (hy : y < a) :
    gammaFarCharge a b y = ENNReal.ofReal (archLevyDensity |y - b|) := by
  have hn : y ∉ Ioo a b := fun h => (not_lt_of_ge hy.le) h.1
  rw [gammaFarCharge, if_neg hn, max_eq_right (by linarith only [hab, hy]),
    abs_of_neg (by linarith only [hab, hy]), neg_sub]

/-- The nonnegative loss in replacing an interval interaction by its far-end charge. -/
def gammaIntervalRowDefect (a b x y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (archLevyDensity |y - x|) - gammaFarCharge a b y

private theorem gamma_right_row_defect_eq {a b x : ℝ} (hx : x ∈ Ioo a b) :
    (∫⁻ y in Ioi b, gammaIntervalRowDefect a b x y) =
      ∫⁻ t in Ioo (b - x) (b - a), ENNReal.ofReal (archLevyDensity t) := by
  have hab := hx.1.trans hx.2
  have hfar : (∫⁻ y in Ioi b, gammaFarCharge a b y) =
      ENNReal.ofReal (gammaTailMass (b - a)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi fun y hy => gammaFarCharge_right hab hy,
      gamma_right_halfLine_row_eq hab]
  change (∫⁻ y in Ioi b, ENNReal.ofReal (archLevyDensity |y - x|) - gammaFarCharge a b y) = _
  rw [lintegral_sub (measurable_gammaFarCharge a b)
    (by rw [hfar]; exact ENNReal.ofReal_ne_top)
    (ae_of_all _ fun y => gammaFarCharge_le_actual hx y), hfar,
    gamma_right_halfLine_row_eq hx.2]
  exact gamma_tail_sub_eq_window (sub_pos.mpr hx.2) (by linarith only [hx.1])

private theorem gamma_left_row_defect_eq {a b x : ℝ} (hx : x ∈ Ioo a b) :
    (∫⁻ y in Iio a, gammaIntervalRowDefect a b x y) =
      ∫⁻ t in Ioo (x - a) (b - a), ENNReal.ofReal (archLevyDensity t) := by
  have hab := hx.1.trans hx.2
  have hfar : (∫⁻ y in Iio a, gammaFarCharge a b y) =
      ENNReal.ofReal (gammaTailMass (b - a)) := by
    rw [setLIntegral_congr_fun measurableSet_Iio fun y hy => gammaFarCharge_left hab hy,
      gamma_left_halfLine_row_eq hab]
  change (∫⁻ y in Iio a, ENNReal.ofReal (archLevyDensity |y - x|) - gammaFarCharge a b y) = _
  rw [lintegral_sub (measurable_gammaFarCharge a b)
    (by rw [hfar]; exact ENNReal.ofReal_ne_top)
    (ae_of_all _ fun y => gammaFarCharge_le_actual hx y), hfar,
    gamma_left_halfLine_row_eq hx.1]
  exact gamma_tail_sub_eq_window (sub_pos.mpr hx.1) (by linarith only [hx.2])

private theorem measurable_gammaWindow (w : ℝ) :
    Measurable (fun s : ℝ => ∫⁻ t in Ioo s w, ENNReal.ofReal (archLevyDensity t)) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 ∧ p.2 < w then ENNReal.ofReal (archLevyDensity p.2) else 0) :=
    Measurable.ite ((measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const))
      ((ENNReal.measurable_ofReal.comp measurable_archLevyDensity).comp measurable_snd)
      measurable_const
  have h := hm.lintegral_prod_right' (ν := volume)
  convert h using 1
  funext s
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro t
  simp only [Set.indicator, mem_Ioo]

/-- Integrating the entire exterior row loss gives twice the finite first Gamma moment. -/
theorem gamma_interval_row_defect_eq {a b : ℝ} (hab : a < b) :
    (∫⁻ x in Ioo a b, ∫⁻ y in Iio a ∪ Ioi b, gammaIntervalRowDefect a b x y) =
      2 * ∫⁻ t in Ioo 0 (b - a), ENNReal.ofReal (t * archLevyDensity t) := by
  let W : ℝ → ℝ≥0∞ := fun s => ∫⁻ t in Ioo s (b - a), ENNReal.ofReal (archLevyDensity t)
  have hW : Measurable W := measurable_gammaWindow (b - a)
  have hleft : (∫⁻ x in Ioo a b, W (x - a)) = ∫⁻ s in Ioo 0 (b - a), W s := by
    have hp : (fun s : ℝ => a + s) ⁻¹' Ioo a b = Ioo 0 (b - a) := by
      ext s
      change (a < a + s ∧ a + s < b) ↔ (0 < s ∧ s < b - a)
      constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
    have he := (measurePreserving_add_left (volume : Measure ℝ) a).setLIntegral_comp_preimage
      (s := Ioo a b) (f := fun x : ℝ => W (x - a)) measurableSet_Ioo
      (hW.comp (measurable_id.sub measurable_const))
    rw [hp] at he
    simpa only [add_sub_cancel_left] using he.symm
  have hright : (∫⁻ x in Ioo a b, W (b - x)) = ∫⁻ s in Ioo 0 (b - a), W s := by
    have hp : (fun s : ℝ => b - s) ⁻¹' Ioo a b = Ioo 0 (b - a) := by
      ext s
      change (a < b - s ∧ b - s < b) ↔ (0 < s ∧ s < b - a)
      constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
    have he := (Measure.measurePreserving_sub_left (volume : Measure ℝ) b).setLIntegral_comp_preimage
      (s := Ioo a b) (f := fun x : ℝ => W (b - x)) measurableSet_Ioo
      (hW.comp (measurable_const.sub measurable_id))
    rw [hp] at he
    simpa only [sub_sub_cancel] using he.symm
  have hd : Disjoint (Iio a) (Ioi b) := by
    apply disjoint_left.mpr
    intro y hy hz
    exact (not_lt_of_ge (hab.trans hz).le) hy
  calc
    _ = ∫⁻ x in Ioo a b, (W (x - a) + W (b - x)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      rw [lintegral_union measurableSet_Ioi hd, gamma_left_row_defect_eq hx,
        gamma_right_row_defect_eq hx]
    _ = (∫⁻ x in Ioo a b, W (x - a)) + ∫⁻ x in Ioo a b, W (b - x) :=
      lintegral_add_left (hW.comp (measurable_id.sub measurable_const)) _
    _ = 2 * ∫⁻ s in Ioo 0 (b - a), W s := by rw [hleft, hright, two_mul]
    _ = _ := by rw [show (∫⁻ s in Ioo 0 (b - a), W s) =
      ∫⁻ t in Ioo 0 (b - a), ENNReal.ofReal (t * archLevyDensity t) from
      gamma_triangle_eq_first_moment (b - a)]

/-- One fixed constant pays the whole exterior averaging loss of every interval of width at most one. -/
theorem gamma_interval_row_defect_le {a b : ℝ} (hab : a < b) (hw : b - a ≤ 1) :
    (∫⁻ x in Ioo a b, ∫⁻ y in Iio a ∪ Ioi b, gammaIntervalRowDefect a b x y) ≤
      ENNReal.ofReal (Real.exp (1 / 2) * (b - a)) := by
  rw [gamma_interval_row_defect_eq hab, ← gamma_triangle_eq_first_moment (b - a)]
  calc
    _ ≤ 2 * ENNReal.ofReal (Real.exp (1 / 2) * (b - a) / 2) :=
      mul_le_mul_right (gamma_triangle_le hw) 2
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring



private theorem gammaFarCharge_exterior_integral {a b : ℝ} (hab : a < b) :
    (∫⁻ y in Iio a ∪ Ioi b, gammaFarCharge a b y) =
      2 * ENNReal.ofReal (gammaTailMass (b - a)) := by
  have hd : Disjoint (Iio a) (Ioi b) := by
    apply disjoint_left.mpr
    intro y hy hz
    exact (not_lt_of_ge (hab.trans hz).le) hy
  have hleft : (∫⁻ y in Iio a, gammaFarCharge a b y) =
      ENNReal.ofReal (gammaTailMass (b - a)) := by
    rw [setLIntegral_congr_fun measurableSet_Iio fun y hy => gammaFarCharge_left hab hy,
      gamma_left_halfLine_row_eq hab]
  have hright : (∫⁻ y in Ioi b, gammaFarCharge a b y) =
      ENNReal.ofReal (gammaTailMass (b - a)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi fun y hy => gammaFarCharge_right hab hy,
      gamma_right_halfLine_row_eq hab]
  rw [lintegral_union measurableSet_Ioi hd, hleft, hright, two_mul]

/-- The actual interval-to-exterior kernel splits into its far-end mass and boundary moment. -/
theorem gamma_interval_exterior_kernel_eq {a b : ℝ} (hab : a < b) :
    (∫⁻ x in Ioo a b, ∫⁻ y in Iio a ∪ Ioi b,
      ENNReal.ofReal (archLevyDensity |y - x|)) =
      ENNReal.ofReal (2 * (b - a) * gammaTailMass (b - a)) +
        2 * ∫⁻ t in Ioo 0 (b - a), ENNReal.ofReal (t * archLevyDensity t) := by
  have hw : 0 < b - a := sub_pos.mpr hab
  calc
    _ = ∫⁻ x in Ioo a b, ∫⁻ y in Iio a ∪ Ioi b,
        (gammaIntervalRowDefect a b x y + gammaFarCharge a b y) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      apply lintegral_congr
      intro y
      exact (tsub_add_cancel_of_le (gammaFarCharge_le_actual hx y)).symm
    _ = (∫⁻ x in Ioo a b, ∫⁻ y in Iio a ∪ Ioi b, gammaIntervalRowDefect a b x y) +
        (∫⁻ _x in Ioo a b, ∫⁻ y in Iio a ∪ Ioi b, gammaFarCharge a b y) := by
      simp_rw [lintegral_add_right _ (measurable_gammaFarCharge a b)]
      exact lintegral_add_right _ measurable_const
    _ = 2 * (∫⁻ t in Ioo 0 (b - a), ENNReal.ofReal (t * archLevyDensity t)) +
        (2 * ENNReal.ofReal (gammaTailMass (b - a))) * ENNReal.ofReal (b - a) := by
      rw [gamma_interval_row_defect_eq hab, gammaFarCharge_exterior_integral hab,
        lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (b - a)),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

/-- The full kernel against the exterior is finite, with its logarithmic tail kept explicit. -/
theorem gamma_interval_exterior_kernel_le {a b : ℝ} (hab : a < b) (hw1 : b - a ≤ 1) :
    (∫⁻ x in Ioo a b, ∫⁻ y in Iio a ∪ Ioi b,
      ENNReal.ofReal (archLevyDensity |y - x|)) ≤
      ENNReal.ofReal ((b - a) * (2 * gammaTailMass (b - a) + Real.exp (1 / 2))) := by
  have hw : 0 < b - a := sub_pos.mpr hab
  have ht := gammaTailMass_nonneg hw
  have hm := gamma_interval_row_defect_le hab hw1
  rw [gamma_interval_row_defect_eq hab] at hm
  rw [gamma_interval_exterior_kernel_eq hab]
  calc
    _ ≤ ENNReal.ofReal (2 * (b - a) * gammaTailMass (b - a)) +
        ENNReal.ofReal (Real.exp (1 / 2) * (b - a)) := add_le_add le_rfl hm
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * (b - a) * gammaTailMass (b - a))
        (by positivity : 0 ≤ Real.exp (1 / 2) * (b - a))]
      congr 1
      ring


#print axioms gamma_right_halfLine_row_le
#print axioms gamma_left_halfLine_row_le
#print axioms gamma_separated_interval_rows_le
#print axioms gamma_triangle_eq_first_moment
#print axioms gamma_triangle_le
#print axioms gamma_right_halfLine_row_eq
#print axioms gamma_left_halfLine_row_eq
#print axioms gammaFarCharge_le_actual
#print axioms gamma_interval_row_defect_eq
#print axioms gamma_interval_row_defect_le
#print axioms gamma_interval_exterior_kernel_eq
#print axioms gamma_interval_exterior_kernel_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
