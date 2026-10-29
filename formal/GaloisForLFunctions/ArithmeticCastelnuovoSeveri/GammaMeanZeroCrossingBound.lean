import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaFiniteMeanZeroCoupling

/-!
# Absolute Gamma coupling between mean-zero intervals

The two signs of the original two-interval energy pay the absolute cross
pairing from positive boundary remainders. These remainders retain finite
mass when the intervals touch, so their costs can be summed over a full
family without a logarithmic loss.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
open HTGeometry LogCells

/-- The part of an interval crossing whose second coordinate lies in a second interval. -/
def gammaRectangleMeasure (a b c d : ℝ) : Measure (ℝ × ℝ) :=
  (gammaCrossMeasure a b).restrict (univ ×ˢ Ioo c d)

/-- The corresponding positive boundary remainder. -/
def gammaRectangleRemainderMeasure (a b c d : ℝ) : Measure (ℝ × ℝ) :=
  (gammaCrossRemainderMeasure a b).restrict (univ ×ˢ Ioo c d)

/-- The part removed by mean cancellation in the first coordinate. -/
def gammaRectangleFarMeasure (a b c d : ℝ) : Measure (ℝ × ℝ) :=
  (gammaCrossFarMeasure a b).restrict (univ ×ˢ Ioo c d)

private theorem crossing_base_restrict {a b c d : ℝ}
    (hd : Disjoint (Ioo a b) (Ioo c d)) :
    (gammaCrossBase a b).restrict (univ ×ˢ Ioo c d) =
      (volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d)) := by
  have hs : (univ ×ˢ Ioo c d) ∩ (Ioo a b ×ˢ (Ioo a b)ᶜ) = Ioo a b ×ˢ Ioo c d := by
    ext p
    constructor
    · rintro ⟨⟨_, hy⟩, hx, _⟩
      exact ⟨hx, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨mem_univ _, hy⟩, hx, fun h => disjoint_left.mp hd h hy⟩
  rw [gammaCrossBase, Measure.prod_restrict, Measure.prod_restrict,
    Measure.restrict_restrict (MeasurableSet.univ.prod measurableSet_Ioo), hs]

theorem gammaRectangleMeasure_eq_density {a b c d : ℝ}
    (hd : Disjoint (Ioo a b) (Ioo c d)) :
    gammaRectangleMeasure a b c d =
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))).withDensity
        (fun p => ENNReal.ofReal (archLevyDensity |p.2 - p.1|)) := by
  rw [gammaRectangleMeasure, gammaCrossMeasure,
    restrict_withDensity (MeasurableSet.univ.prod measurableSet_Ioo), crossing_base_restrict hd]

theorem gammaRectangleFarMeasure_eq_density {a b c d : ℝ}
    (hd : Disjoint (Ioo a b) (Ioo c d)) :
    gammaRectangleFarMeasure a b c d =
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))).withDensity
        (fun p => gammaFarCharge a b p.2) := by
  rw [gammaRectangleFarMeasure, gammaCrossFarMeasure,
    restrict_withDensity (MeasurableSet.univ.prod measurableSet_Ioo), crossing_base_restrict hd]

theorem gammaRectangleMeasure_eq_remainder_add_far (a b c d : ℝ) :
    gammaRectangleMeasure a b c d =
      gammaRectangleRemainderMeasure a b c d + gammaRectangleFarMeasure a b c d := by
  rw [gammaRectangleMeasure, gammaCrossMeasure_eq_remainder_add_far, Measure.restrict_add]
  rfl

theorem gammaRectangleMeasure_le (a b c d : ℝ) :
    gammaRectangleMeasure a b c d ≤ gammaCrossMeasure a b := Measure.restrict_le_self

theorem gammaRectangleRemainderMeasure_le (a b c d : ℝ) :
    gammaRectangleRemainderMeasure a b c d ≤ gammaRectangleMeasure a b c d :=
  Measure.restrict_mono le_rfl (gammaCrossRemainderMeasure_le a b)

theorem gammaRectangleFarMeasure_le (a b c d : ℝ) :
    gammaRectangleFarMeasure a b c d ≤ gammaRectangleMeasure a b c d :=
  Measure.restrict_mono le_rfl (gammaCrossFarMeasure_le a b)

/-- Bounded functions remain integrable on rectangles with a shared boundary. -/
theorem integrable_gammaRectangle_of_bound {a b c d : ℝ}
    (hab : a < b) (hw : b - a ≤ 1) {f : ℝ × ℝ → ℝ}
    (hm : Measurable f) (C : ℝ) (hb : ∀ p, ‖f p‖ ≤ C) :
    Integrable f (gammaRectangleMeasure a b c d) :=
  (integrable_gammaCross_of_bound hab hw hm C hb).mono_measure (gammaRectangleMeasure_le a b c d)

/-- The rectangle retains the original symmetric Gamma measure exactly. -/
theorem gammaRectangleMeasure_eq_restrict {a b c d : ℝ}
    (hd : Disjoint (Ioo a b) (Ioo c d)) :
    gammaRectangleMeasure a b c d = gammaKernelMeasure.restrict (Ioo a b ×ˢ Ioo c d) := by
  rw [gammaRectangleMeasure_eq_density hd, gammaKernelMeasure, Measure.prod_restrict,
    restrict_withDensity (measurableSet_Ioo.prod measurableSet_Ioo)]

private theorem gammaFarCharge_lt_top (a b y : ℝ) : gammaFarCharge a b y < ⊤ := by
  unfold gammaFarCharge
  split_ifs
  · exact ENNReal.zero_lt_top
  · exact ENNReal.ofReal_lt_top

/-- Squared rectangle differences have exactly the kernel normalization used by the
two-interval inequality. -/
theorem ofReal_integral_gammaRectangle_sq {a b c d : ℝ}
    (hd : Disjoint (Ioo a b) (Ioo c d)) {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (fun p : ℝ × ℝ => (f p.1 - g p.2) ^ 2)
      (gammaRectangleMeasure a b c d)) :
    ENNReal.ofReal (∫ p : ℝ × ℝ, (f p.1 - g p.2) ^ 2 ∂gammaRectangleMeasure a b c d) =
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d,
        ENNReal.ofReal ((f x - g y) ^ 2 * archLevyDensity |y - x|) := by
  have hsq : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((f p.1 - g p.2) ^ 2)) := by
    fun_prop
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _),
    gammaRectangleMeasure_eq_density hd,
    lintegral_withDensity_eq_lintegral_mul _ measurable_gammaKernel hsq]
  have he (p : ℝ × ℝ) : ENNReal.ofReal (archLevyDensity |p.2 - p.1|) *
      ENNReal.ofReal ((f p.1 - g p.2) ^ 2) =
      ENNReal.ofReal ((f p.1 - g p.2) ^ 2 * archLevyDensity |p.2 - p.1|) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  simp only [Pi.mul_apply]
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((f p.1 - g p.2) ^ 2 * archLevyDensity |p.2 - p.1|)) :=
    ENNReal.measurable_ofReal.comp
      ((((hf.comp measurable_fst).sub (hg.comp measurable_snd)).pow_const 2).mul
        (measurable_archLevyDensity.comp (measurable_snd.sub measurable_fst).abs))
  rw [lintegral_congr he, lintegral_prod _ hm.aemeasurable]

/-- A far charge separates into the first interval's square mass and the second
interval's kernel charge. -/
theorem ofReal_integral_gammaRectangleFar_sq {a b c d : ℝ}
    (hd : Disjoint (Ioo a b) (Ioo c d)) {f : ℝ → ℝ} (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2) (volume.restrict (Ioo a b)))
    (hi : Integrable (fun p : ℝ × ℝ => f p.1 ^ 2) (gammaRectangleFarMeasure a b c d)) :
    ENNReal.ofReal (∫ p : ℝ × ℝ, f p.1 ^ 2 ∂gammaRectangleFarMeasure a b c d) =
      ENNReal.ofReal (∫ x in Ioo a b, f x ^ 2) * ∫⁻ y in Ioo c d, gammaFarCharge a b y := by
  have hfar : Measurable (fun p : ℝ × ℝ => gammaFarCharge a b p.2) :=
    (measurable_gammaFarCharge a b).comp measurable_snd
  have hsq : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (f p.1 ^ 2)) := by fun_prop
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _),
    gammaRectangleFarMeasure_eq_density hd,
    lintegral_withDensity_eq_lintegral_mul _ hfar hsq]
  simp only [Pi.mul_apply]
  have hm : Measurable (fun p : ℝ × ℝ => gammaFarCharge a b p.2 *
      ENNReal.ofReal (f p.1 ^ 2)) := hfar.mul hsq
  rw [lintegral_prod _ hm.aemeasurable, lintegral_lintegral_swap hm.aemeasurable]
  have hm := ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun _ => sq_nonneg _)
  simp_rw [lintegral_const_mul' _ _ (gammaFarCharge_lt_top a b _).ne, ← hm]
  simp_rw [mul_comm (gammaFarCharge a b _)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Reflection preserves the actual rectangle pairing. -/
theorem integral_gammaRectangle_swap {a b c d : ℝ}
    (hd : Disjoint (Ioo a b) (Ioo c d)) (f : ℝ × ℝ → ℝ) :
    (∫ p, f p.swap ∂gammaRectangleMeasure c d a b) =
      ∫ p, f p ∂gammaRectangleMeasure a b c d := by
  rw [gammaRectangleMeasure_eq_density hd.symm, gammaRectangleMeasure_eq_density hd]
  simp only [integral_withDensity_eq_integral_toReal_smul
    measurable_gammaKernel (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have he := integral_prod_swap (μ := volume.restrict (Ioo a b))
    (ν := volume.restrict (Ioo c d))
    (fun p : ℝ × ℝ => (ENNReal.ofReal (archLevyDensity |p.2 - p.1|)).toReal • f p)
  simpa only [Prod.fst_swap, Prod.snd_swap, abs_sub_comm] using he

/-- Reflection preserves integrability on the ordered rectangle. -/
theorem integrable_gammaRectangle_swap {a b c d : ℝ}
    (hd : Disjoint (Ioo a b) (Ioo c d)) {f : ℝ × ℝ → ℝ}
    (hf : Integrable f (gammaRectangleMeasure a b c d)) :
    Integrable (fun p => f p.swap) (gammaRectangleMeasure c d a b) := by
  rw [gammaRectangleMeasure_eq_density hd,
    integrable_withDensity_iff_integrable_smul' measurable_gammaKernel
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hf
  rw [gammaRectangleMeasure_eq_density hd.symm,
    integrable_withDensity_iff_integrable_smul' measurable_gammaKernel
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, abs_sub_comm] using hf.swap

private theorem gammaRectangle_far_le_energy {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg2 : MemLp g 2 (volume.restrict (Ioo c d)))
    (hf0 : ∫ x in Ioo a b, f x = 0) (hg0 : ∫ x in Ioo c d, g x = 0)
    (hiF : Integrable (fun p : ℝ × ℝ => f p.1 ^ 2) (gammaRectangleFarMeasure a b c d))
    (hiG : Integrable (fun p : ℝ × ℝ => g p.1 ^ 2) (gammaRectangleFarMeasure c d a b))
    (hiE : Integrable (fun p : ℝ × ℝ => (f p.1 - g p.2) ^ 2)
      (gammaRectangleMeasure a b c d)) :
    (∫ p : ℝ × ℝ, f p.1 ^ 2 ∂gammaRectangleFarMeasure a b c d) +
        (∫ p : ℝ × ℝ, g p.1 ^ 2 ∂gammaRectangleFarMeasure c d a b) ≤
      ∫ p : ℝ × ℝ, (f p.1 - g p.2) ^ 2 ∂gammaRectangleMeasure a b c d := by
  have hd : Disjoint (Ioo a b) (Ioo c d) := by
    apply disjoint_left.mpr
    intro x hx hy
    linarith only [hx.2, hy.1, hbc]
  have hleft : (∫⁻ y in Ioo c d, gammaFarCharge a b y) =
      ∫⁻ y in Ioo c d, ENNReal.ofReal (archLevyDensity (y - a)) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    have hout : y ∉ Ioo a b := by intro h; linarith only [h.2, hy.1, hbc]
    have hmax : max (y - a) (b - y) = y - a := max_eq_left (by linarith only [hab, hbc, hy.1])
    simp only [gammaFarCharge, if_neg hout, hmax]
  have hright : (∫⁻ x in Ioo a b, gammaFarCharge c d x) =
      ∫⁻ x in Ioo a b, ENNReal.ofReal (archLevyDensity (d - x)) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hout : x ∉ Ioo c d := by intro h; linarith only [hx.2, h.1, hbc]
    have hmax : max (x - c) (d - x) = d - x := max_eq_right (by linarith only [hbc, hcd, hx.2])
    simp only [gammaFarCharge, if_neg hout, hmax]
  have he : (∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d,
      ENNReal.ofReal ((f x - g y) ^ 2 * archLevyDensity |y - x|)) =
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo c d,
        ENNReal.ofReal ((f x - g y) ^ 2 * archLevyDensity (y - x)) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    rw [abs_of_pos (by linarith only [hx.2, hy.1, hbc])]
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => sq_nonneg _)).mp
  rw [ENNReal.ofReal_add (integral_nonneg fun _ => sq_nonneg _)
      (integral_nonneg fun _ => sq_nonneg _),
    ofReal_integral_gammaRectangleFar_sq hd hf hf2.integrable_sq hiF,
    ofReal_integral_gammaRectangleFar_sq hd.symm hg hg2.integrable_sq hiG,
    ofReal_integral_gammaRectangle_sq hd hf hg hiE, hleft, hright, he]
  exact gamma_twoInterval_ge hab hbc hcd hf hg hf2 hg2 hf0 hg0

/-- Both signs of a mean-zero pair are paid by the original positive row remainders. -/
theorem abs_gammaRectangle_pair_le_remainders_of_le {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg2 : MemLp g 2 (volume.restrict (Ioo c d)))
    (hf0 : ∫ x in Ioo a b, f x = 0) (hg0 : ∫ x in Ioo c d, g x = 0)
    (hiF : Integrable (fun p : ℝ × ℝ => f p.1 ^ 2) (gammaRectangleMeasure a b c d))
    (hiG : Integrable (fun p : ℝ × ℝ => g p.1 ^ 2) (gammaRectangleMeasure c d a b)) :
    2 * |∫ p : ℝ × ℝ, f p.1 * g p.2 ∂gammaRectangleMeasure a b c d| ≤
      (∫ p : ℝ × ℝ, f p.1 ^ 2 ∂gammaRectangleRemainderMeasure a b c d) +
        ∫ p : ℝ × ℝ, g p.1 ^ 2 ∂gammaRectangleRemainderMeasure c d a b := by
  have hd : Disjoint (Ioo a b) (Ioo c d) := by
    apply disjoint_left.mpr
    intro x hx hy
    linarith only [hx.2, hy.1, hbc]
  have hiG' : Integrable (fun p : ℝ × ℝ => g p.2 ^ 2) (gammaRectangleMeasure a b c d) :=
    integrable_gammaRectangle_swap hd.symm hiG
  have hiC : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2)
      (gammaRectangleMeasure a b c d) := integrable_mul_of_sq_integrable
    (hf.comp measurable_fst).aestronglyMeasurable
    (hg.comp measurable_snd).aestronglyMeasurable hiF hiG'
  have hiSum : Integrable (fun p : ℝ × ℝ => f p.1 ^ 2 + g p.2 ^ 2)
      (gammaRectangleMeasure a b c d) := hiF.add hiG'
  have hiTwice : Integrable (fun p : ℝ × ℝ => 2 * (f p.1 * g p.2))
      (gammaRectangleMeasure a b c d) := hiC.const_mul 2
  have hminus : Integrable (fun p : ℝ × ℝ => (f p.1 - g p.2) ^ 2)
      (gammaRectangleMeasure a b c d) := by
    refine ((hiF.add hiG').sub (hiC.const_mul 2)).congr ?_
    exact ae_of_all _ fun p => by
      dsimp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
      ring
  have hplus : Integrable (fun p : ℝ × ℝ => (f p.1 - -g p.2) ^ 2)
      (gammaRectangleMeasure a b c d) := by
    refine ((hiF.add hiG').add (hiC.const_mul 2)).congr ?_
    exact ae_of_all _ fun p => by
      dsimp only [Pi.add_apply, Function.comp_apply]
      ring
  have hiFR := hiF.mono_measure (gammaRectangleRemainderMeasure_le a b c d)
  have hiFF := hiF.mono_measure (gammaRectangleFarMeasure_le a b c d)
  have hiGR := hiG.mono_measure (gammaRectangleRemainderMeasure_le c d a b)
  have hiGF := hiG.mono_measure (gammaRectangleFarMeasure_le c d a b)
  have hlow := gammaRectangle_far_le_energy hab hbc hcd hf hg hf2 hg2 hf0 hg0 hiFF hiGF hminus
  have hneg0 : ∫ x in Ioo c d, -g x = 0 := by rw [integral_neg, hg0, neg_zero]
  have hiGFneg : Integrable (fun p : ℝ × ℝ => (-g p.1) ^ 2)
      (gammaRectangleFarMeasure c d a b) := by simpa only [neg_sq] using hiGF
  have hhigh := gammaRectangle_far_le_energy hab hbc hcd hf hg.neg hf2 hg2.neg
    hf0 hneg0 hiFF hiGFneg hplus
  simp only [Pi.neg_apply, neg_sq] at hhigh
  have heminus : (∫ p : ℝ × ℝ, (f p.1 - g p.2) ^ 2 ∂gammaRectangleMeasure a b c d) =
      (∫ p : ℝ × ℝ, f p.1 ^ 2 ∂gammaRectangleMeasure a b c d) +
        (∫ p : ℝ × ℝ, g p.2 ^ 2 ∂gammaRectangleMeasure a b c d) -
        2 * ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂gammaRectangleMeasure a b c d := by
    have he : (fun p : ℝ × ℝ => (f p.1 - g p.2) ^ 2) =
        fun p => (f p.1 ^ 2 + g p.2 ^ 2) - 2 * (f p.1 * g p.2) := by funext p; ring
    rw [he, integral_sub hiSum hiTwice,
      integral_add hiF hiG', integral_const_mul]
  have heplus : (∫ p : ℝ × ℝ, (f p.1 - -g p.2) ^ 2 ∂gammaRectangleMeasure a b c d) =
      (∫ p : ℝ × ℝ, f p.1 ^ 2 ∂gammaRectangleMeasure a b c d) +
        (∫ p : ℝ × ℝ, g p.2 ^ 2 ∂gammaRectangleMeasure a b c d) +
        2 * ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂gammaRectangleMeasure a b c d := by
    have he : (fun p : ℝ × ℝ => (f p.1 - -g p.2) ^ 2) =
        fun p => (f p.1 ^ 2 + g p.2 ^ 2) + 2 * (f p.1 * g p.2) := by funext p; ring
    rw [he, integral_add hiSum hiTwice,
      integral_add hiF hiG', integral_const_mul]
  have hF := integral_add_measure hiFR hiFF
  have hG := integral_add_measure hiGR hiGF
  rw [← gammaRectangleMeasure_eq_remainder_add_far] at hF hG
  have hswap := integral_gammaRectangle_swap hd.symm (fun p : ℝ × ℝ => g p.1 ^ 2)
  change (∫ p : ℝ × ℝ, g p.2 ^ 2 ∂gammaRectangleMeasure a b c d) =
    ∫ p : ℝ × ℝ, g p.1 ^ 2 ∂gammaRectangleMeasure c d a b at hswap
  rw [heminus, hswap, hF, hG] at hlow
  rw [heplus, hswap, hF, hG] at hhigh
  have hbound : |2 * ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂gammaRectangleMeasure a b c d| ≤
      (∫ p : ℝ × ℝ, f p.1 ^ 2 ∂gammaRectangleRemainderMeasure a b c d) +
        ∫ p : ℝ × ℝ, g p.1 ^ 2 ∂gammaRectangleRemainderMeasure c d a b := by
    rw [abs_le]
    constructor <;> linarith only [hlow, hhigh]
  simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using hbound

/-- The absolute crossing bound does not depend on the order of the two intervals. -/
theorem abs_gammaRectangle_pair_le_remainders {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hsep : b ≤ c ∨ d ≤ a)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg2 : MemLp g 2 (volume.restrict (Ioo c d)))
    (hf0 : ∫ x in Ioo a b, f x = 0) (hg0 : ∫ x in Ioo c d, g x = 0)
    (hiF : Integrable (fun p : ℝ × ℝ => f p.1 ^ 2) (gammaRectangleMeasure a b c d))
    (hiG : Integrable (fun p : ℝ × ℝ => g p.1 ^ 2) (gammaRectangleMeasure c d a b)) :
    2 * |∫ p : ℝ × ℝ, f p.1 * g p.2 ∂gammaRectangleMeasure a b c d| ≤
      (∫ p : ℝ × ℝ, f p.1 ^ 2 ∂gammaRectangleRemainderMeasure a b c d) +
        ∫ p : ℝ × ℝ, g p.1 ^ 2 ∂gammaRectangleRemainderMeasure c d a b := by
  rcases hsep with hbc | hda
  · exact abs_gammaRectangle_pair_le_remainders_of_le hab hbc hcd hf hg hf2 hg2 hf0 hg0 hiF hiG
  · have hd : Disjoint (Ioo a b) (Ioo c d) := by
      apply disjoint_left.mpr
      intro x hx hy
      linarith only [hx.1, hy.2, hda]
    have h := abs_gammaRectangle_pair_le_remainders_of_le hcd hda hab hg hf hg2 hf2 hg0 hf0 hiG hiF
    have he : (∫ p : ℝ × ℝ, g p.1 * f p.2 ∂gammaRectangleMeasure c d a b) =
        ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂gammaRectangleMeasure a b c d := by
      rw [← integral_gammaRectangle_swap hd (fun p : ℝ × ℝ => f p.1 * g p.2)]
      congr 1
      funext p
      dsimp only [Prod.fst_swap, Prod.snd_swap]
      ring
    rw [he, add_comm] at h
    exact h

/-- An interval does not cross its own interior. -/
theorem gammaRectangleMeasure_self (a b : ℝ) : gammaRectangleMeasure a b a b = 0 := by
  have hs : (univ ×ˢ Ioo a b) ∩ (Ioo a b ×ˢ (Ioo a b)ᶜ) = ∅ := by
    ext p
    simp only [mem_inter_iff, mem_prod, mem_univ, true_and, mem_compl_iff, mem_empty_iff_false]
    tauto
  rw [gammaRectangleMeasure, gammaCrossMeasure_eq_restrict,
    Measure.restrict_restrict (MeasurableSet.univ.prod measurableSet_Ioo), hs,
    Measure.restrict_empty]

/-- Disjoint target intervals use each positive boundary remainder at most once. -/
theorem sum_gammaRectangleRemainderMeasure_le {ι : Type*} [Fintype ι]
    (a b : ℝ) (L U : ι → ℝ)
    (hd : Pairwise (Function.onFun Disjoint (fun i => Ioo (L i) (U i)))) :
    (∑ i, gammaRectangleRemainderMeasure a b (L i) (U i)) ≤ gammaCrossRemainderMeasure a b := by
  let S : ι → Set (ℝ × ℝ) := fun i => univ ×ˢ Ioo (L i) (U i)
  have hSm (i : ι) : MeasurableSet (S i) := MeasurableSet.univ.prod measurableSet_Ioo
  have hSd : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    apply disjoint_left.mpr
    intro p hi hj
    exact disjoint_left.mp (hd hij) hi.2 hj.2
  have he : (∑ i, gammaRectangleRemainderMeasure a b (L i) (U i)) =
      (gammaCrossRemainderMeasure a b).restrict (⋃ i, S i) := by
    rw [Measure.restrict_iUnion hSd hSm, Measure.sum_fintype]
    rfl
  rw [he]
  exact Measure.restrict_le_self

/-- Summing all rectangle costs leaves one width-scale boundary cost. -/
theorem sum_gammaRectangle_remainder_sq_le {ι : Type*} [Fintype ι]
    {a b : ℝ} (hab : a < b) (hw : b - a ≤ 1) (L U : ι → ℝ)
    (hd : Pairwise (Function.onFun Disjoint (fun i => Ioo (L i) (U i))))
    {f : ℝ → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D) (hb : ∀ x, f x ^ 2 ≤ D) :
    (∑ i, ∫ p : ℝ × ℝ, f p.1 ^ 2 ∂gammaRectangleRemainderMeasure a b (L i) (U i)) ≤
      Real.exp (1 / 2) * (b - a) * D := by
  letI : IsFiniteMeasure (gammaCrossRemainderMeasure a b) :=
    ⟨(gammaCrossRemainderMeasure_univ_le hab hw).trans_lt ENNReal.ofReal_lt_top⟩
  have hi : Integrable (fun p : ℝ × ℝ => f p.1 ^ 2) (gammaCrossRemainderMeasure a b) := by
    apply Integrable.of_bound ((hf.comp measurable_fst).pow_const 2).aestronglyMeasurable D
    exact ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, abs_of_nonneg (sq_nonneg (f p.1))]
        using hb p.1
  have hii (i : ι) : Integrable (fun p : ℝ × ℝ => f p.1 ^ 2)
      (gammaRectangleRemainderMeasure a b (L i) (U i)) := hi.mono_measure Measure.restrict_le_self
  have hmass := ENNReal.toReal_mono ENNReal.ofReal_ne_top (gammaCrossRemainderMeasure_univ_le hab hw)
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (sub_pos.mpr hab).le)] at hmass
  calc
    _ = ∫ p : ℝ × ℝ, f p.1 ^ 2 ∂(∑ i, gammaRectangleRemainderMeasure a b (L i) (U i)) :=
      (integral_finsetSum_measure (fun i _ => hii i)).symm
    _ ≤ ∫ p : ℝ × ℝ, f p.1 ^ 2 ∂gammaCrossRemainderMeasure a b :=
      integral_mono_measure (sum_gammaRectangleRemainderMeasure_le a b L U hd)
        (ae_of_all _ fun _ => sq_nonneg _) hi
    _ ≤ ∫ _p : ℝ × ℝ, D ∂gammaCrossRemainderMeasure a b :=
      integral_mono hi (integrable_const _) (fun p => hb p.1)
    _ = (gammaCrossRemainderMeasure a b univ).toReal * D := by
      rw [integral_const, smul_eq_mul, measureReal_def]
    _ ≤ _ := mul_le_mul_of_nonneg_right hmass hD

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
