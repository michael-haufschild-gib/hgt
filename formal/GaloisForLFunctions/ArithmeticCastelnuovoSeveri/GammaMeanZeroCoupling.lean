import GaloisForLFunctions.HTGeometry.CauchyDifferenceMultiSourceCapacity
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws
import GaloisForLFunctions.RHTower.WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal

/-!
# Gamma coupling of unequal mean-zero intervals

The Gamma kernel is a positive sum of exponential kernels. The rank-one
inequality for two mean-zero sources therefore pays both far-end charges,
without an equal-width or a separation-gap condition.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
open HTGeometry.CauchyDifference

private def gammaRate (k : ℕ) : ℝ := 2 * k + 1 / 2

private theorem ofReal_gamma_eq_tsum {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (archLevyDensity t) =
      ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(gammaRate k * t))) := by
  rw [archLevyDensity_eq_tsum ht,
    ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le)
      (hasSum_archLevyDensity ht).summable]
  simp only [gammaRate, neg_mul]

private theorem gamma_charge_eq_tsum {μ : Measure ℝ} (g : ℝ → ℝ) (hg : Measurable g)
    (hp : ∀ᵐ x ∂μ, 0 < g x) :
    (∫⁻ x, ENNReal.ofReal (archLevyDensity (g x)) ∂μ) =
      ∑' k : ℕ, ∫⁻ x, ENNReal.ofReal (Real.exp (-(gammaRate k * g x))) ∂μ := by
  calc
    _ = ∫⁻ x, ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(gammaRate k * g x))) ∂μ :=
      lintegral_congr_ae (hp.mono fun x hx => ofReal_gamma_eq_tsum hx)
    _ = _ := lintegral_tsum fun k => by fun_prop

private theorem gamma_pair_eq_tsum {α α' β β' : ℝ} (hsep : α' ≤ β)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x in Ioo α α', ∫⁻ y in Ioo β β',
      ENNReal.ofReal ((f x - g y) ^ 2 * archLevyDensity (y - x))) =
      ∑' k : ℕ, ∫⁻ x in Ioo α α', ∫⁻ y in Ioo β β',
        ENNReal.ofReal ((f x - g y) ^ 2 * Real.exp (-(gammaRate k * (y - x)))) := by
  have hpt : ∀ x ∈ Ioo α α', ∀ y ∈ Ioo β β',
      ENNReal.ofReal ((f x - g y) ^ 2 * archLevyDensity (y - x)) =
        ∑' k : ℕ, ENNReal.ofReal ((f x - g y) ^ 2 *
          Real.exp (-(gammaRate k * (y - x)))) := by
    intro x hx y hy
    rw [ENNReal.ofReal_mul (sq_nonneg _), ofReal_gamma_eq_tsum (by linarith [hx.2, hy.1]),
      ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro k
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
  have hm (k : ℕ) : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((f p.1 - g p.2) ^ 2 * Real.exp (-(gammaRate k * (p.2 - p.1))))) := by
    fun_prop
  calc
    _ = ∫⁻ x in Ioo α α', ∑' k : ℕ, ∫⁻ y in Ioo β β',
        ENNReal.ofReal ((f x - g y) ^ 2 * Real.exp (-(gammaRate k * (y - x)))) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      rw [setLIntegral_congr_fun measurableSet_Ioo fun y hy => hpt x hx y hy]
      exact lintegral_tsum fun k => by fun_prop
    _ = _ := lintegral_tsum fun k => (hm k).lintegral_prod_right'.aemeasurable

/-- Both far-end charges survive the full Gamma coupling of two mean-zero intervals. -/
theorem gamma_twoInterval_ge {α α' β β' : ℝ} (hα : α ≤ α') (hsep : α' ≤ β) (hβ : β ≤ β')
    {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 (volume.restrict (Ioo α α')))
    (hg : MemLp g 2 (volume.restrict (Ioo β β')))
    (hf0 : ∫ x in Ioo α α', f x = 0) (hg0 : ∫ y in Ioo β β', g y = 0) :
    ENNReal.ofReal (∫ x in Ioo α α', f x ^ 2) *
          (∫⁻ y in Ioo β β', ENNReal.ofReal (archLevyDensity (y - α))) +
        ENNReal.ofReal (∫ y in Ioo β β', g y ^ 2) *
          (∫⁻ x in Ioo α α', ENNReal.ofReal (archLevyDensity (β' - x))) ≤
      ∫⁻ x in Ioo α α', ∫⁻ y in Ioo β β',
        ENNReal.ofReal ((f x - g y) ^ 2 * archLevyDensity (y - x)) := by
  have hleft := gamma_charge_eq_tsum (μ := volume.restrict (Ioo β β'))
    (fun y => y - α) (by fun_prop)
    ((ae_restrict_mem measurableSet_Ioo).mono fun y hy => by linarith [hy.1])
  have hright := gamma_charge_eq_tsum (μ := volume.restrict (Ioo α α'))
    (fun x => β' - x) (by fun_prop)
    ((ae_restrict_mem measurableSet_Ioo).mono fun x hx => by linarith [hx.2])
  rw [gamma_pair_eq_tsum hsep hfm hgm, hleft, hright,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro k
  let κf : ℝ := ∫ y in Ioo β β', Real.exp (-(gammaRate k * (y - α)))
  let κg : ℝ := ∫ x in Ioo α α', Real.exp (-(gammaRate k * (β' - x)))
  let Nf : ℝ := ∫ x in Ioo α α', f x ^ 2
  let Ng : ℝ := ∫ y in Ioo β β', g y ^ 2
  have hκf : 0 ≤ κf := integral_nonneg fun _ => (Real.exp_pos _).le
  have hκg : 0 ≤ κg := integral_nonneg fun _ => (Real.exp_pos _).le
  have hNf : 0 ≤ Nf := integral_nonneg fun _ => sq_nonneg _
  have hNg : 0 ≤ Ng := integral_nonneg fun _ => sq_nonneg _
  have heleft : (∫⁻ y in Ioo β β', ENNReal.ofReal
      (Real.exp (-(gammaRate k * (y - α))))) = ENNReal.ofReal κf := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal
      (integrableOn_Ioo_of_continuous (by fun_prop)) (ae_of_all _ fun _ => (Real.exp_pos _).le)
  have heright : (∫⁻ x in Ioo α α', ENNReal.ofReal
      (Real.exp (-(gammaRate k * (β' - x))))) = ENNReal.ofReal κg := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal
      (integrableOn_Ioo_of_continuous (by fun_prop)) (ae_of_all _ fun _ => (Real.exp_pos _).le)
  rw [heleft, heright]
  have hslice := rankOne_twoInterval_le
    (show 0 ≤ gammaRate k by unfold gammaRate; positivity) hf hg hf0 hg0
  calc
    _ = ENNReal.ofReal (κf * Nf + κg * Ng) := by
      rw [ENNReal.ofReal_add (mul_nonneg hκf hNf) (mul_nonneg hκg hNg),
        ENNReal.ofReal_mul hκf, ENNReal.ofReal_mul hκg]
      ring
    _ ≤ ENNReal.ofReal (∫ x in Ioo α α', ∫ y in Ioo β β',
        (f x - g y) ^ 2 * Real.exp (-(gammaRate k * (y - x)))) :=
      ENNReal.ofReal_le_ofReal hslice
    _ ≤ ∫⁻ x in Ioo α α', ENNReal.ofReal (∫ y in Ioo β β',
        (f x - g y) ^ 2 * Real.exp (-(gammaRate k * (y - x)))) :=
      ofReal_setIntegral_le_setLIntegral fun _ => integral_nonneg fun _ =>
        mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    _ ≤ _ := lintegral_mono fun _ => ofReal_setIntegral_le_setLIntegral fun _ =>
      mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

/-- Symmetric positive Gamma difference density. -/
def gammaDifference (f : ℝ → ℝ) (x y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((f x - f y) ^ 2 * archLevyDensity |y - x|)

theorem gammaDifference_comm (f : ℝ → ℝ) (x y : ℝ) :
    gammaDifference f x y = gammaDifference f y x := by
  unfold gammaDifference
  rw [abs_sub_comm, show (f x - f y) ^ 2 = (f y - f x) ^ 2 by ring]

theorem measurable_gammaDifference {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => gammaDifference f p.1 p.2) := by
  unfold gammaDifference
  have hk : Measurable (fun p : ℝ × ℝ => archLevyDensity |p.2 - p.1|) :=
    measurable_archLevyDensity.comp (measurable_snd.sub measurable_fst).abs
  fun_prop

/-- The kernel evaluated at the far endpoint distance, zero inside the interval. -/
def gammaFarCharge (a b y : ℝ) : ℝ≥0∞ :=
  if y ∈ Ioo a b then 0 else ENNReal.ofReal (archLevyDensity (max (y - a) (b - y)))

theorem measurable_gammaFarCharge (a b : ℝ) : Measurable (gammaFarCharge a b) := by
  unfold gammaFarCharge
  have hk : Measurable (fun y : ℝ => archLevyDensity (max (y - a) (b - y))) :=
    measurable_archLevyDensity.comp
      ((measurable_id.sub measurable_const).max (measurable_const.sub measurable_id))
  exact Measurable.ite measurableSet_Ioo measurable_const (ENNReal.measurable_ofReal.comp hk)

/-- A mean-zero interval pays its far-end charge against every exterior point. -/
theorem gamma_free_ge {a b y : ℝ} (hab : a < b) (hy : y ∉ Ioo a b) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (hf0 : ∫ x in Ioo a b, f x = 0) :
    ENNReal.ofReal (∫ x in Ioo a b, f x ^ 2) * gammaFarCharge a b y ≤
      ∫⁻ x in Ioo a b, gammaDifference f x y := by
  let d := max (y - a) (b - y)
  have hd : 0 < d := by
    have h1 := le_max_left (y - a) (b - y)
    have h2 := le_max_right (y - a) (b - y)
    change 0 < max (y - a) (b - y)
    linarith only [hab, h1, h2]
  have hk := (archLevyDensity_pos hd).le
  have hN : 0 ≤ ∫ x in Ioo a b, f x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hmass : (∫ x in Ioo a b, f x ^ 2) ≤ ∫ x in Ioo a b, (f x - f y) ^ 2 := by
    rw [setIntegral_sub_const_sq hab.le hf hf0]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hab.le) (sq_nonneg _))
  have hkernel : ∀ x ∈ Ioo a b, archLevyDensity d ≤ archLevyDensity |y - x| := by
    intro x hx
    have hxy : y ≠ x := fun he => hy (he.symm ▸ hx)
    have hpos : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hle : |y - x| ≤ d := by
      rw [abs_le]
      have h1 := le_max_left (y - a) (b - y)
      have h2 := le_max_right (y - a) (b - y)
      change -(max (y - a) (b - y)) ≤ y - x ∧ y - x ≤ max (y - a) (b - y)
      constructor <;> linarith only [hx.1, hx.2, h1, h2]
    exact strictAntiOn_archLevyDensity.antitoneOn hpos hd hle
  rw [gammaFarCharge, if_neg hy]
  change ENNReal.ofReal (∫ x in Ioo a b, f x ^ 2) * ENNReal.ofReal (archLevyDensity d) ≤ _
  calc
    _ = ENNReal.ofReal ((∫ x in Ioo a b, f x ^ 2) * archLevyDensity d) :=
      (ENNReal.ofReal_mul hN).symm
    _ ≤ ENNReal.ofReal ((∫ x in Ioo a b, (f x - f y) ^ 2) * archLevyDensity d) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hmass hk)
    _ = ENNReal.ofReal (∫ x in Ioo a b, (f x - f y) ^ 2 * archLevyDensity d) := by
      rw [integral_mul_const]
    _ ≤ ∫⁻ x in Ioo a b, ENNReal.ofReal ((f x - f y) ^ 2 * archLevyDensity d) :=
      ofReal_setIntegral_le_setLIntegral fun _ => mul_nonneg (sq_nonneg _) hk
    _ ≤ ∫⁻ x in Ioo a b, gammaDifference f x y := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hkernel x hx) (sq_nonneg _))

#print axioms gamma_twoInterval_ge
#print axioms gamma_free_ge

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
