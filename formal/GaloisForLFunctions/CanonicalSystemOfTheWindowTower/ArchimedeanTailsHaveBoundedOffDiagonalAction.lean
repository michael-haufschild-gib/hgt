import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.PositiveLevelTruncationsStayInTheWeilDomain
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-!
# Bounded off-diagonal action after deleting short archimedean jumps

In theta–cosh mass coordinates the symmetric archimedean kernel is
`ω(|x-y|)/(cosh(x/2)cosh(y/2))`. Removing lags below a positive cutoff makes
this kernel uniformly bounded. The finite mass measure then gives a bounded
pointwise readout on every completed source.
-/

open MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open _root_.RHTower _root_.RHTower.CHMDDoobGraph _root_.RHTower.CHMDPolar
open _root_.RHTower.WeilLevyCoshCrossover

/-- The archimedean kernel in the finite theta–cosh mass measure. -/
def archTailKernel (δ x y : ℝ) : ℝ :=
  if δ ≤ |x - y| then
    archLevyDensity |x - y| / (Real.cosh (x / 2) * Real.cosh (y / 2))
  else 0

def archTailBound (δ : ℝ) : ℝ := (1 - Real.exp (-2 * δ))⁻¹

theorem archTailBound_pos {δ : ℝ} (hδ : 0 < δ) : 0 < archTailBound δ := by
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hδ]))

theorem archTailKernel_symm (δ x y : ℝ) : archTailKernel δ x y = archTailKernel δ y x := by
  simp only [archTailKernel, abs_sub_comm x y, mul_comm]

theorem archTailKernel_nonneg {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    0 ≤ archTailKernel δ x y := by
  unfold archTailKernel
  split_ifs with hxy
  · exact div_nonneg (archLevyDensity_pos (hδ.trans_le hxy)).le
      (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).le
  · exact le_rfl

theorem archTailKernel_le {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    archTailKernel δ x y ≤ archTailBound δ := by
  unfold archTailKernel
  split_ifs with hxy
  · have hw := archLevyDensity_le_of_le hδ hxy
    have he : Real.exp (-(1 / 2) * |x - y|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith only [abs_nonneg (x - y)])
    have hb : archLevyDensity |x - y| ≤ archTailBound δ :=
      hw.trans (by simpa only [archTailBound, mul_one] using
        mul_le_mul_of_nonneg_left he (archTailBound_pos hδ).le)
    apply (div_le_iff₀ (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))).mpr
    have hc : 1 ≤ Real.cosh (x / 2) * Real.cosh (y / 2) := by
      simpa only [one_mul] using mul_le_mul (Real.one_le_cosh (x / 2))
        (Real.one_le_cosh (y / 2)) (by norm_num : (0 : ℝ) ≤ 1) (Real.cosh_pos _).le
    exact hb.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hc (archTailBound_pos hδ).le)
  · exact (archTailBound_pos hδ).le

theorem measurable_archTailKernel (δ x : ℝ) : Measurable (archTailKernel δ x) := by
  have hd : Measurable (fun y : ℝ => |x - y|) := by fun_prop
  exact Measurable.ite (measurableSet_le measurable_const hd)
    ((measurable_archLevyDensity.comp hd).div (by fun_prop)) measurable_const

theorem measurable_archTailKernel_pair (δ : ℝ) :
    Measurable (fun p : ℝ × ℝ => archTailKernel δ p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => |p.1 - p.2|) := by fun_prop
  exact Measurable.ite (measurableSet_le measurable_const hd)
    ((measurable_archLevyDensity.comp hd).div (by fun_prop)) measurable_const

theorem memLp_archTailKernel {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    MemLp (archTailKernel δ x) 2 massMeasure := by
  apply (memLp_const (archTailBound δ)).mono
    (measurable_archTailKernel δ x).aestronglyMeasurable
  filter_upwards [] with y
  simpa only [Real.norm_eq_abs, abs_of_nonneg (archTailKernel_nonneg hδ x y),
    abs_of_pos (archTailBound_pos hδ)] using archTailKernel_le hδ x y

/-- A cutoff archimedean row is an actual mass-space vector. -/
def archTailRow (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : MassSpace :=
  (memLp_archTailKernel hδ x).toLp (archTailKernel δ x)

theorem archTailRow_norm_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ‖archTailRow δ hδ x‖ ≤ archTailBound δ := by
  have hn : ‖archTailRow δ hδ x‖ ≤ ‖(constantLift (archTailBound δ)).val.fst‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(memLp_archTailKernel hδ x).coeFn_toLp,
      (memLp_const (archTailBound δ) :
        MemLp (fun _ : ℝ => archTailBound δ) 2 massMeasure).coeFn_toLp] with y hy hc
    change archTailRow δ hδ x y = archTailKernel δ x y at hy
    change (constantLift (archTailBound δ)).val.fst y = archTailBound δ at hc
    change ‖archTailRow δ hδ x y‖ ≤ _
    rw [hy, hc]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (archTailKernel_nonneg hδ x y),
      abs_of_pos (archTailBound_pos hδ)] using archTailKernel_le hδ x y
  have hc := constantLift_mass (archTailBound δ)
  have hb := archTailBound_pos hδ
  nlinarith only [hn, hc, hb, norm_nonneg ((constantLift (archTailBound δ)).val.fst),
    norm_nonneg (archTailRow δ hδ x)]

/-- The off-diagonal tail, acting on a completed inverse-Doob source. -/
def archTailReadout (δ : ℝ) (hδ : 0 < δ) (F : MassSpace) (x : ℝ) : ℝ :=
  inner ℝ (archTailRow δ hδ x) F

theorem archTailReadout_eq_integral (δ : ℝ) (hδ : 0 < δ) (F : MassSpace) (x : ℝ) :
    archTailReadout δ hδ F x = ∫ y, archTailKernel δ x y * F y ∂massMeasure := by
  rw [archTailReadout, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_archTailKernel hδ x).coeFn_toLp] with y hy
  change archTailRow δ hδ x y = archTailKernel δ x y at hy
  change inner ℝ (archTailRow δ hδ x y) (F y) = _
  rw [hy]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- The tail bound is uniform in position and uses the original mass norm. -/
theorem archTailReadout_abs_le (δ : ℝ) (hδ : 0 < δ) (F : MassSpace) (x : ℝ) :
    |archTailReadout δ hδ F x| ≤ archTailBound δ * ‖F‖ := by
  change |inner ℝ (archTailRow δ hδ x) F| ≤ _
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (archTailRow_norm_le hδ x) (norm_nonneg F))

#print axioms archTailKernel_le
#print axioms archTailReadout_abs_le

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
