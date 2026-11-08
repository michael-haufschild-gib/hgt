import GaloisForLFunctions.RHTower.HamburgerStabilityCriticalLine
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The boundary of an integrable functional-equation defect

Hamburger's Laplace kernel contains a complex power of `πz²`, whose principal branch jumps
on the imaginary axis. Factoring this power on the right half-plane gives a continuous
extension to its nonzero boundary. An integrable defect then has continuous boundary values
away from zero, bounded by a constant times `|y|⁻¹ᐟ²`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ExactEventTheory

/-- The factored kernel has no branch discontinuity on the nonzero imaginary axis. -/
def boundaryPairKernel (v : ℝ) (z : ℂ) : ℂ :=
  gammaPair v * (z * (Real.pi : ℂ) ^ (-(1 - linePt v / 2)) *
    z ^ (2 * (-(1 - linePt v / 2))))

theorem boundaryPairKernel_eq {z : ℂ} (hz : 0 < z.re) (v : ℝ) :
    boundaryPairKernel v z = pairKernel v z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  let w : ℂ := -(1 - linePt v / 2)
  have hmul : ((Real.pi : ℂ) * z ^ 2) ^ w = (Real.pi : ℂ) ^ w * (z ^ 2) ^ w := by
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hπ (pow_ne_zero 2 hz0)),
      Complex.log_ofReal_mul Real.pi_pos (pow_ne_zero 2 hz0),
      Complex.ofReal_log Real.pi_pos.le, add_mul, Complex.exp_add,
      ← Complex.cpow_def_of_ne_zero hπ, ← Complex.cpow_def_of_ne_zero (pow_ne_zero 2 hz0)]
  have ha := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have hs : z ^ (2 * w) = (z ^ (2 : ℕ)) ^ w :=
    Complex.cpow_nat_mul' (n := 2) (by norm_num; linarith only [ha.1])
      (by norm_num; linarith only [ha.2]) w
  dsimp only [boundaryPairKernel, pairKernel]
  change gammaPair v * (z * (Real.pi : ℂ) ^ w * z ^ (2 * w)) =
    gammaPair v * (z * ((Real.pi : ℂ) * z ^ 2) ^ w)
  rw [hmul, hs]
  ring

private theorem mem_slitPlane_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hp : 0 < z.re
  · exact Or.inl hp
  · right
    intro hi
    apply hz0
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith only [hz, hp]
    · simpa only [Complex.zero_im] using hi

theorem continuousAt_boundaryPairKernel (v : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hz0 : z ≠ 0) : ContinuousAt (boundaryPairKernel v) z := by
  unfold boundaryPairKernel
  exact continuousAt_const.mul ((continuousAt_id.mul continuousAt_const).mul
    (continuousAt_cpow_const (mem_slitPlane_of_re_nonneg hz hz0)))

theorem continuous_boundaryPairKernel_parameter {z : ℂ} (hz0 : z ≠ 0) :
    Continuous fun v : ℝ => boundaryPairKernel v z := by
  unfold boundaryPairKernel
  exact continuous_gammaPair.mul ((continuous_const.mul
    (Continuous.const_cpow (by unfold linePt; fun_prop)
      (Or.inl (by exact_mod_cast Real.pi_ne_zero)))).mul
      (Continuous.const_cpow (by unfold linePt; fun_prop) (Or.inl hz0)))

/-- The interior kernel bound persists up to both sides of the imaginary axis. -/
theorem norm_boundaryPairKernel_le (v : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    ‖boundaryPairKernel v z‖ ≤ 3 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
  have ht : Tendsto (fun ε : ℝ => (ε : ℂ) + z) (𝓝[>] 0) (𝓝 z) := by
    simpa using ((by fun_prop : Continuous fun ε : ℝ => (ε : ℂ) + z).tendsto 0
      ).mono_left nhdsWithin_le_nhds
  have hleft := (continuousAt_boundaryPairKernel v hz hz0).norm.tendsto.comp ht
  have hright := ((Real.continuousAt_rpow_const ‖z‖ (-(1 / 2 : ℝ))
    (Or.inl (norm_ne_zero_iff.mpr hz0))).tendsto.comp ht.norm).const_mul 3
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hpos : 0 < ((ε : ℂ) + z).re := by
    simpa only [Complex.add_re, Complex.ofReal_re] using add_pos_of_pos_of_nonneg hε hz
  dsimp only [Function.comp_apply]
  rw [boundaryPairKernel_eq hpos]
  have hb := norm_pairKernel_le v hpos
  have he : Real.exp (-(|v| * (((ε : ℂ) + z).re / ‖(ε : ℂ) + z‖))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (abs_nonneg _) (pos_re_div_norm hpos).le))
  exact hb.trans (mul_le_of_le_one_right (by positivity) he)

/-- The Laplace defect with its continuous branch at nonzero boundary points. -/
def closedDefectLaplace (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, g t * boundaryPairKernel (2 * t) z

theorem closedDefectLaplace_eq {z : ℂ} (hz : 0 < z.re) (g : ℝ → ℂ) :
    closedDefectLaplace g z = defectLaplace g z := by
  simp only [closedDefectLaplace, defectLaplace, boundaryPairKernel_eq hz]

theorem integrable_closedDefectLaplace_integrand {g : ℝ → ℂ} (hg : Integrable g)
    {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    Integrable fun t : ℝ => g t * boundaryPairKernel (2 * t) z := by
  refine (hg.norm.mul_const (3 * ‖z‖ ^ (-(1 / 2 : ℝ)))).mono'
    (hg.aestronglyMeasurable.mul ((continuous_boundaryPairKernel_parameter hz0).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  exact Eventually.of_forall fun t => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_boundaryPairKernel_le (2 * t) hz hz0) (norm_nonneg _)

theorem norm_closedDefectLaplace_le {g : ℝ → ℂ} (hg : Integrable g)
    {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    ‖closedDefectLaplace g z‖ ≤
      3 / (2 * Real.pi) * (∫ t, ‖g t‖) * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
  have hb := norm_integral_le_of_norm_le
    (f := fun t : ℝ => g t * boundaryPairKernel (2 * t) z)
    (hg.norm.mul_const (3 * ‖z‖ ^ (-(1 / 2 : ℝ))))
    (Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_boundaryPairKernel_le (2 * t) hz hz0) (norm_nonneg _))
  rw [integral_mul_const] at hb
  unfold closedDefectLaplace
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, g t * boundaryPairKernel (2 * t) z‖ ≤
      1 / (2 * Real.pi) * ((∫ t, ‖g t‖) * (3 * ‖z‖ ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Dominated convergence gives continuity through the nonzero imaginary boundary. -/
theorem continuousOn_closedDefectLaplace {g : ℝ → ℂ} (hg : Integrable g) :
    ContinuousOn (closedDefectLaplace g) {z : ℂ | 0 ≤ z.re ∧ z ≠ 0} := by
  intro z hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz.2
  have hnear : ∀ᶠ w : ℂ in 𝓝 z, ‖z‖ / 2 < ‖w‖ :=
    continuous_norm.continuousAt.tendsto.eventually (eventually_gt_nhds (half_lt_self hn))
  have hc : ContinuousWithinAt (fun w : ℂ => ∫ t : ℝ, g t * boundaryPairKernel (2 * t) w)
      {w : ℂ | 0 ≤ w.re ∧ w ≠ 0} z := by
    apply continuousWithinAt_of_dominated
      (bound := fun t : ℝ => ‖g t‖ * (3 * (‖z‖ / 2) ^ (-(1 / 2 : ℝ))))
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact (integrable_closedDefectLaplace_integrand hg hw.1 hw.2).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with w hw hnw
      apply Eventually.of_forall
      intro t
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_boundaryPairKernel_le (2 * t) hw.1 hw.2).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (half_pos hn) hnw.le (by norm_num)) (by norm_num))
    · exact hg.norm.mul_const _
    · exact Eventually.of_forall fun t =>
        (continuousAt_const.mul (continuousAt_boundaryPairKernel (2 * t) hz.1 hz.2)).continuousWithinAt
  exact continuousWithinAt_const.mul hc

/-- Boundary values from the right on both rays, normalized to zero at the origin. -/
def defectBoundary (g : ℝ → ℂ) (y : ℝ) : ℂ := closedDefectLaplace g ((y : ℂ) * I)

@[simp] theorem defectBoundary_zero (g : ℝ → ℂ) : defectBoundary g 0 = 0 := by
  simp [defectBoundary, closedDefectLaplace, boundaryPairKernel]

theorem continuousOn_defectBoundary {g : ℝ → ℂ} (hg : Integrable g) :
    ContinuousOn (defectBoundary g) {y : ℝ | y ≠ 0} := by
  apply (continuousOn_closedDefectLaplace hg).comp (by fun_prop)
  intro y hy
  exact ⟨by simp, mul_ne_zero (by exact_mod_cast hy) I_ne_zero⟩

theorem norm_defectBoundary_le {g : ℝ → ℂ} (hg : Integrable g) (y : ℝ) :
    ‖defectBoundary g y‖ ≤
      3 / (2 * Real.pi) * (∫ t, ‖g t‖) * |y| ^ (-(1 / 2 : ℝ)) := by
  by_cases hy : y = 0
  · simp [hy]
  have hh := norm_closedDefectLaplace_le hg (z := (y : ℂ) * I) (by simp)
    (mul_ne_zero (by exact_mod_cast hy) I_ne_zero)
  simpa only [defectBoundary, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one] using hh

theorem measurable_defectBoundary {g : ℝ → ℂ} (hg : Integrable g) :
    Measurable (defectBoundary g) :=
  measurable_of_continuousOn_compl_singleton 0 (continuousOn_defectBoundary hg)

/-- The square-root singularity is locally integrable, including at zero. -/
theorem locallyIntegrable_defectBoundary {g : ℝ → ℂ} (hg : Integrable g) :
    LocallyIntegrable (defectBoundary g) := by
  refine locallyIntegrable_of_norm_le_rpow
    (C := 3 / (2 * Real.pi) * ∫ t, ‖g t‖) (α := 1 / 2) (by simp) (by norm_num)
    (Eventually.of_forall fun y => ?_) (measurable_defectBoundary hg).aestronglyMeasurable
  simpa only [Real.norm_eq_abs] using norm_defectBoundary_le hg y

/-- Boundary values vanish along every family whose absolute ordinate tends to infinity. -/
theorem tendsto_defectBoundary_of_abs_atTop {g : ℝ → ℂ} (hg : Integrable g)
    {α : Type*} {l : Filter α} {y : α → ℝ} (hy : Tendsto (fun x => |y x|) l atTop) :
    Tendsto (fun x => defectBoundary g (y x)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
    (Eventually.of_forall fun x => norm_defectBoundary_le hg (y x)) ?_
  simpa using ((tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp hy
    ).const_mul (3 / (2 * Real.pi) * ∫ t, ‖g t‖)

theorem tendsto_defectLaplace_boundary {g : ℝ → ℂ} (hg : Integrable g) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun ε : ℝ => defectLaplace g ((ε : ℂ) + (y : ℂ) * I))
      (𝓝[>] 0) (𝓝 (defectBoundary g y)) := by
  have hc := continuousOn_closedDefectLaplace hg ((y : ℂ) * I)
    ⟨by simp, mul_ne_zero (by exact_mod_cast hy) I_ne_zero⟩
  have ht : Tendsto (fun ε : ℝ => (ε : ℂ) + (y : ℂ) * I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.re ∧ z ≠ 0}] ((y : ℂ) * I)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((by fun_prop : Continuous fun ε : ℝ => (ε : ℂ) + (y : ℂ) * I).tendsto 0
        ).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hr : 0 < ((ε : ℂ) + (y : ℂ) * I).re := by simpa using hε
      exact ⟨hr.le, fun h => by simp [h] at hr⟩
  apply (hc.tendsto.comp ht).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact closedDefectLaplace_eq (by simpa using hε) g

theorem continuous_defectLaplace_vertical {g : ℝ → ℂ} (hg : Integrable g)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous fun y : ℝ => defectLaplace g ((ε : ℂ) + (y : ℂ) * I) := by
  have hc : ContinuousOn (fun y : ℝ =>
      closedDefectLaplace g ((ε : ℂ) + (y : ℂ) * I)) univ := by
    apply (continuousOn_closedDefectLaplace hg).comp (by fun_prop)
    intro y _
    have hr : 0 < ((ε : ℂ) + (y : ℂ) * I).re := by simpa using hε
    exact ⟨hr.le, fun h => by simp [h] at hr⟩
  convert continuousOn_univ.mp hc using 1
  funext y
  exact (closedDefectLaplace_eq (by simpa using hε) g).symm

/-- Compact continuous tests may pass to the imaginary boundary, even through zero. -/
theorem tendsto_integral_defectLaplace_boundary {g : ℝ → ℂ} (hg : Integrable g)
    {K : ℝ → ℂ} (hK : Continuous K) (hKs : HasCompactSupport K) :
    Tendsto (fun ε : ℝ => ∫ y : ℝ, K y * defectLaplace g ((ε : ℂ) + (y : ℂ) * I))
      (𝓝[>] 0) (𝓝 (∫ y : ℝ, K y * defectBoundary g y)) := by
  let C : ℝ := 3 / (2 * Real.pi) * ∫ t, ‖g t‖
  have hC : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  have hloc : LocallyIntegrable (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) := by
    have hm : Measurable (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) := by fun_prop
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1 / 2)
      (by simp) (by norm_num) ?_ hm.aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), one_mul]
      exact le_rfl
  have hdom : Integrable (fun y : ℝ => (‖K y‖ * |y| ^ (-(1 / 2 : ℝ))) * C) :=
    (hloc.integrable_smul_left_of_hasCompactSupport hK.norm
      (hasCompactSupport_norm_iff.mpr hKs)).mul_const C
  apply tendsto_integral_filter_of_dominated_convergence
    (fun y : ℝ => (‖K y‖ * |y| ^ (-(1 / 2 : ℝ))) * C)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hK.mul (continuous_defectLaplace_vertical hg hε)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
    have hr : 0 < ((ε : ℂ) + (y : ℂ) * I).re := by simpa using hε
    have hz0 : (ε : ℂ) + (y : ℂ) * I ≠ 0 := fun h => by simp [h] at hr
    have hi : |y| ≤ ‖(ε : ℂ) + (y : ℂ) * I‖ := by
      simpa using Complex.abs_im_le_norm ((ε : ℂ) + (y : ℂ) * I)
    have hb : ‖defectLaplace g ((ε : ℂ) + (y : ℂ) * I)‖ ≤
        C * |y| ^ (-(1 / 2 : ℝ)) := by
      rw [← closedDefectLaplace_eq hr]
      exact (norm_closedDefectLaplace_le hg hr.le hz0).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hy) hi (by norm_num)) hC)
    rw [norm_mul]
    calc ‖K y‖ * ‖defectLaplace g ((ε : ℂ) + (y : ℂ) * I)‖ ≤
        ‖K y‖ * (C * |y| ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by ring
  · exact hdom
  · filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
    exact tendsto_const_nhds.mul (tendsto_defectLaplace_boundary hg hy)

end GaloisForLFunctions.ExactEventTheory

#print axioms GaloisForLFunctions.ExactEventTheory.tendsto_defectLaplace_boundary
#print axioms GaloisForLFunctions.ExactEventTheory.locallyIntegrable_defectBoundary
#print axioms GaloisForLFunctions.ExactEventTheory.tendsto_defectBoundary_of_abs_atTop
#print axioms GaloisForLFunctions.ExactEventTheory.tendsto_integral_defectLaplace_boundary
