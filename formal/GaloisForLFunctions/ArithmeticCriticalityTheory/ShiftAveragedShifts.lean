import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftAveragedKernel

/-!
# Averaging one shift over the shift parameter

For each fixed shift `t` the reflected and same-side variations of the shifted ground states,
integrated over `a > 0`, are variations against the averaged kernel `K(x,y) = G(x−y) − G(x+y)`:

    ∫_0^∞ ∫_0^t m_a(x) m_a(t−x) (u(x) − u(t−x))² dx da = ∫_0^t K(x, t−x) (u(x) − u(t−x))² dx,
    ∫_0^∞ ∫_{x>0} m_a(x) m_a(x+t) (u(x) − u(x+t))² dx da = ∫_{x>0} K(x, x+t) (u(x) − u(x+t))² dx.

The exchange of the two integrations is justified by the product majorant
`(Φ(0) 1_{a<c} + Φ(a − c)) · Φ(0) · 4M²`, since `Φ(x − a) ≤ Φ(0) 1_{a<c} + Φ(a − c)` for
`0 ≤ x ≤ c`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The averaged kernel `K(x,y) = G(x − y) − G(x + y)`. -/
def averagedKernel (x y : ℝ) : ℝ := riemannAutocorr (x - y) - riemannAutocorr (x + y)

theorem averagedKernel_eq_integral (x y : ℝ) :
    averagedKernel x y = ∫ a in Ioi (0 : ℝ), shiftDifference a x * shiftDifference a y :=
  (integral_Ioi_shiftDifference_mul_shiftDifference x y).symm

theorem averagedKernel_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ averagedKernel x y := by
  rw [averagedKernel_eq_integral]
  exact setIntegral_nonneg measurableSet_Ioi fun a ha =>
    mul_nonneg (shiftDifference_nonneg_of_nonneg (mem_Ioi.mp ha).le hx)
      (shiftDifference_nonneg_of_nonneg (mem_Ioi.mp ha).le hy)

theorem averagedKernel_le_zero_point (x y : ℝ) : averagedKernel x y ≤ riemannKernelReal 0 := by
  unfold averagedKernel
  have := riemannAutocorr_nonneg (x + y)
  have := riemannAutocorr_le_zero_point (x - y)
  linarith

theorem continuous_riemannAutocorr : Continuous riemannAutocorr := by
  sorry

/-! ### The product majorant -/

/-- `Φ(x − a) ≤ Φ(0) 1_{a < c} + Φ(a − c)` for `0 ≤ x ≤ c`. -/
theorem riemannKernelReal_sub_le_majorant {a x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ c) :
    riemannKernelReal (x - a) ≤
      riemannKernelReal 0 * (Ioo (0 : ℝ) c).indicator (fun _ => (1 : ℝ)) a +
        riemannKernelReal (a - c) := by
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hK := (riemannKernelReal_pos (a - c)).le
  rw [Set.indicator_apply]
  split_ifs with h
  · have := riemannKernelReal_le_zero_point (x - a)
    linarith
  · rcases le_or_gt a 0 with ha | ha
    · -- a ≤ 0 ≤ x ≤ c: |x − a| = x − a ≥ c − a... hmm need Φ(x−a) ≤ Φ(a − c): |a − c| = c − a ≥ x − a = |x − a| ✓
      have h1 : riemannKernelReal (x - a) ≤ riemannKernelReal (c - a) :=
        riemannKernelReal_antitone_of_nonneg (by linarith) (by linarith)
      rw [show c - a = -(a - c) by ring, riemannKernelReal_neg'] at h1
      linarith
    · -- a ≥ c ≥ x: |x − a| = a − x ≥ a − c ≥ 0
      have hac : c ≤ a := by
        rw [mem_Ioo, not_and_or] at h
        rcases h with h | h
        · exact absurd ha (not_lt.mpr (not_lt.mp h))
        · exact not_lt.mp h
      have h1 : riemannKernelReal (x - a) ≤ riemannKernelReal (a - c) := by
        rw [show x - a = -(a - x) by ring, riemannKernelReal_neg']
        exact riemannKernelReal_antitone_of_nonneg (by linarith) (by linarith)
      linarith

theorem integrableOn_majorant (c : ℝ) :
    IntegrableOn (fun a : ℝ => riemannKernelReal 0 * (Ioo (0 : ℝ) c).indicator (fun _ => (1 : ℝ)) a +
      riemannKernelReal (a - c)) (Ioi 0) := by
  have h1 : Integrable fun a : ℝ => riemannKernelReal 0 * (Ioo (0 : ℝ) c).indicator (fun _ => (1 : ℝ)) a := by
    have := ((integrableOn_const (s := Ioo (0 : ℝ) c) (C := (1 : ℝ)) measure_Ioo_lt_top.ne).integrable_indicator
      measurableSet_Ioo).const_mul (riemannKernelReal 0)
    exact this
  exact ((h1.add (integrable_riemannKernelReal.comp_sub_right c))).integrableOn

/-! ### Averaging the reflected variation -/

/-- The averaged reflected variation of one shift. -/
def averagedReflectedShift (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) t, averagedKernel x (t - x) * (u x - u (t - x)) ^ 2

/-- The averaged same-side variation of one shift. -/
def averagedSameSideShift (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), averagedKernel x (x + t) * (u x - u (x + t)) ^ 2

theorem integrable_reflected_prod {u : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |u x| ≤ M) (hu : Continuous u)
    {t : ℝ} (ht : 0 < t) :
    Integrable (Function.uncurry fun a x =>
        shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) t))) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hdom : Integrable (fun z : ℝ × ℝ =>
      (riemannKernelReal 0 * (Ioo (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) z.1 +
        riemannKernelReal (z.1 - t)) * (riemannKernelReal 0 * (4 * M ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) t))) :=
    Integrable.mul_prod (integrableOn_majorant t) (integrableOn_const measure_Ioo_lt_top.ne)
  have hmeas : Measurable fun z : ℝ × ℝ =>
      shiftDifference z.1 z.2 * shiftDifference z.1 (t - z.2) * (u z.2 - u (t - z.2)) ^ 2 := by
    sorry
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioo) fun z hz => ?_
  have ha : 0 < z.1 := hz.1
  have hx : 0 < z.2 := hz.2.1
  have hxt : z.2 < t := hz.2.2
  show ‖shiftDifference z.1 z.2 * shiftDifference z.1 (t - z.2) * (u z.2 - u (t - z.2)) ^ 2‖ ≤
    (riemannKernelReal 0 * (Ioo (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) z.1 +
      riemannKernelReal (z.1 - t)) * (riemannKernelReal 0 * (4 * M ^ 2))
  have h1 : |shiftDifference z.1 z.2| ≤ riemannKernelReal (z.2 - z.1) :=
    abs_shiftDifference_le_kernel_of_nonneg ha.le hx.le
  have h1' := (riemannKernelReal_sub_le_majorant hx.le hxt.le (a := z.1))
  have h2 : |shiftDifference z.1 (t - z.2)| ≤ riemannKernelReal 0 := abs_shiftDifference_le a _
  sorry

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
