import GaloisForLFunctions.HTGeometry.StrelitzMaximumSlope
import GaloisForLFunctions.HTGeometry.StrelitzLogRadialDerivatives

/-!
# Touching-slope bounds at maximum-modulus points

The left slope of a convex function is the supremum of its strict left secants.  If a
differentiable function touches a convex majorant from below, its derivative lies between the
majorant's canonical left and right slopes.  Applied to a fixed radial slice through a
maximum-modulus point, this sandwiches the real Euler logarithmic derivative between the exact
one-sided logarithmic maximum slopes.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set

noncomputable section

/-- Choice-free left slope of a convex real function: the supremum of all strict left secants. -/
def convexLeftSlope (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup (Set.range fun y : Set.Iio x => slope f x y.1)

/-- Left secants of a globally convex real function have a finite common upper bound. -/
theorem bddAbove_range_slope_Iio_of_convexOn {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (x : ℝ) :
    BddAbove (Set.range fun y : Set.Iio x => slope f x y.1) := by
  refine ⟨convexRightSlope f x, ?_⟩
  rintro q ⟨y, rfl⟩
  exact slope_le_convexRightSlope hf y.property

/-- Every strict left secant is at most the canonical left slope. -/
theorem slope_le_convexLeftSlope {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {y x : ℝ} (hyx : y < x) :
    slope f x y ≤ convexLeftSlope f x := by
  apply le_csSup (bddAbove_range_slope_Iio_of_convexOn hf x)
  exact ⟨⟨y, hyx⟩, rfl⟩

/-- Canonical left slope never exceeds canonical right slope. -/
theorem convexLeftSlope_le_convexRightSlope {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (x : ℝ) :
    convexLeftSlope f x ≤ convexRightSlope f x := by
  apply csSup_le (Set.range_nonempty _)
  rintro q ⟨y, rfl⟩
  exact slope_le_convexRightSlope hf y.property

/-- A differentiable function touching a convex majorant from below has derivative no smaller
than the majorant's canonical left slope. -/
theorem convexLeftSlope_le_of_hasDerivAt_of_eventually_le
    {f g : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {x d : ℝ}
    (hg : HasDerivAt g d x) (hle : g ≤ᶠ[nhds x] f) (heq : g x = f x) :
    convexLeftSlope f x ≤ d := by
  apply csSup_le (Set.range_nonempty _)
  rintro q ⟨y, rfl⟩
  have htend : Tendsto (slope g x) (nhdsWithin x (Set.Iio x)) (nhds d) :=
    hg.tendsto_slope.mono_left (nhdsWithin_mono x (by
      intro t ht htx
      exact ht.ne htx))
  apply ge_of_tendsto htend
  filter_upwards [hle.filter_mono inf_le_left, self_mem_nhdsWithin,
      (eventually_gt_nhds y.property).filter_mono inf_le_left] with t hgt htx hyt
  calc
    slope f x y ≤ slope f x t := by
      simpa [slope, div_eq_mul_inv, mul_comm] using
        hf.secant_mono (a := x) (x := y) (y := t)
          (by simp) (by simp) (by simp) (ne_of_lt y.property) (ne_of_lt htx) hyt.le
    _ ≤ slope g x t := by
      have hsub : g t - g x ≤ f t - f x := by
        rw [heq]
        exact sub_le_sub_right hgt _
      have hinv : (t - x)⁻¹ ≤ 0 := inv_nonpos.mpr (sub_nonpos.mpr htx.le)
      simpa [slope, vsub_eq_sub, smul_eq_mul] using
        mul_le_mul_of_nonpos_left hsub hinv

/-- A differentiable function touching a convex majorant from below has derivative no larger
than the majorant's canonical right slope. -/
theorem le_convexRightSlope_of_hasDerivAt_of_eventually_le
    {f g : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {x d : ℝ}
    (hg : HasDerivAt g d x) (hle : g ≤ᶠ[nhds x] f) (heq : g x = f x) :
    d ≤ convexRightSlope f x := by
  apply le_csInf (Set.range_nonempty _)
  rintro q ⟨y, rfl⟩
  have htend : Tendsto (slope g x) (nhdsWithin x (Set.Ioi x)) (nhds d) :=
    hg.tendsto_slope.mono_left (nhdsWithin_mono x (by
      intro t ht htx
      exact ht.ne htx.symm))
  apply le_of_tendsto htend
  filter_upwards [hle.filter_mono inf_le_left, self_mem_nhdsWithin,
      (eventually_lt_nhds y.property).filter_mono inf_le_left] with t hgt hxt hty
  calc
    slope g x t ≤ slope f x t := by
      have hsub : g t - g x ≤ f t - f x := by
        rw [heq]
        exact sub_le_sub_right hgt _
      have hinv : 0 ≤ (t - x)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hxt.le)
      simpa [slope, vsub_eq_sub, smul_eq_mul] using
        mul_le_mul_of_nonneg_left hsub hinv
    _ ≤ slope f x y := by
      simpa [slope, div_eq_mul_inv, mul_comm] using
        hf.secant_mono (a := x) (x := t) (y := y)
          (by simp) (by simp) (by simp) (ne_of_gt hxt) (ne_of_gt y.property) hty.le

/-- Two-sided touching-slope sandwich. -/
theorem convexSlope_sandwich_of_hasDerivAt_of_eventually_le
    {f g : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {x d : ℝ}
    (hg : HasDerivAt g d x) (hle : g ≤ᶠ[nhds x] f) (heq : g x = f x) :
    convexLeftSlope f x ≤ d ∧ d ≤ convexRightSlope f x := by
  exact ⟨convexLeftSlope_le_of_hasDerivAt_of_eventually_le hf hg hle heq,
    le_convexRightSlope_of_hasDerivAt_of_eventually_le hf hg hle heq⟩

/-- Canonical left logarithmic-radius slope of the exact circle maximum norm. -/
def strelitzMaximumLeftSlope (a : ℕ → ℂ) (x : ℝ) : ℝ :=
  convexLeftSlope (strelitzLogMaximum a) x

/-- A normalized logarithmic radial path has logarithmic radius equal to its parameter. -/
theorem norm_logRadialPath_log_norm {z : ℂ} (hz : 0 < ‖z‖) (t : ℝ) :
    ‖logRadialPath (Real.log ‖z‖) z t‖ = Real.exp t := by
  rw [logRadialPath, norm_mul, Complex.norm_exp]
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [Real.exp_sub, Real.exp_log hz]
  exact div_mul_cancel₀ _ (ne_of_gt hz)

/-- At a nonvanishing maximum-modulus point, the real Euler logarithmic derivative lies between
the exact left and right logarithmic maximum slopes. -/
theorem strelitzMaximumSlope_sandwich_of_mem_circleMaximumSet
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {z : ℂ} (hz : 0 < ‖z‖) (hmax : z ∈ circleMaximumSet (coeffFun a)) :
    strelitzMaximumLeftSlope a (Real.log ‖z‖) ≤
        (eulerLogDeriv (coeffFun a) z).re ∧
      (eulerLogDeriv (coeffFun a) z).re ≤
        strelitzMaximumSlope a (Real.log ‖z‖) := by
  have hnormeq :=
    (mem_circleMaximumSet_iff_norm_eq_coeffCircleMaximumNorm ha hz).mp hmax
  have hfz : coeffFun a z ≠ 0 := by
    rw [← norm_ne_zero_iff, hnormeq]
    exact ne_of_gt (coeffCircleMaximumNorm_pos ha hn₀ hz)
  let x := Real.log ‖z‖
  let g : ℝ → ℝ := fun t => Real.log ‖coeffFun a (logRadialPath x z t)‖
  have hg : HasDerivAt g (eulerLogDeriv (coeffFun a) z).re x := by
    simpa [g, x] using
      hasDerivAt_log_norm_logRadialPath (differentiable_coeffFun ha z) hfz
  have hcomp : HasDerivAt (fun t => coeffFun a (logRadialPath x z t))
      (deriv (coeffFun a) z * z) x := by
    have hf : HasDerivAt (coeffFun a) (deriv (coeffFun a) z)
        (logRadialPath x z x) := by
      simpa using (differentiable_coeffFun ha z).hasDerivAt
    exact hf.comp x (hasDerivAt_logRadialPath x z)
  have hnonzero : ∀ᶠ t : ℝ in nhds x, coeffFun a (logRadialPath x z t) ≠ 0 :=
    hcomp.continuousAt.eventually_ne (by simpa [x] using hfz)
  have hle : g ≤ᶠ[nhds x] strelitzLogMaximum a := by
    filter_upwards [hnonzero] with t ht
    have hpathnorm : ‖logRadialPath x z t‖ = Real.exp t := by
      simpa [x] using norm_logRadialPath_log_norm hz t
    have hbound := norm_coeffFun_le_coeffCircleMaximumNorm_of_norm_eq
      ha (Real.exp_pos t) hpathnorm
    exact Real.log_le_log (norm_pos_iff.mpr ht) hbound
  have heq : g x = strelitzLogMaximum a x := by
    dsimp [g, x]
    rw [logRadialPath_self, strelitzLogMaximum, Real.exp_log hz, hnormeq]
  exact convexSlope_sandwich_of_hasDerivAt_of_eventually_le
    (convexOn_strelitzLogMaximum ha hn₀) hg hle heq

end

end GaloisForLFunctions.HTGeometry
