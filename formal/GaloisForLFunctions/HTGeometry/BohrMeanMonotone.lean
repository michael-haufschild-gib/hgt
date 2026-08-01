import GaloisForLFunctions.HTGeometry.BohrMeanValue
import GaloisForLFunctions.HTGeometry.BohrSpectrum

/-!
# The Bohr mean is monotone

Window averages over `[0,T]` are monotone in the integrand, and the mean is their limit, so the mean
of an almost periodic function dominated by another is dominated by the other's mean.  With the mean
of a constant this turns a pointwise estimate into an estimate of means — the step a Fejér
convergence argument takes after bounding the kernel against the modulus of continuity.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **Window averages are monotone.** -/
theorem windowAverage_le_windowAverage {g h : ℝ → ℝ} (hgc : Continuous g) (hhc : Continuous h)
    (hle : ∀ t, g t ≤ h t) {T : ℝ} (hT : 0 < T) :
    windowAverage g T ≤ windowAverage h T := by
  have hint : (∫ t in (0 : ℝ)..T, g t) ≤ ∫ t in (0 : ℝ)..T, h t := by
    refine intervalIntegral.integral_mono_on hT.le
      (hgc.intervalIntegrable _ _) (hhc.intervalIntegrable _ _) fun x _ => hle x
  have hTinv : (0 : ℝ) < T⁻¹ := inv_pos.mpr hT
  show T⁻¹ • (∫ t in (0 : ℝ)..T, g t) ≤ T⁻¹ • ∫ t in (0 : ℝ)..T, h t
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hint hTinv.le

/-- **The Bohr mean is monotone.** -/
theorem bohrMean_le_bohrMean {g h : ℝ → ℝ} (hgc : Continuous g)
    (hga : HTGeometry.IsBohrAlmostPeriodic g) (hhc : Continuous h)
    (hha : HTGeometry.IsBohrAlmostPeriodic h) (hle : ∀ t, g t ≤ h t) :
    bohrMean g ≤ bohrMean h := by
  have hg := tendsto_windowAverage_bohrMean hgc hga
  have hh := tendsto_windowAverage_bohrMean hhc hha
  refine le_of_tendsto_of_tendsto hg hh ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact windowAverage_le_windowAverage hgc hhc hle hT

/-- **A nonnegative almost periodic function has nonnegative mean.** -/
theorem bohrMean_nonneg {g : ℝ → ℝ} (hgc : Continuous g)
    (hga : HTGeometry.IsBohrAlmostPeriodic g) (hnn : ∀ t, 0 ≤ g t) : 0 ≤ bohrMean g := by
  have hzero : bohrMean (fun _ : ℝ => (0 : ℝ)) = 0 := by
    have hcont : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
    have hap : HTGeometry.IsBohrAlmostPeriodic (fun _ : ℝ => (0 : ℝ)) :=
      isBohrAlmostPeriodic_const 0
    have hlim : Tendsto (windowAverage (fun _ : ℝ => (0 : ℝ))) atTop (nhds 0) := by
      refine tendsto_const_nhds.congr fun T => ?_
      show (0 : ℝ) = windowAverage (fun _ : ℝ => (0 : ℝ)) T
      simp [windowAverage]
    exact tendsto_nhds_unique (tendsto_windowAverage_bohrMean hcont hap) hlim
  rw [← hzero]
  exact bohrMean_le_bohrMean continuous_const (isBohrAlmostPeriodic_const 0) hgc hga hnn

/-- The norm of an almost periodic function is almost periodic. -/
theorem isBohrAlmostPeriodic_norm_real {g : ℝ → ℂ} (hga : HTGeometry.IsBohrAlmostPeriodic g) :
    HTGeometry.IsBohrAlmostPeriodic (fun t => ‖g t‖) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hga ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have hx := hτ x
  have habs : ‖‖g (x + τ)‖ - ‖g x‖‖ ≤ ‖g (x + τ) - g x‖ := by
    rw [Real.norm_eq_abs]
    exact abs_norm_sub_norm_le _ _
  linarith [habs, hx]

/-- **The norm of the mean is at most the mean of the norm.** -/
theorem norm_bohrMean_le_bohrMean_norm {g : ℝ → ℂ} (hgc : Continuous g)
    (hga : HTGeometry.IsBohrAlmostPeriodic g) :
    ‖bohrMean g‖ ≤ bohrMean (fun t => ‖g t‖) := by
  have hnc : Continuous (fun t => ‖g t‖) := hgc.norm
  have hna := isBohrAlmostPeriodic_norm_real hga
  have h1 := tendsto_windowAverage_bohrMean hgc hga
  have h2 := tendsto_windowAverage_bohrMean hnc hna
  have hnorm : Tendsto (fun T : ℝ => ‖windowAverage g T‖) atTop (nhds ‖bohrMean g‖) :=
    (continuous_norm.tendsto _).comp h1
  refine le_of_tendsto_of_tendsto hnorm h2 ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  show ‖windowAverage g T‖ ≤ windowAverage (fun t => ‖g t‖) T
  simp only [windowAverage, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hT.le), smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hT.le)
  exact intervalIntegral.norm_integral_le_integral_norm hT.le

/-- Almost periodicity is preserved by the real-to-complex coercion. -/
theorem isBohrAlmostPeriodic_coe_ofReal {g : ℝ → ℝ} (hga : HTGeometry.IsBohrAlmostPeriodic g) :
    HTGeometry.IsBohrAlmostPeriodic (fun t => ((g t : ℝ) : ℂ)) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hga ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have hx := hτ x
  have hcast : ((g (x + τ) : ℝ) : ℂ) - ((g x : ℝ) : ℂ) = (((g (x + τ) - g x : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real]
  exact hx

/-- **The mean commutes with the real-to-complex coercion.** -/
theorem bohrMean_ofReal {g : ℝ → ℝ} (hgc : Continuous g)
    (hga : HTGeometry.IsBohrAlmostPeriodic g) :
    bohrMean (fun t => ((g t : ℝ) : ℂ)) = ((bohrMean g : ℝ) : ℂ) := by
  have hcc : Continuous (fun t => ((g t : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hgc
  have hca := isBohrAlmostPeriodic_coe_ofReal hga
  have h1 := tendsto_windowAverage_bohrMean hcc hca
  have h2 := tendsto_windowAverage_bohrMean hgc hga
  have h3 : Tendsto (fun T : ℝ => ((windowAverage g T : ℝ) : ℂ)) atTop
      (nhds ((bohrMean g : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp h2
  refine tendsto_nhds_unique h1 ?_
  refine h3.congr fun T => ?_
  show ((windowAverage g T : ℝ) : ℂ) = windowAverage (fun t => ((g t : ℝ) : ℂ)) T
  simp only [windowAverage]
  rw [intervalIntegral.integral_ofReal, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_inv]

/-- The mean of a real constant. -/
theorem bohrMean_const_real (b : ℝ) : bohrMean (fun _ : ℝ => b) = b := by
  have hcont : Continuous (fun _ : ℝ => b) := continuous_const
  have hap := isBohrAlmostPeriodic_const b
  have hlim : Tendsto (windowAverage (fun _ : ℝ => b)) atTop (nhds b) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    show b = windowAverage (fun _ : ℝ => b) T
    simp only [windowAverage, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    field_simp
  exact tendsto_nhds_unique (tendsto_windowAverage_bohrMean hcont hap) hlim

/-- A real scalar multiple of an almost periodic function is almost periodic. -/
theorem isBohrAlmostPeriodic_const_mul_real (a : ℝ) {h : ℝ → ℝ}
    (hha : HTGeometry.IsBohrAlmostPeriodic h) :
    HTGeometry.IsBohrAlmostPeriodic (fun t => a * h t) := by
  intro ε hε
  rcases eq_or_lt_of_le (abs_nonneg a) with ha0 | ha0
  · refine ⟨1, one_pos, fun x => ⟨x, ⟨le_refl x, by linarith⟩, fun y => ?_⟩⟩
    have : a = 0 := by
      have := ha0.symm
      exact abs_eq_zero.mp this
    simp [this, hε.le]
  · obtain ⟨L, hL, hdense⟩ := hha (ε / |a|) (by positivity)
    refine ⟨L, hL, fun x => ?_⟩
    obtain ⟨τ, hτmem, hτ⟩ := hdense x
    refine ⟨τ, hτmem, fun y => ?_⟩
    have hy := hτ y
    have hrw : a * h (y + τ) - a * h y = a * (h (y + τ) - h y) := by ring
    rw [hrw, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs] at *
    calc |a| * |h (y + τ) - h y| ≤ |a| * (ε / |a|) := by
          exact mul_le_mul_of_nonneg_left hy (abs_nonneg a)
      _ = ε := by field_simp

/-- The mean is homogeneous for real scalars. -/
theorem bohrMean_const_mul_real (a : ℝ) {h : ℝ → ℝ} (hhc : Continuous h)
    (hha : HTGeometry.IsBohrAlmostPeriodic h) :
    bohrMean (fun t => a * h t) = a * bohrMean h := by
  have hac : Continuous (fun t => a * h t) := continuous_const.mul hhc
  have haa : HTGeometry.IsBohrAlmostPeriodic (fun t => a * h t) :=
    isBohrAlmostPeriodic_const_mul_real a hha
  have h1 := tendsto_windowAverage_bohrMean hac haa
  have h2 := tendsto_windowAverage_bohrMean hhc hha
  have h3 : Tendsto (fun T : ℝ => a * windowAverage h T) atTop (nhds (a * bohrMean h)) :=
    h2.const_mul a
  refine tendsto_nhds_unique h1 ?_
  refine h3.congr fun T => ?_
  show a * windowAverage h T = windowAverage (fun t => a * h t) T
  simp only [windowAverage, smul_eq_mul, intervalIntegral.integral_const_mul]
  ring

/-- Adding a constant preserves almost periodicity. -/
theorem isBohrAlmostPeriodic_add_const_real {h : ℝ → ℝ}
    (hha : HTGeometry.IsBohrAlmostPeriodic h) (b : ℝ) :
    HTGeometry.IsBohrAlmostPeriodic (fun t => h t + b) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hha ε hε
  refine ⟨L, hL, fun x => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense x
  refine ⟨τ, hτmem, fun y => ?_⟩
  have hy := hτ y
  have hrw : h (y + τ) + b - (h y + b) = h (y + τ) - h y := by ring
  rw [hrw]
  exact hy

/-- The mean of a sum with a constant. -/
theorem bohrMean_add_const_real {h : ℝ → ℝ} (hhc : Continuous h)
    (hha : HTGeometry.IsBohrAlmostPeriodic h) (b : ℝ) :
    bohrMean (fun t => h t + b) = bohrMean h + b := by
  have hac : Continuous (fun t => h t + b) := hhc.add continuous_const
  have haa : HTGeometry.IsBohrAlmostPeriodic (fun t => h t + b) :=
    isBohrAlmostPeriodic_add_const_real hha b
  have h1 := tendsto_windowAverage_bohrMean hac haa
  have h2 := tendsto_windowAverage_bohrMean hhc hha
  have h3 : Tendsto (fun T : ℝ => windowAverage h T + b) atTop (nhds (bohrMean h + b)) :=
    h2.add tendsto_const_nhds
  refine tendsto_nhds_unique h1 ?_
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  show windowAverage h T + b = windowAverage (fun t => h t + b) T
  have hint : (∫ t in (0 : ℝ)..T, (h t + b)) = (∫ t in (0 : ℝ)..T, h t) + b * T := by
    rw [intervalIntegral.integral_add (hhc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)]
    simp [intervalIntegral.integral_const, mul_comm]
  simp only [windowAverage, smul_eq_mul, hint]
  field_simp

end GaloisForLFunctions
