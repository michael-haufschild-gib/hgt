import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The entire Fourier extension of a compactly supported test function

For a smooth function `ψ` supported in `[-M, M]` the integral

`Ψ(z) = ∫ ψ(L) e^{izL} dL`

is entire, and two integrations by parts give `z² Ψ(z) = -∫ ψ''(L) e^{izL} dL`, so on every
horizontal strip `Ψ` decays like `|z|^{-2}`.  This is the multiplier that makes a contour shift
legitimate for a boundary datum that is only square integrable.
-/

open Complex MeasureTheory Set Filter

open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The complex Fourier extension of a test function. -/
def testTransform (ψ : ℝ → ℂ) (z : ℂ) : ℂ := ∫ L : ℝ, ψ L * Complex.exp (Complex.I * z * (L : ℂ))

theorem norm_exp_I_mul (z : ℂ) (L : ℝ) :
    ‖Complex.exp (Complex.I * z * (L : ℂ))‖ = Real.exp (-(L * z.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The integrand of the test transform is integrable for a compactly supported continuous
function. -/
theorem integrable_testTransform_integrand {ψ : ℝ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (z : ℂ) :
    Integrable (fun L : ℝ => ψ L * Complex.exp (Complex.I * z * (L : ℂ))) := by
  refine (Continuous.integrable_of_hasCompactSupport ?_ ?_)
  · exact hc.mul (Complex.continuous_exp.comp (by fun_prop))
  · exact hs.mul_right

/-- The test transform is entire. -/
theorem differentiable_testTransform {ψ : ℝ → ℂ} (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    Differentiable ℂ (testTransform ψ) := by
  intro z₀
  set bound : ℝ → ℝ := fun L =>
    ‖ψ L‖ * (|L| * Real.exp ((|z₀.im| + 1) * |L|)) with hbound
  have hboundc : Continuous bound := by
    refine hc.norm.mul (continuous_abs.mul ?_)
    exact Real.continuous_exp.comp (continuous_const.mul continuous_abs)
  have hboundcs : HasCompactSupport bound := by
    refine HasCompactSupport.mul_right ?_
    exact hs.norm
  have hboundint : Integrable bound := hboundc.integrable_of_hasCompactSupport hboundcs
  have hmeas : ∀ᶠ w in nhds z₀,
      AEStronglyMeasurable (fun L : ℝ => ψ L * Complex.exp (Complex.I * w * (L : ℂ)))
        MeasureTheory.volume := by
    filter_upwards with w
    exact (integrable_testTransform_integrand hc hs w).aestronglyMeasurable
  have hint : Integrable (fun L : ℝ => ψ L * Complex.exp (Complex.I * z₀ * (L : ℂ))) :=
    integrable_testTransform_integrand hc hs z₀
  have hderivmeas : AEStronglyMeasurable
      (fun L : ℝ => ψ L * (Complex.exp (Complex.I * z₀ * (L : ℂ)) * (Complex.I * (L : ℂ))))
      MeasureTheory.volume := by
    refine Continuous.aestronglyMeasurable ?_
    exact hc.mul ((Complex.continuous_exp.comp (by fun_prop)).mul (by fun_prop))
  have hdiff : ∀ᵐ L : ℝ, ∀ w ∈ Metric.ball z₀ 1,
      HasDerivAt (fun w : ℂ => ψ L * Complex.exp (Complex.I * w * (L : ℂ)))
        (ψ L * (Complex.exp (Complex.I * w * (L : ℂ)) * (Complex.I * (L : ℂ)))) w := by
    filter_upwards with L w _
    have hlin : HasDerivAt (fun w : ℂ => Complex.I * w * (L : ℂ)) (Complex.I * (L : ℂ)) w := by
      have h1 : HasDerivAt (fun w : ℂ => Complex.I * w) Complex.I w := by
        simpa using (hasDerivAt_id w).const_mul Complex.I
      simpa [mul_comm] using h1.mul_const ((L : ℂ))
    exact hlin.cexp.const_mul (ψ L)
  have hbnd : ∀ᵐ L : ℝ, ∀ w ∈ Metric.ball z₀ 1,
      ‖ψ L * (Complex.exp (Complex.I * w * (L : ℂ)) * (Complex.I * (L : ℂ)))‖ ≤ bound L := by
    filter_upwards with L w hw
    have hwim : |w.im - z₀.im| < 1 := by
      have hdist : dist w z₀ < 1 := Metric.mem_ball.mp hw
      have himle : |w.im - z₀.im| ≤ dist w z₀ := by
        simpa [Complex.dist_eq, Complex.sub_im] using Complex.abs_im_le_norm (w - z₀)
      exact lt_of_le_of_lt himle hdist
    have hwbound : |w.im| ≤ |z₀.im| + 1 := by
      have := abs_sub_abs_le_abs_sub w.im z₀.im
      linarith [hwim, this]
    have hexpbound : Real.exp (-(L * w.im)) ≤ Real.exp ((|z₀.im| + 1) * |L|) := by
      refine Real.exp_le_exp.mpr ?_
      calc -(L * w.im) ≤ |L * w.im| := neg_le_abs _
        _ = |L| * |w.im| := abs_mul L w.im
        _ ≤ |L| * (|z₀.im| + 1) := mul_le_mul_of_nonneg_left hwbound (abs_nonneg L)
        _ = (|z₀.im| + 1) * |L| := by ring
    rw [norm_mul, norm_mul, norm_exp_I_mul, Complex.norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, hbound]
    rw [mul_comm (Real.exp (-(L * w.im))) |L|]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpbound (abs_nonneg L))
      (norm_nonneg _)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun w L =>
      ψ L * Complex.exp (Complex.I * w * (L : ℂ)))
    (F' := fun w L => ψ L * (Complex.exp (Complex.I * w * (L : ℂ)) * (Complex.I * (L : ℂ))))
    (bound := bound) (s := Metric.ball z₀ 1) (Metric.ball_mem_nhds z₀ one_pos)
    hmeas hint hderivmeas hbnd hboundint hdiff
  exact (hres.2).differentiableAt

/-- The derivative of the exponential factor along the real line. -/
theorem hasDerivAt_expLine (z : ℂ) (L : ℝ) :
    HasDerivAt (fun L : ℝ => Complex.exp (Complex.I * z * (L : ℂ)))
      (Complex.exp (Complex.I * z * (L : ℂ)) * (Complex.I * z)) L := by
  have hlin : HasDerivAt (fun L : ℝ => Complex.I * z * (L : ℂ)) (Complex.I * z) L := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := L)).const_mul (Complex.I * z)
  exact hlin.cexp

/-- **Integration by parts against the exponential.**  Multiplying the transform by `iz`
differentiates the test function, up to sign. -/
theorem testTransform_ibp {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) (z : ℂ) :
    testTransform ψ z * (Complex.I * z) = -testTransform (deriv ψ) z := by
  have hψc : Continuous ψ := hψ.continuous
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv_one
  have hds : HasCompactSupport (deriv ψ) := hs.deriv
  have hexpc : Continuous (fun L : ℝ => Complex.exp (Complex.I * z * (L : ℂ))) :=
    Complex.continuous_exp.comp (by fun_prop)
  have hexpc' : Continuous
      (fun L : ℝ => Complex.exp (Complex.I * z * (L : ℂ)) * (Complex.I * z)) :=
    hexpc.mul continuous_const
  have h1 : Integrable (ψ * fun L : ℝ => Complex.exp (Complex.I * z * (L : ℂ))
      * (Complex.I * z)) :=
    (hψc.mul hexpc').integrable_of_hasCompactSupport hs.mul_right
  have h2 : Integrable (deriv ψ * fun L : ℝ => Complex.exp (Complex.I * z * (L : ℂ))) :=
    (hdc.mul hexpc).integrable_of_hasCompactSupport hds.mul_right
  have h3 : Integrable (ψ * fun L : ℝ => Complex.exp (Complex.I * z * (L : ℂ))) :=
    (hψc.mul hexpc).integrable_of_hasCompactSupport hs.mul_right
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := ψ) (u' := deriv ψ) (v := fun L : ℝ => Complex.exp (Complex.I * z * (L : ℂ)))
    (v' := fun L : ℝ => Complex.exp (Complex.I * z * (L : ℂ)) * (Complex.I * z))
    (fun x _ => (hψ.differentiable (by simp) x).hasDerivAt)
    (fun x _ => hasDerivAt_expLine z x) h1 h2 h3
  have hlhs : (∫ x : ℝ, ψ x * (Complex.exp (Complex.I * z * (x : ℂ)) * (Complex.I * z)))
      = testTransform ψ z * (Complex.I * z) := by
    rw [testTransform, ← MeasureTheory.integral_mul_const]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hlhs] at key
  exact key

/-- Two integrations by parts:  `(iz)²` times the transform is the transform of the second
derivative. -/
theorem testTransform_ibp_two {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ)
    (z : ℂ) :
    testTransform ψ z * (Complex.I * z) ^ 2 = testTransform (deriv (deriv ψ)) z := by
  have hle : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le hle
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hdψ1 : ContDiff ℝ 1 (deriv ψ) := hdψ.of_le hle
  have e1 := testTransform_ibp hψ1 hs z
  have e2 := testTransform_ibp hdψ1 hs.deriv z
  calc testTransform ψ z * (Complex.I * z) ^ 2
      = testTransform ψ z * (Complex.I * z) * (Complex.I * z) := by ring
    _ = -testTransform (deriv ψ) z * (Complex.I * z) := by rw [e1]
    _ = -(testTransform (deriv ψ) z * (Complex.I * z)) := by ring
    _ = testTransform (deriv (deriv ψ)) z := by rw [e2, neg_neg]

/-- The transform of a compactly supported continuous function is bounded on a horizontal
strip by the `L¹` norm of the function times the exponential of the strip width. -/
theorem norm_testTransform_le_exp {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x : ℝ, M < |x| → g x = 0) {K : ℝ} (z : ℂ)
    (hz : |z.im| ≤ K) :
    ‖testTransform g z‖ ≤ Real.exp (M * K) * ∫ L : ℝ, ‖g L‖ := by
  have hint : Integrable (fun L : ℝ => g L * Complex.exp (Complex.I * z * (L : ℂ))) :=
    integrable_testTransform_integrand hgc hgs z
  have hnorm : Integrable (fun L : ℝ => ‖g L‖) :=
    (hgc.norm).integrable_of_hasCompactSupport hgs.norm
  have hbound : Integrable (fun L : ℝ => Real.exp (M * K) * ‖g L‖) := hnorm.const_mul _
  rw [testTransform]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono hint.norm hbound (fun L => ?_)
  rw [norm_mul, norm_exp_I_mul]
  by_cases hgL : g L = 0
  · simp [hgL]
  · have hLM : |L| ≤ M := by
      by_contra hcon
      exact hgL (hM L (lt_of_not_ge hcon))
    have hexp : Real.exp (-(L * z.im)) ≤ Real.exp (M * K) := by
      refine Real.exp_le_exp.mpr ?_
      calc -(L * z.im) ≤ |L * z.im| := neg_le_abs _
        _ = |L| * |z.im| := abs_mul L z.im
        _ ≤ M * K := mul_le_mul hLM hz (abs_nonneg _) hM0
    calc ‖g L‖ * Real.exp (-(L * z.im)) ≤ ‖g L‖ * Real.exp (M * K) :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = Real.exp (M * K) * ‖g L‖ := by ring

/-- Every compactly supported smooth function has a transform decaying quadratically, uniformly
on each horizontal strip. -/
theorem exists_testTransform_decay {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ)
    (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.im ∈ uIcc a b →
      ‖testTransform ψ z‖ ≤ C / (1 + ‖z‖ ^ 2) := by
  classical
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    hs.isCompact.isBounded
  set M : ℝ := |r| with hMdef
  have hM0 : (0 : ℝ) ≤ M := abs_nonneg r
  have hMsupp : ∀ {f : ℝ → ℂ}, tsupport f ⊆ tsupport ψ → ∀ x : ℝ, M < |x| → f x = 0 := by
    intro f hf x hx
    refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
    have hx' : x ∈ Metric.closedBall (0 : ℝ) r := hr (hf hmem)
    have hxr : |x| ≤ r := by simpa [Real.dist_eq] using hx'
    exact absurd (lt_of_lt_of_le hx (le_trans hxr (le_abs_self r))) (lt_irrefl _)
  set K : ℝ := |a| + |b| with hKdef
  have hKmem : ∀ y : ℝ, y ∈ uIcc a b → |y| ≤ K := by
    intro y hy
    have h1 : min a b ≤ y := (Set.mem_uIcc.mp hy).elim (fun h => le_trans (min_le_left a b) h.1)
      (fun h => le_trans (min_le_right a b) h.1)
    have h2 : y ≤ max a b := (Set.mem_uIcc.mp hy).elim (fun h => le_trans h.2 (le_max_right a b))
      (fun h => le_trans h.2 (le_max_left a b))
    have hmax : max a b ≤ K := by
      rw [hKdef]
      rcases max_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        [linarith [le_abs_self a, abs_nonneg b]; linarith [le_abs_self b, abs_nonneg a]]
    have hmin : -K ≤ min a b := by
      rw [hKdef]
      rcases min_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        [linarith [neg_abs_le a, abs_nonneg b]; linarith [neg_abs_le b, abs_nonneg a]]
    exact abs_le.mpr ⟨le_trans hmin h1, le_trans h2 hmax⟩
  have hψc : Continuous ψ := hψ.continuous
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hd2ψ : ContDiff ℝ ∞ (deriv (deriv ψ)) := (contDiff_infty_iff_deriv.mp hdψ).2
  have hgc : Continuous (deriv (deriv ψ)) := hd2ψ.continuous
  have hgs : HasCompactSupport (deriv (deriv ψ)) := hs.deriv.deriv
  have hgsub : tsupport (deriv (deriv ψ)) ⊆ tsupport ψ := by
    refine closure_minimal (le_trans support_deriv_subset ?_) isClosed_closure
    exact closure_minimal support_deriv_subset isClosed_closure
  refine ⟨Real.exp (M * K) * ((∫ L : ℝ, ‖ψ L‖) + ∫ L : ℝ, ‖deriv (deriv ψ) L‖), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∫ L : ℝ, ‖ψ L‖ := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
    have h2 : (0 : ℝ) ≤ ∫ L : ℝ, ‖deriv (deriv ψ) L‖ :=
      MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
    positivity
  · intro z hz
    have hzK : |z.im| ≤ K := hKmem _ hz
    have hb1 : ‖testTransform ψ z‖ ≤ Real.exp (M * K) * ∫ L : ℝ, ‖ψ L‖ :=
      norm_testTransform_le_exp hψc hs hM0 (hMsupp (le_refl _)) z hzK
    have hb2 : ‖testTransform (deriv (deriv ψ)) z‖
        ≤ Real.exp (M * K) * ∫ L : ℝ, ‖deriv (deriv ψ) L‖ :=
      norm_testTransform_le_exp hgc hgs hM0 (hMsupp hgsub) z hzK
    have hsq : ‖z‖ ^ 2 * ‖testTransform ψ z‖ = ‖testTransform (deriv (deriv ψ)) z‖ := by
      have hkey := testTransform_ibp_two hψ hs z
      have hnorm : ‖testTransform ψ z * (Complex.I * z) ^ 2‖
          = ‖testTransform (deriv (deriv ψ)) z‖ := by rw [hkey]
      rw [norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul] at hnorm
      rw [← hnorm]; ring
    rw [le_div_iff₀ (by positivity)]
    calc ‖testTransform ψ z‖ * (1 + ‖z‖ ^ 2)
        = ‖testTransform ψ z‖ + ‖z‖ ^ 2 * ‖testTransform ψ z‖ := by ring
      _ = ‖testTransform ψ z‖ + ‖testTransform (deriv (deriv ψ)) z‖ := by rw [hsq]
      _ ≤ (Real.exp (M * K) * ∫ L : ℝ, ‖ψ L‖)
            + Real.exp (M * K) * ∫ L : ℝ, ‖deriv (deriv ψ) L‖ := add_le_add hb1 hb2
      _ = Real.exp (M * K) * ((∫ L : ℝ, ‖ψ L‖) + ∫ L : ℝ, ‖deriv (deriv ψ) L‖) := by ring

/-- The Fourier extension in the `2π` normalisation, so that its restriction to the real axis is
the inverse Fourier transform of the test function. -/
def testTransformTwoPi (ψ : ℝ → ℂ) (z : ℂ) : ℂ :=
  testTransform ψ (((2 * Real.pi : ℝ) : ℂ) * z)

theorem differentiable_testTransformTwoPi {ψ : ℝ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) : Differentiable ℂ (testTransformTwoPi ψ) := by
  intro z
  have hlin : DifferentiableAt ℂ (fun w : ℂ => ((2 * Real.pi : ℝ) : ℂ) * w) z :=
    differentiableAt_id.const_mul _
  exact ((differentiable_testTransform hc hs) _).comp z hlin

/-- The exponential of the rescaled transform splits into the oscillation on the line and the
exponential weight of the height. -/
theorem exp_twoPi_line_split (σ x L : ℝ) :
    Complex.exp (((2 * Real.pi * L * x : ℝ) : ℂ) * Complex.I)
        * Complex.exp (-(((2 * Real.pi * σ * L : ℝ)) : ℂ))
      = Complex.exp (Complex.I * (((2 * Real.pi : ℝ) : ℂ)
          * ((x : ℂ) + (σ : ℂ) * Complex.I)) * (L : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  refine Complex.ext ?_ ?_
  · simp
  · simp
    ring

theorem testTransformTwoPi_ofReal_line {ψ : ℝ → ℂ} (σ x : ℝ) :
    testTransformTwoPi ψ ((x : ℂ) + (σ : ℂ) * Complex.I)
      = ∫ L : ℝ, Complex.exp (((2 * Real.pi * L * x : ℝ) : ℂ) * Complex.I)
          * (ψ L * Complex.exp (-(((2 * Real.pi * σ * L : ℝ)) : ℂ))) := by
  rw [testTransformTwoPi, testTransform]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
  show ψ L * Complex.exp (Complex.I * (((2 * Real.pi : ℝ) : ℂ)
        * ((x : ℂ) + (σ : ℂ) * Complex.I)) * (L : ℂ))
      = Complex.exp (((2 * Real.pi * L * x : ℝ) : ℂ) * Complex.I)
        * (ψ L * Complex.exp (-(((2 * Real.pi * σ * L : ℝ)) : ℂ)))
  rw [← exp_twoPi_line_split σ x L]
  ring

/-- The quadratic decay of the transform survives the `2π` rescaling. -/
theorem exists_testTransformTwoPi_decay {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.im ∈ uIcc a b →
      ‖testTransformTwoPi ψ z‖ ≤ C / (1 + ‖z‖ ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_testTransform_decay hψ hs (2 * Real.pi * a) (2 * Real.pi * b)
  refine ⟨C, hC0, fun z hz => ?_⟩
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hzim : (((2 * Real.pi : ℝ) : ℂ) * z).im = 2 * Real.pi * z.im := by simp
  have hmem : (((2 * Real.pi : ℝ) : ℂ) * z).im ∈ uIcc (2 * Real.pi * a) (2 * Real.pi * b) := by
    rw [hzim]
    rcases Set.mem_uIcc.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Set.mem_uIcc.mpr (Or.inl ⟨by nlinarith, by nlinarith⟩)
    · exact Set.mem_uIcc.mpr (Or.inr ⟨by nlinarith, by nlinarith⟩)
  have hnorm : ‖z‖ ≤ ‖((2 * Real.pi : ℝ) : ℂ) * z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    nlinarith [norm_nonneg z, Real.two_le_pi]
  refine le_trans (hC _ hmem) ?_
  refine div_le_div_of_nonneg_left hC0 (by positivity) ?_
  nlinarith [norm_nonneg z, norm_nonneg (((2 * Real.pi : ℝ) : ℂ) * z)]

end

end GaloisForLFunctions.HTGeometry
