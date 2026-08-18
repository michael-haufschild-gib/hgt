import GaloisForLFunctions.RHTower.HardyThetaSource
import GaloisForLFunctions.HTGeometry.ResolventSubordination

/-!
# The completed zeta function on the critical line is the Fourier transform of the Hardy source

Mathlib's logarithmic theta source differs from the strip-holomorphic Hardy source by the
two-sided exponential kernel `e^{-|u|/4}`, whose Fourier transform is exactly the rational polar
part removed by the completion.  Hence

`𝓕 hardySource (t/4π) = Λ(1/2 + it)`,

with no polar correction left.  Shifting the contour inside the strip then converts the horizontal
exponential decay of the source into exponential decay of `Λ` on the critical line, at every rate
below `π/4`.
-/

namespace RHTower

open Complex Filter Topology MeasureTheory

open scoped Real FourierTransform

noncomputable section

/-! ## The source decomposition on the real axis -/

theorem xiThetaLogSource_eq_add {a : ℝ} (ha : a ≠ 0) :
    xiThetaLogSource a = 2 * hardySource (a : ℂ) + ((Real.exp (-(1 / 4 * |a|)) : ℝ) : ℂ) := by
  rcases lt_trichotomy a 0 with hneg | hzero | hpos
  · have h := xiThetaLogSource_eq_hardySource (a := -a) (by linarith)
    rw [xiThetaLogSource_neg] at h
    have hcast : ((-a : ℝ) : ℂ) = -(a : ℂ) := by push_cast; ring
    rw [hcast, hardySource_neg (ofReal_mem_hardyStrip a)] at h
    rw [h]
    congr 2
    rw [abs_of_neg hneg]
    ring
  · exact absurd hzero ha
  · have h := xiThetaLogSource_eq_hardySource hpos
    rw [h]
    congr 2
    rw [abs_of_pos hpos]
    ring

/-! ## Integrability -/

theorem integrable_hardySource_real : Integrable (fun a : ℝ => hardySource (a : ℂ)) := by
  have h := integrable_hardySource_line (c := 0) le_rfl (by linarith [Real.pi_pos])
  refine h.congr ?_
  filter_upwards with a
  congr 1
  push_cast
  ring

theorem integrable_polarKernel :
    Integrable (fun a : ℝ => ((Real.exp (-(1 / 4 * |a|)) : ℝ) : ℂ)) := by
  exact (integrable_exp_neg_mul_abs' (by norm_num)).ofReal

theorem integrable_xiThetaLogSource : Integrable xiThetaLogSource := by
  have hsum : Integrable
      (fun a : ℝ => 2 * hardySource (a : ℂ) + ((Real.exp (-(1 / 4 * |a|)) : ℝ) : ℂ)) :=
    (integrable_hardySource_real.const_mul 2).add integrable_polarKernel
  refine hsum.congr ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with a ha
  exact (xiThetaLogSource_eq_add ha).symm

/-! ## The Fourier identity -/

theorem fourier_xiThetaLogSource_eq (w : ℝ) :
    𝓕 xiThetaLogSource w
      = 2 * 𝓕 (fun a : ℝ => hardySource (a : ℂ)) w
        + 𝓕 (fun a : ℝ => ((Real.exp (-(1 / 4 * |a|)) : ℝ) : ℂ)) w := by
  have hH : Integrable (fun v : ℝ => (𝐞 (-(v * w))) • hardySource (v : ℂ)) := by
    have h := (Real.fourierIntegral_convergent_iff
      (f := fun a : ℝ => hardySource (a : ℂ)) w).2 integrable_hardySource_real
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm w] using h
  have hP : Integrable
      (fun v : ℝ => (𝐞 (-(v * w))) • ((Real.exp (-(1 / 4 * |v|)) : ℝ) : ℂ)) := by
    have h := (Real.fourierIntegral_convergent_iff
      (f := fun a : ℝ => ((Real.exp (-(1 / 4 * |a|)) : ℝ) : ℂ)) w).2 integrable_polarKernel
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm w] using h
  rw [Real.fourier_real_eq, Real.fourier_real_eq, Real.fourier_real_eq,
    ← integral_const_mul, ← integral_add (hH.const_mul 2) hP]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with a ha
  rw [xiThetaLogSource_eq_add ha]
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- **The completed zeta function on the critical line is the Fourier transform of the Hardy
source.**  The polar part of the completion is exactly the Fourier transform of the two-sided
exponential kernel that separates the source from mathlib's logarithmic theta source. -/
theorem fourier_hardySource (t : ℝ) :
    𝓕 (fun a : ℝ => hardySource (a : ℂ)) (t / (4 * π))
      = completedRiemannZeta (1 / 2 + (t : ℂ) * I) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hcorpus := completedRiemannZeta₀_critical_eq_fourier_xiThetaLogSource t
  have hpolar := GaloisForLFunctions.HTGeometry.fourierIntegral_exp_neg_mul_abs
    (μ := 1 / 4) (by norm_num) (t / (4 * π))
  have hsplit := fourier_xiThetaLogSource_eq (t / (4 * π))
  have hpolarval : 𝓕 (fun a : ℝ => ((Real.exp (-(1 / 4 * |a|)) : ℝ) : ℂ)) (t / (4 * π))
      = 2 / ((t : ℂ) ^ 2 + 1 / 4) := by
    rw [hpolar]
    have hcast : ((t / (4 * π) : ℝ) : ℂ) = (t : ℂ) / (4 * (π : ℂ)) := by
      push_cast
      ring
    rw [hcast]
    have hπC : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hπ
    push_cast
    field_simp
    ring
  have hzeta := completedRiemannZeta_eq (1 / 2 + (t : ℂ) * I)
  have hden1 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hden2 : (1 - (1 / 2 + (t : ℂ) * I)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    norm_num at this
  have hpole : 1 / (1 / 2 + (t : ℂ) * I) + 1 / (1 - (1 / 2 + (t : ℂ) * I))
      = 1 / ((t : ℂ) ^ 2 + 1 / 4) := by
    have hne : ((t : ℂ) ^ 2 + 1 / 4) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [Complex.add_re, pow_two, Complex.mul_re] at hre
      nlinarith [sq_nonneg t]
    rw [div_add_div _ _ hden1 hden2, div_eq_div_iff (mul_ne_zero hden1 hden2) hne]
    linear_combination ((t : ℂ) ^ 2) * Complex.I_sq
  rw [hsplit, hpolarval] at hcorpus
  rw [hzeta, hcorpus]
  linear_combination hpole

/-! ## Exponential decay on the critical line -/

/-- The `L¹` bound of the source on a horizontal line of the strip. -/
def hardyLineBound (c : ℝ) : ℝ :=
  hardySourceBound c * ∫ x : ℝ, Real.exp (-(1 / 4 * |x|))

theorem completedZeta_critical_eq_integral (t : ℝ) :
    completedRiemannZeta (1 / 2 + (t : ℂ) * I)
      = ∫ a : ℝ, cexp (-I * (a : ℂ) * (t : ℂ) / 2) * hardySource (a : ℂ) := by
  rw [← fourier_hardySource t, Real.fourier_real_eq]
  refine integral_congr_ae ?_
  filter_upwards with a
  rw [Circle.smul_def]
  congr 1
  rw [Real.fourierChar_apply]
  congr 1
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hπC : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hπ
  push_cast
  field_simp
  ring

theorem norm_completedZeta_critical_le_of_nonpos {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 2)
    {t : ℝ} (_ht : t ≤ 0) :
    ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖
      ≤ hardyLineBound c * Real.exp (c * t / 2) := by
  set F : ℂ → ℂ := fun z => cexp (-I * z * (t : ℂ) / 2) * hardySource z with hF
  have hstrip : ∀ z : ℂ, |z.im| ≤ c → z ∈ hardyStrip := by
    intro z hz
    rw [mem_hardyStrip]
    exact lt_of_le_of_lt hz hc
  have hdiff : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ F z := by
    intro z hz
    refine DifferentiableAt.mul ?_ (differentiableAt_hardySource (hstrip z hz))
    exact (differentiable_exp.differentiableAt).comp z (by fun_prop)
  have hnormexp : ∀ z : ℂ, ‖cexp (-I * z * (t : ℂ) / 2)‖ = Real.exp (t * z.im / 2) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hbound : ∀ z : ℂ, |z.im| ≤ c →
      ‖F z‖ ≤ (hardySourceBound c * Real.exp (|t| * c / 2)) * Real.exp (-(1 / 4 * |z.re|)) := by
    intro z hz
    rw [hF]
    simp only
    rw [norm_mul, hnormexp]
    have hsrc := norm_hardySource_le hc0 hc hz
    have hexpmono : Real.exp (t * z.im / 2) ≤ Real.exp (|t| * c / 2) := by
      rw [Real.exp_le_exp]
      have h1 : t * z.im ≤ |t * z.im| := le_abs_self _
      have h2 : |t * z.im| = |t| * |z.im| := abs_mul t z.im
      have h3 : |t| * |z.im| ≤ |t| * c := mul_le_mul_of_nonneg_left hz (abs_nonneg t)
      linarith
    have hbnn : 0 ≤ hardySourceBound c := by
      have hcos : 0 < Real.cos c := cos_pos_of_lt_pi_div_two hc0 hc
      have hlt : Real.exp (-π * Real.cos c) < 1 := by
        rw [Real.exp_lt_one_iff]
        nlinarith [Real.pi_pos]
      have hden : 0 < 1 - Real.exp (-π * Real.cos c) := by linarith
      rw [hardySourceBound]
      positivity
    calc Real.exp (t * z.im / 2) * ‖hardySource z‖
        ≤ Real.exp (|t| * c / 2) * (hardySourceBound c * Real.exp (-(|z.re| / 4))) := by
          refine mul_le_mul hexpmono hsrc (norm_nonneg _) (Real.exp_pos _).le
      _ = (hardySourceBound c * Real.exp (|t| * c / 2)) * Real.exp (-(1 / 4 * |z.re|)) := by
          rw [show -(|z.re| / 4) = -(1 / 4 * |z.re|) by ring]
          ring
  have hshift := integral_horizontal_shift_of_decay (F := F) (c := c)
    (C := hardySourceBound c * Real.exp (|t| * c / 2)) (r := 1 / 4) hc0 (by norm_num) hdiff hbound
  have hbnn : 0 ≤ hardySourceBound c := by
    have hcos : 0 < Real.cos c := cos_pos_of_lt_pi_div_two hc0 hc
    have hlt : Real.exp (-π * Real.cos c) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [Real.pi_pos]
    have hden : 0 < 1 - Real.exp (-π * Real.cos c) := by linarith
    rw [hardySourceBound]
    positivity
  have hline : ∀ x : ℝ, F ((x : ℂ) + (c : ℂ) * I)
      = cexp ((c : ℂ) * (t : ℂ) / 2) * (cexp (-I * (x : ℂ) * (t : ℂ) / 2) *
        hardySource ((x : ℂ) + (c : ℂ) * I)) := by
    intro x
    have hexp : -I * ((x : ℂ) + (c : ℂ) * I) * (t : ℂ) / 2
        = (c : ℂ) * (t : ℂ) / 2 + -I * (x : ℂ) * (t : ℂ) / 2 := by
      linear_combination (-((c : ℂ) * (t : ℂ)) / 2) * Complex.I_sq
    rw [hF]
    simp only
    rw [hexp, Complex.exp_add, mul_assoc]
  have hunit : ∀ x : ℝ, ‖cexp (-I * (x : ℂ) * (t : ℂ) / 2)‖ = 1 := by
    intro x
    rw [hnormexp]
    simp
  have hintline : Integrable (fun x : ℝ => cexp (-I * (x : ℂ) * (t : ℂ) / 2) *
      hardySource ((x : ℂ) + (c : ℂ) * I)) := by
    refine Integrable.mono' (g := fun x : ℝ => ‖hardySource ((x : ℂ) + (c : ℂ) * I)‖)
      (integrable_hardySource_line hc0 hc).norm ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul
        (integrable_hardySource_line hc0 hc).aestronglyMeasurable
    · filter_upwards with x
      show ‖cexp (-I * (x : ℂ) * (t : ℂ) / 2) * hardySource ((x : ℂ) + (c : ℂ) * I)‖
        ≤ ‖hardySource ((x : ℂ) + (c : ℂ) * I)‖
      rw [norm_mul, hunit x, one_mul]
  have hnormc : ‖cexp ((c : ℂ) * (t : ℂ) / 2)‖ = Real.exp (c * t / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hmass : (∫ x : ℝ, ‖hardySource ((x : ℂ) + (c : ℂ) * I)‖)
      ≤ hardySourceBound c * ∫ x : ℝ, Real.exp (-(1 / 4 * |x|)) := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_hardySource_line hc0 hc).norm
      ((integrable_exp_neg_mul_abs' (by norm_num)).const_mul _) ?_
    intro x
    have him : |((x : ℂ) + (c : ℂ) * I).im| ≤ c := by
      simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im]
      rw [abs_of_nonneg hc0]
    have hre : ((x : ℂ) + (c : ℂ) * I).re = x := by
      simp [Complex.add_re, Complex.mul_re]
    have h := norm_hardySource_le hc0 hc him
    rw [hre] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    ring
  rw [completedZeta_critical_eq_integral t, ← hshift]
  have hrewrite : (∫ x : ℝ, F ((x : ℂ) + (c : ℂ) * I))
      = cexp ((c : ℂ) * (t : ℂ) / 2) *
        ∫ x : ℝ, cexp (-I * (x : ℂ) * (t : ℂ) / 2) * hardySource ((x : ℂ) + (c : ℂ) * I) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (by filter_upwards with x; exact hline x)
  rw [hrewrite, norm_mul, hnormc, hardyLineBound]
  have hnormint : ‖∫ x : ℝ, cexp (-I * (x : ℂ) * (t : ℂ) / 2) *
      hardySource ((x : ℂ) + (c : ℂ) * I)‖
      ≤ hardySourceBound c * ∫ x : ℝ, Real.exp (-(1 / 4 * |x|)) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_trans ?_ hmass
    refine integral_mono hintline.norm (integrable_hardySource_line hc0 hc).norm ?_
    intro x
    show ‖cexp (-I * (x : ℂ) * (t : ℂ) / 2) * hardySource ((x : ℂ) + (c : ℂ) * I)‖
      ≤ ‖hardySource ((x : ℂ) + (c : ℂ) * I)‖
    rw [norm_mul, hunit x, one_mul]
  have hexppos : (0 : ℝ) < Real.exp (c * t / 2) := Real.exp_pos _
  nlinarith [hnormint, hexppos]

/-! ## The reflected decay bound -/

theorem completedZeta_critical_neg (t : ℝ) :
    completedRiemannZeta (1 / 2 + ((-t : ℝ) : ℂ) * I)
      = completedRiemannZeta (1 / 2 + (t : ℂ) * I) := by
  have h := completedRiemannZeta_one_sub (1 / 2 + (t : ℂ) * I)
  rw [← h]
  congr 1
  push_cast
  ring

/-- **Exponential decay of the completed zeta function on the critical line**, at every rate below
`π/4`. -/
theorem norm_completedZeta_critical_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 2) (t : ℝ) :
    ‖completedRiemannZeta (1 / 2 + (t : ℂ) * I)‖
      ≤ hardyLineBound c * Real.exp (-(c * |t| / 2)) := by
  rcases le_total t 0 with ht | ht
  · have h := norm_completedZeta_critical_le_of_nonpos hc0 hc ht
    rw [abs_of_nonpos ht]
    refine h.trans (le_of_eq ?_)
    congr 2
    ring
  · have h := norm_completedZeta_critical_le_of_nonpos hc0 hc (t := -t) (by linarith)
    rw [completedZeta_critical_neg t] at h
    rw [abs_of_nonneg ht]
    refine h.trans (le_of_eq ?_)
    congr 2
    ring

/-! ## Inversion on the horizontal lines of the strip -/

/-- The transform of the completed zeta function in Fourier coordinates. -/
def completedZetaFourier (w : ℝ) : ℂ :=
  completedRiemannZeta (1 / 2 + ((4 * π * w : ℝ) : ℂ) * I)

theorem fourier_hardySource_eq (w : ℝ) :
    𝓕 (fun a : ℝ => hardySource (a : ℂ)) w = completedZetaFourier w := by
  have h := fourier_hardySource (4 * π * w)
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  show 𝓕 (fun a : ℝ => hardySource (a : ℂ)) w
    = completedRiemannZeta (1 / 2 + ((4 * π * w : ℝ) : ℂ) * I)
  rw [← h]
  field_simp

theorem continuous_completedZetaFourier : Continuous completedZetaFourier := by
  rw [continuous_iff_continuousAt]
  intro w
  have hne0 : (1 / 2 + ((4 * π * w : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at hre
  have hne1 : (1 / 2 + ((4 * π * w : ℝ) : ℂ) * I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re] at hre
  exact ContinuousAt.comp (g := completedRiemannZeta)
    (f := fun w : ℝ => 1 / 2 + ((4 * π * w : ℝ) : ℂ) * I) (x := w)
    (differentiableAt_completedZeta hne0 hne1).continuousAt (by fun_prop)

theorem norm_completedZetaFourier_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 2) (w : ℝ) :
    ‖completedZetaFourier w‖ ≤ hardyLineBound c * Real.exp (-(2 * π * c * |w|)) := by
  have h := norm_completedZeta_critical_le hc0 hc (4 * π * w)
  show ‖completedRiemannZeta (1 / 2 + ((4 * π * w : ℝ) : ℂ) * I)‖ ≤ _
  refine h.trans (le_of_eq ?_)
  congr 2
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * π)]
  ring

theorem integrable_completedZetaFourier_mul_exp {c y : ℝ} (hc0 : 0 ≤ c) (hc : c < π / 2)
    (hy : |y| < c) :
    Integrable (fun w : ℝ => Real.exp (2 * π * |y| * |w|) * ‖completedZetaFourier w‖) := by
  have hkey : ∀ w : ℝ, Real.exp (2 * π * |y| * |w|) * ‖completedZetaFourier w‖
      ≤ hardyLineBound c * Real.exp (-(2 * π * (c - |y|) * |w|)) := by
    intro w
    have h := norm_completedZetaFourier_le hc0 hc w
    have hpos : (0 : ℝ) < Real.exp (2 * π * |y| * |w|) := Real.exp_pos _
    calc Real.exp (2 * π * |y| * |w|) * ‖completedZetaFourier w‖
        ≤ Real.exp (2 * π * |y| * |w|) * (hardyLineBound c * Real.exp (-(2 * π * c * |w|))) :=
          mul_le_mul_of_nonneg_left h hpos.le
      _ = hardyLineBound c * (Real.exp (2 * π * |y| * |w|) *
            Real.exp (-(2 * π * c * |w|))) := by ring
      _ = hardyLineBound c * Real.exp (-(2 * π * (c - |y|) * |w|)) := by
          rw [← Real.exp_add]
          ring_nf
  refine Integrable.mono' (g := fun w : ℝ => hardyLineBound c *
      Real.exp (-(2 * π * (c - |y|) * |w|))) ?_ ?_ ?_
  · have hrate : 0 < 2 * π * (c - |y|) := by
      have : 0 < c - |y| := by linarith
      have := Real.pi_pos
      positivity
    exact (integrable_exp_neg_mul_abs' hrate).const_mul _
  · exact (Continuous.aestronglyMeasurable
      ((by fun_prop : Continuous fun w : ℝ => Real.exp (2 * π * |y| * |w|)).mul
        continuous_completedZetaFourier.norm))
  · filter_upwards with w
    rw [Real.norm_of_nonneg (by positivity)]
    exact hkey w

/-- **Contour shift for the Fourier transform**: transforming the source along the horizontal line
at height `y` multiplies its transform by `exp (-2π y w)`. -/
theorem fourier_hardySource_line {y : ℝ} (hy0 : 0 ≤ y) (hy : y < π / 2) (w : ℝ) :
    𝓕 (fun a : ℝ => hardySource ((a : ℂ) + (y : ℂ) * I)) w
      = (Real.exp (-(2 * π * y * w)) : ℂ) * completedZetaFourier w := by
  set H : ℂ → ℂ := fun z => cexp (-(2 * π * I * z * (w : ℂ))) * hardySource z with hH
  have hstrip : ∀ z : ℂ, |z.im| ≤ y → z ∈ hardyStrip := by
    intro z hz
    rw [mem_hardyStrip]
    exact lt_of_le_of_lt hz hy
  have hdiff : ∀ z : ℂ, |z.im| ≤ y → DifferentiableAt ℂ H z := by
    intro z hz
    refine DifferentiableAt.mul ?_ (differentiableAt_hardySource (hstrip z hz))
    exact (differentiable_exp.differentiableAt).comp z (by fun_prop)
  have hnormexp : ∀ z : ℂ, ‖cexp (-(2 * π * I * z * (w : ℂ)))‖ = Real.exp (2 * π * w * z.im) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hbnn : 0 ≤ hardySourceBound y := by
    have hcos : 0 < Real.cos y := cos_pos_of_lt_pi_div_two hy0 hy
    have hlt : Real.exp (-π * Real.cos y) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [Real.pi_pos]
    have hden : 0 < 1 - Real.exp (-π * Real.cos y) := by linarith
    rw [hardySourceBound]
    positivity
  have hbound : ∀ z : ℂ, |z.im| ≤ y →
      ‖H z‖ ≤ (hardySourceBound y * Real.exp (2 * π * |w| * y)) * Real.exp (-(1 / 4 * |z.re|)) := by
    intro z hz
    rw [hH]
    simp only
    rw [norm_mul, hnormexp]
    have hsrc := norm_hardySource_le hy0 hy hz
    have hexpmono : Real.exp (2 * π * w * z.im) ≤ Real.exp (2 * π * |w| * y) := by
      rw [Real.exp_le_exp]
      have h1 : w * z.im ≤ |w * z.im| := le_abs_self _
      have h2 : |w * z.im| = |w| * |z.im| := abs_mul w z.im
      have h3 : |w| * |z.im| ≤ |w| * y := mul_le_mul_of_nonneg_left hz (abs_nonneg w)
      have h4 : (0 : ℝ) < 2 * π := by positivity
      nlinarith [h1, h2, h3]
    calc Real.exp (2 * π * w * z.im) * ‖hardySource z‖
        ≤ Real.exp (2 * π * |w| * y) * (hardySourceBound y * Real.exp (-(|z.re| / 4))) :=
          mul_le_mul hexpmono hsrc (norm_nonneg _) (Real.exp_pos _).le
      _ = (hardySourceBound y * Real.exp (2 * π * |w| * y)) * Real.exp (-(1 / 4 * |z.re|)) := by
          rw [show -(|z.re| / 4) = -(1 / 4 * |z.re|) by ring]
          ring
  have hshift := integral_horizontal_shift_of_decay (F := H) (c := y)
    (C := hardySourceBound y * Real.exp (2 * π * |w| * y)) (r := 1 / 4) hy0 (by norm_num)
    hdiff hbound
  have hline : ∀ a : ℝ, H ((a : ℂ) + (y : ℂ) * I)
      = cexp ((2 * π * y * w : ℝ) : ℂ) * (cexp (-(2 * π * I * (a : ℂ) * (w : ℂ))) *
        hardySource ((a : ℂ) + (y : ℂ) * I)) := by
    intro a
    have hexp : -(2 * π * I * ((a : ℂ) + (y : ℂ) * I) * (w : ℂ))
        = ((2 * π * y * w : ℝ) : ℂ) + -(2 * π * I * (a : ℂ) * (w : ℂ)) := by
      push_cast
      linear_combination (-(2 * (π : ℂ) * (y : ℂ) * (w : ℂ))) * Complex.I_sq
    rw [hH]
    simp only
    rw [hexp, Complex.exp_add, mul_assoc]
  have hfourierline : 𝓕 (fun a : ℝ => hardySource ((a : ℂ) + (y : ℂ) * I)) w
      = ∫ a : ℝ, cexp (-(2 * π * I * (a : ℂ) * (w : ℂ))) *
          hardySource ((a : ℂ) + (y : ℂ) * I) := by
    rw [Real.fourier_real_eq]
    refine integral_congr_ae ?_
    filter_upwards with a
    show (Real.fourierChar (-(a * w))) • hardySource ((a : ℂ) + (y : ℂ) * I)
      = cexp (-(2 * π * I * (a : ℂ) * (w : ℂ))) * hardySource ((a : ℂ) + (y : ℂ) * I)
    rw [Circle.smul_def]
    congr 1
    rw [Real.fourierChar_apply]
    push_cast
    ring_nf
  have hfourierbase : 𝓕 (fun a : ℝ => hardySource (a : ℂ)) w
      = ∫ a : ℝ, H (a : ℂ) := by
    rw [Real.fourier_real_eq]
    refine integral_congr_ae ?_
    filter_upwards with a
    show (Real.fourierChar (-(a * w))) • hardySource (a : ℂ)
      = cexp (-(2 * π * I * (a : ℂ) * (w : ℂ))) * hardySource (a : ℂ)
    rw [Circle.smul_def]
    congr 1
    rw [Real.fourierChar_apply]
    push_cast
    ring_nf
  have hleft : (∫ a : ℝ, H ((a : ℂ) + (y : ℂ) * I))
      = cexp ((2 * π * y * w : ℝ) : ℂ) *
        ∫ a : ℝ, cexp (-(2 * π * I * (a : ℂ) * (w : ℂ))) *
          hardySource ((a : ℂ) + (y : ℂ) * I) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (by filter_upwards with a; exact hline a)
  rw [hleft, hfourierbase.symm] at hshift
  rw [hfourierline, ← fourier_hardySource_eq w]
  rw [← hshift]
  have hcancel : ((Real.exp (-(2 * π * y * w)) : ℝ) : ℂ) * cexp (((2 * π * y * w : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add]
    norm_num
  rw [← mul_assoc, hcancel, one_mul]

/-- **Fourier inversion on the vertical axis of the strip.** -/
theorem hardySource_line_eq_integral {y : ℝ} (hy0 : 0 ≤ y) (hy : y < π / 2) (a : ℝ) :
    hardySource ((a : ℂ) + (y : ℂ) * I)
      = ∫ w : ℝ, (Real.fourierChar (w * a)) •
          ((Real.exp (-(2 * π * y * w)) : ℂ) * completedZetaFourier w) := by
  set g : ℝ → ℂ := fun a => hardySource ((a : ℂ) + (y : ℂ) * I) with hg
  have hgint : Integrable g := integrable_hardySource_line hy0 hy
  set c : ℝ := (y + π / 2) / 2 with hc
  have hc0 : 0 ≤ c := by
    have := Real.pi_pos
    rw [hc]; linarith
  have hcy : |y| < c := by
    rw [abs_of_nonneg hy0, hc]; linarith
  have hclt : c < π / 2 := by rw [hc]; linarith
  have hfint : Integrable (𝓕 g) := by
    have hbound := integrable_completedZetaFourier_mul_exp hc0 hclt hcy
    refine Integrable.mono' hbound ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by
        refine Continuous.mul ?_ continuous_completedZetaFourier
        exact Complex.continuous_ofReal.comp (by fun_prop))).congr
        (Filter.Eventually.of_forall (fun w => (fourier_hardySource_line hy0 hy w).symm))
    · filter_upwards with w
      rw [fourier_hardySource_line hy0 hy w, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.exp_le_exp, abs_of_nonneg hy0]
      have h1 : -(w) ≤ |w| := neg_le_abs w
      have h2 : (0 : ℝ) ≤ 2 * π * y := by
        have := Real.pi_pos
        positivity
      have h3 := mul_le_mul_of_nonneg_left h1 h2
      nlinarith [h3]
  have hcont : ∀ b : ℝ, ContinuousAt g b := by
    intro b
    have hmem : ((b : ℝ) : ℂ) + (y : ℂ) * I ∈ hardyStrip := by
      rw [mem_hardyStrip]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [abs_of_nonneg hy0]
      exact hy
    exact ContinuousAt.comp (g := hardySource) (f := fun t : ℝ => (t : ℂ) + (y : ℂ) * I) (x := b)
      (differentiableAt_hardySource hmem).continuousAt (by fun_prop)
  have hinv := hgint.fourierInv_fourier_eq hfint (hcont a)
  rw [Real.fourierInv_eq] at hinv
  have hga : g a = hardySource ((a : ℂ) + (y : ℂ) * I) := rfl
  rw [hga] at hinv
  rw [← hinv]
  refine integral_congr_ae ?_
  filter_upwards with w
  rw [fourier_hardySource_line hy0 hy w]
  congr 2
  simp [RCLike.inner_apply, mul_comm]

/-- **Fourier inversion on the vertical axis of the strip.** -/
theorem hardySource_imaginary_eq_integral {y : ℝ} (hy0 : 0 ≤ y) (hy : y < π / 2) :
    hardySource ((y : ℂ) * I)
      = ∫ w : ℝ, (Real.exp (-(2 * π * y * w)) : ℂ) * completedZetaFourier w := by
  have h := hardySource_line_eq_integral hy0 hy 0
  rw [show ((0 : ℝ) : ℂ) + (y : ℂ) * I = (y : ℂ) * I by norm_num] at h
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards with w
  rw [show w * (0 : ℝ) = 0 by ring]
  simp

/-- The inversion integral bounds the source on every horizontal line of the strip. -/
theorem norm_hardySource_line_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y < π / 2) (a : ℝ) :
    ‖hardySource ((a : ℂ) + (y : ℂ) * I)‖
      ≤ ∫ w : ℝ, Real.exp (-(2 * π * y * w)) * ‖completedZetaFourier w‖ := by
  rw [hardySource_line_eq_integral hy0 hy a]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae ?_
  filter_upwards with w
  rw [Circle.norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

end

end RHTower
