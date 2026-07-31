import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The finite-aperture Fourier pairing

On the window `(-a, a)` the Fourier transform

`F_v (z) = ∫_{-a}^{a} v x * exp (i z x) dx`

of a square-integrable density is the inner product of `v` against an explicit exponential test
vector of `L²(-a, a)`.  Cauchy–Schwarz therefore converts `L²` convergence of the densities into
convergence of the transforms that is uniform on every set of bounded imaginary height — with the
completely explicit constant `√(2a) · exp(|Im z| a)`.

This is the analytic bridge between a strong resolvent limit in `L²(-a, a)` and a locally uniform
limit of the associated entire transforms.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Topology Set

noncomputable section

/-- Lebesgue measure on the aperture window `(-a, a)`. -/
def apertureMeasure (a : ℝ) : Measure ℝ := volume.restrict (Set.Ioo (-a) a)

instance apertureMeasure_isFiniteMeasure (a : ℝ) : IsFiniteMeasure (apertureMeasure a) := by
  unfold apertureMeasure
  infer_instance

theorem apertureMeasure_ae_mem (a : ℝ) : ∀ᵐ x ∂(apertureMeasure a), x ∈ Set.Ioo (-a) a := by
  unfold apertureMeasure
  exact ae_restrict_mem measurableSet_Ioo

theorem abs_le_of_mem_aperture {a x : ℝ} (hx : x ∈ Set.Ioo (-a) a) : |x| ≤ a := by
  obtain ⟨h1, h2⟩ := hx
  exact le_of_lt (abs_lt.mpr ⟨h1, h2⟩)

/-! ## The exponential test vector -/

/-- The exponential test vector of the aperture window: its conjugate is `exp (i z x)`. -/
def apertureCharFun (z : ℂ) (x : ℝ) : ℂ := Complex.exp ((starRingEnd ℂ) (I * z * (x : ℂ)))

theorem conj_apertureCharFun (z : ℂ) (x : ℝ) :
    (starRingEnd ℂ) (apertureCharFun z x) = Complex.exp (I * z * (x : ℂ)) := by
  rw [apertureCharFun, ← Complex.exp_conj]
  simp

theorem norm_apertureCharFun (z : ℂ) (x : ℝ) :
    ‖apertureCharFun z x‖ = Real.exp (-(z.im * x)) := by
  rw [apertureCharFun, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem continuous_apertureCharFun (z : ℂ) : Continuous (apertureCharFun z) := by
  unfold apertureCharFun
  fun_prop

theorem apertureCharFun_memLp (a : ℝ) (z : ℂ) :
    MemLp (apertureCharFun z) 2 (apertureMeasure a) := by
  refine MemLp.of_bound (continuous_apertureCharFun z).aestronglyMeasurable
    (Real.exp (|z.im| * a)) ?_
  filter_upwards [apertureMeasure_ae_mem a] with x hx
  rw [norm_apertureCharFun]
  apply Real.exp_monotone
  have habs : |x| ≤ a := abs_le_of_mem_aperture hx
  have h1 : -(z.im * x) ≤ |z.im * x| := neg_le_abs _
  have h2 : |z.im * x| = |z.im| * |x| := abs_mul _ _
  have h3 : |z.im| * |x| ≤ |z.im| * a := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  linarith [h1, h2.le, h2.ge, h3]

/-- The exponential test vector as an `L²` vector of the aperture window. -/
def apertureChar (a : ℝ) (z : ℂ) : Lp ℂ 2 (apertureMeasure a) :=
  (apertureCharFun_memLp a z).toLp _

/-- The square root of the window length, the Cauchy–Schwarz factor. -/
def apertureWindow (a : ℝ) : ℝ := (measureUnivNNReal (apertureMeasure a) : ℝ) ^ ((2 : ℝ)⁻¹)

theorem apertureWindow_nonneg (a : ℝ) : 0 ≤ apertureWindow a :=
  Real.rpow_nonneg (by positivity) _

theorem norm_apertureChar_le (a : ℝ) (z : ℂ) :
    ‖apertureChar a z‖ ≤ apertureWindow a * Real.exp (|z.im| * a) := by
  have hbound : ∀ᵐ x ∂(apertureMeasure a),
      ‖(apertureChar a z : ℝ → ℂ) x‖ ≤ Real.exp (|z.im| * a) := by
    filter_upwards [(apertureCharFun_memLp a z).coeFn_toLp, apertureMeasure_ae_mem a]
      with x hx hmem
    rw [show (apertureChar a z : ℝ → ℂ) x = apertureCharFun z x from hx,
      norm_apertureCharFun]
    apply Real.exp_monotone
    have habs : |x| ≤ a := abs_le_of_mem_aperture hmem
    have h1 : -(z.im * x) ≤ |z.im * x| := neg_le_abs _
    have h2 : |z.im * x| = |z.im| * |x| := abs_mul _ _
    have h3 : |z.im| * |x| ≤ |z.im| * a := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    linarith [h1, h2.le, h2.ge, h3]
  have := Lp.norm_le_of_ae_bound (f := apertureChar a z) (Real.exp_pos _).le hbound
  simpa [apertureWindow] using this

/-! ## The aperture Fourier transform -/

/-- The finite-aperture Fourier transform of a square-integrable density. -/
def apertureFourier (a : ℝ) (v : Lp ℂ 2 (apertureMeasure a)) (z : ℂ) : ℂ :=
  inner ℂ (apertureChar a z) v

theorem apertureFourier_eq_integral (a : ℝ) (v : Lp ℂ 2 (apertureMeasure a)) (z : ℂ) :
    apertureFourier a v z
      = ∫ x, Complex.exp (I * z * (x : ℂ)) * (v : ℝ → ℂ) x ∂(apertureMeasure a) := by
  rw [apertureFourier, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(apertureCharFun_memLp a z).coeFn_toLp] with x hx
  rw [show (apertureChar a z : ℝ → ℂ) x = apertureCharFun z x from hx, RCLike.inner_apply,
    conj_apertureCharFun]
  ring

/-- The transform of a genuine function is the interval integral. -/
theorem apertureFourier_toLp (a : ℝ) (ha : 0 ≤ a) (f : ℝ → ℂ)
    (hf : MemLp f 2 (apertureMeasure a)) (z : ℂ) :
    apertureFourier a (hf.toLp f) z = ∫ x in (-a)..a, Complex.exp (I * z * (x : ℂ)) * f x := by
  rw [apertureFourier_eq_integral, intervalIntegral.integral_of_le (by linarith),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- **Cauchy–Schwarz for the aperture pairing.** -/
theorem norm_apertureFourier_sub_le (a : ℝ) (v w : Lp ℂ 2 (apertureMeasure a)) (z : ℂ) :
    ‖apertureFourier a v z - apertureFourier a w z‖
      ≤ apertureWindow a * Real.exp (|z.im| * a) * ‖v - w‖ := by
  have hsub : apertureFourier a v z - apertureFourier a w z
      = inner ℂ (apertureChar a z) (v - w) := by
    rw [apertureFourier, apertureFourier, inner_sub_right]
  rw [hsub]
  refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
  exact mul_le_mul_of_nonneg_right (norm_apertureChar_le a z) (norm_nonneg _)

/-- **Uniform transfer of `L²` convergence.**  On every set of bounded imaginary height the
transforms converge uniformly whenever the densities converge in `L²`. -/
theorem norm_apertureFourier_sub_le_of_im_bound
    {a M : ℝ} (v w : Lp ℂ 2 (apertureMeasure a)) {z : ℂ} (hz : |z.im| ≤ M) (ha : 0 ≤ a) :
    ‖apertureFourier a v z - apertureFourier a w z‖
      ≤ apertureWindow a * Real.exp (M * a) * ‖v - w‖ := by
  refine le_trans (norm_apertureFourier_sub_le a v w z) ?_
  have hexp : Real.exp (|z.im| * a) ≤ Real.exp (M * a) :=
    Real.exp_monotone (mul_le_mul_of_nonneg_right hz ha)
  have h1 : apertureWindow a * Real.exp (|z.im| * a) ≤ apertureWindow a * Real.exp (M * a) :=
    mul_le_mul_of_nonneg_left hexp (apertureWindow_nonneg a)
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-! ## The free exponential density -/

theorem apertureExpFun_memLp (a : ℝ) :
    MemLp (fun x : ℝ => Complex.exp (x : ℂ)) 2 (apertureMeasure a) := by
  refine MemLp.of_bound (by fun_prop) (Real.exp a) ?_
  filter_upwards [apertureMeasure_ae_mem a] with x hx
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_re]
  exact Real.exp_monotone (le_trans (le_abs_self x) (abs_le_of_mem_aperture hx))

/-- The free-interval density `exp x` as an `L²` vector of the aperture window. -/
def apertureExp (a : ℝ) : Lp ℂ 2 (apertureMeasure a) :=
  (apertureExpFun_memLp a).toLp _

theorem apertureFourier_apertureExp (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    apertureFourier a (apertureExp a) z
      = ∫ x in (-a)..a, Complex.exp ((1 + I * z) * (x : ℂ)) := by
  rw [apertureExp, apertureFourier_toLp a ha _ (apertureExpFun_memLp a) z]
  refine intervalIntegral.integral_congr ?_
  intro x _
  show Complex.exp (I * z * (x : ℂ)) * Complex.exp ((x : ℂ)) = Complex.exp ((1 + I * z) * (x : ℂ))
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The closed form of the free transform away from the anchor point. -/
theorem apertureFourier_apertureExp_eq (a : ℝ) (ha : 0 ≤ a) {z : ℂ} (hz : 1 + I * z ≠ 0) :
    apertureFourier a (apertureExp a) z
      = (Complex.exp ((1 + I * z) * (a : ℂ)) - Complex.exp (-((1 + I * z) * (a : ℂ))))
          / (1 + I * z) := by
  have hneg : (1 + I * z) * ((-a : ℝ) : ℂ) = -((1 + I * z) * (a : ℂ)) := by
    push_cast
    ring
  rw [apertureFourier_apertureExp a ha z, integral_exp_mul_complex hz, hneg]

end

end GaloisForLFunctions.HTGeometry
