import GaloisForLFunctions.RHTower.BoundedSupportFourierUncertainty
import GaloisForLFunctions.RHTower.SoninL2Model
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTitchmarshUniqueness
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Compactly supported `L²` Fourier uniqueness at the Suzuki zero set

This is the Paley--Wiener/uniqueness step used in the strict clause of Suzuki (2022),
Theorem 1.3.  An arbitrary `L²(ℝ)` vector is cut to `[-a,a]`; the cut vector is integrable, so its
literal Fourier integral

`∫ x, f(x) exp(I z x)`

is defined for every complex `z`.  Compact support gives an entire function of exponential type.
Suzuki's Lemma 2.1 then says that constancy on every centered Xi zero forces global constancy;
Riemann--Lebesgue forces that constant to be zero, and Fourier injectivity forces the cut vector to
vanish.  No continuity or pointwise boundedness of the `L²` representative is assumed.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform ENNReal

noncomputable section

namespace RHTower

/-- The literal compactly supported Fourier integral used by Suzuki, for an arbitrary `L²`
representative.  The physical cutoff makes the representative integrable. -/
def suzukiCompactL2Fourier (a : ℝ) (f : SoninL2) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (indicatorCutoff (Icc (-a) a) measurableSet_Icc f) x *
    Complex.exp (I * z * (x : ℂ))

/-- The literal compact Fourier readout preserves scalar coefficients.  This is formulated at
the `L²` level, so it uses equality almost everywhere rather than selecting representatives. -/
theorem suzukiCompactL2Fourier_smul
    (a : ℝ) (c : ℂ) (f : SoninL2) (z : ℂ) :
    suzukiCompactL2Fourier a (c • f) z =
      c * suzukiCompactL2Fourier a f z := by
  unfold suzukiCompactL2Fourier
  rw [map_smul]
  change (∫ x : ℝ,
      ((c • indicatorCutoff (Icc (-a) a) measurableSet_Icc f : SoninL2) : ℝ → ℂ) x *
        Complex.exp (I * z * (x : ℂ))) =
    c • ∫ x : ℝ,
      ((indicatorCutoff (Icc (-a) a) measurableSet_Icc f : SoninL2) : ℝ → ℂ) x *
        Complex.exp (I * z * (x : ℂ))
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c
    (indicatorCutoff (Icc (-a) a) measurableSet_Icc f)] with x hx
  rw [hx]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Physical zero extension to `[-a,a]`; fixed points are the global model of `L²(-a,a)`. -/
abbrev suzukiCutoff (a : ℝ) (f : SoninL2) : SoninL2 :=
  indicatorCutoff (Icc (-a) a) measurableSet_Icc f

theorem integrable_suzukiCutoff (a : ℝ) (f : SoninL2) :
    Integrable (suzukiCutoff a f : ℝ → ℂ) :=
  integrable_indicatorCutoff_Icc (-a) a f

theorem suzukiCutoff_ae_eq_zero_off (a : ℝ) (f : SoninL2) :
    ∀ᵐ x ∂volume, x ∉ Icc (-a) a → (suzukiCutoff a f) x = 0 := by
  filter_upwards [indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc f] with x hx
  intro hnot
  rw [hx, indicator_of_notMem hnot]

private theorem abs_le_aperture_of_mem_Icc {a x : ℝ} (ha : 0 ≤ a)
    (hx : x ∈ Icc (-a) a) : |x| ≤ a := by
  rw [abs_le]
  exact hx

private theorem hasDerivAt_suzukiFourier_integrand
    (g : ℝ → ℂ) (x : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => g x * Complex.exp (I * w * (x : ℂ)))
      (g x * (I * (x : ℂ)) * Complex.exp (I * z * (x : ℂ))) z := by
  have hlin : HasDerivAt (fun w : ℂ => I * w * (x : ℂ)) (I * (x : ℂ)) z := by
    simpa only [id_eq, one_mul, mul_assoc] using
      ((hasDerivAt_id z).const_mul I).mul_const (x : ℂ)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hlin.cexp.const_mul (g x)

theorem integrable_suzukiCompactL2Fourier_integrand
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) (z : ℂ) :
    Integrable fun x : ℝ => (suzukiCutoff a f) x * Complex.exp (I * z * (x : ℂ)) := by
  let g : ℝ → ℂ := (suzukiCutoff a f : ℝ → ℂ)
  have hg : Integrable g := integrable_suzukiCutoff a f
  refine Integrable.mono' (hg.norm.const_mul (Real.exp (a * |z.im|))) ?_ ?_
  · exact hg.aestronglyMeasurable.mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [suzukiCutoff_ae_eq_zero_off a f] with x hx
    by_cases hmem : x ∈ Icc (-a) a
    · have hxabs : |x| ≤ a := abs_le_aperture_of_mem_Icc ha hmem
      rw [norm_mul, Complex.norm_exp]
      have hre : (I * z * (x : ℂ)).re = -(z.im * x) := by
        simp [Complex.mul_re]
      have hle : -(z.im * x) ≤ a * |z.im| := by
        calc
          -(z.im * x) ≤ |z.im * x| := neg_le_abs _
          _ = |z.im| * |x| := abs_mul _ _
          _ ≤ |z.im| * a := mul_le_mul_of_nonneg_left hxabs (abs_nonneg _)
          _ = a * |z.im| := by ring
      rw [hre]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (norm_nonneg (g x))
    · rw [hx hmem]
      simpa only [zero_mul, norm_zero] using
        mul_nonneg (Real.exp_nonneg (a * |z.im|)) (norm_nonneg (g x))

/-- Differentiation under the integral for arbitrary compactly supported `L²` data. -/
theorem hasDerivAt_suzukiCompactL2Fourier
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) (z₀ : ℂ) :
    HasDerivAt (suzukiCompactL2Fourier a f)
      (∫ x : ℝ, (suzukiCutoff a f) x * (I * (x : ℂ)) *
        Complex.exp (I * z₀ * (x : ℂ))) z₀ := by
  let g : ℝ → ℂ := (suzukiCutoff a f : ℝ → ℂ)
  have hg : Integrable g := integrable_suzukiCutoff a f
  have hball : Metric.ball z₀ 1 ∈ nhds z₀ := Metric.ball_mem_nhds z₀ one_pos
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (z : ℂ) (x : ℝ) => g x * Complex.exp (I * z * (x : ℂ)))
    (F' := fun (z : ℂ) (x : ℝ) =>
      g x * (I * (x : ℂ)) * Complex.exp (I * z * (x : ℂ)))
    (bound := fun x : ℝ => ‖g x‖ * (a * Real.exp ((‖z₀‖ + 1) * a)))
    hball ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with z
    exact hg.aestronglyMeasurable.mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · simpa [g] using integrable_suzukiCompactL2Fourier_integrand ha f z₀
  · exact ((hg.aestronglyMeasurable.mul (by fun_prop)).mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
  · filter_upwards [suzukiCutoff_ae_eq_zero_off a f] with x hx
    intro z hz
    by_cases hmem : x ∈ Icc (-a) a
    · have hxabs : |x| ≤ a := abs_le_aperture_of_mem_Icc ha hmem
      have hznorm : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have hdist : ‖z - z₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        calc
          ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
            simpa [sub_add_cancel] using norm_add_le (z - z₀) z₀
          _ ≤ ‖z₀‖ + 1 := by linarith
      rw [norm_mul, norm_mul, Complex.norm_exp]
      have hIx : ‖I * (x : ℂ)‖ = |x| := by simp
      rw [hIx]
      have hre : (I * z * (x : ℂ)).re = -(z.im * x) := by
        simp [Complex.mul_re]
      have hzim : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      have hle : -(z.im * x) ≤ (‖z₀‖ + 1) * a := by
        calc
          -(z.im * x) ≤ |z.im * x| := neg_le_abs _
          _ = |z.im| * |x| := abs_mul _ _
          _ ≤ ‖z‖ * a := mul_le_mul hzim hxabs (abs_nonneg _) (norm_nonneg _)
          _ ≤ (‖z₀‖ + 1) * a :=
            mul_le_mul_of_nonneg_right hznorm ha
      rw [hre]
      have hexp := Real.exp_le_exp.mpr hle
      have hga : ‖g x‖ * |x| ≤ ‖g x‖ * a :=
        mul_le_mul_of_nonneg_left hxabs (norm_nonneg _)
      calc
        ‖g x‖ * |x| * Real.exp (-(z.im * x))
            ≤ ‖g x‖ * a * Real.exp (-(z.im * x)) :=
          mul_le_mul_of_nonneg_right hga (Real.exp_nonneg _)
        _ ≤ ‖g x‖ * a * Real.exp ((‖z₀‖ + 1) * a) :=
          mul_le_mul_of_nonneg_left hexp
            (mul_nonneg (norm_nonneg _) ha)
        _ = ‖g x‖ * (a * Real.exp ((‖z₀‖ + 1) * a)) := by ring
    · have hgzero : g x = 0 := by simpa [g] using hx hmem
      rw [hgzero]
      simp
  · exact hg.norm.mul_const _
  · filter_upwards with x
    intro z _
    exact hasDerivAt_suzukiFourier_integrand g x z

/-- The literal compactly supported `L²` Fourier integral is entire. -/
theorem differentiable_suzukiCompactL2Fourier
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) :
    Differentiable ℂ (suzukiCompactL2Fourier a f) := fun z =>
  (hasDerivAt_suzukiCompactL2Fourier ha f z).differentiableAt

/-- Paley--Wiener exponential-type bound for arbitrary compactly supported `L²` data. -/
theorem norm_suzukiCompactL2Fourier_le
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) (z : ℂ) :
    ‖suzukiCompactL2Fourier a f z‖ ≤
      (∫ x : ℝ, ‖(suzukiCutoff a f) x‖) * Real.exp (a * |z.im|) := by
  let g : ℝ → ℂ := (suzukiCutoff a f : ℝ → ℂ)
  have hg : Integrable g := integrable_suzukiCutoff a f
  calc
    ‖suzukiCompactL2Fourier a f z‖
        ≤ ∫ x : ℝ, ‖g x * Complex.exp (I * z * (x : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, ‖g x‖ * Real.exp (a * |z.im|) := by
      refine integral_mono_ae ?_ (hg.norm.mul_const _) ?_
      · exact (integrable_suzukiCompactL2Fourier_integrand ha f z).norm
      · filter_upwards [suzukiCutoff_ae_eq_zero_off a f] with x hx
        by_cases hmem : x ∈ Icc (-a) a
        · have hxabs : |x| ≤ a := abs_le_aperture_of_mem_Icc ha hmem
          rw [norm_mul, Complex.norm_exp]
          have hre : (I * z * (x : ℂ)).re = -(z.im * x) := by
            simp [Complex.mul_re]
          have hle : -(z.im * x) ≤ a * |z.im| := by
            calc
              -(z.im * x) ≤ |z.im * x| := neg_le_abs _
              _ = |z.im| * |x| := abs_mul _ _
              _ ≤ |z.im| * a := mul_le_mul_of_nonneg_left hxabs (abs_nonneg _)
              _ = a * |z.im| := by ring
          rw [hre]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (norm_nonneg _)
        · have hgzero : g x = 0 := by simpa [g] using hx hmem
          rw [hgzero]
          simp
    _ = (∫ x : ℝ, ‖(suzukiCutoff a f) x‖) * Real.exp (a * |z.im|) := by
      rw [integral_mul_const]

theorem suzukiCompactL2Fourier_exponentialType
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ,
      ‖suzukiCompactL2Fourier a f z‖ ≤ C * Real.exp (a * ‖z‖) := by
  let M : ℝ := ∫ x : ℝ, ‖(suzukiCutoff a f) x‖
  refine ⟨max 1 M, le_max_left _ _, fun z => ?_⟩
  have hM0 : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  have hbase := norm_suzukiCompactL2Fourier_le ha f z
  have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hexp : Real.exp (a * |z.im|) ≤ Real.exp (a * ‖z‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left him ha)
  calc
    ‖suzukiCompactL2Fourier a f z‖ ≤ M * Real.exp (a * |z.im|) := hbase
    _ ≤ M * Real.exp (a * ‖z‖) := mul_le_mul_of_nonneg_left hexp hM0
    _ ≤ max 1 M * Real.exp (a * ‖z‖) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)

/-- On the real axis, Suzuki's `exp(I z x)` convention is the classical Fourier transform at
frequency `-z/(2π)`. -/
theorem suzukiCompactL2Fourier_real_eq_fourier
    (a : ℝ) (f : SoninL2) (w : ℝ) :
    suzukiCompactL2Fourier a f ((-2 * Real.pi * w : ℝ) : ℂ) =
      FourierTransform.fourier (suzukiCutoff a f : ℝ → ℂ) w := by
  rw [suzukiCompactL2Fourier, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hexp : Complex.exp (I * ((-2 * Real.pi * w : ℝ) : ℂ) * (x : ℂ)) =
      Complex.exp ((-2 * Real.pi * x * w : ℝ) * I) := by
    congr 1
    push_cast
    ring
  rw [hexp, mul_comm]

theorem suzukiCompactL2Fourier_constant_eq_zero
    {a : ℝ} (f : SoninL2) {c : ℂ}
    (hconst : suzukiCompactL2Fourier a f = fun _ => c) : c = 0 := by
  let g : ℝ → ℂ := (suzukiCutoff a f : ℝ → ℂ)
  have hfourier : FourierTransform.fourier g = fun _ => c := by
    funext w
    rw [← suzukiCompactL2Fourier_real_eq_fourier a f w]
    exact congrFun hconst _
  have hrl : Tendsto (fun _ : ℝ => c) atTop (nhds 0) := by
    rw [← hfourier]
    exact (Real.zero_at_infty_fourier g).mono_left _root_.atTop_le_cocompact
  exact tendsto_nhds_unique tendsto_const_nhds hrl

/-- **Compact `L²` Fourier uniqueness at the centered Xi zero set.**  If the literal Fourier
integral of the cut vector takes one constant value at every zero of `xi(1/2-Iz)`, then the cut
vector vanishes in `L²`.  This is the exact strictness input in Suzuki's Theorem 1.3. -/
theorem suzukiCutoff_eq_zero_of_fourier_constant_on_xiZeros
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) {c : ℂ}
    (hvalues : ∀ z : ℂ, xi (1 / 2 - I * z) = 0 →
      suzukiCompactL2Fourier a f z = c) :
    suzukiCutoff a f = 0 := by
  obtain ⟨C, hC, hgrow⟩ := suzukiCompactL2Fourier_exponentialType ha f
  have hconst := suzuki_lemma_two_one
    (differentiable_suzukiCompactL2Fourier ha f) c
      ⟨a, C, ha, hC, hgrow⟩ hvalues
  have hc : c = 0 := suzukiCompactL2Fourier_constant_eq_zero f hconst
  have hFzero : ∀ w : ℝ, FourierTransform.fourier
      (suzukiCutoff a f : ℝ → ℂ) w = 0 := by
    intro w
    rw [← suzukiCompactL2Fourier_real_eq_fourier a f w, congrFun hconst, hc]
  have hae : (suzukiCutoff a f : ℝ → ℂ) =ᵐ[volume] 0 :=
    integrable_ae_eq_zero_of_fourier_eq_zero (integrable_suzukiCutoff a f) hFzero
  exact Lp.ext (hae.trans (Lp.coeFn_zero ℂ 2 volume).symm)

/-- Fixed points of the physical cutoff are the exact zero-extended model of `L²(-a,a)`.
Constancy of their Fourier transform on every centered Xi zero forces the original vector to
vanish. -/
theorem eq_zero_of_supported_fourier_constant_on_xiZeros
    {a : ℝ} (ha : 0 ≤ a) {f : SoninL2}
    (hsupp : suzukiCutoff a f = f) {c : ℂ}
    (hvalues : ∀ z : ℂ, xi (1 / 2 - I * z) = 0 →
      suzukiCompactL2Fourier a f z = c) :
    f = 0 := by
  rw [← hsupp]
  exact suzukiCutoff_eq_zero_of_fourier_constant_on_xiZeros ha f hvalues

end RHTower
