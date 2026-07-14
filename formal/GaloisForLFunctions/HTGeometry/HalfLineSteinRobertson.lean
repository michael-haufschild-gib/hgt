import Mathlib

/-!
# Half-line Stein--Robertson value relations

A positive half-line density with logarithmic half-density derivative `W` has
`rho' = -2 W rho`.  Pairing this equation with a vector field `P` produces the symmetric
first-order score `P W - P'/2`.  Half-line integration by parts then gives the exact covariance,
including the Robin/contact endpoint current `c`,

`integral f (P W - P'/2) rho = (1/2) (c + integral f' P rho)`.

This is the static integral form of the generalized Robertson commutator used in affine quantum
mechanics and polynomial quantum bootstraps.  The file also supplies the square-integrability form
of integral Cauchy--Schwarz needed to turn the covariance into an uncertainty bound.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HTGeometry

noncomputable section

/-- Symmetric first-order score associated to a vector field `P` and logarithmic
half-density derivative `W`. -/
def halfLineSteinScore (P P' W : ℝ → ℝ) (x : ℝ) : ℝ :=
  P x * W x - P' x / 2

/-- Half-line integration by parts turns the symmetric first-order score into an exact Stein
covariance with its Robin/contact anomaly retained as the endpoint current `c`. -/
theorem integral_Ioi_mul_halfLineSteinScore_with_boundary
    {f f' P P' ρ W : ℝ → ℝ}
    {c : ℝ}
    (hf : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (f' x) x)
    (hP : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt P (P' x) x)
    (hρ : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt ρ (-2 * W x * ρ x) x)
    (hleft : IntegrableOn
      (fun x => f x * halfLineSteinScore P P' W x * ρ x) (Ioi 0))
    (hright : IntegrableOn (fun x => f' x * P x * ρ x) (Ioi 0))
    (hzero : Tendsto (fun x => f x * P x * ρ x) (𝓝[>] 0) (𝓝 c))
    (hinfty : Tendsto (fun x => f x * P x * ρ x) atTop (𝓝 0)) :
    (∫ x : ℝ in Ioi 0, f x * halfLineSteinScore P P' W x * ρ x) =
      (1 / 2 : ℝ) *
        (c + ∫ x : ℝ in Ioi 0, f' x * P x * ρ x) := by
  let v : ℝ → ℝ := fun x => P x * ρ x
  let v' : ℝ → ℝ := fun x => -2 * halfLineSteinScore P P' W x * ρ x
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := by
    intro x hx
    convert (hP x hx).mul (hρ x hx) using 1
    simp only [v', halfLineSteinScore]
    ring
  have hfv' : IntegrableOn (f * v') (Ioi 0) := by
    have heq : (f * v') = fun x =>
        -2 * (f x * halfLineSteinScore P P' W x * ρ x) := by
      funext x
      simp only [Pi.mul_apply, v']
      ring
    rw [heq]
    exact hleft.const_mul (-2 : ℝ)
  have hf'v : IntegrableOn (f' * v) (Ioi 0) := by
    exact hright.congr_fun (fun x _ => by
      simp only [Pi.mul_apply, v]
      ring) measurableSet_Ioi
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := c) (b' := (0 : ℝ))
    (u := f) (u' := f') (v := v) (v' := v')
    hf hv hfv' hf'v
    (by simpa only [Pi.mul_apply, v, mul_assoc] using hzero)
    (by simpa only [Pi.mul_apply, v, mul_assoc] using hinfty)
  have hleftIntegral :
      (∫ x : ℝ in Ioi 0, f x * v' x) =
        -2 * (∫ x : ℝ in Ioi 0,
          f x * halfLineSteinScore P P' W x * ρ x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [v']
    ring
  have hrightIntegral :
      (∫ x : ℝ in Ioi 0, f' x * v x) =
        ∫ x : ℝ in Ioi 0, f' x * P x * ρ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [v]
    ring
  have hibp' :
      -2 * (∫ x : ℝ in Ioi 0,
        f x * halfLineSteinScore P P' W x * ρ x) =
      -c - (∫ x : ℝ in Ioi 0, f' x * P x * ρ x) := by
    rw [hleftIntegral, hrightIntegral] at hibp
    simpa only [zero_sub] using hibp
  linarith

/-- Zero-current specialization of the anomaly-corrected half-line Stein covariance. -/
theorem integral_Ioi_mul_halfLineSteinScore
    {f f' P P' ρ W : ℝ → ℝ}
    (hf : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (f' x) x)
    (hP : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt P (P' x) x)
    (hρ : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt ρ (-2 * W x * ρ x) x)
    (hleft : IntegrableOn
      (fun x => f x * halfLineSteinScore P P' W x * ρ x) (Ioi 0))
    (hright : IntegrableOn (fun x => f' x * P x * ρ x) (Ioi 0))
    (hzero : Tendsto (fun x => f x * P x * ρ x) (𝓝[>] 0) (𝓝 0))
    (hinfty : Tendsto (fun x => f x * P x * ρ x) atTop (𝓝 0)) :
    (∫ x : ℝ in Ioi 0, f x * halfLineSteinScore P P' W x * ρ x) =
      (1 / 2 : ℝ) * ∫ x : ℝ in Ioi 0, f' x * P x * ρ x := by
  simpa only [zero_add] using
    integral_Ioi_mul_halfLineSteinScore_with_boundary
      hf hP hρ hleft hright hzero hinfty

/-- Derivative of the local virial current selected by a vector field, a logarithmic
half-density derivative, and its density. -/
theorem hasDerivAt_halfLineSteinVirialCurrent
    {P P' ρ W W' : ℝ → ℝ} {x : ℝ}
    (hP : HasDerivAt P (P' x) x)
    (hW : HasDerivAt W (W' x) x)
    (hρ : HasDerivAt ρ (-2 * W x * ρ x) x) :
    HasDerivAt (fun y : ℝ => P y ^ 2 * W y * ρ y)
      ((2 * P x * P' x * W x + P x ^ 2 * W' x -
          2 * P x ^ 2 * W x ^ 2) * ρ x) x := by
  convert (((hP.pow 2).mul hW).mul hρ) using 1
  simp only [Pi.pow_apply, Pi.mul_apply]
  ring

/-- **Local Stein--virial value law.**  The squared symmetric first-order score is the
curvature/field-gradient energy minus one half of an exact current derivative.  This is the
pointwise ground-state form of the generalized quantum virial identity; on a half-line the
current term records the possible boundary anomaly. -/
theorem halfLineSteinScore_sq_mul_eq_curvature_sub_deriv
    {P P' ρ W W' : ℝ → ℝ} {x : ℝ}
    (hP : HasDerivAt P (P' x) x)
    (hW : HasDerivAt W (W' x) x)
    (hρ : HasDerivAt ρ (-2 * W x * ρ x) x) :
    halfLineSteinScore P P' W x ^ 2 * ρ x =
      ((1 / 2 : ℝ) * P x ^ 2 * W' x + (1 / 4 : ℝ) * P' x ^ 2) * ρ x -
        (1 / 2 : ℝ) * deriv (fun y : ℝ => P y ^ 2 * W y * ρ y) x := by
  rw [(hasDerivAt_halfLineSteinVirialCurrent hP hW hρ).deriv]
  simp only [halfLineSteinScore]
  ring

/-- Derivative of the polarized local virial current selected by two vector
fields.  The square-current theorem is its diagonal specialization. -/
theorem hasDerivAt_halfLineSteinBilinearVirialCurrent
    {P P' Q Q' ρ W W' : ℝ → ℝ} {x : ℝ}
    (hP : HasDerivAt P (P' x) x)
    (hQ : HasDerivAt Q (Q' x) x)
    (hW : HasDerivAt W (W' x) x)
    (hρ : HasDerivAt ρ (-2 * W x * ρ x) x) :
    HasDerivAt (fun y : ℝ => P y * Q y * W y * ρ y)
      (((P' x * Q x + P x * Q' x) * W x + P x * Q x * W' x -
          2 * P x * Q x * W x ^ 2) * ρ x) x := by
  convert (((hP.mul hQ).mul hW).mul hρ) using 1
  simp only [Pi.mul_apply]
  ring

/-- **Polarized local Stein--virial value law.**  A mixed score product is a
bilinear curvature/field-gradient value modulo one exact half-line current.
This is the off-diagonal generalized quantum virial identity needed for
multi-generator Rayleigh--Ritz matrices. -/
theorem halfLineSteinScore_mul_mul_eq_curvature_sub_deriv
    {P P' Q Q' ρ W W' : ℝ → ℝ} {x : ℝ}
    (hP : HasDerivAt P (P' x) x)
    (hQ : HasDerivAt Q (Q' x) x)
    (hW : HasDerivAt W (W' x) x)
    (hρ : HasDerivAt ρ (-2 * W x * ρ x) x) :
    halfLineSteinScore P P' W x * halfLineSteinScore Q Q' W x * ρ x =
      ((1 / 2 : ℝ) * P x * Q x * W' x +
          (1 / 4 : ℝ) * P' x * Q' x) * ρ x -
        (1 / 2 : ℝ) * deriv (fun y : ℝ => P y * Q y * W y * ρ y) x := by
  rw [(hasDerivAt_halfLineSteinBilinearVirialCurrent hP hQ hW hρ).deriv]
  simp only [halfLineSteinScore]
  ring

/-- **Integrated polarized hypervirial identity.**  If the mixed score and
curvature values are integrable and the half-line current vanishes at both
ends, their integrals agree exactly.  The current derivative and its
integrability are discharged internally from the local value law. -/
theorem integral_Ioi_halfLineSteinScore_mul_eq_virial
    {P P' Q Q' ρ W W' : ℝ → ℝ}
    (hP : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt P (P' x) x)
    (hQ : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt Q (Q' x) x)
    (hW : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (W' x) x)
    (hρ : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt ρ (-2 * W x * ρ x) x)
    (hscore : IntegrableOn (fun x =>
      halfLineSteinScore P P' W x * halfLineSteinScore Q Q' W x * ρ x)
        (Ioi 0))
    (hvirial : IntegrableOn (fun x =>
      ((1 / 2 : ℝ) * P x * Q x * W' x +
        (1 / 4 : ℝ) * P' x * Q' x) * ρ x) (Ioi 0))
    (hzero : Tendsto (fun x => P x * Q x * W x * ρ x)
      (𝓝[>] 0) (𝓝 0))
    (hinfty : Tendsto (fun x => P x * Q x * W x * ρ x)
      atTop (𝓝 0)) :
    (∫ x : ℝ in Ioi 0,
      halfLineSteinScore P P' W x * halfLineSteinScore Q Q' W x * ρ x) =
      ∫ x : ℝ in Ioi 0,
        ((1 / 2 : ℝ) * P x * Q x * W' x +
          (1 / 4 : ℝ) * P' x * Q' x) * ρ x := by
  let current : ℝ → ℝ := fun x => P x * Q x * W x * ρ x
  have hcurrent : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt current (deriv current x) x := by
    intro x hx
    have h := hasDerivAt_halfLineSteinBilinearVirialCurrent
      (hP x hx) (hQ x hx) (hW x hx) (hρ x hx)
    change HasDerivAt current (deriv current x) x
    rw [h.deriv]
    exact h
  have hderiv : IntegrableOn (fun x => deriv current x) (Ioi 0) := by
    have hdiff := hvirial.sub hscore
    have hscaled := hdiff.const_mul (2 : ℝ)
    apply hscaled.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hlocal := halfLineSteinScore_mul_mul_eq_curvature_sub_deriv
      (hP x hx) (hQ x hx) (hW x hx) (hρ x hx)
    change 2 *
      ((((1 / 2 : ℝ) * P x * Q x * W' x +
          (1 / 4 : ℝ) * P' x * Q' x) * ρ x) -
        halfLineSteinScore P P' W x * halfLineSteinScore Q Q' W x * ρ x) =
      deriv current x
    nlinarith
  have hderivZero : (∫ x : ℝ in Ioi 0, deriv current x) = 0 := by
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
      (u := fun _ : ℝ => 1) (u' := fun _ : ℝ => 0)
      (v := current) (v' := fun x : ℝ => deriv current x)
      (fun x _ => hasDerivAt_const x 1)
      hcurrent
      (hderiv.congr_fun (fun x _ => by simp) measurableSet_Ioi)
      ((integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi 0)).congr_fun
        (g := (fun _ : ℝ => 0) * current) (fun x _ => by simp) measurableSet_Ioi)
      (by
        convert hzero using 1
        funext x
        simp only [Pi.mul_apply, one_mul, current])
      (by
        convert hinfty using 1
        funext x
        simp only [Pi.mul_apply, one_mul, current])
    simpa only [Pi.mul_apply, one_mul, zero_mul, integral_zero, sub_zero,
      zero_sub, neg_zero] using hibp
  calc
    (∫ x : ℝ in Ioi 0,
      halfLineSteinScore P P' W x * halfLineSteinScore Q Q' W x * ρ x) =
      ∫ x : ℝ in Ioi 0,
        (((1 / 2 : ℝ) * P x * Q x * W' x +
          (1 / 4 : ℝ) * P' x * Q' x) * ρ x -
            (1 / 2 : ℝ) * deriv current x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa only [current] using
        halfLineSteinScore_mul_mul_eq_curvature_sub_deriv
          (hP x hx) (hQ x hx) (hW x hx) (hρ x hx)
    _ = ∫ x : ℝ in Ioi 0,
        ((1 / 2 : ℝ) * P x * Q x * W' x +
          (1 / 4 : ℝ) * P' x * Q' x) * ρ x := by
      rw [integral_sub hvirial (hderiv.const_mul (1 / 2 : ℝ)),
        integral_const_mul, hderivZero]
      ring

/-- Integral Cauchy--Schwarz in a form that only asks for square integrability. -/
theorem sq_integral_mul_le_integral_sq_mul_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hfmeas : AEStronglyMeasurable f μ)
    (hgmeas : AEStronglyMeasurable g μ)
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hfLp : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfmeas).2 hf
  have hgLp : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgmeas).2 hg
  have hfLp' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hfLp
  have hgLp' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hgLp
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two hfLp' hgLp'
  have habs : |∫ x, f x * g x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    calc
      |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ :=
        abs_integral_le_integral_abs
      _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [abs_mul, Real.norm_eq_abs]
  have hbound : |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
    have hfsqnorm : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) =
        ∫ x, f x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
      exact sq_abs _
    have hgsqnorm : (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) =
        ∫ x, g x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
      exact sq_abs _
    apply habs.trans
    rw [hfsqnorm, hgsqnorm] at hholder
    simpa only [← Real.sqrt_eq_rpow] using hholder
  have hfnonneg : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hgnonneg : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hright : 0 ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) *
      Real.sqrt (∫ x, g x ^ 2 ∂μ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ (abs_nonneg _) hright).2 hbound
  rw [sq_abs, mul_pow, Real.sq_sqrt hfnonneg, Real.sq_sqrt hgnonneg] at hsq
  exact hsq

end

end HTGeometry
