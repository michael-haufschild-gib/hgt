import GaloisForLFunctions.HTGeometry.BesselOrderRecurrence
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Elementary real-argument differentiation of the Schlaefli Bessel integral

Extracted unchanged from the argument-derivative module so that local boundary
proofs can use the integral calculus without importing the Eisenstein expansion.
The original theorem names and namespace are preserved.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Derivative of the Schlaefli integrand in its real Bessel argument. -/
def d4BMBesselArgumentKernelDeriv (s : ℝ) (nu : ℂ) (t : ℝ) : ℂ :=
  -Complex.cosh (t : ℂ) * GaloisForLFunctions.HTGeometry.besselOrderKernel s nu t

/-- Hyperbolic product-to-sum identifies the argument derivative with the two adjacent orders. -/
theorem d4BMBesselArgumentKernelDeriv_eq_shiftAverage
    (s : ℝ) (nu : ℂ) (t : ℝ) :
    d4BMBesselArgumentKernelDeriv s nu t =
      -(1 / 2 : ℂ) *
        (GaloisForLFunctions.HTGeometry.besselOrderKernel s (nu + 1) t +
          GaloisForLFunctions.HTGeometry.besselOrderKernel s (nu - 1) t) := by
  simp only [d4BMBesselArgumentKernelDeriv,
    GaloisForLFunctions.HTGeometry.besselOrderKernel]
  rw [add_mul, sub_mul, Complex.cosh_add, Complex.cosh_sub]
  simp only [one_mul]
  ring

/-- The real-argument derivative kernel is integrable on the Schlaefli half-line. -/
theorem d4BM_integrableOn_besselArgumentKernelDeriv
    {s : ℝ} (hs : 0 < s) (nu : ℂ) :
    IntegrableOn (d4BMBesselArgumentKernelDeriv s nu) (Ioi 0) := by
  have hp := GaloisForLFunctions.HTGeometry.integrableOn_besselOrderKernel hs (nu + 1)
  have hm := GaloisForLFunctions.HTGeometry.integrableOn_besselOrderKernel hs (nu - 1)
  refine ((hp.add hm).const_mul (-(1 / 2 : ℂ))).congr ?_
  filter_upwards with t
  exact (d4BMBesselArgumentKernelDeriv_eq_shiftAverage s nu t).symm

private theorem d4BM_hasDerivAt_besselOrderKernel_argument
    (s : ℝ) (nu : ℂ) (t : ℝ) :
    HasDerivAt (fun q : ℝ =>
      GaloisForLFunctions.HTGeometry.besselOrderKernel q nu t)
      (d4BMBesselArgumentKernelDeriv s nu t) s := by
  have hlinear : HasDerivAt
      (fun q : ℝ => -(q : ℂ) * Complex.cosh (t : ℂ))
      (-Complex.cosh (t : ℂ)) s := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := s)).neg.mul_const
      (Complex.cosh (t : ℂ))
    simpa [neg_mul] using h
  have hexp := (Complex.hasDerivAt_exp (-(s : ℂ) * Complex.cosh (t : ℂ))).comp s hlinear
  have hmul := hexp.mul_const (Complex.cosh (nu * (t : ℂ)))
  simpa [Function.comp_apply, d4BMBesselArgumentKernelDeriv,
    GaloisForLFunctions.HTGeometry.besselOrderKernel,
    mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Differentiation under the Schlaefli integral in the positive real argument. -/
theorem d4BM_hasDerivAt_integral_besselOrderKernel_argument
    {s : ℝ} (hs : 0 < s) (nu : ℂ) :
    HasDerivAt (fun q : ℝ =>
      ∫ t in Ioi (0 : ℝ),
        GaloisForLFunctions.HTGeometry.besselOrderKernel q nu t)
      (∫ t in Ioi (0 : ℝ), d4BMBesselArgumentKernelDeriv s nu t) s := by
  let radius : ℝ := s / 2
  let S : Set ℝ := Metric.ball s radius
  let q0 : ℝ := s / 2
  let bound : ℝ → ℝ := fun t => ‖d4BMBesselArgumentKernelDeriv q0 nu t‖
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hS : S ∈ nhds s := Metric.ball_mem_nhds s hradius
  have hq0 : 0 < q0 := by dsimp [q0]; linarith
  have hmeas : ∀ᶠ q in nhds s,
      AEStronglyMeasurable
        (GaloisForLFunctions.HTGeometry.besselOrderKernel q nu)
        (volume.restrict (Ioi 0)) := by
    filter_upwards with q
    exact (by
      unfold GaloisForLFunctions.HTGeometry.besselOrderKernel
      fun_prop : Continuous fun t : ℝ =>
        GaloisForLFunctions.HTGeometry.besselOrderKernel q nu t).aestronglyMeasurable
  have hint := GaloisForLFunctions.HTGeometry.integrableOn_besselOrderKernel hs nu
  have hderivMeas := (d4BM_integrableOn_besselArgumentKernelDeriv hs nu).aestronglyMeasurable
  have hboundInt : Integrable bound (volume.restrict (Ioi 0)) :=
    (d4BM_integrableOn_besselArgumentKernelDeriv hq0 nu).norm
  have hdom : ∀ᵐ t ∂volume.restrict (Ioi 0),
      ∀ q ∈ S,
        ‖d4BMBesselArgumentKernelDeriv q nu t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht q hq
    have habs : |q - s| < radius := by simpa [S, Real.dist_eq] using hq
    have hqLower : q0 < q := by
      dsimp [radius] at habs
      rw [abs_lt] at habs
      dsimp [q0]
      linarith
    have hcosh0 : 0 ≤ Real.cosh t := (Real.cosh_pos t).le
    have hExp : Real.exp (-(q * Real.cosh t)) ≤
        Real.exp (-(q0 * Real.cosh t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hnormExp (a : ℝ) :
        ‖Complex.exp (-(a : ℂ) * Complex.cosh (t : ℂ))‖ =
          Real.exp (-(a * Real.cosh t)) := by
      rw [Complex.norm_exp]
      simp [← Complex.ofReal_cosh]
    dsimp [bound]
    simp only [d4BMBesselArgumentKernelDeriv, norm_mul, norm_neg,
      GaloisForLFunctions.HTGeometry.besselOrderKernel]
    rw [hnormExp q, hnormExp q0]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hExp (norm_nonneg _)) (norm_nonneg _)
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioi 0),
      ∀ q ∈ S,
        HasDerivAt (fun a : ℝ =>
          GaloisForLFunctions.HTGeometry.besselOrderKernel a nu t)
          (d4BMBesselArgumentKernelDeriv q nu t) q := by
    filter_upwards with t
    intro q _
    exact d4BM_hasDerivAt_besselOrderKernel_argument q nu t
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hS hmeas hint hderivMeas hdom hboundInt hderiv).2

/-- Integral of the argument derivative is the adjacent-order average. -/
theorem d4BM_integral_besselArgumentKernelDeriv_eq
    {s : ℝ} (hs : 0 < s) (nu : ℂ) :
    (∫ t in Ioi (0 : ℝ), d4BMBesselArgumentKernelDeriv s nu t) =
      -(1 / 2 : ℂ) *
        (GaloisForLFunctions.HTGeometry.modifiedBesselKOrder s (nu + 1) +
          GaloisForLFunctions.HTGeometry.modifiedBesselKOrder s (nu - 1)) := by
  have hp := GaloisForLFunctions.HTGeometry.integrableOn_besselOrderKernel hs (nu + 1)
  have hm := GaloisForLFunctions.HTGeometry.integrableOn_besselOrderKernel hs (nu - 1)
  rw [show (∫ t in Ioi (0 : ℝ), d4BMBesselArgumentKernelDeriv s nu t) =
      ∫ t in Ioi (0 : ℝ), -(1 / 2 : ℂ) *
        (GaloisForLFunctions.HTGeometry.besselOrderKernel s (nu + 1) t +
          GaloisForLFunctions.HTGeometry.besselOrderKernel s (nu - 1) t) by
    apply integral_congr_ae
    filter_upwards with t
    exact d4BMBesselArgumentKernelDeriv_eq_shiftAverage s nu t]
  rw [integral_const_mul, integral_add hp hm]
  rfl

/-- Exact positive-real argument derivative of the arbitrary-complex-order modified Bessel
carrier. -/
theorem d4BM_hasDerivAt_modifiedBesselKOrder_argument
    {s : ℝ} (hs : 0 < s) (nu : ℂ) :
    HasDerivAt (fun q : ℝ =>
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder q nu)
      (-(1 / 2 : ℂ) *
        (GaloisForLFunctions.HTGeometry.modifiedBesselKOrder s (nu + 1) +
          GaloisForLFunctions.HTGeometry.modifiedBesselKOrder s (nu - 1))) s := by
  change HasDerivAt (fun q : ℝ =>
      ∫ t in Ioi (0 : ℝ),
        GaloisForLFunctions.HTGeometry.besselOrderKernel q nu t) _ s
  rw [← d4BM_integral_besselArgumentKernelDeriv_eq hs nu]
  exact d4BM_hasDerivAt_integral_besselOrderKernel_argument hs nu

end

end RHTower
