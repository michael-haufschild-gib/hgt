import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCuspExponentialJetTail
import GaloisForLFunctions.HTGeometry.BesselOrderIntegral
import GaloisForLFunctions.HTGeometry.BesselExteriorEnvelope

/-!
# Exterior envelope for arbitrary complex Bessel order

The completed weight `0,+4,-4` Eisenstein Fourier expansions require modified Bessel `K` with an
arbitrary complex spectral order.  The corpus Schläfli construction proves entire order dependence
but had no large-positive-argument envelope; the existing exterior theorem covered only order one.

For positive real argument `s` and arbitrary complex order `nu`, this module proves directly from
the Schläfli integral

`‖K_nu(s)‖ <= exp(-s) * exp(‖nu‖^(2 : ℕ)/(2s)) * sqrt(2*pi/s)`.

The proof uses `cosh t >= 1+t^(2 : ℕ)/2`, the elementary bound
`‖cosh(nu*t)‖ <= exp(‖nu‖t)`, and exact Gaussian completion of the square.  Positivity of `s` is
encoded in its subtype, so every exported theorem is premise-free.  This is the sharp exponential
argument decay needed to admit actual Eisenstein Whittaker coefficients into the cusp jet-tail
packet.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [BESSEL ORDER ENVELOPE]`
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Exact Gaussian completion for the arbitrary-order Schläfli majorant. -/
theorem d4BMBesselOrder_exp_quadratic_eq
    (s : {x : ℝ // 0 < x}) (R t : ℝ) :
    Real.exp (-((s : ℝ) * (1 + t ^ (2 : ℕ) / 2)) + R * t) =
      Real.exp (-(s : ℝ)) * Real.exp (R ^ (2 : ℕ) / (2 * (s : ℝ))) *
        Real.exp (-((s : ℝ) / 2) * (t - R / (s : ℝ)) ^ (2 : ℕ)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp [ne_of_gt s.property]
  ring

/-- Shifted Gaussian integral appearing in the arbitrary-order envelope. -/
theorem d4BM_integral_besselOrder_exp_quadratic
    (s : {x : ℝ // 0 < x}) (R : ℝ) :
    (∫ t : ℝ, Real.exp (-((s : ℝ) / 2) * (t - R / (s : ℝ)) ^ (2 : ℕ))) =
      Real.sqrt (2 * Real.pi / (s : ℝ)) := by
  have hshift :
      (∫ t : ℝ, Real.exp (-((s : ℝ) / 2) * (t - R / (s : ℝ)) ^ (2 : ℕ))) =
        ∫ t : ℝ, Real.exp (-((s : ℝ) / 2) * t ^ (2 : ℕ)) :=
    MeasureTheory.integral_sub_right_eq_self
      (μ := (volume : Measure ℝ))
      (fun t : ℝ => Real.exp (-((s : ℝ) / 2) * t ^ (2 : ℕ)))
      (R / (s : ℝ))
  rw [hshift, integral_gaussian]
  congr 1
  field_simp [ne_of_gt s.property]

/-- Sharp large-argument envelope for the corpus modified Bessel `K` at arbitrary complex order. -/
theorem d4BM_norm_modifiedBesselKOrder_le
    (s : {x : ℝ // 0 < x}) (nu : ℂ) :
    ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder (s : ℝ) nu‖ ≤
      Real.exp (-(s : ℝ)) *
        Real.exp (‖nu‖ ^ (2 : ℕ) / (2 * (s : ℝ))) *
        Real.sqrt (2 * Real.pi / (s : ℝ)) := by
  let M : ℝ → ℝ := fun t =>
    Real.exp (-(s : ℝ)) * Real.exp (‖nu‖ ^ (2 : ℕ) / (2 * (s : ℝ))) *
      Real.exp (-((s : ℝ) / 2) * (t - ‖nu‖ / (s : ℝ)) ^ (2 : ℕ))
  have hM : Integrable M := by
    have hbase : Integrable fun t : ℝ =>
        Real.exp (-((s : ℝ) / 2) * (t - ‖nu‖ / (s : ℝ)) ^ (2 : ℕ)) := by
      have hgauss : Integrable fun t : ℝ =>
          Real.exp (-((s : ℝ) / 2) * t ^ (2 : ℕ)) :=
        integrable_exp_neg_mul_sq (div_pos s.property (by norm_num))
      simpa using hgauss.comp_sub_right (‖nu‖ / (s : ℝ))
    simpa [M, mul_assoc] using
      hbase.const_mul
        (Real.exp (-(s : ℝ)) * Real.exp (‖nu‖ ^ (2 : ℕ) / (2 * (s : ℝ))))
  have hmajorant : ∀ t ∈ Ioi (0 : ℝ),
      ‖GaloisForLFunctions.HTGeometry.besselOrderKernel (s : ℝ) nu t‖ ≤ M t := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hnut : ‖nu * (t : ℂ)‖ = ‖nu‖ * t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hexp :
        ‖Complex.exp (-(s : ℂ) * Complex.cosh (t : ℂ))‖ =
          Real.exp (-(s : ℝ) * Real.cosh t) := by
      rw [Complex.norm_exp]
      simp [← Complex.ofReal_cosh]
    calc
      ‖GaloisForLFunctions.HTGeometry.besselOrderKernel (s : ℝ) nu t‖ =
          Real.exp (-(s : ℝ) * Real.cosh t) *
            ‖Complex.cosh (nu * (t : ℂ))‖ := by
        rw [GaloisForLFunctions.HTGeometry.besselOrderKernel, norm_mul, hexp]
      _ ≤ Real.exp (-(s : ℝ) * Real.cosh t) *
          Real.exp ‖nu * (t : ℂ)‖ :=
        mul_le_mul_of_nonneg_left
          (GaloisForLFunctions.HTGeometry.norm_complex_cosh_le_exp_norm _)
          (Real.exp_nonneg _)
      _ = Real.exp (-(s : ℝ) * Real.cosh t + ‖nu‖ * t) := by
        rw [hnut, Real.exp_add]
      _ ≤ Real.exp (-((s : ℝ) * (1 + t ^ (2 : ℕ) / 2)) + ‖nu‖ * t) := by
        apply Real.exp_le_exp.mpr
        have hcosh := HTGeometry.one_add_sq_div_two_le_cosh ht0
        have hmul := mul_le_mul_of_nonneg_left hcosh (le_of_lt s.property)
        linarith
      _ = M t := by
        rw [d4BMBesselOrder_exp_quadratic_eq]
  have hnorm :
      ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder (s : ℝ) nu‖ ≤
        ∫ t in Ioi (0 : ℝ),
          ‖GaloisForLFunctions.HTGeometry.besselOrderKernel (s : ℝ) nu t‖ :=
    norm_integral_le_integral_norm _
  refine le_trans hnorm ?_
  have hkernel : IntegrableOn
      (fun t : ℝ =>
        ‖GaloisForLFunctions.HTGeometry.besselOrderKernel (s : ℝ) nu t‖)
      (Ioi 0) := by
    refine Integrable.mono' hM.integrableOn ?_ ?_
    · exact (GaloisForLFunctions.HTGeometry.integrableOn_besselOrderKernel
        s.property nu).norm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hmajorant t ht
  have hcomp :
      (∫ t in Ioi (0 : ℝ),
          ‖GaloisForLFunctions.HTGeometry.besselOrderKernel (s : ℝ) nu t‖) ≤
        ∫ t in Ioi (0 : ℝ), M t :=
    setIntegral_mono_on hkernel hM.integrableOn measurableSet_Ioi hmajorant
  refine le_trans hcomp ?_
  have hsubset : (∫ t in Ioi (0 : ℝ), M t) ≤ ∫ t : ℝ, M t := by
    refine setIntegral_le_integral hM ?_
    filter_upwards with t
    dsimp [M]
    positivity
  refine le_trans hsubset (le_of_eq ?_)
  dsimp [M]
  rw [integral_const_mul, d4BM_integral_besselOrder_exp_quadratic]

end

end RHTower
