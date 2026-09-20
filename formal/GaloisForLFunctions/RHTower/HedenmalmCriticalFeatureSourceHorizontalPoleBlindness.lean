import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureSourcePlemeljTrace
import GaloisForLFunctions.RHTower.XiWeilCriterionConverse

/-!
# Horizontal-pole blindness of the HCF source density

The HCF positive-shift source uses the imaginary part of a logarithmic
derivative while its observation variable moves horizontally.  At a zero on
that horizontal line, the local logarithmic pole is `m / (x - x₀)`, which is
real.  Therefore the source density annihilates the entire positive
multiplicity residue and agrees off the zero with the imaginary part of the
analytic cofactor.

This closes a source-side no-go relevant to the HCF `L¹` producer gate:
horizontal zero crossings cannot be detected by an `L¹` bound on this scalar
source.  A useful replacement must retain transverse information, for
example a quadratic frame across the shift parameter.
-/

open Complex Filter Topology Metric Set MeasureTheory
open RHTower.RealBoundaryDivisor

namespace RHTower

noncomputable section

private theorem im_div_ofReal_mul_I (m r : ℝ) :
    ((m : ℂ) / ((r : ℂ) * I)).im = -m / r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  rw [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  simp [div_eq_mul_inv, hr]

/-- On a horizontal positive-shift scan, the continued pole--Gamma source
annihilates the complete local logarithmic pole.  Away from the zero, it is
exactly the imaginary logarithmic derivative of the analytic nonvanishing
cofactor. -/
theorem criticalFeaturePositiveShiftPoleGammaDensity_eq_cofactor_im_of_horizontal_factor
    {x x0 eta R : ℝ} {g : ℂ → ℂ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hgan : AnalyticOnNhd ℂ g
      (ball ((x0 : ℂ) + (eta : ℂ) * I) R))
    (hg0 : ∀ z ∈ ball ((x0 : ℂ) + (eta : ℂ) * I) R, g z ≠ 0)
    (hfact : ∀ z ∈ ball ((x0 : ℂ) + (eta : ℂ) * I) R,
      XiC z = (z - ((x0 : ℂ) + (eta : ℂ) * I)) ^
        (analyticOrderAt XiC ((x0 : ℂ) + (eta : ℂ) * I)).toNat * g z)
    (hx : (x : ℂ) + (eta : ℂ) * I ∈
      ball ((x0 : ℂ) + (eta : ℂ) * I) R)
    (hne : x ≠ x0) :
    criticalFeaturePositiveShiftPoleGammaDensity eta x =
      -(Real.pi)⁻¹ * (logDeriv g ((x : ℂ) + (eta : ℂ) * I)).im := by
  let z : ℂ := (x : ℂ) + (eta : ℂ) * I
  let p : ℂ := (x0 : ℂ) + (eta : ℂ) * I
  have hzne : z ≠ p := by
    intro h
    apply hne
    simpa [z, p] using congrArg Complex.re h
  have hXi : XiC z ≠ 0 := by
    rw [hfact z (by simpa [z, p] using hx)]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzne))
      (hg0 z (by simpa [z, p] using hx))
  have hXiLower : XiC ((x : ℂ) - (eta : ℂ) * I) ≠ 0 := by
    have hconj := XiC_ne_zero_conj hXi
    have hcoord : (starRingEnd ℂ) z = (x : ℂ) - (eta : ℂ) * I := by
      simp only [z, map_add, map_mul, conj_ofReal, conj_I]
      ring
    rwa [hcoord] at hconj
  have hsource := boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity
    heta0 hetaHalf hXiLower
  have hpole := logDeriv_XiC_eq_pole_add hgan hg0 hfact
    (by simpa [z, p] using hx) hzne
  have hdiff : z - p = ((x - x0 : ℝ) : ℂ) := by
    simp [z, p]
  rw [← hsource, boundaryDensity, hpole, Complex.add_im, hdiff]
  rw [div_eq_mul_inv]
  simp [z]

/-- On a vertical scan through a positive-shift Xi zero, the source retains
the complete logarithmic pole.  Its signed coefficient is the positive
multiplicity divided by `π`; only the analytic cofactor remains after this
principal part. -/
theorem criticalFeaturePositiveShiftPoleGammaDensity_eq_transverse_pole_sub_cofactor_im_of_vertical_factor
    {eta eta0 x0 R : ℝ} {g : ℂ → ℂ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hgan : AnalyticOnNhd ℂ g
      (ball ((x0 : ℂ) + (eta0 : ℂ) * I) R))
    (hg0 : ∀ z ∈ ball ((x0 : ℂ) + (eta0 : ℂ) * I) R, g z ≠ 0)
    (hfact : ∀ z ∈ ball ((x0 : ℂ) + (eta0 : ℂ) * I) R,
      XiC z = (z - ((x0 : ℂ) + (eta0 : ℂ) * I)) ^
        (analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat * g z)
    (hmem : (x0 : ℂ) + (eta : ℂ) * I ∈
      ball ((x0 : ℂ) + (eta0 : ℂ) * I) R)
    (hne : eta ≠ eta0) :
    criticalFeaturePositiveShiftPoleGammaDensity eta x0 =
      (Real.pi)⁻¹ *
        ((analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat : ℝ) /
          (eta - eta0) -
      (Real.pi)⁻¹ * (logDeriv g ((x0 : ℂ) + (eta : ℂ) * I)).im := by
  let z : ℂ := (x0 : ℂ) + (eta : ℂ) * I
  let p : ℂ := (x0 : ℂ) + (eta0 : ℂ) * I
  have hzne : z ≠ p := by
    intro h
    apply hne
    simpa [z, p] using congrArg Complex.im h
  have hXi : XiC z ≠ 0 := by
    rw [hfact z (by simpa [z, p] using hmem)]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzne))
      (hg0 z (by simpa [z, p] using hmem))
  have hXiLower : XiC ((x0 : ℂ) - (eta : ℂ) * I) ≠ 0 := by
    have hconj := XiC_ne_zero_conj hXi
    have hcoord : (starRingEnd ℂ) z = (x0 : ℂ) - (eta : ℂ) * I := by
      simp only [z, map_add, map_mul, conj_ofReal, conj_I]
      ring
    rwa [hcoord] at hconj
  have hsource := boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity
    heta0 hetaHalf hXiLower
  have hpole := logDeriv_XiC_eq_pole_add hgan hg0 hfact
    (by simpa [z, p] using hmem) hzne
  have hdiff : z - p = (eta - eta0 : ℝ) * I := by
    simp [z, p]
    ring
  have hpole_im :
      (((analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat : ℂ) /
          (((eta - eta0 : ℝ) : ℂ) * I)).im =
        -((analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat : ℝ) /
          (eta - eta0) := by
    simpa using
      (im_div_ofReal_mul_I
        ((analyticOrderAt XiC ((x0 : ℂ) + (eta0 : ℂ) * I)).toNat : ℝ)
        (eta - eta0))
  rw [← hsource, boundaryDensity, hpole, Complex.add_im, hdiff, hpole_im]
  ring

/-- At every positive-shift Xi zero, the source has a punctured horizontal
factorization with a positive residue that is completely absent from the
scalar source density. -/
theorem exists_criticalFeaturePositiveShiftPoleGamma_horizontal_pole_blindness
    {x0 eta : ℝ} (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hzero : XiC ((x0 : ℂ) + (eta : ℂ) * I) = 0) :
    ∃ R > 0, ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball ((x0 : ℂ) + (eta : ℂ) * I) R) ∧
      (∀ z ∈ ball ((x0 : ℂ) + (eta : ℂ) * I) R, g z ≠ 0) ∧
      0 < (analyticOrderAt XiC ((x0 : ℂ) + (eta : ℂ) * I)).toNat ∧
      ∀ {x : ℝ},
        (x : ℂ) + (eta : ℂ) * I ∈
            ball ((x0 : ℂ) + (eta : ℂ) * I) R →
        x ≠ x0 →
        criticalFeaturePositiveShiftPoleGammaDensity eta x =
          -(Real.pi)⁻¹ * (logDeriv g ((x : ℂ) + (eta : ℂ) * I)).im := by
  obtain ⟨R, hR, g, hgan, hg0, hfact⟩ :=
    XiC_peel_ball ((x0 : ℂ) + (eta : ℂ) * I)
  refine ⟨R, hR, g, hgan, hg0,
    XiC_order_toNat_pos hzero, ?_⟩
  intro x hx hne
  exact criticalFeaturePositiveShiftPoleGammaDensity_eq_cofactor_im_of_horizontal_factor
    heta0 hetaHalf hgan hg0 hfact hx hne

end

end RHTower
