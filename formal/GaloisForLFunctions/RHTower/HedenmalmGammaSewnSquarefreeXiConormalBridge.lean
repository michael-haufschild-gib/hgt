import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeParityLocalization
import GaloisForLFunctions.RHTower.SquarefreeFixedCurrentLocalization
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

/-!
# Squarefree reporter landing of strict-right Xi conormals

The Route N modular class is supported on the squarefree parity digit.  Its source-defined Mellin
reporter is the squarefree partition `ζ(s) / ζ(2s)`.  On `Re s > 1/2`, the doubled zeta factor is
an analytic unit.  Therefore the squarefree reporter and completed Xi have the same zero germ and
the same full analytic order at every strict-right Xi point.

This closes algebraic principal-conormal and multiplicity landing into the squarefree reporter.
It does not prove that the resulting germ is normal/nonexpansive in the exceptional critical
completion; that strict topological statement remains the RH-bearing producer.
-/

open Complex

namespace RHTower

noncomputable section

/-- Analytic unit converting the zeta germ to the squarefree Mellin reporter. -/
def routeNSquarefreeReporterUnit (s : ℂ) : ℂ :=
  (riemannZeta (2 * s))⁻¹

theorem routeNSquarefreeReporterUnit_ne_zero
    {s : ℂ} (hs : 1 / 2 < s.re) :
    routeNSquarefreeReporterUnit s ≠ 0 := by
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  exact inv_ne_zero (riemannZeta_ne_zero_of_one_lt_re h2re)

theorem analyticAt_routeNSquarefreeReporterUnit
    {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ routeNSquarefreeReporterUnit s := by
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have h2one : 2 * s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, one_re] at hre
    linarith
  have hden : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s :=
    (analyticOn_riemannZeta (2 * s) h2one).comp
      (show AnalyticAt ℂ (fun z : ℂ => 2 * z) s by fun_prop)
  exact hden.inv (riemannZeta_ne_zero_of_one_lt_re h2re)

/-- Global factorization of the squarefree reporter by its strict-right analytic unit. -/
theorem squarefreePartition_eq_riemannZeta_mul_routeNReporterUnit
    (s : ℂ) :
    GaloisForLFunctions.squarefreePartition s =
      riemannZeta s * routeNSquarefreeReporterUnit s := by
  rw [GaloisForLFunctions.squarefreePartition, routeNSquarefreeReporterUnit,
    div_eq_mul_inv]

theorem analyticAt_squarefreePartition_of_half_lt_re
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ GaloisForLFunctions.squarefreePartition s := by
  change AnalyticAt ℂ
    (fun z : ℂ => riemannZeta z * routeNSquarefreeReporterUnit z) s
  exact (analyticOn_riemannZeta s hs1).mul
    (analyticAt_routeNSquarefreeReporterUnit hs)

/-- Division by `ζ(2s)` preserves the complete analytic zero order, hence every squarefree
principal conormal multiplicity jet, throughout the strict-right half-plane. -/
theorem analyticOrderAt_squarefreePartition_eq_riemannZeta
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt GaloisForLFunctions.squarefreePartition s =
      analyticOrderAt riemannZeta s := by
  have hzeta : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hunit : AnalyticAt ℂ routeNSquarefreeReporterUnit s :=
    analyticAt_routeNSquarefreeReporterUnit hs
  rw [show GaloisForLFunctions.squarefreePartition =
      riemannZeta * routeNSquarefreeReporterUnit by
        funext z
        exact squarefreePartition_eq_riemannZeta_mul_routeNReporterUnit z,
    analyticOrderAt_mul hzeta hunit,
    hunit.analyticOrderAt_eq_zero.mpr (routeNSquarefreeReporterUnit_ne_zero hs),
    add_zero]

/-- **Strict-right Xi conormal landing.**  The squarefree Mellin reporter and completed Xi carry
the same complete zero order at every point of the strict-right open critical half-strip. -/
theorem analyticOrderAt_squarefreePartition_eq_xi_of_strictRightStrip
    {ρ : ℂ} (hρhalf : 1 / 2 < ρ.re) (hρone : ρ.re < 1) :
    analyticOrderAt GaloisForLFunctions.squarefreePartition ρ =
      analyticOrderAt xi ρ := by
  have hρ0 : 0 < ρ.re := by linarith
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at hρone
    norm_num at hρone
  rw [analyticOrderAt_squarefreePartition_eq_riemannZeta hρhalf hρ1,
    ← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρ0, hρone⟩]

/-- The distinguished squarefree reporter has exactly the Xi divisor on the strict-right strip,
before any zero is selected. -/
theorem squarefreePartition_eq_zero_iff_xi_eq_zero_of_strictRightStrip
    {ρ : ℂ} (hρhalf : 1 / 2 < ρ.re) (hρone : ρ.re < 1) :
    GaloisForLFunctions.squarefreePartition ρ = 0 ↔ xi ρ = 0 := by
  rw [GaloisForLFunctions.squarefreePartition_eq_zero_iff_riemannZeta_eq_zero hρhalf]
  exact (xi_zero_iff_zeta_zero_of_mem_strip (by linarith) hρone).symm

end

end RHTower
