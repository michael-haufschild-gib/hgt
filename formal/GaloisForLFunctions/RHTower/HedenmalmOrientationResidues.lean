import GaloisForLFunctions.RHTower.HedenmalmInfiniteOrientationSingularities

/-!
# Exact residue germs at forced Hedenmalm orientation singularities

At a translated-divisor boundary zero `rho`, the canonical orientation multiplier has a
nonremovable singularity.  This module constructs its removable residue germ explicitly.  In the
affine Hedenmalm frequency coordinate, the germ value is

`-I * analyticOrderAt xi rho`.

Thus every forced singular frequency carries the exact Xi multiplicity rather than merely the
support of the divisor.  The statements use punctured-neighborhood equality and an analytic germ,
so no informal meromorphic-residue convention is hidden in the interface.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

def xiFluxShiftDifferenceResidueGerm (h : ℝ) (ρ x : ℂ) : ℂ :=
  completedFluxGermAt ρ x -
    x * seamFluxCochain ((ρ + x) - (h : ℂ))

theorem analyticAt_xiFluxShiftDifferenceResidueGerm
    {h : ℝ} {ρ : ℂ} (hshift : xi (ρ - (h : ℂ)) ≠ 0) :
    AnalyticAt ℂ (xiFluxShiftDifferenceResidueGerm h ρ) 0 := by
  have hshiftAn : AnalyticAt ℂ seamFluxCochain (ρ - (h : ℂ)) := by
    have hxi : AnalyticAt ℂ xi (ρ - (h : ℂ)) :=
      xi_analyticOnNhd_univ _ (Set.mem_univ _)
    change AnalyticAt ℂ (fun z => -logDeriv xi z) (ρ - (h : ℂ))
    exact (hxi.deriv.div hxi hshift).neg
  have hshiftComp : AnalyticAt ℂ
      (fun x : ℂ => seamFluxCochain ((ρ + x) - (h : ℂ))) 0 := by
    apply AnalyticAt.comp_of_eq hshiftAn
    · fun_prop
    · ring
  exact (completedFluxGermAt_analyticAt_zero ρ).sub
    (analyticAt_id.mul hshiftComp)

theorem xiFluxShiftDifferenceResidueGerm_zero (h : ℝ) (ρ : ℂ) :
    xiFluxShiftDifferenceResidueGerm h ρ 0 =
      -((analyticOrderAt xi ρ).toNat : ℂ) := by
  rw [xiFluxShiftDifferenceResidueGerm, completedFluxGermAt_zero,
    zero_mul, sub_zero]

theorem xiFluxShiftDifferenceResidueGerm_eventuallyEq
    (h : ℝ) (ρ : ℂ) :
    xiFluxShiftDifferenceResidueGerm h ρ =ᶠ[𝓝[≠] 0]
      fun x : ℂ => x * xiFluxShiftDifference h (ρ + x) := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  rw [xiFluxShiftDifferenceResidueGerm, completedFluxGermAt,
    if_neg hx0, xiFluxShiftDifference]
  ring

def xiCanonicalOrientationBoundaryResidueGerm
    (a : ℝ) (ρ x : ℂ) : ℂ :=
  I * xiFluxShiftDifferenceResidueGerm (2 * a) ρ x

theorem analyticAt_xiCanonicalOrientationBoundaryResidueGerm
    {a : ℝ} {ρ : ℂ} (hρ : ρ ∈ xiLeftShiftBoundary (2 * a)) :
    AnalyticAt ℂ (xiCanonicalOrientationBoundaryResidueGerm a ρ) 0 := by
  exact analyticAt_const.mul
    (analyticAt_xiFluxShiftDifferenceResidueGerm hρ.2)

theorem xiCanonicalOrientationBoundaryResidueGerm_zero
    (a : ℝ) (ρ : ℂ) :
    xiCanonicalOrientationBoundaryResidueGerm a ρ 0 =
      -I * ((analyticOrderAt xi ρ).toNat : ℂ) := by
  rw [xiCanonicalOrientationBoundaryResidueGerm,
    xiFluxShiftDifferenceResidueGerm_zero]
  ring

theorem xiCanonicalOrientationBoundaryResidueGerm_eventuallyEq
    (a : ℝ) (ρ : ℂ) :
    xiCanonicalOrientationBoundaryResidueGerm a ρ =ᶠ[𝓝[≠] 0]
      fun x : ℂ =>
        (xiOrientationFrequencyOfPoint a (ρ + x) -
          xiOrientationFrequencyOfPoint a ρ) *
            xiCanonicalHorizontalOrientationMultiplier a
              (xiOrientationFrequencyOfPoint a (ρ + x)) := by
  filter_upwards
    [xiFluxShiftDifferenceResidueGerm_eventuallyEq (2 * a) ρ,
      self_mem_nhdsWithin] with x hx hxmem
  rw [xiCanonicalOrientationBoundaryResidueGerm, hx,
    xiFluxShiftDifference_eq_neg_canonicalOrientation]
  have hfreq : xiOrientationFrequencyOfPoint a (ρ + x) -
      xiOrientationFrequencyOfPoint a ρ = -I * x := by
    unfold xiOrientationFrequencyOfPoint
    ring
  rw [hfreq]
  ring

theorem xiCanonicalOrientationBoundary_residue_ne_zero
    {a : ℝ} {ρ : ℂ} (hρ : ρ ∈ xiLeftShiftBoundary (2 * a)) :
    xiCanonicalOrientationBoundaryResidueGerm a ρ 0 ≠ 0 := by
  rw [xiCanonicalOrientationBoundaryResidueGerm_zero]
  exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
    (Nat.cast_ne_zero.mpr (xi_order_toNat_ne_zero hρ.1))

end

end RHTower
