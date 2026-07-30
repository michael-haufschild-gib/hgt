import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# Pointed analytic-moment determinacy for the Hedenmalm--de Branges seam

An abstract all-order moment sequence need not determine its representing measure.  The fixed
prime--archimedean moment carrier used here has additional structure: it is an analytic germ with
an exact odd lift to the continued Euler--Gamma trace.  Its complete Taylor jet therefore
determines that analytic germ, and the source differential identity reconstructs the local
Hedenmalm--de Branges function and its off-diagonal Bezoutian.

This is unconditional source-rigidity infrastructure.  It proves no positivity statement for the
Bezoutian and therefore does not prove RH.
-/

open Complex Set Filter Function FormalMultilinearSeries
open scoped Topology

noncomputable section

namespace RHTower

/-- A homogeneous first-order analytic constraint has no nonzero local solution vanishing at the
base point.  This is the analytic uniqueness mechanism used below. -/
theorem analyticAt_eventuallyEq_zero_of_deriv_eq_mul
    {h a : ℂ → ℂ} {z : ℂ}
    (hh : AnalyticAt ℂ h z) (ha : AnalyticAt ℂ a z)
    (hode : deriv h =ᶠ[𝓝 z] fun w => a w * h w)
    (hz : h z = 0) :
    h =ᶠ[𝓝 z] 0 := by
  by_cases htop : analyticOrderAt h z = ⊤
  · exact analyticOrderAt_eq_top.mp htop
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  have hm0 : m ≠ 0 := by
    intro hmzero
    have hord0 : analyticOrderAt h z = 0 := by simpa [hmzero] using hm.symm
    exact (hh.analyticOrderAt_eq_zero.mp hord0) hz
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hm' : analyticOrderAt h z = ((n + 1 : ℕ) : ℕ∞) := by
    simpa using hm.symm
  have hderord : analyticOrderAt (deriv h) z = n :=
    analyticOrderAt_deriv_of_pos hh hm'
  have hmulord : analyticOrderAt (fun w => a w * h w) z =
      analyticOrderAt a z + analyticOrderAt h z := by
    simpa only [Pi.mul_apply] using! analyticOrderAt_mul ha hh
  have hordEq : analyticOrderAt (deriv h) z =
      analyticOrderAt (fun w => a w * h w) z :=
    analyticOrderAt_congr hode
  rw [hderord, hmulord, hm'] at hordEq
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
    rw [hordEq]
    exact le_add_self
  have : n + 1 ≤ n := by exact_mod_cast hle
  omega

/-- The distinguished continued Euler--Gamma trace is exactly the odd analytic lift of its
normalized moment germ.  This is a global identity, not merely an equality of formal jets. -/
theorem oddTracePreimage_normalizedPrimeArchMomentGerm_eq_source :
    oddTracePreimage normalizedPrimeArchMomentGerm =
      continuedPrimeArchSourceRelativeTrace := by
  exact oddTracePreimage_normalizedTraceMomentGerm_eq
    continuedPrimeArchSourceRelativeTrace continuedPrimeArchSourceRelativeTrace_zero

/-- The complete Taylor jet of the normalized prime--archimedean moment germ is determinate inside
the analytic-germ category. -/
theorem normalizedPrimeArchMomentGerm_allOrder_determinate
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hjet : ∀ n : ℕ,
      iteratedDeriv n g 0 = iteratedDeriv n normalizedPrimeArchMomentGerm 0) :
    g =ᶠ[𝓝 0] normalizedPrimeArchMomentGerm := by
  apply analyticAt_eventuallyEq_of_iteratedDeriv_eq hg
  · simpa only [normalizedPrimeArchMomentGerm] using
      analyticAt_normalizedTraceMomentGerm_continuedPrimeArchSource
  · exact hjet

/-- Any analytic germ with the complete prime--archimedean moment jet has the distinguished
Euler--Gamma trace as its odd lift.  This is the nonflat marking absent from an unpointed
indeterminate moment fiber. -/
theorem normalizedPrimeArchMomentGerm_allOrder_determines_sourceTrace
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hjet : ∀ n : ℕ,
      iteratedDeriv n g 0 = iteratedDeriv n normalizedPrimeArchMomentGerm 0) :
    oddTracePreimage g =ᶠ[𝓝 0] continuedPrimeArchSourceRelativeTrace := by
  have heq := normalizedPrimeArchMomentGerm_allOrder_determinate hg hjet
  have hlift : oddTracePreimage g =ᶠ[𝓝 0]
      oddTracePreimage normalizedPrimeArchMomentGerm := by
    filter_upwards [heq] with z hz
    simp only [oddTracePreimage, hz]
  exact hlift.trans (Filter.Eventually.of_forall fun z =>
    congrFun oddTracePreimage_normalizedPrimeArchMomentGerm_eq_source z)

/-- The pointed moment flux whose odd lift is the continued Euler--Gamma trace. -/
def xiHedenmalmPointedMomentFlux (z : ℂ) : ℂ :=
  z * normalizedPrimeArchMomentGerm z

/-- Exact source recovery from the pointed analytic moment germ. -/
theorem continuedPrimeArchSourceRelativeTrace_eq_neg_pointedMomentFlux (z : ℂ) :
    continuedPrimeArchSourceRelativeTrace z =
      -xiHedenmalmPointedMomentFlux z := by
  have h := congrFun oddTracePreimage_normalizedPrimeArchMomentGerm_eq_source z
  rw [← h]
  simp only [oddTracePreimage, xiHedenmalmPointedMomentFlux]
  ring

/-- Near the functional-equation center, the theta trace solves the first-order constraint fixed
by the pointed prime--archimedean moment germ. -/
theorem deriv_XiC_eventuallyEq_neg_pointedMomentFlux_mul :
    deriv XiC =ᶠ[𝓝 0]
      fun z => -xiHedenmalmPointedMomentFlux z * XiC z := by
  filter_upwards [normalizedPrimeArch_differential_identity] with z hz
  change deriv XiC z +
    xiHedenmalmPointedMomentFlux z * XiC z = 0 at hz
  linear_combination hz

/-- The pointed moment germ and the central theta normalization determine `XiC` globally among
entire solutions of the local source constraint. -/
theorem XiC_unique_entire_solution_of_pointedMomentConstraint
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ)
    (hF0 : F 0 = XiC 0)
    (hconstraint : deriv F =ᶠ[𝓝 0]
      fun z => -xiHedenmalmPointedMomentFlux z * F z) :
    F = XiC := by
  have hXi : AnalyticOnNhd ℂ XiC Set.univ := XiC_analytic
  have hdiff : AnalyticAt ℂ (F - XiC) 0 :=
    (hF 0 (Set.mem_univ 0)).sub (hXi 0 (Set.mem_univ 0))
  have hflux : AnalyticAt ℂ (fun z => -xiHedenmalmPointedMomentFlux z) 0 := by
    have hG : AnalyticAt ℂ normalizedPrimeArchMomentGerm 0 := by
      simpa only [normalizedPrimeArchMomentGerm] using
        analyticAt_normalizedTraceMomentGerm_continuedPrimeArchSource
    exact (analyticAt_id.mul hG).neg
  have hdiffConstraint : deriv (F - XiC) =ᶠ[𝓝 0]
      fun z => -xiHedenmalmPointedMomentFlux z * (F - XiC) z := by
    have hFdiff : Differentiable ℂ F :=
      analyticOnNhd_univ_iff_differentiable.mp hF
    filter_upwards [hconstraint,
      deriv_XiC_eventuallyEq_neg_pointedMomentFlux_mul] with z hFz hXiz
    rw [deriv_sub hFdiff.differentiableAt XiC_differentiable.differentiableAt,
      hFz, hXiz]
    simp only [Pi.sub_apply]
    ring
  have hdiff0 : (F - XiC) 0 = 0 := by simp [hF0]
  have hlocalZero := analyticAt_eventuallyEq_zero_of_deriv_eq_mul
    hdiff hflux hdiffConstraint hdiff0
  have hlocal : F =ᶠ[𝓝 0] XiC := by
    filter_upwards [hlocalZero] with z hz
    exact sub_eq_zero.mp hz
  exact hF.eq_of_eventuallyEq hXi hlocal

/-- The Hedenmalm--de Branges candidate written directly in the pointed analytic moment
coordinate. -/
def xiHedenmalmPointedMomentE (z : ℂ) : ℂ :=
  XiC z * (1 - I * xiHedenmalmPointedMomentFlux z)

/-- The pointed moment germ reconstructs the local Hedenmalm--de Branges candidate. -/
theorem xiHedenmalmDeBrangesE_eventuallyEq_pointedMomentE :
    xiHedenmalmDeBrangesE =ᶠ[𝓝 0] xiHedenmalmPointedMomentE := by
  filter_upwards [deriv_XiC_eventuallyEq_neg_pointedMomentFlux_mul] with z hz
  rw [xiHedenmalmDeBrangesE, xiHedenmalmPointedMomentE, hz]
  ring

/-- Removable pointed-moment form of the Xi derivative Bezoutian. -/
def xiHedenmalmPointedMomentBezoutian (z v : ℂ) : ℂ :=
  XiC z * XiC v * dslope xiHedenmalmPointedMomentFlux z v

/-- Off the diagonal, the Xi Bezoutian is reconstructed from the pointed moment germ whenever the
local source differential constraint holds at both nodes. -/
theorem xiHedenmalmBezoutian_eq_pointedMomentBezoutian_of_deriv_eq
    {z v : ℂ} (hvz : v ≠ z)
    (hz : deriv XiC z = -xiHedenmalmPointedMomentFlux z * XiC z)
    (hv : deriv XiC v = -xiHedenmalmPointedMomentFlux v * XiC v) :
    xiHedenmalmBezoutian z v = xiHedenmalmPointedMomentBezoutian z v := by
  rw [xiHedenmalmBezoutian_eq_div hvz, xiHedenmalmPointedMomentBezoutian,
    dslope_of_ne _ hvz, slope_def_module, hz, hv]
  simp only [smul_eq_mul]
  ring

/-- Unconditionally, every sufficiently central off-diagonal node pair has its Hedenmalm--de
Branges Bezoutian reconstructed by the pointed analytic moment germ. -/
theorem xiHedenmalmBezoutian_eventuallyEq_pointedMomentBezoutian_offDiagonal :
    ∀ᶠ z in 𝓝 0, ∀ᶠ v in 𝓝 0, v ≠ z →
      xiHedenmalmBezoutian z v = xiHedenmalmPointedMomentBezoutian z v := by
  filter_upwards [deriv_XiC_eventuallyEq_neg_pointedMomentFlux_mul] with z hz
  filter_upwards [deriv_XiC_eventuallyEq_neg_pointedMomentFlux_mul] with v hv
  intro hvz
  exact xiHedenmalmBezoutian_eq_pointedMomentBezoutian_of_deriv_eq hvz hz hv

end RHTower
