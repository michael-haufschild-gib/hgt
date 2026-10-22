import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspPeriodization
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOperatorCore
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
Smooth compact height profiles are constructed as actual modular fields and admitted to the original unbounded operator domain.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- A smooth compact height profile entirely inside the actual modular cusp. -/
structure CuspHeightTest where
  field : ℝ → ℂ
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field
  support : tsupport field ⊆ Ioi 2

theorem CuspHeightTest.zero_low (h : CuspHeightTest) {y : ℝ} (hy : y ≤ 2) : h.field y = 0 :=
  image_eq_zero_of_notMem_tsupport (fun hm => (not_lt_of_ge hy) (h.support hm))

/-- The actual compact planar generator whose full modular periodization produces the profile. -/
def CuspHeightTest.planarField (h : CuspHeightTest) (z : ℂ) : ℂ :=
  (cuspWindow z.re : ℂ)*h.field z.im

theorem CuspHeightTest.planarField_smooth (h : CuspHeightTest) :
    ContDiff ℝ ∞ h.planarField :=
  (Complex.ofRealCLM.contDiff.comp (cuspWindow_smooth.comp Complex.reCLM.contDiff)).mul
    (h.smooth.comp Complex.imCLM.contDiff)

private theorem CuspHeightTest.planarField_support (h : CuspHeightTest) :
    tsupport h.planarField ⊆ {z : ℂ | z.re ∈ Icc (-1) 1 ∧ z.im ∈ tsupport h.field} := by
  apply closure_minimal _ (isClosed_Icc.reProdIm isClosed_closure)
  intro z hz
  have hl : cuspWindow z.re ≠ 0 := by
    intro he
    exact hz (by simp [CuspHeightTest.planarField,he])
  have hr : h.field z.im ≠ 0 := by
    intro he
    exact hz (by simp [CuspHeightTest.planarField,he])
  exact ⟨cuspWindow_support (subset_tsupport _ hl),subset_tsupport _ hr⟩

def CuspHeightTest.planarTest (h : CuspHeightTest) : PlanarChartTest where
  field := h.planarField
  smooth := h.planarField_smooth
  compact := (isCompact_Icc.reProdIm h.compact).of_isClosed_subset isClosed_closure
    h.planarField_support
  support := by
    intro z hz
    have hh := h.support (h.planarField_support hz).2
    change 2 < z.im at hh
    change 0 < z.im
    linarith

/-- The constructed globally smooth modular field with the prescribed full cusp profile. -/
def CuspHeightTest.modularField (h : CuspHeightTest) : UpperHalfPlane → ℂ :=
  periodize h.planarTest.toChartTest.field

theorem CuspHeightTest.modularField_eq (h : CuspHeightTest) (z : UpperHalfPlane) (hz : z ∈ fd) :
    h.modularField z = h.field z.im :=
  periodize_cuspWindow h.field (fun _ hy => h.zero_low hy) z hz

/-- The cusp profile is admitted to the actual completed energy space and
the original unbounded operator, without an operator-domain assumption. -/
def CuspHeightTest.operatorVector (h : CuspHeightTest) : energyOperator.domain :=
  ⟨embedding h.planarTest.toChartTest.energyTest,h.planarTest.mem_energyOperator_domain⟩

theorem CuspHeightTest.operatorVector_coe (h : CuspHeightTest) :
    ((h.operatorVector : Space) : UpperHalfPlane → ℂ) =ᵐ[measure] (fun z => h.field z.im) := by
  filter_upwards [h.planarTest.toChartTest.energyTest_scalar,
    ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z he hz
  exact he.trans (h.modularField_eq z hz)

end
end RHTower.D4BMModularCore
