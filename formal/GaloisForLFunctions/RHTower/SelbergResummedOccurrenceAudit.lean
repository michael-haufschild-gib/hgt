import GaloisForLFunctions.RHTower.SelbergResummedSource
import GaloisForLFunctions.RHTower.SelbergNativeConstantMode

/-!
# Full-Xi occurrence audit of the actual locally resummed source

The literal complete exponential resummation is nonzero in the original L2
space and has mean Gamma(s-1). Every actual Xi target differs from the native
constant eigenvalue one. The exact mean identity for the actual covariance
therefore gives a nonzero full source residual, with a quantitative norm bound.

The admitted source cannot be an entire eigenvector at its common scalar term
value. Applying the actual covariance constructs a nonzero entire-domain vector
whose normalized full-Xi residual is strictly positive. Exact centering isolates
the remaining source equation without asserting its solution or nonvanishing.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace
namespace RHTower.SelbergResummedOccurrenceAudit
open D4BMModularCore D4BMGlobalAngularResponse SelbergResummedSource SelbergNativeConstantMode
open SelbergScatteringEntireOperator SelbergScatteringEntireTransform SelbergScatteringEntireXiPackets
noncomputable section

/-- An actual Xi target never equals the original constant-mode eigenvalue. -/
theorem xiEntireTarget_ne_one (q : XiZeroCopy) : xiEntireTarget q ≠ 1 := by
  intro he
  have hp : casimirTransform (0:ℝ) = xiEntireTarget q := by
    rw [he]
    exact casimirTransform_zero
  have h := ((xi_real_native_preimage_iff q 0).mp hp).2
  dsimp [nativePartner] at h
  nlinarith [sq_nonneg (q.1:ℂ).im]

/-- The exact mean belongs to the original resummed native vector. -/
theorem xiVector_integral (q : XiZeroCopy) :
    (∫ z, (xiVector q) z ∂measure) = Complex.Gamma (xiParameter q-1) := by
  rw [integral_congr_ae (xiVector_coe q)]
  exact source_integral_eq_gamma _ (xiParameter_strip q).1 (xiParameter_strip q).2

/-- Complete bounded occurrence residual for the actual resummed Xi source. -/
def sourceDefect (q : XiZeroCopy) : Space := boundedDefect (xiEntireTarget q) (xiVector q)

/-- The complete residual has an explicit, non-discarded original mean. -/
theorem sourceDefect_integral (q : XiZeroCopy) :
    (∫ z, (sourceDefect q) z ∂measure) =
      ((1-xiEntireTarget q)/3)*Complex.Gamma (xiParameter q-1) := by
  rw [sourceDefect,integral_boundedDefect,xiVector_integral]

/-- Local resummation creates an admitted nonzero source but leaves a nonzero occurrence defect. -/
theorem sourceDefect_ne_zero (q : XiZeroCopy) : sourceDefect q ≠ 0 :=
  boundedDefect_ne_zero_of_integral_ne_zero _ (xiEntireTarget_ne_one q) _
    (xiVector_integral_ne_zero q)

/-- Exact quantitative lower demand on the full source residual. -/
theorem sourceDefect_norm_lower (q : XiZeroCopy) :
    ‖1-xiEntireTarget q‖*‖Complex.Gamma (xiParameter q-1)‖ ≤
      3*‖constantVector‖*‖sourceDefect q‖ := by
  simpa only [xiVector_integral,sourceDefect] using boundedDefect_norm_lower (xiEntireTarget q) (xiVector q)

/-- The admitted original vector cannot be an entire eigenvector at its shared scalar term value. -/
theorem xiVector_not_entire_eigenvector (q : XiZeroCopy) :
    ¬ ∃ x : entireOperator.domain, (x:Space)=xiVector q ∧
      entireOperator x = xiEntireTarget q • (x:Space) := by
  rintro ⟨x,hx,hT⟩
  have h := entireCovariance_apply_operator x
  rw [hT,hx,map_add,map_smul,map_smul] at h
  apply sourceDefect_ne_zero q
  unfold sourceDefect boundedDefect
  have he : (2+xiEntireTarget q) • entireCovariance (xiVector q) = xiVector q := by
    rw [add_smul,add_comm]
    exact h
  rw [he,sub_self]

/-- Applying the actual covariance constructs a source in the full native entire graph. -/
def domainSource (q : XiZeroCopy) : entireOperator.domain :=
  ⟨entireCovariance (xiVector q),entireCovariance_mem_domain _⟩

theorem domainSource_ne_zero (q : XiZeroCopy) : (domainSource q : Space) ≠ 0 := by
  intro he
  apply xiVector_ne_zero q
  apply entireCovariance_injective
  simpa [domainSource] using he

/-- The actual domain source has the same complete bounded defect as its literal operator residual. -/
theorem domainSource_operator_defect (q : XiZeroCopy) :
    entireOperator (domainSource q)-xiEntireTarget q • (domainSource q : Space) = sourceDefect q := by
  change entireOperator ⟨entireCovariance (xiVector q),entireCovariance_mem_domain _⟩ -
    xiEntireTarget q • entireCovariance (xiVector q) = _
  rw [entireOperator_apply_covariance]
  unfold sourceDefect boundedDefect
  module

/-- The actual native entire-domain source has strictly positive normalized full-Xi residual. -/
theorem domainSource_normalized_residual_pos (q : XiZeroCopy) :
    0 < ‖entireOperator (domainSource q)-xiEntireTarget q • (domainSource q : Space)‖ /
      ‖(domainSource q : Space)‖ := by
  rw [domainSource_operator_defect]
  exact div_pos (norm_pos_iff.mpr (sourceDefect_ne_zero q)) (norm_pos_iff.mpr (domainSource_ne_zero q))

/-- The survivor retains an admitted centered source with exact zero original mean. -/
theorem centered_xiVector_mean (q : XiZeroCopy) :
    (∫ z, (centered (xiVector q)) z ∂measure) = 0 := integral_centered _

/-- Exact separation of the detected obstruction from the remaining centered source equation. -/
theorem sourceDefect_decomposition (q : XiZeroCopy) :
    sourceDefect q = boundedDefect (xiEntireTarget q) (centered (xiVector q))+
      ((1-xiEntireTarget q)/3) • constantComponent (xiVector q) :=
  boundedDefect_decomposition _ _

end
end RHTower.SelbergResummedOccurrenceAudit
