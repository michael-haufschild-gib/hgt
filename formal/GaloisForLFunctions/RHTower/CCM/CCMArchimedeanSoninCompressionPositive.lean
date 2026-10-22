import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanScalingStar
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positivity of the archimedean Sonin compression

This is the unconditional operator-level content behind Connes--Consani's statement that
rho(g) S rho(g)† is positive by construction. Trace-class and trace-formula identifications
are deliberately separate analytic obligations.
-/

open Complex Real MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Source Sonin projection at phase-space cutoff one. -/
def ccmArchimedeanSoninProjection : evenSubspace →L[ℂ] evenSubspace :=
  evenCentralSoninProjection 1

theorem ccmArchimedeanSoninProjection_eq_starProjection :
    ccmArchimedeanSoninProjection =
      (evenCentralSoninCarrier 1).starProjection := by
  exact evenCentralSoninProjection_eq_starProjection 1

theorem adjoint_ccmArchimedeanSoninProjection :
    ContinuousLinearMap.adjoint ccmArchimedeanSoninProjection =
      ccmArchimedeanSoninProjection := by
  rw [ccmArchimedeanSoninProjection_eq_starProjection]
  exact (isStarProjection_starProjection
    (U := evenCentralSoninCarrier 1)).2.star_eq

theorem ccmArchimedeanSoninProjection_isPositive :
    ccmArchimedeanSoninProjection.IsPositive := by
  rw [ccmArchimedeanSoninProjection_eq_starProjection,
    ContinuousLinearMap.isPositive_def']
  constructor
  · exact isSelfAdjoint_starProjection (evenCentralSoninCarrier 1)
  · intro x
    exact (evenCentralSoninCarrier 1).re_inner_starProjection_nonneg x

/-- Positive Sonin-compressed Gram operator rho(g) S rho(g)†. -/
def ccmArchimedeanSoninGram (g : CCMLogKernel) :
    evenSubspace →L[ℂ] evenSubspace :=
  ccmIntegratedScaling g ∘L ccmArchimedeanSoninProjection ∘L
    ContinuousLinearMap.adjoint (ccmIntegratedScaling g)

theorem ccmArchimedeanSoninGram_eq_starKernel (g : CCMLogKernel) :
    ccmArchimedeanSoninGram g =
      ccmIntegratedScaling g ∘L ccmArchimedeanSoninProjection ∘L
        ccmIntegratedScaling (ccmLogKernelStar g) := by
  rw [ccmArchimedeanSoninGram, adjoint_ccmIntegratedScaling]

/-- Source compression is a positive operator for every intrinsic L¹ kernel. -/
theorem ccmArchimedeanSoninGram_isPositive (g : CCMLogKernel) :
    (ccmArchimedeanSoninGram g).IsPositive := by
  exact ccmArchimedeanSoninProjection_isPositive.conj_adjoint
    (ccmIntegratedScaling g)

theorem reApplyInnerSelf_ccmArchimedeanSoninGram_nonneg
    (g : CCMLogKernel) (x : evenSubspace) :
    0 ≤ (ccmArchimedeanSoninGram g).reApplyInnerSelf x :=
  (ccmArchimedeanSoninGram_isPositive g).2 x

end RHTower
