import GaloisForLFunctions.HTGeometry.Critical.Sheet.JetUnit
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Schur.JacobianDivisor

/-!
# The source scale is a unit at every sheet

The Schur coordinates normalise the raw coefficients by the zeroth one, `criticalSourceScale`.  For
the argument that two colliding sheets cut out the same place, that division has to stay inside the
upper Schur valuation ring — for *every* sheet.

```text
coe_criticalSheetJetCoeffZero   the jet's zeroth coefficient IS the sheet's value on the scale
criticalSheetScale_mem          so the scale lands in the valuation ring
isUnit_criticalSheetScale       ** and it is a UNIT there **
```

The unit comes from `CriticalSheetJetUnit`: the fibre equation reads `A(0)·B(0) = 1` in whatever
ring the fibre point lives, and the sheet's fibre point lives in the valuation ring.  No integrality
over the observation DVR is needed — and none is available.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ}

/-- The zeroth coefficient of a sheet's jet is the sheet's value on the source scale. -/
theorem coe_criticalSheetJetCoeffZero (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) :
    (((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff 0 :
        criticalNormalClosureSchurValuationSubring K (by omega) (by omega)) :
      criticalNormalClosure K m n)
      = σ (criticalSourceScale K (by omega : 0 < m) (by omega : 0 < n)) := by
  have hmap := criticalFibreMap_criticalGeometricSheetToSchurFibre K hm hn σ
  have h1 : ((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.map
        (criticalNormalClosureSchurValuationSubring K (by omega : 0 < m)
          (by omega : 0 < n)).subtype).coeff 0
      = (criticalGeometricSheetToSchurFieldFibre K (by omega : 0 < m)
          (by omega : 0 < n) σ).1.1.coeff 0 :=
    congrArg (fun p => p.1.1.coeff 0) hmap
  rw [Polynomial.coeff_map] at h1
  refine h1.trans ?_
  show ((criticalSourceRawLow K m n).map σ.toRingHom).coeff 0 = _
  rw [Polynomial.coeff_map, criticalSourceRawLow, lowPolynomial_coeff, dif_pos (by omega : 0 < m)]
  rfl

/-- Every sheet sends the source scale into the upper Schur valuation ring. -/
theorem criticalSheetScale_mem (hm : 1 < m) (hn : 1 < n) (σ : criticalGeometricSheet K m n) :
    σ (criticalSourceScale K (by omega : 0 < m) (by omega : 0 < n))
      ∈ criticalNormalClosureSchurValuationSubring K (by omega : 0 < m) (by omega : 0 < n) := by
  rw [← coe_criticalSheetJetCoeffZero K hm hn σ]
  exact ((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff 0).property

/-- **Every sheet sends the source scale to a UNIT of the upper Schur valuation ring.**  This is
what makes the Schur normalisation legitimate sheet by sheet. -/
theorem isUnit_criticalSheetScale (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) :
    IsUnit ((⟨σ (criticalSourceScale K (by omega : 0 < m) (by omega : 0 < n)),
      criticalSheetScale_mem K hm hn σ⟩ :
        criticalNormalClosureSchurValuationSubring K (by omega : 0 < m) (by omega : 0 < n))) := by
  have hcoe : (⟨σ (criticalSourceScale K (by omega : 0 < m) (by omega : 0 < n)),
      criticalSheetScale_mem K hm hn σ⟩ :
        criticalNormalClosureSchurValuationSubring K (by omega : 0 < m) (by omega : 0 < n))
      = (criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff 0 :=
    Subtype.ext (coe_criticalSheetJetCoeffZero K hm hn σ).symm
  rw [hcoe]
  exact isUnit_criticalSheetJetCoeffZero K hm hn σ

end

end GaloisForLFunctions.HTGeometry
