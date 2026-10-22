import GaloisForLFunctions.HTGeometry.IndexedBlaschkeIsometry
import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiInfiniteBlaschkeDenominator

/-!
# Hardy isometry of the shifted-Xi pole Blaschke denominator

The literal denominator over all strict-right shifted-Xi pole copies satisfies the indexed
Blaschke condition already proved for the actual Xi divisor.  Therefore multiplication by this
infinite product preserves the `H²(D)` norm.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The literal infinite shifted-Xi pole denominator acts isometrically on `H²(D)`. -/
theorem xiShiftPoleBlaschkeMultiplier_isometry
    {omega : ℝ} (homega : 0 ≤ omega) :
    HardyMultiplierIsometry (xiShiftPoleBlaschkeMultiplier homega) := by
  exact indexedBlaschkeMultiplier_isometry
    (xiShiftPoleDiskCoordinate omega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega)
    (summable_one_sub_norm_xiShiftPoleDiskCoordinate homega)

end

end RHTower
