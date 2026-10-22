import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiInfiniteLeakageRank
import GaloisForLFunctions.HTGeometry.ModelSpaceLeakageNorm

open GaloisForLFunctions.HTGeometry
open Filter Topology

namespace RHTower

noncomputable section

@[simp]
theorem xiShiftInfiniteSchurNumerator_bd
    {omega : ℝ} (homega : 0 ≤ omega) :
    (xiShiftInfiniteSchurNumerator homega).bd = 1 := by
  change 1 * 1 = 1
  norm_num

/-- The literal full-divisor shifted-Xi projected leakage is contractive. -/
theorem norm_xiShiftInfiniteLeakageCore_le_one
    {omega : ℝ} (homega : 0 ≤ omega) :
    ‖xiShiftInfiniteLeakageCore homega‖ ≤ 1 := by
  simpa [xiShiftInfiniteLeakageCore] using
    norm_modelSpaceLeakageCore_le_bd
      (xiShiftInfiniteSchurNumerator homega)
      (xiShiftPoleBlaschkeMultiplier homega)

/-- At every literal denominator zero, numerator modulus lower-bounds the full-divisor projected
leakage norm. -/
theorem norm_xiShiftInfiniteSchurNumerator_pole_le_leakage
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega) :
    ‖(xiShiftInfiniteSchurNumerator homega).fn
        (xiShiftPoleDiskCoordinate omega q)‖ ≤
      ‖xiShiftInfiniteLeakageCore homega‖ := by
  simpa [xiShiftInfiniteLeakageCore] using
    norm_apply_le_norm_modelSpaceLeakageCore_of_zero
      (xiShiftInfiniteSchurNumerator homega)
      (xiShiftPoleBlaschkeMultiplier homega)
      (norm_xiShiftPoleDiskCoordinate_lt_one omega q)
      (xiShiftPoleBlaschkeMultiplier_apply_zero homega q)

/-- If one crossing numerator value tends to unit modulus, the literal shifted-Xi projected
leakage norm tends to one.  This is the exact operator squeeze used by the isolated-layer law. -/
theorem tendsto_norm_xiShiftInfiniteLeakageCore_one_of_poleValue
    {ι : Type*} {l : Filter ι} (omega : ι → ℝ)
    (homega : ∀ i, 0 ≤ omega i)
    (q : ∀ i, XiShiftRightZeroCopy (omega i))
    (hnum : Filter.Tendsto (fun i =>
      ‖(xiShiftInfiniteSchurNumerator (homega i)).fn
        (xiShiftPoleDiskCoordinate (omega i) (q i))‖) l (𝓝 1)) :
    Filter.Tendsto (fun i =>
      ‖xiShiftInfiniteLeakageCore (homega i)‖) l (𝓝 1) := by
  exact hnum.squeeze tendsto_const_nhds
    (fun i => norm_xiShiftInfiniteSchurNumerator_pole_le_leakage
      (homega i) (q i))
    (fun i => norm_xiShiftInfiniteLeakageCore_le_one (homega i))

end

end RHTower
