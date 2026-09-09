import GaloisForLFunctions.HTGeometry.FokasLenellsHardyArcUniqueness
import GaloisForLFunctions.HTGeometry.FokasLenellsCayleyGapTransfer
import GaloisForLFunctions.RHTower.FokasLenellsHardyOrientation

/-!
# Hardy and Cauchy uniqueness on every real open gap

The exact Hardy Cayley unitary transports the unconditional circle arc law to
the original real-line Hardy subspace. Consequently no nonzero Cauchy-kernel
vector can vanish on a real interval, although the full Cauchy kernel is large.
-/

open MeasureTheory Complex Filter Topology Metric Set
open scoped ENNReal NNReal lp
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- An actual upper Hardy L² vector is determined by its trace on any positive real interval. -/
theorem upperHardyL2_gap_zero_iff (u : UpperHardyL2) (c a : ℝ) :
    (∀ᵐ x : ℝ ∂volume, dist x c < Real.exp a → u.val x = 0) ↔ u = 0 := by
  constructor
  · intro hgap
    let f : HardyDisk := hardyDiskLineCayleyUnitary.symm u
    have hu : hardyDiskLineCayleyUnitary f = u := hardyDiskLineCayleyUnitary.apply_symm_apply u
    have hc : circleLineCayleyIsometry (hardyDiskBoundary f) = I • u.val := by
      rw [circleLineCayleyIsometry_hardyDiskBoundary,hu]
    have hline : ∀ᵐ x : ℝ ∂volume,
        dist x c < Real.exp a → circleLineCayleyIsometry (hardyDiskBoundary f) x = 0 := by
      rw [hc]
      filter_upwards [hgap,Lp.coeFn_smul I u.val] with x hx hs
      intro hnear
      rw [hs,Pi.smul_apply,hx hnear,smul_zero]
    obtain ⟨b,hb⟩ := (circleLineCayleyIsometry_local_zero_iff (hardyDiskBoundary f) c).1 ⟨a,hline⟩
    have hf : f = 0 := (hardyDiskBoundary_arc_zero_iff f (circleCayley c) b).1 hb
    calc
      u = hardyDiskLineCayleyUnitary f := hu.symm
      _ = 0 := by rw [hf,map_zero]
  · rintro rfl
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    intro _
    exact hx

/-- Agreement of Hardy boundary values almost everywhere on one real interval gives global equality. -/
theorem upperHardyL2_gap_eq_iff (u v : UpperHardyL2) (c a : ℝ) :
    (∀ᵐ x : ℝ ∂volume, dist x c < Real.exp a → u.val x = v.val x) ↔ u = v := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply (upperHardyL2_gap_zero_iff (u-v) c a).1
    filter_upwards [h,Lp.coeFn_sub u.val v.val] with x hx hs
    intro hnear
    change (u.val-v.val) x = 0
    rw [hs,Pi.sub_apply,hx hnear,sub_self]
  · rintro rfl
    exact Eventually.of_forall (fun _ _ => rfl)

/-- The actual Cauchy kernel has trivial intersection with every real spectral-gap class. -/
theorem negativeCauchy_gap_kernel_iff (u : RealLineL2) (c a : ℝ) :
    ((∀ᵐ x : ℝ ∂volume, dist x c < Real.exp a → u x = 0) ∧
      RHTower.FokasLenells.negativeCauchy u = 0) ↔ u = 0 := by
  constructor
  · rintro ⟨hgap,hC⟩
    let v : UpperHardyL2 := ⟨u,(RHTower.FokasLenells.negativeCauchy_eq_zero_iff u).1 hC⟩
    have hv : v = 0 := (upperHardyL2_gap_zero_iff v c a).1 hgap
    exact congrArg Subtype.val hv
  · rintro rfl
    refine ⟨?_,map_zero _⟩
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    intro _
    exact hx

end
end GaloisForLFunctions.HTGeometry.FokasLenells
