import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Summability under uniformly positive reweighting

A nonnegative real family remains summable, and only remains summable, after multiplication by a
weight bounded above and bounded away from zero.  This is the common comparison interface behind
the fixed, tangent, and cubic source/value reflection apertures in `RHTower`.
-/

namespace HTGeometry

/-- Multiplication by a uniformly bounded positive weight preserves and reflects summability of a
nonnegative real family.  The index type is arbitrary, and the upper bound needs no separate sign
hypothesis. -/
theorem summable_mul_iff_of_nonneg_of_uniform_pos_le_of_le
    {ι : Type*} (f w : ι → ℝ) {c C : ℝ}
    (hf : ∀ i, 0 ≤ f i) (hc : 0 < c)
    (hlower : ∀ i, c ≤ w i) (hupper : ∀ i, w i ≤ C) :
    Summable (fun i => w i * f i) ↔ Summable f := by
  constructor
  · intro hweighted
    have hscaled : Summable (fun i => c * f i) := by
      exact Summable.of_nonneg_of_le
        (fun i => mul_nonneg hc.le (hf i))
        (fun i => mul_le_mul_of_nonneg_right (hlower i) (hf i))
        hweighted
    exact (summable_mul_left_iff hc.ne').mp hscaled
  · intro hbase
    have hmajor : Summable (fun i => C * f i) := hbase.mul_left C
    exact Summable.of_nonneg_of_le
      (fun i => mul_nonneg (le_trans hc.le (hlower i)) (hf i))
      (fun i => mul_le_mul_of_nonneg_right (hupper i) (hf i))
      hmajor

end HTGeometry
