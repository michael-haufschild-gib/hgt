import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Instances.Rat

/-!
# Rational points avoiding a finite exceptional set

This module packages the elementary density argument used when an analytic construction has only
finitely many bad real parameters.  The witness retains its rational provenance explicitly.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- Every nonempty real open interval contains a rational point outside any prescribed finite set. -/
theorem exists_ratCast_mem_Ioo_not_mem_finset {a b : ℝ} (hab : a < b)
    (F : Finset ℝ) :
    ∃ x ∈ Set.Ioo a b, x ∉ F ∧ ∃ q : ℚ, x = (q : ℝ) := by
  let U : Set ℝ := Set.Ioo a b \ (F : Set ℝ)
  have hIoo : IsOpen (Set.Ioo a b) := _root_.isOpen_Ioo
  have hUopen : IsOpen U := IsOpen.sdiff hIoo F.finite_toSet.isClosed
  have hUinfinite : U.Infinite := (Set.Ioo_infinite hab).sdiff F.finite_toSet
  have hUne : U.Nonempty := hUinfinite.nonempty
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hUopen hUne
  refine ⟨(q : ℝ), hq.1, ?_, q, rfl⟩
  simpa using hq.2

end GaloisForLFunctions.HTGeometry
