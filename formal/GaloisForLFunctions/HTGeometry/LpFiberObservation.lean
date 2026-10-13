import GaloisForLFunctions.HTGeometry.LpFiberSolidHull
import GaloisForLFunctions.HTGeometry.CompactUniformStrongSet
import Mathlib.Topology.Order.Compact

/-! # Attained full-channel observations under bounded strong convergence

The complete norm-dominated fiber hull supplies an attained largest response.
Bounded strong convergence is uniform over this actual compact history family.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology
variable {I A Y : Type*} {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] {l : Filter A}

def lpFiberObservation (T : lp E 2 →L[ℂ] Y) (x : lp E 2) : ℝ :=
  sSup ((fun y => ‖T y‖) '' lpFiberSolidHull x)

variable [∀ i, ProperSpace (E i)]

theorem lpFiberObservation_attained (T : lp E 2 →L[ℂ] Y) (x : lp E 2) :
    ∃ y ∈ lpFiberSolidHull x, ‖T y‖ = lpFiberObservation T x :=
  ((isCompact_lpFiberSolidHull x).image T.continuous.norm).sSup_mem
    ((show (lpFiberSolidHull x).Nonempty from ⟨0, zero_mem_lpFiberSolidHull x⟩).image _)

theorem lpFiberObservation_nonneg (T : lp E 2 →L[ℂ] Y) (x : lp E 2) :
    0 ≤ lpFiberObservation T x := by
  obtain ⟨y, _, hy⟩ := lpFiberObservation_attained T x
  rw [← hy]
  exact norm_nonneg _

theorem norm_apply_le_lpFiberObservation (T : lp E 2 →L[ℂ] Y)
    {x y : lp E 2} (hy : y ∈ lpFiberSolidHull x) : ‖T y‖ ≤ lpFiberObservation T x :=
  le_csSup ((isCompact_lpFiberSolidHull x).image T.continuous.norm).bddAbove ⟨y, hy, rfl⟩

theorem lpFiberObservation_le (T : lp E 2 →L[ℂ] Y) (x : lp E 2) :
    lpFiberObservation T x ≤ ‖T‖ * ‖x‖ := by
  obtain ⟨y, hy, he⟩ := lpFiberObservation_attained T x
  rw [← he]
  exact (T.le_opNorm y).trans
    (mul_le_mul_of_nonneg_left (lpFiberSolidHull_norm_le hy) (norm_nonneg T))

theorem tendstoUniformlyOn_lpFiberSolidHull
    (T : A → lp E 2 →L[ℂ] Y) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a, ‖T a‖ ≤ C)
    (hp : ∀ y, Tendsto (fun a => T a y) l (𝓝 0)) (x : lp E 2) :
    TendstoUniformlyOn (fun a y => T a y) (fun _ => 0) l (lpFiberSolidHull x) :=
  tendstoUniformlyOn_zero_of_strong T C hC hb hp _ (isCompact_lpFiberSolidHull x)

theorem tendsto_lpFiberObservation
    (T : A → lp E 2 →L[ℂ] Y) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a, ‖T a‖ ≤ C)
    (hp : ∀ y, Tendsto (fun a => T a y) l (𝓝 0)) (x : lp E 2) :
    Tendsto (fun a => lpFiberObservation (T a) x) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_lpFiberSolidHull T C hC hb hp x) ε hε] with a ha
  obtain ⟨y, hy, he⟩ := lpFiberObservation_attained (T a) x
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (lpFiberObservation_nonneg _ _), ← he]
  simpa only [dist_zero_left] using ha y hy

end
end GaloisForLFunctions.HTGeometry
