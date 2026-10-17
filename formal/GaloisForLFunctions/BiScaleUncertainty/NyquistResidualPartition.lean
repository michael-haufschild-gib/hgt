import GaloisForLFunctions.BiScaleUncertainty.NyquistResidualMass
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # The actual half-open Nyquist partition and its residual kernel -/

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistResidualCell (k : ℕ) : Set ℝ :=
  Ioc (nyquistResidualNode k) (nyquistResidualNode (k + 1))

theorem measurableSet_nyquistResidualCell (k : ℕ) :
    MeasurableSet (nyquistResidualCell k) := measurableSet_Ioc

theorem pairwise_disjoint_nyquistResidualCell :
    Pairwise (fun i j => Disjoint (nyquistResidualCell i) (nyquistResidualCell j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact Ioc_disjoint_Ioc_of_le
      (strictMono_nyquistResidualNode.monotone (by omega : i + 1 ≤ j))
  · exact (Ioc_disjoint_Ioc_of_le
      (strictMono_nyquistResidualNode.monotone (by omega : j + 1 ≤ i))).symm

theorem iUnion_nyquistResidualCell (N : ℕ) :
    (⋃ k : ℕ, nyquistResidualCell (N + k)) = Ioi (nyquistResidualNode N) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact (strictMono_nyquistResidualNode.monotone (Nat.le_add_right N k)).trans_lt hk.1
  · intro hx
    obtain ⟨M, hM⟩ := (tendsto_nyquistResidualNode.eventually (eventually_ge_atTop x)).exists
    have hMx : x ≤ nyquistResidualNode (N + M) :=
      hM.trans (strictMono_nyquistResidualNode.monotone (Nat.le_add_left M N))
    have hh := Ioc_subset_biUnion_Ioc M (fun k => nyquistResidualNode (N + k))
      (show x ∈ Ioc (nyquistResidualNode (N + 0)) (nyquistResidualNode (N + M)) from
        ⟨by simpa using hx, hMx⟩)
    obtain ⟨k, hk⟩ := mem_iUnion.mp hh
    obtain ⟨_, hkx⟩ := mem_iUnion.mp hk
    exact mem_iUnion.mpr ⟨k, by simpa only [nyquistResidualCell, Nat.add_assoc] using hkx⟩

def nyquistResidualKernel (N : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (nyquistResidualCell (N + k)).indicator (nyquistResidualDensity (N + k)) x

theorem measurable_nyquistResidualKernel (N : ℕ) :
    Measurable (nyquistResidualKernel N) :=
  Measurable.tsum (fun k => (continuous_nyquistResidualDensity (N + k)).measurable.indicator
    (measurableSet_nyquistResidualCell (N + k)))

theorem nyquistResidualKernel_on_cell (N k : ℕ) {x : ℝ}
    (hx : x ∈ nyquistResidualCell (N + k)) :
    nyquistResidualKernel N x = nyquistResidualDensity (N + k) x := by
  unfold nyquistResidualKernel
  rw [tsum_eq_single k]
  · exact indicator_of_mem hx _
  · intro j hj
    apply indicator_of_notMem
    intro hjx
    exact (disjoint_left.mp (pairwise_disjoint_nyquistResidualCell (by omega : N + j ≠ N + k))) hjx hx

theorem nyquistResidualKernel_eq_zero (N : ℕ) {x : ℝ}
    (hx : x ≤ nyquistResidualNode N) : nyquistResidualKernel N x = 0 := by
  unfold nyquistResidualKernel
  have hz (k : ℕ) :
      (nyquistResidualCell (N + k)).indicator (nyquistResidualDensity (N + k)) x = 0 := by
    apply indicator_of_notMem
    intro hk
    have hh := strictMono_nyquistResidualNode.monotone (Nat.le_add_right N k)
    exact (not_lt_of_ge (hx.trans hh)) hk.1
  rw [tsum_eq_single 0 (fun k _ => hz k), hz 0]

theorem nyquistResidualKernel_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ nyquistResidualKernel N x := by
  apply tsum_nonneg
  intro k
  by_cases hx : x ∈ nyquistResidualCell (N + k)
  · rw [indicator_of_mem hx]
    exact (nyquistResidualDensity_bounds (N + k) ⟨hx.1.le, hx.2⟩).1
  · rw [indicator_of_notMem hx]

theorem nyquistResidualKernel_indicator (N : ℕ) :
    (Ioi (nyquistResidualNode N)).indicator (nyquistResidualKernel N) =
      nyquistResidualKernel N := by
  funext x
  by_cases hx : x ∈ Ioi (nyquistResidualNode N)
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, nyquistResidualKernel_eq_zero N (le_of_not_gt hx)]

theorem nyquistResidualKernel_eq_tail_indicator (N : ℕ) :
    nyquistResidualKernel N =
      (Ioi (nyquistResidualNode N)).indicator (nyquistResidualKernel 0) := by
  funext x
  by_cases hx : x ∈ Ioi (nyquistResidualNode N)
  · rw [indicator_of_mem hx]
    obtain ⟨k, hk⟩ := mem_iUnion.mp ((iUnion_nyquistResidualCell N).symm ▸ hx)
    rw [nyquistResidualKernel_on_cell N k hk]
    simpa only [Nat.zero_add] using
      (nyquistResidualKernel_on_cell 0 (N + k) (by simpa only [Nat.zero_add] using hk)).symm
  · rw [indicator_of_notMem hx, nyquistResidualKernel_eq_zero N (le_of_not_gt hx)]

end
end GaloisForLFunctions.BiScaleUncertainty
