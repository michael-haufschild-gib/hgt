import GaloisForLFunctions.RHTower.Deninger.DeningerExtendByZero
import Mathlib.Algebra.BigOperators.Fin

/-!
# Fineness kills the first Čech cohomology

A one-cocycle of continuous functions for a finite open cover splits as soon as the cover carries a
subordinate partition of unity: averaging the cocycle against the partition, extended by zero,
produces the splitting cochain.

This is the first — and, for a leafwise coefficient sheaf, the decisive — instance of "a fine sheaf
is acyclic": the contracting homotopy is multiplication by the partition of unity.

* `deningerCechSplitCochain` : the averaged cochain.
* `deningerCechSplit` : every one-cocycle splits.
-/

namespace RHTower

open Set Topology
open scoped Classical

section CechSplit

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]

/-- The cochain obtained by averaging a cocycle against a partition of unity. -/
noncomputable def deningerCechSplitCochain (U : ι → Set X) (ρ : ι → X → ℝ)
    (c : ι → ι → X → ℝ) (i : ι) (x : X) : ℝ :=
  ∑ k : ι, deningerExtendByZero (U k) (ρ k) (c k i) x

/-- **The averaged cochain is continuous on its open set.** -/
theorem deningerCechSplitCochain_continuousOn {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    {ρ : ι → X → ℝ} (hρcont : ∀ i, Continuous (ρ i)) (hρsupp : ∀ i, tsupport (ρ i) ⊆ U i)
    {c : ι → ι → X → ℝ} (hc : ∀ i j, ContinuousOn (c i j) (U i ∩ U j)) (i : ι) :
    ContinuousOn (deningerCechSplitCochain U ρ c i) (U i) := by
  refine continuousOn_finsetSum _ fun k _ => ?_
  exact deningerExtendByZero_continuousOn (hU k) (hU i) (hρcont k) (hρsupp k) (hc k i)

/-- **Fineness splits a one-cocycle.**  Averaging the cocycle against the partition of unity, each
term extended by zero, gives a cochain whose coboundary is the cocycle.  The cocycle relation turns
the difference of two averages into the cocycle times the total mass of the partition, which is
one. -/
theorem deningerCechSplit {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    {ρ : ι → X → ℝ} (hρcont : ∀ i, Continuous (ρ i)) (hρsupp : ∀ i, tsupport (ρ i) ⊆ U i)
    (hρsum : ∀ x, ∑ i : ι, ρ i x = 1)
    {c : ι → ι → X → ℝ} (hc : ∀ i j, ContinuousOn (c i j) (U i ∩ U j))
    (hcocycle : ∀ (i j k : ι) (x : X), x ∈ U i → x ∈ U j → x ∈ U k →
      c k i x + c i j x = c k j x) :
    ∃ b : ι → X → ℝ, (∀ i, ContinuousOn (b i) (U i))
      ∧ ∀ (i j : ι) (x : X), x ∈ U i → x ∈ U j → c i j x = b j x - b i x := by
  refine ⟨deningerCechSplitCochain U ρ c, fun i =>
    deningerCechSplitCochain_continuousOn hU hρcont hρsupp hc i, fun i j x hxi hxj => ?_⟩
  have hterm : ∀ k : ι,
      deningerExtendByZero (U k) (ρ k) (c k j) x - deningerExtendByZero (U k) (ρ k) (c k i) x
        = ρ k x * c i j x := by
    intro k
    by_cases hxk : x ∈ U k
    · rw [deningerExtendByZero_eq_of_mem hxk, deningerExtendByZero_eq_of_mem hxk, ← mul_sub]
      congr 1
      have h := hcocycle i j k x hxi hxj hxk
      linarith
    · rw [deningerExtendByZero_eq_zero hxk, deningerExtendByZero_eq_zero hxk,
        deningerExtendByZero_bump_zero (hρsupp k) hxk]
      ring
  have hsum : deningerCechSplitCochain U ρ c j x - deningerCechSplitCochain U ρ c i x
      = ∑ k : ι, ρ k x * c i j x := by
    rw [deningerCechSplitCochain, deningerCechSplitCochain, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => hterm k
  rw [hsum, ← Finset.sum_mul, hρsum x, one_mul]

end CechSplit

end RHTower
