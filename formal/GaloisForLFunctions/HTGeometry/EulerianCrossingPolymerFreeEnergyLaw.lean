import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Eulerian crossing-polymer free energy

This module closes the collective summation step in the static-local-Hamiltonian crossing-memory
route.  Compatibility is kept exactly: every compatible polymer collection is summed, then bounded
by the exponential of total connected activity.  Since every nonempty simple Eulerian component
has at least three vertices, its activity series begins cubically in replica density.  A cubic
free-energy tax cannot erase a linear planar action gap at sufficiently small fixed density.

The module does not assert the separate physical estimate that exact cavity dressing bounds each
connected activity.  It proves the resummation and action-gap implications needed once that concrete
activity estimate has been derived from the local Hamiltonian ensemble.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Partition function of any selected subfamilies of a finite polymer family. -/
noncomputable def compatiblePolymerPartition {α : Type*} [DecidableEq α]
    (P : Finset α) (compatible : Finset α → Prop) [DecidablePred compatible]
    (w : α → ℝ) : ℝ :=
  ∑ F ∈ P.powerset.filter compatible, ∏ γ ∈ F, w γ

/-- Dropping compatibility bounds a nonnegative polymer gas by its exponential activity mass. -/
theorem compatiblePolymerPartition_le_exp_sum {α : Type*} [DecidableEq α]
    (P : Finset α) (compatible : Finset α → Prop) [DecidablePred compatible]
    (w : α → ℝ) (hw : ∀ γ, 0 ≤ w γ) :
    compatiblePolymerPartition P compatible w ≤ Real.exp (∑ γ ∈ P, w γ) := by
  unfold compatiblePolymerPartition
  calc
    (∑ F ∈ P.powerset.filter compatible, ∏ γ ∈ F, w γ)
        ≤ ∑ F ∈ P.powerset, ∏ γ ∈ F, w γ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro F hF _
            exact Finset.prod_nonneg fun γ _ => hw γ
    _ = ∏ γ ∈ P, (1 + w γ) := (Finset.prod_one_add P).symm
    _ ≤ Real.exp (∑ γ ∈ P, w γ) := Real.prod_one_add_le_exp_sum P hw

/-- A total activity bound transfers directly to a free-energy bound. -/
theorem compatiblePolymerPartition_le_cubic_freeEnergy {α : Type*} [DecidableEq α]
    (P : Finset α) (compatible : Finset α → Prop) [DecidablePred compatible]
    (w : α → ℝ) (n q x : ℝ)
    (hw : ∀ γ, 0 ≤ w γ)
    (hactivity : (∑ γ ∈ P, w γ) ≤ n / q ^ 2 * (x ^ 3 / (9 * (1 - x)))) :
    compatiblePolymerPartition P compatible w ≤
      Real.exp (n / q ^ 2 * (x ^ 3 / (9 * (1 - x)))) := by
  exact (compatiblePolymerPartition_le_exp_sum P compatible w hw).trans
    (Real.exp_le_exp.mpr hactivity)

/-- The activity series of polymers with at least three vertices has a cubic leading envelope. -/
theorem eulerian_activity_series_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∑' j : ℕ, x ^ (j + 3) / ((j + 3 : ℕ) : ℝ) ^ 2) ≤
      x ^ 3 / (9 * (1 - x)) := by
  let f : ℕ → ℝ := fun j => x ^ (j + 3) / ((j + 3 : ℕ) : ℝ) ^ 2
  let g : ℕ → ℝ := fun j => x ^ (j + 3) / 9
  have hfg : ∀ j, f j ≤ g j := by
    intro j
    dsimp [f, g]
    have hden : (9 : ℝ) ≤ ((j + 3 : ℕ) : ℝ) ^ 2 := by
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      push_cast
      nlinarith
    have hpow : 0 ≤ x ^ (j + 3) := pow_nonneg hx0 _
    exact div_le_div_of_nonneg_left hpow (by norm_num) hden
  have hgeom : Summable (fun j : ℕ => x ^ j) :=
    summable_geometric_of_lt_one hx0 hx1
  have hg : Summable g := by
    have hrewrite : g = fun j : ℕ => (x ^ 3 / 9) * x ^ j := by
      funext j
      dsimp [g]
      rw [pow_add]
      ring
    rw [hrewrite]
    exact hgeom.mul_left _
  have hf : Summable f := Summable.of_nonneg_of_le
    (fun j => by dsimp [f]; positivity) hfg hg
  calc
    (∑' j : ℕ, x ^ (j + 3) / ((j + 3 : ℕ) : ℝ) ^ 2) = ∑' j, f j := rfl
    _ ≤ ∑' j, g j := Summable.tsum_le_tsum hfg hf hg
    _ = x ^ 3 / (9 * (1 - x)) := by
      rw [show g = fun j : ℕ => (x ^ 3 / 9) * x ^ j by
        funext j
        dsimp [g]
        rw [pow_add]
        ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1]
      field_simp

/-- Cubic crossing free energy cannot erase a linear action gap at small density. -/
theorem linear_action_gap_survives_cubic_polymer_tax
    (Z η κ C n k : ℝ)
    (hZ : Z ≤ Real.exp (C * κ ^ 3 * n))
    (hk : κ * n / 2 ≤ k)
    (hη : 0 ≤ η)
    (hκ : 0 ≤ κ)
    (hn : 0 ≤ n)
    (hsmall : C * κ ^ 2 ≤ η / 4) :
    Real.exp (-η * k) * Z ≤ Real.exp (-η * κ * n / 4) := by
  calc
    Real.exp (-η * k) * Z
        ≤ Real.exp (-η * k) * Real.exp (C * κ ^ 3 * n) := by
          exact mul_le_mul_of_nonneg_left hZ (Real.exp_nonneg _)
    _ = Real.exp (-η * k + C * κ ^ 3 * n) := by rw [← Real.exp_add]
    _ ≤ Real.exp (-η * κ * n / 4) := by
      rw [Real.exp_le_exp]
      have hκn : 0 ≤ κ * n := mul_nonneg hκ hn
      have htax : C * κ ^ 3 * n ≤ (η / 4) * (κ * n) := by
        calc
          C * κ ^ 3 * n = (C * κ ^ 2) * (κ * n) := by ring
          _ ≤ (η / 4) * (κ * n) := mul_le_mul_of_nonneg_right hsmall hκn
      have hlinear : -η * k ≤ -η * (κ * n / 2) :=
        mul_le_mul_of_nonpos_left hk (neg_nonpos.mpr hη)
      linarith

end GaloisForLFunctions.HTGeometry
