import GaloisForLFunctions.HTGeometry.LocalExtensionQuadraticRateRigidity
import Mathlib.Data.Matrix.Basic

/-!
# The second-order response of a one-qubit layer extension

Attaching a qubit with local field `z` to a simple old spectrum `E` splits every old level into
`E_α ± z/2`.  An edge perturbation `A ⊗ X` is, in the split eigenbasis, the matrix that carries
`M_{αβ}` across the two layers and nothing inside a layer.  Its first-order response therefore
vanishes and its second-order response is a sum of simple poles at the ordered old gaps.

This file computes that response and the affine uncoupled spectral action; the residue collapse
of the resulting pole packet is in `LocalExtensionQuadraticRateRigidity`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The uncoupled energies of a one-qubit extension: the old spectrum split by the new field. -/
def layerSplitEnergy (E : A → ℂ) (z : ℂ) : A × Bool → ℂ :=
  fun x => E x.1 + (if x.2 then -(z / 2) else z / 2)

/-- The edge perturbation `A ⊗ X` in the split eigenbasis: it acts only across the two layers. -/
def layerCrossPerturbation (M : Matrix A A ℂ) : Matrix (A × Bool) (A × Bool) ℂ :=
  Matrix.of fun x y => if x.2 = y.2 then 0 else M x.1 y.1

omit [Fintype A] [DecidableEq A] in
theorem layerCrossPerturbation_apply_same {M : Matrix A A ℂ} {x y : A × Bool} (h : x.2 = y.2) :
    layerCrossPerturbation M x y = 0 := by
  simp [layerCrossPerturbation, h]

omit [Fintype A] [DecidableEq A] in
theorem layerCrossPerturbation_apply_cross {M : Matrix A A ℂ} {x y : A × Bool} (h : x.2 ≠ y.2) :
    layerCrossPerturbation M x y = M x.1 y.1 := by
  simp [layerCrossPerturbation, h]

omit [Fintype A] [DecidableEq A] in
theorem layerCrossPerturbation_diagonal (M : Matrix A A ℂ) (x : A × Bool) :
    layerCrossPerturbation M x x = 0 :=
  layerCrossPerturbation_apply_same rfl

omit [Fintype A] [DecidableEq A] in
theorem layerSplitEnergy_sub_cross (E : A → ℂ) (z : ℂ) (α β : A) :
    layerSplitEnergy E z (α, false) - layerSplitEnergy E z (β, true) = z + E α - E β := by
  simp only [layerSplitEnergy]
  norm_num
  ring

omit [Fintype A] [DecidableEq A] in
theorem layerSplitEnergy_sub_cross' (E : A → ℂ) (z : ℂ) (α β : A) :
    layerSplitEnergy E z (α, true) - layerSplitEnergy E z (β, false) = -z + E α - E β := by
  simp only [layerSplitEnergy]
  norm_num
  ring

omit [DecidableEq A] in
/-- **The uncoupled spectral action is affine in the new local field.** -/
theorem layerSplitAction_affine (E : A → ℂ) (c : A × Bool → ℂ) (z : ℂ) :
    (∑ x : A × Bool, c x * layerSplitEnergy E z x)
      = (∑ α, (c (α, false) + c (α, true)) * E α)
        + ((∑ α, c (α, false) - ∑ α, c (α, true)) / 2) * z := by
  rw [Fintype.sum_prod_type]
  have hrhs : (∑ α, (c (α, false) + c (α, true)) * E α)
        + ((∑ α, c (α, false) - ∑ α, c (α, true)) / 2) * z
      = ∑ α, ((c (α, false) + c (α, true)) * E α + (c (α, false) - c (α, true)) / 2 * z) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_mul]
  rw [hrhs]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Fintype.sum_bool, layerSplitEnergy]
  norm_num
  ring

/-- **The second-order response of one split branch.**  Only the opposite layer contributes, and
the poles are the ordered old gaps. -/
theorem layerCrossSecondOrder_response (E : A → ℂ) (M : Matrix A A ℂ) (z : ℂ) (α : A) (r : Bool) :
    (∑ y ∈ Finset.univ.erase (α, r),
        layerCrossPerturbation M (α, r) y * layerCrossPerturbation M y (α, r)
          / (layerSplitEnergy E z (α, r) - layerSplitEnergy E z y))
      = if r then ∑ β, M α β * M β α / (-z + E α - E β)
        else ∑ β, M α β * M β α / (z + E α - E β) := by
  classical
  have hdrop : layerCrossPerturbation M (α, r) (α, r) * layerCrossPerturbation M (α, r) (α, r)
      / (layerSplitEnergy E z (α, r) - layerSplitEnergy E z (α, r)) = 0 := by
    rw [layerCrossPerturbation_diagonal]
    simp
  have hstep : (∑ y ∈ Finset.univ.erase (α, r),
      layerCrossPerturbation M (α, r) y * layerCrossPerturbation M y (α, r)
        / (layerSplitEnergy E z (α, r) - layerSplitEnergy E z y))
      = ∑ y : A × Bool, layerCrossPerturbation M (α, r) y * layerCrossPerturbation M y (α, r)
        / (layerSplitEnergy E z (α, r) - layerSplitEnergy E z y) := by
    refine Finset.sum_subset (Finset.erase_subset _ _) ?_
    intro y _ hy
    have hy' : y = (α, r) := by
      by_contra hcon
      exact hy (Finset.mem_erase.mpr ⟨hcon, Finset.mem_univ y⟩)
    rw [hy']
    exact hdrop
  rw [hstep, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  cases r with
  | false =>
      have hsame : ∀ β : A,
          layerCrossPerturbation M (α, false) (β, false)
              * layerCrossPerturbation M (β, false) (α, false)
            / (layerSplitEnergy E z (α, false) - layerSplitEnergy E z (β, false)) = 0 := by
        intro β
        rw [layerCrossPerturbation_apply_same (x := ((α, false) : A × Bool))
          (y := ((β, false) : A × Bool)) rfl]
        simp
      have hcross : ∀ β : A,
          layerCrossPerturbation M (α, false) (β, true)
              * layerCrossPerturbation M (β, true) (α, false)
            / (layerSplitEnergy E z (α, false) - layerSplitEnergy E z (β, true))
            = M α β * M β α / (z + E α - E β) := by
        intro β
        rw [layerCrossPerturbation_apply_cross (x := ((α, false) : A × Bool))
            (y := ((β, true) : A × Bool)) (by simp),
          layerCrossPerturbation_apply_cross (x := ((β, true) : A × Bool))
            (y := ((α, false) : A × Bool)) (by simp),
          layerSplitEnergy_sub_cross]
      simp only [hsame, hcross, add_zero, Bool.false_eq_true, if_false]
  | true =>
      have hsame : ∀ β : A,
          layerCrossPerturbation M (α, true) (β, true)
              * layerCrossPerturbation M (β, true) (α, true)
            / (layerSplitEnergy E z (α, true) - layerSplitEnergy E z (β, true)) = 0 := by
        intro β
        rw [layerCrossPerturbation_apply_same (x := ((α, true) : A × Bool))
          (y := ((β, true) : A × Bool)) rfl]
        simp
      have hcross : ∀ β : A,
          layerCrossPerturbation M (α, true) (β, false)
              * layerCrossPerturbation M (β, false) (α, true)
            / (layerSplitEnergy E z (α, true) - layerSplitEnergy E z (β, false))
            = M α β * M β α / (-z + E α - E β) := by
        intro β
        rw [layerCrossPerturbation_apply_cross (x := ((α, true) : A × Bool))
            (y := ((β, false) : A × Bool)) (by simp),
          layerCrossPerturbation_apply_cross (x := ((β, false) : A × Bool))
            (y := ((α, true) : A × Bool)) (by simp),
          layerSplitEnergy_sub_cross']
      simp only [hsame, hcross, zero_add, if_true]

/-- **The weighted second-order response.**  Summing the split responses against a coefficient
packet produces exactly the crown pole packet of the extension. -/
theorem layerCrossSecondOrder_weighted_sum (E : A → ℂ) (M : Matrix A A ℂ) (c : A × Bool → ℂ)
    (z : ℂ) :
    (∑ x : A × Bool, c x * ∑ y ∈ Finset.univ.erase x,
        layerCrossPerturbation M x y * layerCrossPerturbation M y x
          / (layerSplitEnergy E z x - layerSplitEnergy E z y))
      = ∑ α, ∑ β, (c (α, false) - c (β, true)) * (M α β * M β α) / (z + E α - E β) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, layerCrossSecondOrder_response, Bool.false_eq_true, if_false,
    if_true]
  rw [Finset.sum_add_distrib]
  have htrue : (∑ α, c (α, true) * ∑ β, M α β * M β α / (-z + E α - E β))
      = -∑ α, ∑ β, c (β, true) * (M α β * M β α) / (z + E α - E β) := by
    have h1 : (∑ α, c (α, true) * ∑ β, M α β * M β α / (-z + E α - E β))
        = ∑ α, ∑ β, -(c (α, true) * (M β α * M α β) / (z + E β - E α)) := by
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [show -z + E α - E β = -(z + E β - E α) from by ring,
        show M α β * M β α = M β α * M α β from by ring]
      field_simp
    rw [h1]
    have h2 : (∑ α, ∑ β, -(c (α, true) * (M β α * M α β) / (z + E β - E α)))
        = -∑ α, ∑ β, c (α, true) * (M β α * M α β) / (z + E β - E α) := by
      simp [Finset.sum_neg_distrib]
    rw [h2]
    congr 1
    exact Finset.sum_comm
  have hfalse : (∑ α, c (α, false) * ∑ β, M α β * M β α / (z + E α - E β))
      = ∑ α, ∑ β, c (α, false) * (M α β * M β α) / (z + E α - E β) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  rw [htrue, hfalse, neg_add_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

end

end GaloisForLFunctions.HTGeometry
