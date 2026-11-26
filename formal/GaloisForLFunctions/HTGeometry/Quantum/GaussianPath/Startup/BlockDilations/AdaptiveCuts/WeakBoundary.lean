import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.BoundaryEnergy
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.DrawConstraints

/-! # Separate prices for a weak cut and its surrounding interactions -/

open Finset Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n : ℕ}

/-- Across any cut, multiply the outer coefficients by b and the inner
ones by its reciprocal. Every product in the commutator is invariant. -/
private theorem reweight_boundary (S C : Finset (PathLabel n)) (u : PathShell n)
    (hSC : Disjoint S C) (hcut : ∀ q∉S, ∀ l∈S, l∈pathOverlaps q → q∈C)
    {b : ℝ} (hb : 0<b) :
    let v : PathShell n := WithLp.toLp 2 (fun i => if i∈C then b*u i else b⁻¹*u i)
    boundaryMass u S=boundaryMass v S := by
  intro v
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro l hl
  obtain ⟨hs,ho⟩ := mem_inter.mp hl
  have hqC := hcut q (mem_compl.mp hq) l hs ho
  have hlC : l∉C := fun h => disjoint_left.mp hSC hs h
  rw [show v q=b*u q from if_pos hqC,show v l=b⁻¹*u l from if_neg hlC,
    abs_mul,abs_mul,abs_of_pos hb,abs_of_pos (inv_pos.mpr hb)]
  field_simp

/-- The boundary price is controlled by a weighted sum of squared
couplings. Only the cut bonds themselves pay the large weight. -/
theorem weak_boundary_price (S C : Finset (PathLabel n)) (u : PathShell n)
    (hSC : Disjoint S C) (hcut : ∀ q∉S, ∀ l∈S, l∈pathOverlaps q → q∈C)
    {b : ℝ} (hb : 0<b) :
    let T := seamNeighbourhood C
    boundaryMass u S≤84*(b^2*energyOn C u.ofLp+b⁻¹^2*energyOn (T\C) u.ofLp) := by
  classical
  intro T
  let v : PathShell n := WithLp.toLp 2 (fun i => if i∈C then b*u i else b⁻¹*u i)
  have hCT : C⊆T := fun i hi => mem_biUnion.mpr ⟨i,hi,mem_insert_self ..⟩
  rw [reweight_boundary S C u hSC hcut hb]
  apply (boundaryMass_le_seam S C v hcut).trans_eq
  congr 1
  rw [restricted_energy]
  unfold energyOn
  rw [←sum_sdiff hCT,mul_sum,mul_sum]
  apply (add_comm ..).trans
  apply congrArg₂ (·+·)
  · apply sum_congr rfl
    intro i hi
    change (if i∈C then b*u i else b⁻¹*u i)^2=_
    rw [if_pos hi,mul_pow]
  · apply sum_congr rfl
    intro i hi
    change (if i∈C then b*u i else b⁻¹*u i)^2=_
    rw [if_neg (mem_sdiff.mp hi).2,mul_pow]

/-- A cut with at most k Pauli labels, each of size at most w, costs
at most 84 k w R when every neighbouring coefficient is at most R. -/
theorem boundary_from_weak_cuts (S C : Finset (PathLabel n)) (u : PathShell n)
    (hcut : ∀ q∉S, ∀ l∈S, l∈pathOverlaps q → q∈C)
    {w R : ℝ} (hw : 0≤w) (hR : 0≤R)
    (hweak : ∀ q∈C, |u q|≤w) (hnear : ∀ l∈seamNeighbourhood C, |u l|≤R) :
    boundaryMass u S≤84*(C.card:ℝ)*w*R := by
  classical
  let B := 2*w*R
  have hB : 0≤B := mul_nonneg (mul_nonneg zero_le_two hw) hR
  have hrow (q : PathLabel n) (hq : q∈Sᶜ) :
      (∑ l ∈ S∩pathOverlaps q, 2*|u q| * |u l|) ≤ if q∈C then 42*B else 0 := by
    by_cases hc : q∈C
    · rw [if_pos hc]
      calc
        _ ≤ ∑ _l ∈ S∩pathOverlaps q, B := by
          apply sum_le_sum
          intro l hl
          have hn : l∈seamNeighbourhood C := mem_biUnion.mpr
            ⟨q,hc,mem_insert_of_mem (mem_inter.mp hl).2⟩
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hweak q hc) zero_le_two)
            (hnear l hn) (abs_nonneg _) (mul_nonneg zero_le_two hw)
        _ = ((S∩pathOverlaps q).card:ℝ)*B := by simp only [sum_const,nsmul_eq_mul]
        _ ≤ 42*B := mul_le_mul_of_nonneg_right
          (by exact_mod_cast ((card_le_card (show S∩pathOverlaps q⊆pathOverlaps q from inter_subset_right)).trans
            (pathOverlaps_card_le q))) hB
    · rw [if_neg hc]
      apply le_of_eq
      apply sum_eq_zero
      intro l hl
      exact (hc (hcut q (mem_compl.mp hq) l (mem_inter.mp hl).1 (mem_inter.mp hl).2)).elim
  calc
    _ ≤ ∑ q ∈ Sᶜ, if q∈C then 42*B else 0 := sum_le_sum hrow
    _ ≤ ∑ q, if q∈C then 42*B else 0 := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun q _ _ => by split <;> positivity)
    _ = _ := by rw [←sum_filter]; simp [B]; ring

#print axioms boundary_from_weak_cuts
#print axioms weak_boundary_price
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
