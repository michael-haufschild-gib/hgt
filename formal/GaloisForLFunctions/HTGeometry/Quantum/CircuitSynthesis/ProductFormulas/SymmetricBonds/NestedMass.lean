import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.SymmetricBonds.OverlapCubes
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.BlockCommutators
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.InteractionPicture

/-! # Cubic mass bound for nested commutators of physical interactions -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
noncomputable section
open LocalPatches
variable {n : ℕ}
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance (N : ℕ) : CStarAlgebra (Reg N) where

private theorem bracket_norm {R : Type*} [NormedRing R] (a b : R) : ‖b*a-a*b‖ ≤ 2*‖a‖*‖b‖ := by
  apply (norm_sub_le ..).trans ((add_le_add (norm_mul_le ..) (norm_mul_le ..)).trans_eq ?_)
  ring

private theorem far_commute (u : PathShell n) {i j : PathLabel n} (h : i∉pathOverlaps j) :
    Commute (pathTermGenerator u i) (pathTermGenerator u j) := by
  have hd : Disjoint (labelSupport (pathWord j)) (labelSupport (pathWord i)) := by
    by_contra hn; exact h (mem_pathOverlaps.mpr hn)
  have hp := commute_finitePauliMatrix_of_disjoint hd.symm
  exact (((hp.smul_left (u i:ℂ)).smul_left (-Complex.I)).smul_right (u j:ℂ)).smul_right (-Complex.I)

/-- One of the two labels in the inner commutator must meet the outer
one. The two choices of middle label contribute two overlap-walk sums. -/
theorem path_nested_mass (u : PathShell n) :
    let X := pathTermGenerator u
    (∑ j, ∑ k, ∑ i, ‖bracketStep (X i) (bracketStep (X j) (X k))‖) ≤
      (24*42^2)*∑ i,|u i|^3 := by
  classical
  intro X
  let a (l : PathLabel n) := |u l|
  let term (j k i : PathLabel n) := a k*a j*a i
  let W (j k i : PathLabel n) := if k∈pathOverlaps j then (if i∈pathOverlaps j then term j k i else 0) else 0
  have hx (l : PathLabel n) : ‖X l‖=a l := (pathTerm_properties u l).1
  have hn (j k i : PathLabel n) : 0 ≤ W j k i := by unfold W term a; positivity
  have hpair (j k i : PathLabel n) : ‖bracketStep (X i) (bracketStep (X j) (X k))‖ ≤ 4*term j k i := by
    have h := (bracket_norm (X i) (bracketStep (X j) (X k))).trans
      (mul_le_mul_of_nonneg_left (bracket_norm (X j) (X k)) (by positivity))
    simp only [hx] at h
    exact h.trans_eq (by dsimp only [term]; ring)
  have h (j k i : PathLabel n) : ‖bracketStep (X i) (bracketStep (X j) (X k))‖ ≤ 4*(W j k i+W k j i) := by
    by_cases hk : k ∈ pathOverlaps j
    · by_cases hi : i ∈ pathOverlaps j
      · exact (hpair j k i).trans (mul_le_mul_of_nonneg_left
          ((show term j k i=W j k i by simp [W,hk,hi]).le.trans (le_add_of_nonneg_right (hn k j i))) (by norm_num))
      · by_cases hi' : i ∈ pathOverlaps k
        · have hj : j∈pathOverlaps k := mem_pathOverlaps.mpr (by rw [disjoint_comm]; exact mem_pathOverlaps.mp hk)
          have hw : term j k i=W k j i := by simp [W,hj,hi',term,mul_comm (a k) (a j)]
          exact (hpair ..).trans (mul_le_mul_of_nonneg_left (hw.le.trans (le_add_of_nonneg_left (hn j k i))) (by norm_num))
        · have hij := far_commute u hi
          have hik := far_commute u hi'
          have hc : Commute (X i) (bracketStep (X j) (X k)) := (hik.mul_right hij).sub_right (hij.mul_right hik)
          rw [bracketStep,hc.symm.eq,sub_self,norm_zero]
          exact mul_nonneg (by norm_num) (add_nonneg (hn ..) (hn ..))
    · have hc := far_commute u hk
      have he : bracketStep (X j) (X k)=0 := sub_eq_zero.mpr hc.eq
      rw [he,bracketStep,zero_mul,mul_zero,sub_self,norm_zero]
      exact mul_nonneg (by norm_num) (add_nonneg (hn ..) (hn ..))
  have hsum : (∑ j, ∑ k, ∑ i, W j k i) ≤ 3*42^2*∑ i,(a i)^3 := by
    have hr (j) : (∑ k, ∑ i, W j k i)=∑ k∈pathOverlaps j, ∑ i∈pathOverlaps j, term j k i := by
      simp [W,Finset.sum_filter,Finset.sum_ite_irrel]
    simp_rw [hr]
    exact overlap_triple_mass a (fun i => abs_nonneg _)
  have hf : (∑ j, ∑ k, ∑ i, W k j i) = ∑ j, ∑ k, ∑ i, W j k i := Finset.sum_comm
  apply (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun i _ => h j k i)))).trans
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,hf]
  linarith only [hsum]

end
end GaloisForLFunctions.HTGeometry.BondProducts.Symmetric
