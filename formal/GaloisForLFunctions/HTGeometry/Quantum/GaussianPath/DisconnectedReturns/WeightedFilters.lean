import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.DominantInvolution

/-! # Conjugation isolates the anticommuting terms of a two-family Hamiltonian -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DisconnectedReturns
noncomputable section
variable {d ι : Type*} [Fintype d] [DecidableEq d] [Nonempty d] [Fintype ι] [DecidableEq ι]
abbrev Matrices (d : Type*) := Matrix d d ℂ

/-- Ternary weights distinguish all simultaneous signs in one commuting family. -/
def weight (i : ι) : ℝ := 3^((Fintype.equivFin ι) i).val

def weighted (P : ι → Matrices d) (s : Finset ι) : Matrices d :=
  ∑ i∈s, (weight i:ℂ) • P i

omit [DecidableEq ι] in
theorem resolve_weighted (P : ι → Matrices d) (hP : ∀ i, P i∈unitary (Matrices d))
    (hinv : ∀ i, P i*P i=1) (hc : ∀ i j, Commute (P i) (P j)) (X : Matrices d)
    (s : Finset ι) (h : Commute X (weighted P s)) : ∀ i∈s, Commute X (P i) := by
  classical
  let e := Fintype.equivFin ι
  let T := s.map e.toEmbedding
  have he : (∑ i∈T, (3:ℂ)^i.val • P (e.symm i))=weighted P s := by
    simp only [T,Finset.sum_map,Equiv.coe_toEmbedding,Equiv.symm_apply_apply,weighted,weight,
      Complex.ofReal_pow,Complex.ofReal_ofNat,e]
  have hall := (commute_weighted_spins (P ∘ e.symm) (fun i => hP _) (fun i => hinv _)
    X T (fun i _ j _ => hc _ _)).mp (he.symm ▸ h)
  intro i hi
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hall (e i)
    (Finset.mem_map.mpr ⟨i,hi,rfl⟩)

omit [DecidableEq d] [Nonempty d] in
/-- If conjugation by Q changes precisely the signs in T, subtracting its
conjugate selects twice the sum of those terms. -/
theorem weighted_rejection (P : ι → Matrices d) (Q : Matrices d) (T : Finset ι)
    (h : ∀ i, Q*P i*Q=if i∈T then -(P i) else P i) :
    weighted P Finset.univ-Q*weighted P Finset.univ*Q=(2:ℂ) • weighted P T := by
  classical
  unfold weighted
  rw [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  have he (i : ι) : (weight i:ℂ) • P i-Q*((weight i:ℂ) • P i)*Q =
      if i∈T then (2:ℂ) • ((weight i:ℂ) • P i) else 0 := by
    rw [Matrix.mul_smul,Matrix.smul_mul,h]
    by_cases hi : i∈T
    · simp only [if_pos hi,smul_neg,sub_neg_eq_add,two_smul]
    · simp only [if_neg hi,sub_self]
  simp only [he,←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.smul_sum]

/-- A known symmetry Q of the tested matrix exposes each flipped term
when the other part of the Hamiltonian is fixed under conjugation. -/
theorem resolve_rejection (P : ι → Matrices d) (hP : ∀ i, P i∈unitary (Matrices d))
    (hinv : ∀ i, P i*P i=1) (hc : ∀ i j, Commute (P i) (P j)) (X Q K : Matrices d)
    (T : Finset ι) (hQ : Commute X Q) (hH : Commute X (weighted P Finset.univ+K))
    (hK : Q*K*Q=K) (hf : ∀ i, Q*P i*Q=if i∈T then -(P i) else P i) :
    ∀ i∈T, Commute X (P i) := by
  have h := hH.sub_right ((hQ.mul_right hH).mul_right hQ)
  rw [mul_add,add_mul,hK,add_sub_add_right_eq_sub,weighted_rejection P Q T hf] at h
  apply resolve_weighted P hP hinv hc X T
  simpa only [smul_smul,inv_mul_cancel₀ (by norm_num : (2:ℂ)≠0),one_smul] using
    h.smul_right ((2:ℂ)⁻¹)

end
end GaloisForLFunctions.HTGeometry.DisconnectedReturns
