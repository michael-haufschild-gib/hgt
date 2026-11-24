import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.Packets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.EnergyMesh.MovingCut

/-! # Moving the cut by one site in the physical Pauli path -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
open WeakBonds
noncomputable section
variable {n : ℕ}

private def leftSites (n k : ℕ) := univ.filter (fun i : Fin (n+2) => i.val<k)
private def rightSites (n k : ℕ) := univ.filter (fun i : Fin (n+2) => k ≤ i.val)

private def part (u : PathShell n) (S : Finset (Fin (n+2))) :
    EnergyOperator (Fin (n+2)→Bool) := ⟨packet u S,packet_selfAdjoint u S⟩

private def before {A I : Type*} [AddCommMonoid A] [Fintype I] (v : I→ℕ) (x : I→A) (k : ℕ) :=
  ∑ i, if v i<k then x i else 0

private def afterCut {A I : Type*} [AddCommMonoid A] [Fintype I] (v : I→ℕ) (x : I→A) (k : ℕ) :=
  ∑ i, if k ≤ v i then x i else 0

private def atCut {A I : Type*} [AddCommMonoid A] [Fintype I] (v : I→ℕ) (x : I→A) (k : ℕ) :=
  ∑ i, if v i=k then x i else 0

private theorem one_row {A I : Type*} [SeminormedAddCommGroup A] [Fintype I] (v : I→ℕ)
    (hv : Function.Injective v) (x : I→A) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (hx : ∀ i, ‖x i‖ ≤ r) :
    ‖atCut v x k‖ ≤ r := by
  classical
  by_cases h : ∃ i, v i=k
  · obtain ⟨i,rfl⟩ := h
    simpa only [atCut,hv.eq_iff,sum_ite_eq',mem_univ,if_true] using hx i
  · push Not at h
    simpa only [atCut,if_neg (h _),sum_const_zero,norm_zero] using hr

private theorem before_step {A I : Type*} [AddCommGroup A] [Fintype I] (v : I→ℕ) (x : I→A) (k : ℕ) :
    before v x (k+1)-before v x k=atCut v x k := by
  rw [before,before,atCut,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rcases lt_trichotomy (v i) k with h|h|h
  · simp [h,Nat.lt_succ_of_lt h,h.ne]
  · simp [h]
  · simp [h.not_gt,show ¬v i<k+1 by omega,h.ne']

private theorem after_step {A I : Type*} [AddCommGroup A] [Fintype I] (v : I→ℕ) (x : I→A) (k : ℕ) :
    afterCut v x k-afterCut v x (k+1)=atCut v x k := by
  rw [afterCut,afterCut,atCut,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rcases lt_trichotomy (v i) k with h|h|h
  · simp only [if_neg h.not_ge,if_neg (by omega : ¬k+1 ≤ v i),if_neg h.ne,sub_zero]
  · simp [h]
  · simp [h.le,Nat.succ_le_of_lt h,h.ne']

private theorem left_part (u : PathShell n) (k : ℕ) :
    (part u (leftSites n k)).val=before Fin.val (onsiteAt u) k+
      before (fun e : Fin (n+1) => e.val+1) (edgePart u) k := by
  change packet u (leftSites n k)=_
  simp only [packet,leftSites,mem_filter,mem_univ,true_and,Fin.val_castSucc,Fin.val_succ,before]
  congr 1
  apply sum_congr rfl
  intro i _
  exact if_congr (show (i.val<k ∧ i.val+1<k) ↔ i.val+1<k from ⟨And.right,fun h => ⟨by omega,h⟩⟩) rfl rfl

private theorem right_part (u : PathShell n) (k : ℕ) :
    (part u (rightSites n k)).val=afterCut Fin.val (onsiteAt u) k+afterCut Fin.val (edgePart u) k := by
  change packet u (rightSites n k)=_
  simp only [packet,rightSites,mem_filter,mem_univ,true_and,Fin.val_castSucc,Fin.val_succ,afterCut]
  congr 1
  apply sum_congr rfl
  intro i _
  exact if_congr (show (k ≤ i.val ∧ k ≤ i.val+1) ↔ k ≤ i.val from ⟨And.left,fun h => ⟨h,by omega⟩⟩) rfl rfl

private theorem seam_row (u : PathShell n) (k : ℕ) :
    pathHamiltonian u-((part u (leftSites n k)).val+(part u (rightSites n k)).val)=
      atCut (fun e : Fin (n+1) => e.val+1) (edgePart u) k := by
  have hs : onsitePart u=∑ i, onsiteAt u i := by simp only [onsitePart,onsiteAt,Fintype.sum_prod_type]
  have hsite : (∑ i, onsiteAt u i)=before Fin.val (onsiteAt u) k+afterCut Fin.val (onsiteAt u) k := by
    rw [before,afterCut,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases h : i.val<k
    · simp [h,h.not_ge]
    · simp [h,le_of_not_gt h]
  have hedge : (∑ e, edgePart u e)=before (fun e : Fin (n+1) => e.val+1) (edgePart u) k+
      afterCut Fin.val (edgePart u) k+atCut (fun e : Fin (n+1) => e.val+1) (edgePart u) k := by
    rw [before,afterCut,atCut,←sum_add_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro e _
    rcases lt_trichotomy (e.val+1) k with h|h|h
    · simp [h,h.ne,show ¬k ≤ e.val by omega]
    · simp [h,show ¬k ≤ e.val by omega]
    · simp [h.not_gt,h.ne',show k ≤ e.val by omega]
  rw [pathHamiltonian,hs,hsite,hedge,left_part,right_part]
  abel

private theorem zero_edges (N : ℕ) :
    lower (0 : EnergyOperator (Fin N→Bool))=0 ∧ upper (0 : EnergyOperator (Fin N→Bool))=0 := by
  let Z : EnergyOperator (Fin N→Bool) := 0
  have hz (i) : Z.2.isHermitian.eigenvalues i=0 := by
    apply abs_nonpos_iff.mp
    exact (abs_eigenvalue_le_l2_opNorm Z.2.isHermitian i).trans_eq (norm_zero)
  constructor
  · obtain ⟨i,_,hi⟩ := exists_mem_eq_inf' univ_nonempty Z.2.isHermitian.eigenvalues
    exact hi.trans (hz i)
  · obtain ⟨i,_,hi⟩ := exists_mem_eq_sup' univ_nonempty Z.2.isHermitian.eigenvalues
    exact hi.trans (hz i)

/-- Each energy between the two physical edges is within a+2b of a
level, where a bounds each onsite term and b bounds each bond. -/
theorem path_energy_mesh (u : PathShell n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hon : ∀ i, ‖onsiteAt u i‖ ≤ a) (hed : ∀ e, ‖edgePart u e‖ ≤ b) :
    let H : EnergyOperator (Fin (n+2)→Bool) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    ∀ y ∈ Set.Icc (lower H) (upper H), ∃ i, |H.2.isHermitian.eigenvalues i-y| ≤ a+2*b := by
  intro H y hy
  let A (k) := part u (leftSites n k)
  let B (k) := part u (rightSites n k)
  have he₀ : A 0=0 := by ext1; simp [A,left_part,before]
  have heN : B (n+2)=0 := by
    ext1
    simp [B,right_part,afterCut,(fun i : Fin (n+2) => i.isLt.not_ge),
      (fun e : Fin (n+1) => (Nat.lt_succ_of_lt e.isLt).not_ge)]
  have se (k) := seam_row u k
  have h₀ : B 0=H := by
    apply Subtype.ext
    have h := se 0
    change H.val-((A 0).val+(B 0).val)=_ at h
    have hA : (A 0).val=0 := congrArg Subtype.val he₀
    have hz : atCut (fun e : Fin (n+1) => e.val+1) (edgePart u) 0=0 := by simp [atCut]
    rw [hA,zero_add,hz] at h
    exact (sub_eq_zero.mp h).symm
  have hN : A (n+2)=H := by
    apply Subtype.ext
    have h := se (n+2)
    change H.val-((A (n+2)).val+(B (n+2)).val)=_ at h
    have hB : (B (n+2)).val=0 := congrArg Subtype.val heN
    have hne (e : Fin (n+1)) : e.val+1 ≠ n+2 := by omega
    have hz : atCut (fun e : Fin (n+1) => e.val+1) (edgePart u) (n+2)=0 := by
      simp only [atCut,if_neg (hne _),sum_const_zero]
    rw [hB,add_zero,hz] at h
    exact (sub_eq_zero.mp h).symm
  have hinj : Function.Injective (fun e : Fin (n+1) => e.val+1) :=
    fun _ _ h => Fin.ext (Nat.add_right_cancel h)
  have hs (j : ℕ) := one_row Fin.val Fin.val_injective (onsiteAt u) j ha hon
  have hl (j : ℕ) := one_row _ hinj (edgePart u) j hb hed
  have hr (j : ℕ) := one_row Fin.val Fin.val_injective (edgePart u) j hb hed
  have step (k : ℕ) : ‖(A k).val-(A (k+1)).val‖+‖(B k).val-(B (k+1)).val‖ ≤ 2*(a+b) := by
    rw [norm_sub_rev (A k).val]
    dsimp only [A,B]
    rw [left_part,left_part,right_part,right_part,
      add_sub_add_comm,add_sub_add_comm, before_step,before_step,after_step,after_step]
    linarith only [norm_add_le (atCut Fin.val (onsiteAt u) k) (atCut (fun e : Fin (n+1) => e.val+1) (edgePart u) k),
      norm_add_le (atCut Fin.val (onsiteAt u) k) (atCut Fin.val (edgePart u) k),hs k,hl k,hr k]
  obtain ⟨i,hi⟩ := moving_cut_cover H A B (leftSites n) (rightSites n) (add_nonneg ha hb)
    (by rw [he₀,h₀,(zero_edges _).1,zero_add])
    (by rw [heN,hN,(zero_edges _).2,add_zero])
    (fun j _ => by
      change ‖((A j).val+(B j).val)-H.val‖ ≤ b
      rw [norm_sub_rev]
      change ‖pathHamiltonian u-((part u (leftSites n j)).val+(part u (rightSites n j)).val)‖ ≤ b
      rw [se j]
      exact hl j)
    (fun j _ => ⟨disjoint_left.mpr (fun _ h₁ h₂ => (mem_filter.mp h₁).2.not_ge (mem_filter.mp h₂).2),
      packet_supported _ _,packet_supported _ _⟩) (fun j _ => step j) hy
  exact ⟨i,by linarith only [hi]⟩

#print axioms path_energy_mesh
end
end GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
