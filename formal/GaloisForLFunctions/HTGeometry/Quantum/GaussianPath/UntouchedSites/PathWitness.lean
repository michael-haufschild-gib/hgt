import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.SpinRelations
import GaloisForLFunctions.HTGeometry.PathShellDelayFloor

/-! # A nearest-neighbor path distinguished by a probe on any one site -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.UntouchedSites
noncomputable section
variable {n : ℕ}

/-- Oriented XY and YZ exchange on each bond. -/
def detectingShell (n : ℕ) : PathShell n :=
  WithLp.toLp 2 fun l => match l with
    | .inl _ => 0
    | .inr (_,ab) => if ab=(0,1) then 1 else if ab=(1,2) then 1 else 0

private def bond (e : Fin (n+1)) (a b : Fin 3) : SpinMatrix (Fin (n+2)) :=
  finitePauliMatrix (pairLabel e.castSucc e.succ a b)

private theorem witness_sum : pathHamiltonian (detectingShell n) =
    ∑ e : Fin (n+1), (bond e 0 1 + bond e 1 2) := by
  have ho : onsitePart (detectingShell n)=0 := by simp [onsitePart,detectingShell]
  rw [pathHamiltonian,ho,zero_add]
  apply Finset.sum_congr rfl
  intro e _
  simp only [edgePart,detectingShell]
  classical
  have hfun (ab : Fin 3 × Fin 3) :
      (((if ab=(0,1) then 1 else if ab=(1,2) then 1 else 0 : ℝ):ℂ)) • finitePauliMatrix (couplingWord e ab) =
        (if ab=(0,1) then bond e 0 1 else 0)+(if ab=(1,2) then bond e 1 2 else 0) := by
    by_cases h : ab=(0,1)
    · subst ab; simp [bond]; rfl
    · by_cases h' : ab=(1,2)
      · subst ab; simp [bond]; rfl
      · simp [h,h']
  simp only [hfun,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]

private def left (v : Fin (n+2)) (a : Fin 3) : SpinMatrix (Fin (n+2)) :=
  ∑ e : Fin (n+1), if e.succ=v then spin e.castSucc a else 0
private def right (v : Fin (n+2)) (a : Fin 3) : SpinMatrix (Fin (n+2)) :=
  ∑ e : Fin (n+1), if e.castSucc=v then spin e.succ a else 0

private theorem left_at (e : Fin (n+1)) (a : Fin 3) : left e.succ a = spin e.castSucc a := by
  simp [left,Fin.succ_inj]
private theorem right_at (e : Fin (n+1)) (a : Fin 3) : right e.castSucc a = spin e.succ a := by
  simp [right,Fin.castSucc_inj]

private theorem split_bond (e : Fin (n+1)) (v : Fin (n+2)) (q a b : Fin 3) :
    selectAxis v q (bond e a b) = spin v q *
      ((if e.castSucc=v ∧ q=a then spin e.succ b else 0) +
       (if e.succ=v ∧ q=b then spin e.castSucc a else 0)) := by
  have hne : e.castSucc ≠ e.succ := fun h => by have := congrArg Fin.val h; simp at this
  change selectAxis _ _ (finitePauliMatrix _) = _
  rw [selectAxis_word]
  by_cases h : v=e.castSucc
  · subst v
    rw [show pairLabel e.castSucc e.succ a b e.castSucc = some a by simp [pairLabel]]
    by_cases eq : q=a
    · subst q; simp [hne.symm,spin_pair hne]
    · simp [eq,Ne.symm eq,hne.symm]
  · by_cases h' : v=e.succ
    · subst v
      rw [show pairLabel e.castSucc e.succ a b e.succ = some b by simp [pairLabel,h]]
      by_cases eq : q=b
      · subst q
        simpa [hne,spin_pair hne] using (spin_comm hne a b).eq
      · simp [hne,eq,Ne.symm eq]
    · rw [show pairLabel e.castSucc e.succ a b v=none by simp [pairLabel,h,h']]
      simp [Ne.symm h,Ne.symm h']

/-- The local X,Y,Z coefficients are respectively Y on the right,
X on the left plus Z on the right, and Y on the left. -/
private theorem local_fields (v : Fin (n+2)) {U : SpinMatrix (Fin (n+2))}
    (hH : Commute U (pathHamiltonian (detectingShell n))) (hs : ∀ a, Commute U (spin v a)) :
    Commute U (right v 1) ∧ Commute U (left v 0 + right v 2) ∧ Commute U (left v 1) := by
  have extract (a : Fin 3) (B : SpinMatrix (Fin (n+2)))
      (he : selectAxis v a (pathHamiltonian (detectingShell n)) = spin v a*B) : Commute U B := by
    have hh := (hs a).mul_right (commute_selectAxis hs hH a)
    rwa [he,←mul_assoc,spin_sq,one_mul] at hh
  have he (q : Fin 3) := congrArg (selectAxis v q) (witness_sum (n := n))
  simp only [map_sum,map_add,split_bond] at he
  refine ⟨extract 0 _ ?_,extract 1 _ ?_,extract 2 _ ?_⟩
  · simpa [right,Matrix.mul_sum] using he 0
  · simpa [left,right,Matrix.mul_add,Matrix.mul_sum,Finset.sum_add_distrib] using he 1
  · simpa [left,Matrix.mul_sum] using he 2

private theorem commute_other_neighbor (e : Fin (n+1)) (a b : Fin 3) :
    Commute (spin e.succ b) (left e.castSucc a) ∧ Commute (right e.succ b) (spin e.castSucc a) := by
  constructor
  · apply Commute.sum_right
    intro k _
    split
    · next h =>
        apply spin_comm
        intro he
        have hh := congrArg Fin.val h
        have hh' := congrArg Fin.val he
        simp only [Fin.val_castSucc,Fin.val_succ] at hh hh'
        omega
    · exact Commute.zero_right _
  · apply Commute.sum_left
    intro k _
    split
    · next h =>
        apply spin_comm
        intro he
        have hh := congrArg Fin.val h
        have hh' := congrArg Fin.val he
        simp only [Fin.val_castSucc,Fin.val_succ] at hh hh'
        omega
    · exact Commute.zero_left _

private theorem undo_scale {S : Type*} [Fintype S] [DecidableEq S] {U X : SpinMatrix S}
    (h : Commute U ((2*Complex.I) • X)) : Commute U X := by
  simpa only [smul_smul,inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) Complex.I_ne_zero),one_smul] using
    h.smul_right ((2*Complex.I)⁻¹ : ℂ)

private theorem move_right (e : Fin (n+1)) {U : SpinMatrix (Fin (n+2))}
    (hH : Commute U (pathHamiltonian (detectingShell n)))
    (h : ∀ a, Commute U (spin e.castSucc a)) : ∀ a, Commute U (spin e.succ a) := by
  obtain ⟨hy,hm,_⟩ := local_fields e.castSucc hH h
  rw [right_at] at hy hm
  have hb := (hy.mul_right hm).sub_right (hm.mul_right hy)
  have hs := (commute_other_neighbor e 0 1).1.eq
  rw [mul_add,add_mul,hs] at hb
  have he (A B C : SpinMatrix (Fin (n+2))) : A+B-(A+C)=B-C := by abel
  rw [he,show spin e.succ 1*spin e.succ 2-spin e.succ 2*spin e.succ 1 =
    (2*Complex.I) • spin e.succ 0 from spin_bracket _ 1] at hb
  have hx := undo_scale hb
  intro a
  rcases fin3_eq_cases a with rfl|rfl|rfl
  · exact hx
  · exact hy
  · exact commute_third 0 hx hy

private theorem move_left (e : Fin (n+1)) {U : SpinMatrix (Fin (n+2))}
    (hH : Commute U (pathHamiltonian (detectingShell n)))
    (h : ∀ a, Commute U (spin e.succ a)) : ∀ a, Commute U (spin e.castSucc a) := by
  obtain ⟨_,hm,hy⟩ := local_fields e.succ hH h
  rw [left_at] at hy hm
  have hb := (hm.mul_right hy).sub_right (hy.mul_right hm)
  rw [add_mul,mul_add,(commute_other_neighbor e 1 2).2.eq] at hb
  have he (A B C : SpinMatrix (Fin (n+2))) : A+B-(C+B)=A-C := by abel
  rw [he,show spin e.castSucc 0*spin e.castSucc 1-spin e.castSucc 1*spin e.castSucc 0 =
    (2*Complex.I) • spin e.castSucc 2 from spin_bracket _ 0] at hb
  have hz := undo_scale hb
  intro a
  rcases fin3_eq_cases a with rfl|rfl|rfl
  · exact commute_third 1 hy hz
  · exact hy
  · exact hz

/-- One site probe algebra distinguishes all matrices commuting with this
single translation-invariant path Hamiltonian. -/
theorem witness_scalar (v : Fin (n+2)) (r : Fin (n+2) → Bool) (U : SpinMatrix (Fin (n+2)))
    (hH : Commute U (pathHamiltonian (detectingShell n))) (h : ∀ a, Commute U (spin v a)) :
    U = U r r • (1 : SpinMatrix (Fin (n+2))) := by
  let K (j : Fin (n+2)) := ∀ a, Commute U (spin j a)
  have eqn (e : Fin (n+1)) : K e.castSucc ↔ K e.succ := ⟨move_right e hH,move_left e hH⟩
  have hbase (j : Fin (n+2)) : K 0 ↔ K j := by
    induction j using Fin.induction with
    | zero => rfl
    | succ e ih => exact ih.trans (eqn e)
  exact scalar_of_all_sites r fun j => (hbase j).mp ((hbase v).mpr h)

#print axioms witness_scalar
end
end GaloisForLFunctions.HTGeometry.UntouchedSites
