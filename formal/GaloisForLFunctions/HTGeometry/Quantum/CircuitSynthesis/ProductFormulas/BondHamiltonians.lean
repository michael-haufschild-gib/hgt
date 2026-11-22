import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.PathFactors
import GaloisForLFunctions.HTGeometry.HaferkampTerminalPhaseAnalytic
import GaloisForLFunctions.HTGeometry.PauliCharacterProjectorExtraction

/-! # Decomposing a nearest-neighbor path into one four-dimensional generator per bond -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BondProducts
noncomputable section
abbrev LocalMatrix := Matrix (Bool × Bool) (Bool × Bool) ℂ
variable {n : ℕ}

theorem endpoints_ne (e : Fin (n+1)) : e.castSucc ≠ e.succ := by
  intro h
  have hh := congrArg Fin.val h
  simp at hh

private def siteBond (v : Fin (n+2)) : Fin (n+1) :=
  if h : v.val<n+1 then ⟨v.val,h⟩ else Fin.last n

private theorem site_endpoint (v : Fin (n+2)) :
    (siteBond v).castSucc=v ∨ (siteBond v).succ=v := by
  by_cases h : v.val<n+1
  · exact Or.inl (Fin.ext (by simp [siteBond,h]))
  · right
    apply Fin.ext
    simp only [siteBond,dif_neg h,Fin.val_succ,Fin.val_last]
    omega

private def termBond : PathLabel n → Fin (n+1)
  | .inl (v,_) => siteBond v
  | .inr (e,_) => e

private theorem word_off_bond (l : PathLabel n) (i : Fin (n+2))
    (ha : i≠(termBond l).castSucc) (hb : i≠(termBond l).succ) : pathWord l i=none := by
  rcases l with ⟨v,q⟩ | ⟨e,p⟩
  · have hn : i≠v := by
      rintro rfl
      rcases site_endpoint v with h | h
      · exact ha h.symm
      · exact hb h.symm
    simp [pathWord,onsiteWord,hn]
  · simp [pathWord,couplingWord,show i≠e.castSucc from ha,show i≠e.succ from hb]

private theorem word_lift (l : PathLabel n) :
    let e := termBond l
    finitePauliMatrix (pathWord l)=twoQubitLiftMatrix e.castSucc e.succ (endpoints_ne e)
      (boolTwoQubitPauli (pathWord l e.castSucc) (pathWord l e.succ)) := by
  intro e
  let p := pathWord l
  let a := e.castSucc
  let b := e.succ
  let v := splitTwoQubitConfig a b (endpoints_ne e)
  have hrest : twoQubitRestPauliLabel p a b=(fun _ => none) := by
    funext j
    exact word_off_bond l j.val j.2.1 j.2.2
  apply (Matrix.reindexAlgEquiv ℂ ℂ v).injective
  change Matrix.reindex v v (finitePauliMatrix p)=Matrix.reindex v v (twoQubitLiftMatrix a b _ _)
  rw [show Matrix.reindex v v (finitePauliMatrix p)=_ from
    reindex_splitTwoQubitConfig_finitePauliMatrix a b (endpoints_ne e) p,hrest,finitePauliMatrix_const_none]
  simp [twoQubitLiftMatrix,v]

/-- Each onsite term belongs to its right bond except at the right
endpoint. Every coupling term belongs to its own bond. -/
theorem exists_bond_hamiltonians (u : PathShell n) :
    ∃ B : Fin (n+1) → selfAdjoint LocalMatrix, pathHamiltonian u =
      ∑ e, twoQubitLiftMatrix e.castSucc e.succ (endpoints_ne e) (B e).val := by
  classical
  let term (e : Fin (n+1)) (l : PathLabel n) : LocalMatrix :=
    ((u l:ℝ):ℂ) • boolTwoQubitPauli (pathWord l e.castSucc) (pathWord l e.succ)
  let B (e : Fin (n+1)) := ∑ l : PathLabel n, if termBond l=e then term e l else 0
  have herm (e : Fin (n+1)) : (B e).IsHermitian := by
    change (∑ l : PathLabel n, if termBond l=e then term e l else 0)ᴴ=_
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro l _
    split
    · simp only [term,Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,
        (boolTwoQubitPauli_isHermitian ..).eq]
    · exact Matrix.conjTranspose_zero
  refine ⟨fun e => ⟨B e,(herm e).isSelfAdjoint⟩,?_⟩
  let L (e : Fin (n+1)) := twoQubitLiftMatrixCLM e.castSucc e.succ (endpoints_ne e)
  have hblock (e : Fin (n+1)) : L e (B e)=∑ l : PathLabel n,
      if termBond l=e then ((u l:ℝ):ℂ) • finitePauliMatrix (pathWord l) else 0 := by
    dsimp only [B]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _
    by_cases he : termBond l=e
    · subst e
      simp only [if_pos rfl,term,map_smul]
      exact congrArg (((u l:ℝ):ℂ) • ·) (word_lift l).symm
    · simp only [if_neg he,map_zero]
  change pathHamiltonian u=∑ e, L e (B e)
  simp only [hblock,Finset.sum_comm (s:=Finset.univ (α:=Fin (n+1))) (t:=Finset.univ (α:=PathLabel n)),
    Finset.sum_ite_eq,Finset.mem_univ,if_true,pathHamiltonian_eq_sum]

end
end GaloisForLFunctions.HTGeometry.BondProducts
