import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Transversals.Columns
import GaloisForLFunctions.HTGeometry.CauchyBinet

/-! # Squared transversal minor weights of a row isometry -/

open Matrix Finset Equiv Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
noncomputable section

private theorem sum_minors {q n : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (hA : A*A.conjTranspose=1) :
    (∑ k : Fin q → Fin n, ‖(A.submatrix id k).det‖^2)=(q.factorial:ℝ) := by
  have hh := GaloisForLFunctions.factorial_mul_det_mul A A.conjTranspose
  rw [hA,Matrix.det_one,mul_one] at hh
  have he (k : Fin q → Fin n) :
      (A.submatrix id k).det*(A.conjTranspose.submatrix k id).det=((‖(A.submatrix id k).det‖^2:ℝ):ℂ) := by
    change _*(A.submatrix id k).conjTranspose.det=_
    rw [Matrix.det_conjTranspose,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  simp_rw [he] at hh
  simpa only [Complex.re_sum,Complex.ofReal_re,Complex.natCast_re] using congrArg Complex.re hh.symm

private theorem fin_transversal_mass {q n : ℕ} (A : Matrix (Fin q) (Fin n) ℂ)
    (hA : A*A.conjTranspose=1) (f : Fin q × Bool ↪ Fin n) :
    (∑ x : Fin q → Bool, ‖transversalMinor A f x‖^2)≤1 := by
  let g (v : (Fin q → Bool) × Perm (Fin q)) (j : Fin q) := f (v.2 j,v.1 (v.2 j))
  have hg : Function.Injective g := by
    intro u v hh
    have hp (j : Fin q) : (u.2 j,u.1 (u.2 j))=(v.2 j,v.1 (v.2 j)) :=
      f.injective (congrFun hh j)
    have hs : u.2=v.2 := Equiv.ext (fun j => congrArg Prod.fst (hp j))
    refine Prod.ext (funext fun i => ?_) hs
    obtain ⟨j,rfl⟩ := u.2.surjective i
    exact (congrArg Prod.snd (hp j)).trans (congrArg v.1 (congrFun (congrArg DFunLike.coe hs.symm) j))
  let w (k : Fin q → Fin n) := ‖(A.submatrix id k).det‖^2
  have he (v : (Fin q → Bool) × Perm (Fin q)) : w (g v)=‖transversalMinor A f v.1‖^2 := by
    let M := A.submatrix id (fun i => f (i,v.1 i))
    change ‖(M.submatrix id v.2).det‖^2=‖M.det‖^2
    rw [det_permute',norm_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign v.2) with hs|hs <;> simp [hs]
  let emb := Function.Embedding.mk g hg
  have hh := sum_le_sum_of_subset_of_nonneg (f:=w) (subset_univ (univ.map emb))
    (fun i _ _ => sq_nonneg ‖(A.submatrix id i).det‖)
  change _≤∑ k, ‖(A.submatrix id k).det‖^2 at hh
  rw [sum_minors A hA,sum_map] at hh
  simp only [emb,Function.Embedding.coeFn_mk,he,Fintype.sum_prod_type,sum_const,card_univ,
    Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul,←mul_sum] at hh
  apply le_of_mul_le_mul_left _ (show (0:ℝ)<q.factorial by exact_mod_cast Nat.factorial_pos q)
  simpa only [mul_one] using hh

/-- Cauchy–Binet counts the full set of maximal minors. Each transversal
occurs with all column orderings and the other squared minors are nonnegative. -/
theorem transversal_mass {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}
    (A : Matrix (Fin q) I ℂ) (hA : A*A.conjTranspose=1) (f : Fin q × Bool ↪ I) :
    (∑ x : Fin q → Bool, ‖transversalMinor A f x‖^2)≤1 := by
  let e := Fintype.equivFin I
  let U := A.submatrix id e.symm
  have hu : U*U.conjTranspose=1 := by
    ext i j
    have h := congrFun (congrFun hA i) j
    rw [Matrix.mul_apply] at h ⊢
    exact (Equiv.sum_comp e.symm (fun k => A i k*A.conjTranspose k j)).trans h
  have h := fin_transversal_mass U hu (f.trans e.toEmbedding)
  have hw (x : Fin q → Bool) :
      transversalMinor U (f.trans e.toEmbedding) x=transversalMinor A f x := by
    unfold transversalMinor
    apply congrArg Matrix.det
    ext i j
    change A i (e.symm (e (f (j,x j))))=A i (f (j,x j))
    rw [e.symm_apply_apply]
  simpa only [hw] using h

#print axioms transversal_mass
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
