import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! # Transversal minors for disjoint pairs of energy indices -/

open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}

/-- Common positive coordinate of a normalized two-level superposition. -/
def halfAmplitude : ℝ := Real.sqrt (1/2)

private theorem half_square : halfAmplitude*halfAmplitude=1/2 := by
  rw [←sq,halfAmplitude,Real.sq_sqrt (by norm_num)]

/-- Each column is supported on its two assigned energy levels. -/
def pairColumns (f : Fin q × Bool ↪ I) : Matrix I (Fin q) ℂ := fun i j =>
  (if i=f (j,false) then (halfAmplitude:ℂ) else 0)+
  (if i=f (j,true) then (halfAmplitude:ℂ) else 0)

private theorem on_column (f : Fin q × Bool ↪ I) (a : I → ℂ) (j : Fin q) :
    (∑ i, a i*pairColumns f i j)=(halfAmplitude:ℂ)*(a (f (j,false))+a (f (j,true))) := by
  simp [pairColumns,mul_add,Finset.sum_add_distrib,mul_ite]
  ring

/-- Disjoint supports make the normalized columns orthonormal. -/
theorem columns_isometry (f : Fin q × Bool ↪ I) :
    (pairColumns f).conjTranspose*pairColumns f=1 := by
  ext i j
  rw [Matrix.mul_apply,on_column]
  by_cases h : i=j
  · subst j
    have h₀ : f (i,false)≠f (i,true) := fun he => Bool.false_ne_true (congrArg Prod.snd (f.injective he))
    simp only [Matrix.conjTranspose_apply,pairColumns,if_neg h₀,if_neg (Ne.symm h₀),eq_self,if_true,add_zero,zero_add,
      Matrix.one_apply_eq,Complex.star_def,Complex.conj_ofReal]
    have hs := congrArg Complex.ofReal half_square
    push_cast at hs
    linear_combination 2*hs
  · simp [Matrix.conjTranspose_apply,pairColumns,f.injective.eq_iff,h,Ne.symm h]

/-- Coefficient of a choice of exactly one level from each pair. -/
def transversalMinor (A : Matrix (Fin q) I ℂ) (f : Fin q × Bool ↪ I) (x : Fin q → Bool) : ℂ :=
  (A.submatrix id (fun j => f (j,x j))).det

/-- Multilinearity expands the compressed determinant over exactly the
transversals. No choice contains both levels of a pair. -/
theorem paired_expansion (A : Matrix (Fin q) I ℂ) (f : Fin q × Bool ↪ I) (p : I → ℂ) :
    (A*diagonal p*pairColumns f).det=(halfAmplitude:ℂ)^q*
      ∑ x : Fin q → Bool, transversalMinor A f x*∏ j, p (f (j,x j)) := by
  let M : Matrix (Fin q) (Fin q) ℂ := fun i j => ∑ b : Bool, A i (f (j,b))*p (f (j,b))
  have he : A*diagonal p*pairColumns f=(halfAmplitude:ℂ) • M := by
    ext i j
    rw [Matrix.mul_apply,on_column]
    simp only [Matrix.mul_diagonal,Matrix.smul_apply,smul_eq_mul,M,Fintype.sum_bool]
    ring
  rw [he,Matrix.det_smul,Fintype.card_fin]
  congr 1
  rw [Matrix.det_apply']
  simp only [M,prod_univ_sum,Fintype.piFinset_univ,mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ => ?_
  simp only [transversalMinor,Matrix.det_apply',Finset.sum_mul,Matrix.submatrix_apply,id_eq,prod_mul_distrib]
  exact sum_congr rfl fun _ _ => (mul_assoc ..).symm

#print axioms paired_expansion
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
