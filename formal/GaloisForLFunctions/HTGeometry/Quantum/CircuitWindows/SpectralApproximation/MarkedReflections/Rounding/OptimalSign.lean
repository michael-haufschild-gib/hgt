import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.Rounding.SignedPhases
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # Below √2 a real spectral sign fits every reflection as well as arbitrary phases -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections.Rounding
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where

private theorem magnitude_interval (V : unitaryGroup I ℂ) (i : I) (f : I → ℂ) (hf : ∀ j, ‖f j‖=1) :
    reading V i (magnitude f) ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · change 0≤((star V.val*diagonal _*V.val) i i).re
    rw [column_mean]
    exact sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (by change 0≤|(f j).re|; exact abs_nonneg _)
  · apply (reading_le_norm V i (magnitude f)).trans
    rw [magnitude,Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_abs]
    exact (Complex.abs_re_le_norm _).trans_eq (hf j)

/-- Allow all complex phases first. If their error against a self-adjoint
unitary is strictly below √2, assigning their half-plane signs can only
decrease that error. Eigenvectors of the anticommutator supply the tests. -/
theorem round_reflection (W : unitaryGroup I ℂ) (hW : star W.val=W.val) (f : I → ℂ)
    (hf : ∀ j, ‖f j‖=1) (hsmall : ‖diagonal f-W.val‖^2<2) :
    ‖(signs f).val-W.val‖ ≤ ‖diagonal f-W.val‖ := by
  let S := (signs f).val
  let A := W.val*S+S*W.val
  let e := ‖diagonal f-W.val‖
  have hA : A.IsHermitian := by
    change star (W.val*S+S*W.val)=_
    rw [star_add,star_mul,star_mul,hW,show star S=S from star_signs f,add_comm]
  let V := hA.eigenvectorUnitary
  let d := hA.eigenvalues
  let D := diagonal (fun j => (d j:ℂ))
  have hs : A=V.val*D*star V.val := isHermitian_eq_conj_diagonal hA
  have hleft : star V.val*A=D*star V.val := by
    rw [hs,←mul_assoc,←mul_assoc,(Unitary.mem_iff.mp V.property).1,one_mul]
  have htest (i : I) : 2-d i≤e^2 := by
    let m := reading V i (magnitude f)
    have hm := magnitude_interval V i f hf
    have he : reading V i (A*magnitude f)=d i*m := by
      change ((star V.val*(A*magnitude f)*V.val) i i).re=_
      rw [←mul_assoc (star V.val) A,hleft,mul_assoc D,mul_assoc D,Matrix.diagonal_mul,Complex.re_ofReal_mul]
    have ht := signed_gram W.val W.property hW f hf V i
    change 2-reading V i (A*magnitude f)≤e^2 at ht
    rw [he] at ht
    have hd : 0≤d i := by
      by_contra! hh
      have hneg := mul_nonpos_of_nonpos_of_nonneg hh.le hm.1
      change e^2<2 at hsmall
      linarith only [ht,hneg,hsmall]
    have hu : d i*m≤d i := mul_le_of_le_one_right hd hm.2
    linarith only [hu,ht]
  have hG : star (S-W.val)*(S-W.val)=1+1-A := by
    have hS := (Unitary.mem_iff.mp (signs f).property).1
    have hw := (Unitary.mem_iff.mp W.property).1
    rw [star_sub,sub_mul,mul_sub,mul_sub,show star S*S=1 from hS,hw,hW,show star S=S from star_signs f]
    dsimp only [A]
    abel
  have hcon : star V.val*(1+1-A)*V.val=diagonal (fun i => ((2-d i:ℝ):ℂ)) := by
    rw [mul_sub,mul_add,mul_one,hleft,sub_mul,add_mul,(Unitary.mem_iff.mp V.property).1,
      mul_assoc,(Unitary.mem_iff.mp V.property).1,mul_one]
    ext i j
    by_cases h : i=j
    · subst j; simp [D]; ring
    · simp [D,h]
  have hA₂ : ‖A‖≤2 := by
    have h₁ := CStarRing.norm_of_mem_unitary (mul_mem W.property (signs f).property)
    have h₂ := CStarRing.norm_of_mem_unitary (mul_mem (signs f).property W.property)
    exact (norm_add_le _ _).trans (by change ‖W.val*S‖+‖S*W.val‖≤2; linarith only [h₁,h₂])
  have hbound (i : I) : d i≤2 := by
    have he : reading V i A=d i := by
      change ((star V.val*A*V.val) i i).re=_
      rw [hleft,mul_assoc,(Unitary.mem_iff.mp V.property).1,mul_one]
      simp [D]
    exact he ▸ (reading_le_norm V i A).trans hA₂
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [sq,←CStarRing.norm_star_mul_self,hG]
  have hunit := l2_opNorm_unitary_conj_eq (Unitary.star_mem V.property) (1+1-A)
  rw [star_star,hcon] at hunit
  rw [←hunit,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg e)).mpr
  intro i
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hbound i))] using htest i

#print axioms round_reflection
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections.Rounding
