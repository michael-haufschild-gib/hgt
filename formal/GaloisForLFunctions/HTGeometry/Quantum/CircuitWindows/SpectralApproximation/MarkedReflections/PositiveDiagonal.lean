import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryDiagonal
import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-! # A reflection with nonnegative diagonal misses every spectral phase -/
open Matrix Complex Finset
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
open StaticLocalLaboratoryComplexityGrowthLaw
open private diagonal_overlap from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryDiagonal
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
local instance : CStarAlgebra (Mat I) where

/-- The diagonal of a conjugated phase has real part equal to the
column-weighted average of the real parts of the phases. -/
theorem column_mean (V : Mat I) (f : I → ℂ) (j : I) :
    ((star V*diagonal f*V) j j).re=∑ i, ‖V i j‖^2*(f i).re := by
  rw [Matrix.mul_apply,Complex.re_sum]
  apply sum_congr rfl
  intro i _
  rw [Matrix.mul_diagonal,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]
  change (conj (V i j)*f i*V i j).re=_
  rw [show conj (V i j)*f i*V i j=((‖V i j‖^2:ℝ):ℂ)*f i by
    rw [Complex.ofReal_pow,←Complex.conj_mul']; ring,Complex.re_ofReal_mul]

/-- If no diagonal coordinate of a reflection favors its negative
eigenspace, every diagonal unitary has operator distance at least √2.
The marked eigenvector can lie anywhere in the register. -/
theorem minority_floor [Nonempty I] (V : Matrix.unitaryGroup I ℂ) (g : I → ℂ) (hg : ∀ j, ‖g j‖=1)
    (j : I) (hj : g j= -1)
    (hpos : ∀ i, ∃ w : ℝ, 0≤w ∧ ((V:Mat I)*diagonal g*star (V:Mat I)) i i=(w:ℂ))
    (f : I → ℂ) (hf : ∀ i, ‖f i‖=1) :
    Real.sqrt 2 ≤ ‖diagonal f-(V:Mat I)*diagonal g*star (V:Mat I)‖ := by
  let W := (V:Mat I)*diagonal g*star (V:Mat I)
  let L := star (V:Mat I)*diagonal f*(V:Mat I)
  let d := ‖diagonal f-W‖
  have hW : W∈unitary (Mat I) :=
    mul_mem (mul_mem V.property (mem_unitaryGroup_diagonal_general g hg)) (Unitary.star_mem V.property)
  have hL : L∈unitary (Mat I) :=
    mul_mem (mul_mem (Unitary.star_mem V.property) (mem_unitaryGroup_diagonal_general f hf)) V.property
  by_contra! h
  have hs : d^2<2 := by
    change d < Real.sqrt 2 at h
    nlinarith only [mul_pos (sub_pos.mpr h) (add_pos_of_pos_of_nonneg
      (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)) (norm_nonneg (diagonal f-W))),
      Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have hsign (i : I) : 0 ≤ (f i).re := by
    obtain ⟨w,hw,he⟩ := hpos i
    have hb := diagonal_overlap f hf W hW i
    change 2-2*(f i*conj (W i i)).re ≤ d^2 at hb
    change W i i=(w:ℂ) at he
    rw [he,Complex.conj_ofReal,mul_comm (f i) (w:ℂ),Complex.re_ofReal_mul] at hb
    by_contra! hn
    linarith only [hb,hs,mul_nonpos_of_nonneg_of_nonpos hw hn.le]
  have hconj : (V:Mat I)*L*star (V:Mat I)=diagonal f := by
    simp only [L,←mul_assoc,(Unitary.mem_iff.mp V.property).2,one_mul]
    rw [mul_assoc,(Unitary.mem_iff.mp V.property).2,mul_one]
  have he : ‖diagonal g-L‖=d := by
    rw [←l2_opNorm_unitary_conj_eq V.property,Matrix.mul_sub,Matrix.sub_mul,hconj]
    exact norm_sub_rev _ _
  have hb := diagonal_overlap g hg L hL j
  rw [he,hj,neg_one_mul,Complex.neg_re,Complex.conj_re] at hb
  have hn : 0≤(L j j).re := by
    rw [show (L j j).re=∑ i, ‖(V:Mat I) i j‖^2*(f i).re from column_mean _ _ _]
    exact sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hsign i))
  linarith only [hb,hs,hn]

#print axioms minority_floor
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
