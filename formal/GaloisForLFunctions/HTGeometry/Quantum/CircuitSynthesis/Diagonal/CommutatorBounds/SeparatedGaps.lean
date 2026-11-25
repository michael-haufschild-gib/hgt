import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.CommutatorBounds.SchurRows
import GaloisForLFunctions.HTGeometry.SeparatedPointsInverseSquarePacking

/-! # A dimension-free inverse commutator bound for real separated energies -/

open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.CommutatorBounds
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

private def inverseGap (d : I→ℝ) : Matrix I I ℂ :=
  Matrix.of fun i j => ((d i:ℂ)-(d j:ℂ))⁻¹

private theorem inverseGap_row (d : I→ℝ) {g : ℝ} (hg : 0<g)
    (hsep : ∀ i j, i≠j → g≤|d i-d j|) (i : I) :
    ∑ j, ‖inverseGap d i j‖^2 ≤ (sqrt packConstant/g)^2 := by
  classical
  let S := Finset.univ.erase i
  let P := S.image d
  have hinj : Function.Injective d := by
    intro a b he
    by_contra hab
    have hh := hsep a b hab
    rw [he,sub_self,abs_zero] at hh
    exact hg.not_ge hh
  have hp (a : ℝ) (ha : a∈P) (b : ℝ) (hb : b∈P) (hab : a≠b) : g≤|a-b| := by
    obtain ⟨j,_,rfl⟩ := mem_image.mp ha
    obtain ⟨l,_,rfl⟩ := mem_image.mp hb
    exact hsep j l (fun h => hab (congrArg d h))
  have hf (a : ℝ) (ha : a∈P) : g≤‖(d i:ℂ)-(a:ℂ)‖ := by
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact hsep i j (ne_of_mem_erase hj).symm
  have hh := sum_inv_sq_le_of_separated hg P hp (d i) hf
  rw [show P=S.image d from rfl,sum_image (fun _ _ _ _ he => hinj he)] at hh
  rw [←sum_erase_add _ _ (mem_univ i)]
  simp only [inverseGap,Matrix.of_apply,sub_self,inv_zero,norm_zero,zero_pow (by decide : 2≠0),add_zero]
  rw [div_pow,sq_sqrt packConstant_pos.le]
  simpa only [S,norm_inv,inv_pow,one_div] using hh

/-- The off-diagonal part is the Schur product of the commutator with
the reciprocal energy differences. Real-line spacing bounds its norm
with an absolute constant, uniformly in dimension. -/
theorem offDiagonal_le_commutator (d : I→ℝ) {g : ℝ} (hg : 0<g)
    (hsep : ∀ i j, i≠j → g≤|d i-d j|) (U : Matrix I I ℂ) :
    let Z := Matrix.diagonal fun i => (d i:ℂ)
    ‖U-Matrix.diagonal (fun i => U i i)‖ ≤ sqrt packConstant/g*‖Z*U-U*Z‖ := by
  intro Z
  let C := Z*U-U*Z
  have he : (Matrix.of fun i j => inverseGap d i j*C i j)=U-Matrix.diagonal (fun i => U i i) := by
    ext i j
    simp only [Matrix.of_apply,inverseGap,C,Z,Matrix.sub_apply,diagonal_mul,mul_diagonal]
    by_cases h : i=j
    · subst j; simp
    · rw [diagonal_apply_ne _ h,sub_zero]
      have hne : (d i:ℂ)-(d j:ℂ)≠0 := sub_ne_zero.mpr fun eq => by
        have hd := Complex.ofReal_injective eq
        have hh := hsep i j h
        rw [hd,sub_self,abs_zero] at hh
        exact hg.not_ge hh
      rw [show (d i:ℂ)*U i j-U i j*(d j:ℂ)=((d i:ℂ)-(d j:ℂ))*U i j by ring,
        ←mul_assoc,inv_mul_cancel₀ hne,one_mul]
  rw [←he]
  exact norm_schur_of_rows _ C (div_nonneg (sqrt_nonneg _) hg.le) (inverseGap_row d hg hsep)

#print axioms offDiagonal_le_commutator
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.CommutatorBounds
