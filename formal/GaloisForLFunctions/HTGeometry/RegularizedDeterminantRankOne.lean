import GaloisForLFunctions.HTGeometry.RegularizedDeterminantMultiplication
import GaloisForLFunctions.HTGeometry.FiniteRankDeterminant
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne

/-! # Exact entire determinant of a rank-one feedback perturbation -/

noncomputable section
open HilbertSchmidt ContinuousLinearMap InnerProductSpace

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

theorem entireDet2_eq_of_powerTrace_eq
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (K : ι × ι → ℂ) (L : κ × κ → ℂ)
    (h : ∀ n : ℕ, (∑' i, hsPow K (n + 1) (i, i)) =
      ∑' j, hsPow L (n + 1) (j, j)) : entireDet2 K = entireDet2 L := by
  have he : fredholmExp K = fredholmExp L := by
    funext z
    unfold fredholmExp
    apply tsum_congr
    intro n
    rw [h n]
  have hf : fredholmDet K = fredholmDet L := by
    funext z
    rw [fredholmDet, fredholmDet, he]
  unfold entireDet2 detCoeff
  rw [hf]

theorem entireDet2_unit_diag (c z : ℂ) :
    entireDet2 (diagMul (fun _ : Unit => c)) z = (1 - z * c) * Complex.exp (z * c) := by
  letI : Unique ↥(Finset.univ : Finset Unit) :=
    { default := ⟨(), Finset.mem_univ _⟩
      uniq := fun x => Subtype.ext (Subsingleton.elim _ _) }
  have hK : IsHS (diagMul (fun _ : Unit => c)) :=
    isHS_diagMul _ Finset.univ (by simp)
  have hs : ∀ p : Unit × Unit, p ∉ (Finset.univ : Finset Unit) ×ˢ Finset.univ →
      diagMul (fun _ : Unit => c) p = 0 := by simp
  rw [entireDet2_eq_finiteDet2_of_support hK hs]
  simp [finiteDet2, Matrix.det_unique, Matrix.trace, blockMatrix, diagMul, sub_eq_add_neg]

section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem rankOne_pow_succ (x y : H) (n : ℕ) :
    (rankOne ℂ x y) ^ (n + 1) = (inner ℂ y x) ^ n • rankOne ℂ x y := by
  have hR : (rankOne ℂ x y) * (rankOne ℂ x y) = inner ℂ y x • rankOne ℂ x y :=
    rankOne_comp_rankOne x y x y
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (rankOne ℂ x y) (n + 1), ih, smul_mul_assoc, hR, smul_smul, pow_succ]

theorem opTrace_rankOne_pow (x y : H) (n : ℕ) :
    opTrace ((rankOne ℂ x y) ^ (n + 1)) = (inner ℂ y x) ^ (n + 1) := by
  rw [rankOne_pow_succ, opTrace_smul', opTrace_rankOne_eq, pow_succ]

/-- This is the global determinant, including the possible rank-one zero. -/
theorem det2Op_rankOne {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H) (x y : H) :
    det2Op b (rankOne ℂ x y) = (1 + inner ℂ y x) * Complex.exp (-inner ℂ y x) := by
  have he : entireDet2 (coordMatrix b (rankOne ℂ x y)) =
      entireDet2 (diagMul (fun _ : Unit => inner ℂ y x)) := by
    apply entireDet2_eq_of_powerTrace_eq
    intro n
    rw [tsum_diag_hsPow_coordMatrix b (isHilbertSchmidt_rankOne x y),
      opTrace_rankOne_pow]
    simp [hsPow_diagMul, diagMul]
  rw [det2Op, he, entireDet2_unit_diag]
  simp

/-- A supplied response vector gives the exact rank-one update even at singular parameters.
No inverse of `I+A` is assumed. -/
theorem det2Op_rankOne_update {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (u x y : H) (hu : u + A u = x) :
    det2Op b (A + rankOne ℂ x y) =
      det2Op b A * (1 + inner ℂ y u) * Complex.exp (-inner ℂ y x) := by
  have he : A + rankOne ℂ u y + A ∘L rankOne ℂ u y = A + rankOne ℂ x y := by
    ext v
    simp only [add_apply, ContinuousLinearMap.comp_apply, rankOne_apply, map_smul]
    rw [add_assoc, ← smul_add, hu]
  have h := det2Op_multiplication b hA (isHilbertSchmidt_rankOne u y)
  rw [he, det2Op_rankOne, comp_rankOne, opTrace_rankOne_eq] at h
  rw [h]
  have hi : inner ℂ y u + inner ℂ y (A u) = inner ℂ y x := by
    rw [← inner_add_right, hu]
  calc det2Op b A * ((1 + inner ℂ y u) * Complex.exp (-inner ℂ y u)) *
        Complex.exp (-inner ℂ y (A u)) =
      det2Op b A * (1 + inner ℂ y u) *
        (Complex.exp (-inner ℂ y u) * Complex.exp (-inner ℂ y (A u))) := by ring
    _ = _ := by rw [← Complex.exp_add, ← neg_add, hi]

end Operators
end GaloisForLFunctions.HTGeometry
