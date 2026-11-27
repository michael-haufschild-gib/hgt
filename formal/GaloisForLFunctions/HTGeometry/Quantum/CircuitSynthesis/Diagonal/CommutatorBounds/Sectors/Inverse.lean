import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.CommutatorBounds.SeparatedGaps

/-! # Inverse commutator restricted to opposite symmetry sectors -/

open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.CommutatorBounds.Sectors
open private inverseGap inverseGap_row from
  GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.CommutatorBounds.SeparatedGaps
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] {J : Type*} [DecidableEq J]

/-- An odd matrix vanishes within each sector. -/
def Across (b : I → J) (A : Matrix I I ℂ) := ∀ i j, b i=b j → A i j=0

/-- An even matrix preserves each sector. -/
def Within (b : I → J) (A : Matrix I I ℂ) := ∀ i j, b i≠b j → A i j=0

/-- Commutation with a diagonal observable forces preservation of its levels. -/
theorem within_of_commute (b : I → ℂ) {E : Matrix I I ℂ} (he : Commute (diagonal b) E) :
    Within b E := by
  intro i j hij
  have h := congrArg (fun A : Matrix I I ℂ => A i j) he.eq
  change (diagonal b*E) i j=(E*diagonal b) i j at h
  rw [diagonal_mul,mul_diagonal] at h
  have hz : (b i-b j)*E i j=0 := by rw [sub_mul,h,mul_comm (E i j),sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hij)

/-- Anticommutation with an invertible diagonal observable kills all
entries within a level. -/
theorem across_of_anticommute (b : I → ℂ) (hb : ∀ i, b i≠0) {V : Matrix I I ℂ}
    (hv : diagonal b*V=-(V*diagonal b)) : Across b V := by
  intro i j hij
  have h := congrArg (fun A : Matrix I I ℂ => A i j) hv
  change (diagonal b*V) i j=(-(V*diagonal b)) i j at h
  rw [Matrix.neg_apply,diagonal_mul,mul_diagonal,hij,mul_comm (V i j)] at h
  have hz : b j*V i j=0 := by linear_combination (1/2:ℂ)*h
  exact (mul_eq_zero.mp hz).resolve_left (hb j)

private def kernel (b : I → J) (d : I → ℝ) : Matrix I I ℂ :=
  Matrix.of fun i j => if b i=b j then 0 else inverseGap d i j

/-- Divide opposite-sector entries by their energy differences. -/
def inverse (b : I → J) (d : I → ℝ) (A : Matrix I I ℂ) : Matrix I I ℂ :=
  Matrix.of fun i j => kernel b d i j*A i j

omit [Fintype I] [DecidableEq I] in
theorem inverse_across (b : I → J) (d : I → ℝ) (A : Matrix I I ℂ) :
    Across b (inverse b d A) := by
  intro i j h
  simp only [inverse,kernel,Matrix.of_apply,if_pos h,zero_mul]

omit [Fintype I] [DecidableEq I] in
theorem inverse_sub (b : I → J) (d : I → ℝ) (A B : Matrix I I ℂ) :
    inverse b d (A-B) = inverse b d A-inverse b d B := by
  ext i j
  simp only [inverse,Matrix.of_apply,Matrix.sub_apply,mul_sub]

/-- Erasing within-sector entries only decreases the squared row sums
of the inverse-gap kernel. -/
theorem norm_inverse_le (b : I → J) (d : I → ℝ) {g : ℝ} (hg : 0<g)
    (hsep : ∀ i j, i≠j → g ≤ |d i-d j|) (A : Matrix I I ℂ) :
    ‖inverse b d A‖ ≤ sqrt packConstant/g*‖A‖ := by
  apply norm_schur_of_rows _ _ (div_nonneg (sqrt_nonneg _) hg.le)
  intro i
  apply le_trans _ (inverseGap_row d hg hsep i)
  apply sum_le_sum
  intro j _
  by_cases h : b i=b j
  · simp only [kernel,Matrix.of_apply,if_pos h,norm_zero,zero_pow (by decide : 2≠0)]
    exact sq_nonneg _
  · simp only [kernel,Matrix.of_apply,if_neg h,le_refl]

/-- On odd data the diagonal commutator is an exact left inverse. -/
theorem commutator_inverse (b : I → J) (d : I → ℝ) (hd : Function.Injective d)
    (A : Matrix I I ℂ) (ha : Across b A) :
    let D := diagonal fun i => (d i:ℂ)
    D*inverse b d A-inverse b d A*D = A := by
  intro D
  ext i j
  simp only [D,Matrix.sub_apply,diagonal_mul,mul_diagonal,inverse,kernel,Matrix.of_apply,inverseGap]
  by_cases h : b i=b j
  · simp only [if_pos h,ha i j h,zero_mul,mul_zero,sub_zero]
  · have hn : (d i:ℂ)-(d j:ℂ)≠0 := sub_ne_zero.mpr fun he =>
      h (congrArg b (hd (Complex.ofReal_injective he)))
    rw [if_neg h]
    field_simp [hn]

omit [DecidableEq I] in
/-- Commuting an even perturbation with an odd field retains only
opposite-sector entries. -/
theorem across_bracket {b : I → J} {E X : Matrix I I ℂ} (he : Within b E) (hx : Across b X) :
    Across b (E*X-X*E) := by
  intro i j hij
  rw [Matrix.sub_apply,Matrix.mul_apply,Matrix.mul_apply,←sum_sub_distrib]
  apply sum_eq_zero
  intro k _
  by_cases h : b i=b k
  · simp only [hx i k h,hx k j (h.symm.trans hij),mul_zero,zero_mul,sub_zero]
  · have hkj : b k≠b j := fun hh => h (hij.trans hh.symm)
    simp only [he i k h,he k j hkj,zero_mul,mul_zero,sub_zero]

#print axioms commutator_inverse
#print axioms norm_inverse_le
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.CommutatorBounds.Sectors
