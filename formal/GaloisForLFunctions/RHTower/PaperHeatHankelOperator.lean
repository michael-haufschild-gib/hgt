import GaloisForLFunctions.RHTower.PaperHeatHankelKernel
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.PaperCompactIdealTrace

/-! # The full compact heat-Hankel operator

The compact-ideal trace vanishes for this completion without any assumption on
RH. Polynomial tests embed faithfully; their signs are retained exactly.
-/

namespace RHTower.PaperHeatHankel
noncomputable section
open Filter Topology Polynomial GaloisForLFunctions.HTGeometry
open scoped ENNReal

abbrev Space := lp (fun _ : ℕ => ℂ) 2

def operator (a : Time) : Space →L[ℂ] Space := HilbertSchmidt.toOperator (kernel_isHS a)

theorem operator_single (a : Time) (i j : ℕ) :
    operator a (lp.single 2 j (1 : ℂ)) i = kernel a (i,j) :=
  HilbertSchmidt.toOperator_single _ _ _

theorem operator_isHilbertSchmidt (a : Time) : (operator a).IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator _

theorem operator_compact (a : Time) : IsCompactOperator (operator a) :=
  (operator_isHilbertSchmidt a).isCompactOperator

theorem operator_selfAdjoint (a : Time) : IsSelfAdjoint (operator a) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  rw [operator, HilbertSchmidt.adjoint_toOperator]
  apply HilbertSchmidt.toOperator_congr
  funext p
  exact (kernel_conj a (p.2,p.1)).trans (kernel_symm a p.2 p.1)

theorem operator_traceCost (a : Time) : compactOperatorTraceCost Space (operator a) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (operator_compact a)

theorem operator_traceCost_add (a : Time) (T : Space →L[ℂ] Space) :
    compactOperatorTraceCost Space (T + operator a) = compactOperatorTraceCost Space T :=
  compactOperatorTraceCost_add_compact T ⟨_, operator_compact a⟩

/-- All polynomial coefficients, with the inverse of the positive source scaling. -/
def vector (a : Time) (P : ℂ[X]) : Space :=
  ∑ i ∈ P.support, (P.coeff i / (scale a i : ℂ)) • lp.single 2 i (1 : ℂ)

theorem vector_apply (a : Time) (P : ℂ[X]) (n : ℕ) :
    vector a P n = P.coeff n / (scale a n : ℂ) := by
  classical
  simp only [vector, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lp.single_apply]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _ hbn
    simp [Pi.single_eq_of_ne (Ne.symm hbn)]
  · intro hn
    simp [Polynomial.notMem_support_iff.mp hn]

def polynomialEmbedding (a : Time) : ℂ[X] →ₗ[ℂ] Space where
  toFun := vector a
  map_add' P Q := by
    apply lp.ext
    funext n
    simp only [vector_apply, lp.coeFn_add, Pi.add_apply, coeff_add, add_div]
  map_smul' c P := by
    apply lp.ext
    funext n
    simp only [vector_apply, lp.coeFn_smul, Pi.smul_apply, coeff_smul, smul_eq_mul,
      RingHom.id_apply, mul_div_assoc]

theorem polynomialEmbedding_injective (a : Time) : Function.Injective (polynomialEmbedding a) := by
  intro P Q h
  apply Polynomial.ext
  intro n
  have he := congrArg (fun v : Space => v n) h
  change vector a P n = vector a Q n at he
  rw [vector_apply, vector_apply] at he
  have hn : (scale a n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (scale_pos a n).ne'
  have he' := congrArg (fun z : ℂ => z * (scale a n : ℂ)) he
  simpa only [div_mul_cancel₀ _ hn] using he'

theorem inner_vector_operator (a : Time) (P R : ℂ[X]) :
    inner ℂ (vector a P) (operator a (vector a R)) = heatHankel a.val R P := by
  classical
  rw [vector, vector, map_sum]
  simp only [sum_inner, inner_sum, map_smul, inner_smul_left, inner_smul_right,
    lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, operator_single]
  rw [heatHankel_eq_moments a.property]
  simp only [Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hi : (scale a i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (scale_pos a i).ne'
  have hj : (scale a j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (scale_pos a j).ne'
  simp only [kernel, map_div₀, Complex.conj_ofReal]
  rw [Nat.add_comm i j]
  field_simp

end
end RHTower.PaperHeatHankel
