import GaloisForLFunctions.HTGeometry.RationalRankHyperplaneAvoidance
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A finite family of integral similarities transverse to prescribed normals

Streck's simultaneous change of chart requires a row transverse to a
bounded number of real normals. A scaled Householder reflection at the
moment vector (1,t,…,tⁿ) has integral coefficients for integral t. Its
first coordinate on a nonzero normal is a nonzero polynomial of degree at
most 2n. Consequently 2nk+1 fixed choices suffice for k real normals.
-/

noncomputable section
open Finset Matrix Polynomial
namespace GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- Householder reflection with its only denominator cleared. -/
def scaled (u x : ι → R) : ι → R := (u ⬝ᵥ u) • x -(2*(u ⬝ᵥ x)) • u

/-- All scalar products are multiplied by the same squared integer factor. -/
theorem scaled_gram (u x y : ι → R) :
    scaled u x ⬝ᵥ scaled u y = (u ⬝ᵥ u)^2 * (x ⬝ᵥ y) := by
  simp only [scaled,sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [dotProduct_comm x u]
  ring

/-- Repeating the same transformation clears exactly the square of the common length. -/
theorem scaled_square (u x : ι → R) : scaled u (scaled u x)=(u ⬝ᵥ u)^2 • x := by
  ext i
  simp only [scaled,dotProduct_sub,dotProduct_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

variable {n : ℕ}

/-- Integer first-coordinate probe obtained by changing chart at parameter t. -/
def menuRow (n : ℕ) (t : ℕ) : Fin (n+1) → ℤ :=
  scaled (fun i => (t : ℤ)^(i : ℕ)) (Pi.single 0 1)

/-- The chart row paired against a real normal. -/
def test (v : Fin (n+1) → ℝ) : ℝ[X] :=
  C (v 0)*(∑ i : Fin (n+1), X^(2*(i : ℕ))) -
    C (2 : ℝ)*(∑ i : Fin (n+1), C (v i)*X^(i : ℕ))

private theorem coeff_packet (v : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    (∑ j : Fin (n+1), C (v j)*X^(j : ℕ)).coeff (i : ℕ)=v i := by
  rw [finsetSum_coeff,sum_eq_single i]
  · simp
  · intro j _ hj
    rw [coeff_C_mul,coeff_X_pow,if_neg (fun h => hj (Fin.val_injective h.symm)),mul_zero]
  · simp

/-- A vanishing chart polynomial forces every coordinate of its normal to vanish. -/
theorem test_ne_zero (v : Fin (n+1) → ℝ) (hv : v ≠ 0) : test v ≠ 0 := by
  intro he
  have hv₀ := congrArg (Polynomial.eval (0 : ℝ)) he
  simp [test,Fin.sum_univ_succ,Polynomial.eval_finsetSum] at hv₀
  have hp : (∑ i : Fin (n+1), C (v i)*X^(i : ℕ))=0 := by
    simpa [test,hv₀] using he
  apply hv
  funext i
  rw [← coeff_packet v i,hp,coeff_zero]
  rfl

theorem test_degree (v : Fin (n+1) → ℝ) : (test v).natDegree ≤ 2*n := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · apply (natDegree_C_mul_le _ _).trans
    exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (natDegree_X_pow_le _).trans (by have := i.isLt; omega)
  · apply (natDegree_C_mul_le _ _).trans
    exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans (by have := i.isLt; omega))

/-- The real polynomial counts zeros of an actual integral chart row. -/
theorem row_evaluation (v : Fin (n+1) → ℝ) (t : ℕ) :
    (fun i => (menuRow n t i : ℝ)) ⬝ᵥ v = (test v).eval (t : ℝ) := by
  let u (i : Fin (n+1)) : ℤ := (t : ℤ)^(i : ℕ)
  have hu : u ⬝ᵥ Pi.single 0 1=1 := by simp [dotProduct_single,u]
  have he : (fun i => (menuRow n t i : ℝ)) =
      (∑ i : Fin (n+1), (t : ℝ)^(2*(i : ℕ))) • Pi.single 0 (1 : ℝ) -
        (2 : ℝ) • (fun i : Fin (n+1) => (t : ℝ)^(i : ℕ)) := by
    funext i
    change (((u ⬝ᵥ u)*Pi.single 0 (1 : ℤ) i - (2*(u ⬝ᵥ Pi.single 0 1))*u i : ℤ) : ℝ) = _
    rw [hu]
    simp only [dotProduct,u,Int.cast_sub,Int.cast_mul,Int.cast_sum,Int.cast_pow,Int.cast_natCast,
      mul_one,Int.cast_ofNat,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,two_mul,pow_add]
    by_cases hi : i=0 <;> simp [hi]
  rw [he,sub_dotProduct,smul_dotProduct,smul_dotProduct,single_dotProduct]
  simp only [test,eval_sub,eval_mul,eval_C,eval_finsetSum,eval_pow,eval_X,smul_eq_mul,
    dotProduct,one_mul]
  simp_rw [mul_comm ((t : ℝ)^_)]
  ring

/-- A fixed menu of 2nk+1 integral orthogonal charts separates any k nonzero
real normals simultaneously in dimension n+1. -/
theorem finite_menu {κ : Type*} [Fintype κ] (v : κ → Fin (n+1) → ℝ) (hv : ∀ a, v a ≠ 0) :
    ∃ t : Fin (2*n*Fintype.card κ+1), ∀ a,
      (fun i => (menuRow n t.val i : ℝ)) ⬝ᵥ v a ≠ 0 := by
  classical
  let P := ∏ a, test (v a)
  have hP : P ≠ 0 := prod_ne_zero_iff.mpr fun a _ => test_ne_zero _ (hv a)
  have hD : P.natDegree ≤ 2*n*Fintype.card κ := by
    apply (natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ _a : κ, 2*n := sum_le_sum fun a _ => test_degree (v a)
      _ = _ := by simp [mul_comm]
  by_contra! h
  apply hP
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun t : Fin (2*n*Fintype.card κ+1) => (t.val : ℝ))
    (fun _ _ he => Fin.val_injective (Nat.cast_injective he))
  · intro t
    obtain ⟨a,ha⟩ := h t
    rw [row_evaluation] at ha
    change (∏ a, test (v a)).eval _ = 0
    rw [eval_prod]
    exact prod_eq_zero (mem_univ a) ha
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hD

end GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart

#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart.scaled_gram
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart.scaled_square
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart.test_ne_zero
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart.test_degree
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart.row_evaluation
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart.finite_menu
