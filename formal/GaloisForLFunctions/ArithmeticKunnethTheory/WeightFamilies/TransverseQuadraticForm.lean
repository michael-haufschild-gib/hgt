import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.CriticalPointTateTrace
import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuDeterminant

/-!
# The transverse quadratic form of the reciprocal locus

Fix the normalized coordinate and eliminate a second coordinate using the
sum-zero tangent equation. This gives a complete linear chart of the transverse
tangent space. At a sign critical point its quadratic matrix is diagonal plus
a rank-one matrix, with determinant minus the product of all coordinates.
-/

open Finset Matrix
open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {K : Type*} [Field K]

/-- The chart fixes the normalized coordinate and eliminates the sum-zero constraint. -/
def reciprocalTangentVector {m : ℕ} (w : Fin m → K) : Fin (m + 2) → K :=
  Fin.cons 0 (Fin.cons (-(∑ i, w i)) w)

theorem reciprocalTangentVector_zero {m : ℕ} (w : Fin m → K) :
    reciprocalTangentVector w 0 = 0 := rfl

theorem reciprocalTangentVector_one {m : ℕ} (w : Fin m → K) :
    reciprocalTangentVector w (Fin.succ 0) = -(∑ i, w i) := rfl

theorem reciprocalTangentVector_tail {m : ℕ} (w : Fin m → K) (i : Fin m) :
    reciprocalTangentVector w i.succ.succ = w i := rfl

/-- Every chart vector satisfies both transverse tangent equations. -/
theorem reciprocalTangentVector_sum {m : ℕ} (w : Fin m → K) :
    (∑ i, reciprocalTangentVector w i) = 0 := by
  simp only [Fin.sum_univ_succ, reciprocalTangentVector_zero,
    reciprocalTangentVector_one, reciprocalTangentVector_tail, zero_add, neg_add_cancel]

/-- The chart exhausts the tangent space, including dimension zero. -/
theorem reciprocalTangentVector_reconstruct {m : ℕ} (v : Fin (m + 2) → K)
    (hv : (∑ i, v i) = 0) (h₀ : v 0 = 0) :
    reciprocalTangentVector (fun i => v i.succ.succ) = v := by
  have hs : v (Fin.succ 0) + ∑ i : Fin m, v i.succ.succ = 0 := by
    simpa only [Fin.sum_univ_succ, h₀, zero_add] using hv
  funext i
  refine Fin.cases h₀.symm (fun j => ?_) i
  refine Fin.cases ?_ (fun _ => rfl) j
  change -(∑ i : Fin m, v i.succ.succ) = v (Fin.succ 0)
  linear_combination -hs

/-- The chart is injective because its free coordinates are unchanged. -/
theorem reciprocalTangentVector_injective (m : ℕ) :
    Function.Injective (reciprocalTangentVector (K := K) (m := m)) := by
  intro v w h
  funext i
  exact congrFun h i.succ.succ

/-- The bilinear matrix in the free coordinates of the actual tangent chart. -/
def reciprocalTransverseMatrix {m : ℕ} (x : Fin (m + 2) → K) : Matrix (Fin m) (Fin m) K :=
  diagonal (fun i => x i.succ.succ) + vecMulVec (fun _ => x (Fin.succ 0)) (fun _ => 1)

theorem reciprocalTransverseMatrix_mulVec {m : ℕ} (x : Fin (m + 2) → K)
    (w : Fin m → K) (i : Fin m) :
    (reciprocalTransverseMatrix x).mulVec w i =
      x i.succ.succ * w i + x (Fin.succ 0) * ∑ j, w j := by
  rw [reciprocalTransverseMatrix, add_mulVec]
  simp only [Pi.add_apply, mulVec_diagonal]
  change x i.succ.succ * w i + (∑ j, (x (Fin.succ 0) * 1) * w j) = _
  rw [mul_one, ← mul_sum]

/-- Restricting the reciprocal pairing gives a diagonal term and one rank-one term. -/
theorem reciprocalPairing_tangentVector {m : ℕ} (x : Fin (m + 2) → K) (v w : Fin m → K) :
    reciprocalPairing x (reciprocalTangentVector v) (reciprocalTangentVector w) =
      x (Fin.succ 0) * (∑ i, v i) * (∑ i, w i) + ∑ i, x i.succ.succ * v i * w i := by
  simp only [reciprocalPairing, Fin.sum_univ_succ, reciprocalTangentVector_zero,
    reciprocalTangentVector_one, reciprocalTangentVector_tail, mul_zero,
    zero_add, mul_neg, neg_mul, neg_neg]

/-- The actual quadratic coefficient in the same tangent chart. -/
theorem reciprocalQuadratic_tangentVector {m : ℕ} (x : Fin (m + 2) → K) (w : Fin m → K) :
    reciprocalQuadratic x (reciprocalTangentVector w) =
      x (Fin.succ 0) * (∑ i, w i) ^ 2 + ∑ i, x i.succ.succ * w i ^ 2 := by
  simp only [reciprocalQuadratic, Fin.sum_univ_succ, reciprocalTangentVector_zero,
    reciprocalTangentVector_one, reciprocalTangentVector_tail, zero_pow two_ne_zero,
    mul_zero, zero_add, neg_sq]

/-- The matrix represents the restricted pairing, not merely a form with the same determinant. -/
theorem reciprocalPairing_tangentVector_eq_matrix {m : ℕ} (x : Fin (m + 2) → K)
    (v w : Fin m → K) :
    reciprocalPairing x (reciprocalTangentVector v) (reciprocalTangentVector w) =
      v ⬝ᵥ (reciprocalTransverseMatrix x).mulVec w := by
  rw [reciprocalPairing_tangentVector]
  simp only [dotProduct, reciprocalTransverseMatrix_mulVec, mul_add, sum_add_distrib]
  have hd : (∑ i, v i * (x i.succ.succ * w i)) =
      ∑ i, x i.succ.succ * v i * w i := by
    apply sum_congr rfl
    intro i _
    ring
  rw [hd, ← sum_mul]
  ring

/-- The actual quadratic coefficient is the matrix quadratic form in the complete tangent chart. -/
theorem reciprocalQuadratic_tangentVector_eq_matrix {m : ℕ} (x : Fin (m + 2) → K)
    (w : Fin m → K) :
    reciprocalQuadratic x (reciprocalTangentVector w) =
      w ⬝ᵥ (reciprocalTransverseMatrix x).mulVec w := by
  rw [← reciprocalPairing_tangentVector_eq_matrix]
  simp only [reciprocalQuadratic, reciprocalPairing, pow_two, mul_assoc]

/-- At a sign critical point the matrix quadratic form is the formal reciprocal series coefficient. -/
theorem reciprocalSeries_transverse_quadratic {m : ℕ} (x : Fin (m + 2) → K)
    (hx : ∀ i, x i ^ 2 = 1) (w : Fin m → K) :
    PowerSeries.coeff 2 (reciprocalSeries x (reciprocalTangentVector w)) =
      w ⬝ᵥ (reciprocalTransverseMatrix x).mulVec w := by
  rw [reciprocalSeries_quadratic x _ hx, reciprocalQuadratic_tangentVector_eq_matrix]

/-- For square-one diagonal entries, a rank-one determinant factors through their sum. -/
theorem signDiagonal_rankOne_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → K) (a : K) (hd : ∀ i, d i ^ 2 = 1) :
    (diagonal d + vecMulVec (fun _ => a) (fun _ => (1 : K))).det =
      (∏ i, d i) * (1 + a * ∑ i, d i) := by
  have herase (i : ι) : (∏ j ∈ univ.erase i, d j) = d i * ∏ j, d j := by
    calc (∏ j ∈ univ.erase i, d j) = (d i * d i) * ∏ j ∈ univ.erase i, d j := by
          rw [← pow_two, hd, one_mul]
      _ = d i * ((∏ j ∈ univ.erase i, d j) * d i) := by ring
      _ = d i * ∏ j, d j := by rw [prod_erase_mul univ d (mem_univ i)]
  rw [HTGeometry.bgv_det_diagonal_add_vecMulVec]
  simp only [mul_one, herase]
  have hsum : (∑ i, a * (d i * ∏ j, d j)) = a * (∏ j, d j) * ∑ i, d i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

/-- At a normalized sign point of the sum-zero hyperplane, the transverse determinant
is minus the full coordinate product. -/
theorem reciprocalTransverseMatrix_det {m : ℕ} (x : Fin (m + 2) → K)
    (hx : ∀ i, x i ^ 2 = 1) (h₀ : x 0 = 1) (hs : (∑ i, x i) = 0) :
    (reciprocalTransverseMatrix x).det = -(∏ i, x i) := by
  have hsum : 1 + (x (Fin.succ 0) + ∑ i : Fin m, x i.succ.succ) = 0 := by
    simpa only [Fin.sum_univ_succ, h₀] using hs
  have hfactor : 1 + x (Fin.succ 0) * (∑ i : Fin m, x i.succ.succ) = -x (Fin.succ 0) := by
    linear_combination x (Fin.succ 0) * hsum - hx (Fin.succ 0)
  rw [reciprocalTransverseMatrix,
    signDiagonal_rankOne_det (fun i : Fin m => x i.succ.succ) (x (Fin.succ 0))
      (fun i => hx i.succ.succ),
    hfactor, Fin.prod_univ_succ, Fin.prod_univ_succ, h₀, one_mul]
  ring

/-- The determinant certificate itself proves that the transverse matrix is nonsingular. -/
theorem reciprocalTransverseMatrix_det_ne_zero {m : ℕ} (x : Fin (m + 2) → K)
    (hx : ∀ i, x i ^ 2 = 1) (h₀ : x 0 = 1) (hs : (∑ i, x i) = 0) :
    (reciprocalTransverseMatrix x).det ≠ 0 := by
  rw [reciprocalTransverseMatrix_det x hx h₀ hs]
  apply neg_ne_zero.mpr
  apply prod_ne_zero_iff.mpr
  intro i _ hi
  have h := hx i
  simp only [hi, zero_pow two_ne_zero, zero_ne_one] at h

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The determinant formula applies to every actual normalized torus critical point. -/
theorem reciprocalTransverseMatrix_det_critical {m : ℕ} (x : MomentTorus F (m + 1))
    (hx : x ∈ reciprocalTorusCriticalPoints F (m + 1)) :
    (reciprocalTransverseMatrix (Fin.cons 1 (fun i => (x i : F)))).det = -∏ i, (x i : F) := by
  obtain ⟨hd, hsign⟩ := (mem_reciprocalTorusCriticalPoints_iff x).mp hx
  have hs := (mem_filter.mp (mem_filter.mp hd).1).2
  have hsq : ∀ i : Fin (m + 2),
      ((Fin.cons (1 : F) (fun j => (x j : F)) : Fin (m + 2) → F) i) ^ 2 = 1 := by
    intro i
    refine Fin.cases (show (1 : F) ^ 2 = 1 from one_pow 2) (fun j => ?_) i
    rcases hsign j with hj | hj <;> simp only [Fin.cons_succ, hj, one_pow, neg_sq]
  simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, one_mul] using
    reciprocalTransverseMatrix_det (Fin.cons 1 (fun i => (x i : F))) hsq rfl
      (by simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using hs)

omit [Fintype F] [DecidableEq F] in
/-- The sign product is determined by the number of negative coordinates. -/
theorem signedMomentTorus_prod {m : ℕ} (S : Finset (Fin m)) :
    (∏ i, (signedMomentTorus (F := F) S i : F)) = (-1) ^ S.card := by
  simp [signedMomentTorus]

/-- The discriminant representative at a critical sign point records exactly its sign parity. -/
theorem reciprocalTransverseMatrix_det_signs {m : ℕ} (S : Finset (Fin (m + 1)))
    (hS : ((m + 2 : ℕ) : F) = 2 * S.card) :
    (reciprocalTransverseMatrix (Fin.cons 1
      (fun i => (signedMomentTorus (F := F) S i : F)))).det = (-1) ^ (S.card + 1) := by
  have hc := (signedMomentTorus_mem_critical_iff (F := F) S).mpr hS
  rw [reciprocalTransverseMatrix_det_critical _ hc, signedMomentTorus_prod, pow_succ]
  ring

end FiniteField

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
