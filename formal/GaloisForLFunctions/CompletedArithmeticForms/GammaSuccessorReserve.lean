import GaloisForLFunctions.HTGeometry.PoleUnitGammaBase
import GaloisForLFunctions.HTGeometry.GammaShiftCasoratian
import GaloisForLFunctions.HTGeometry.BinomialNodeDeterminant
import GaloisForLFunctions.HTGeometry.HankelSuccessorSchurStrict

/-!
# Exact Gamma-model successor reserves

The Gamma Hankel determinant factors into factorials and ascending moments. The proof
uses monic factorial evaluation at consecutive nodes. Its determinant quotient gives an
explicit successor reserve at every order, including after source mass and scale changes.
-/

noncomputable section

open Finset Matrix Polynomial

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry

theorem gammaShapeMoment_pos {r : ℝ} (hr : 0 < r) (n : ℕ) :
    0 < gammaShapeMoment r n := by
  unfold gammaShapeMoment
  exact prod_pos fun i _ => add_pos_of_pos_of_nonneg hr (Nat.cast_nonneg i)

theorem gammaShapeMoment_add (r : ℝ) (i j : ℕ) :
    gammaShapeMoment r (i + j) = gammaShapeMoment r i * gammaShapeMoment (r + i) j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show i + (j + 1) = (i + j) + 1 by omega, gammaShapeMoment_succ, ih,
      gammaShapeMoment_succ]
    push_cast
    ring

theorem gammaShapeMoment_eq_pochhammer (r : ℝ) (n : ℕ) :
    gammaShapeMoment r n = (ascPochhammer ℝ n).eval r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [gammaShapeMoment_succ, ascPochhammer_succ_eval, ih]

/-- Consecutive integer nodes have the factorial Vandermonde determinant. -/
theorem det_vandermonde_natCast (N : ℕ) :
    (Matrix.vandermonde (fun i : Fin N => (i.val : ℝ))).det =
      ∏ i : Fin N, (i.val.factorial : ℝ) := by
  let E : Matrix (Fin N) (Fin N) ℝ :=
    fun i j => (fallingFactorialPoly ℝ i.val).eval (j.val : ℝ)
  have hE : E.det = (Matrix.vandermonde (fun i : Fin N => (i.val : ℝ))).det := by
    rw [← Matrix.det_transpose]
    exact (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun i : Fin N => (i.val : ℝ)) (fun j => fallingFactorialPoly ℝ j.val)
      (fun j => fallingFactorialPoly_natDegree j.val)
      (fun j => fallingFactorialPoly_monic j.val)).symm
  have htri : E.BlockTriangular id := by
    intro i j hji
    have hji' : j.val < i.val := hji
    dsimp [E]
    rw [eval_fallingFactorialPoly, Nat.choose_eq_zero_of_lt hji', Nat.cast_zero, zero_mul]
  rw [← hE, Matrix.det_of_upperTriangular htri]
  exact prod_congr rfl fun i _ => by simp [E, eval_fallingFactorialPoly]

/-- Exact determinant of every Gamma moment head, without a positivity premise. -/
theorem det_gammaShapeHankel (r : ℝ) (N : ℕ) :
    (finiteHankelMatrix (gammaShapeMoment r) N).det =
      ∏ i : Fin N, ((i.val.factorial : ℝ) * gammaShapeMoment r i.val) := by
  have hm : finiteHankelMatrix (gammaShapeMoment r) N =
      Matrix.of fun i j : Fin N => gammaShapeMoment r j.val *
        ascPochhammerEvalMatrix (fun j : Fin N => r + j.val) i j := by
    ext i j
    simp only [finiteHankelMatrix, Matrix.of_apply, ascPochhammerEvalMatrix]
    rw [Nat.add_comm i.val j.val, gammaShapeMoment_add,
      gammaShapeMoment_eq_pochhammer (r + j.val) i.val]
  rw [hm, Matrix.det_mul_row, det_ascPochhammerEvalMatrix]
  simp only [add_sub_add_left_eq_sub]
  rw [← Matrix.det_vandermonde, det_vandermonde_natCast, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => by ring

/-- Source mass and scale applied to the Gamma moment model. -/
def scaledGammaMoment (g w r : ℝ) (n : ℕ) : ℝ := g * w ^ n * gammaShapeMoment r n

theorem scaledGammaHankel_eq (g w r : ℝ) (N : ℕ) :
    finiteHankelMatrix (scaledGammaMoment g w r) N =
      g • (diagonal (fun i : Fin N => w ^ i.val) *
        finiteHankelMatrix (gammaShapeMoment r) N * diagonal (fun i : Fin N => w ^ i.val)) := by
  ext i j
  simp only [finiteHankelMatrix, scaledGammaMoment, Matrix.smul_apply, smul_eq_mul,
    diagonal_mul, mul_diagonal, pow_add]
  ring

/-- Each diagonal factor is the exact payment for adjoining its corresponding moment. -/
theorem det_scaledGammaHankel (g w r : ℝ) (N : ℕ) :
    (finiteHankelMatrix (scaledGammaMoment g w r) N).det =
      ∏ i : Fin N, (g * w ^ (2 * i.val) * (i.val.factorial : ℝ) * gammaShapeMoment r i.val) := by
  rw [scaledGammaHankel_eq, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, det_gammaShapeHankel]
  have hgprod : g ^ N = ∏ _i : Fin N, g := by simp
  simp only [Fintype.card_fin]
  rw [hgprod]
  rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => by rw [show 2 * i.val = i.val + i.val by omega, pow_add]; ring

theorem scaledGammaHankel_posDef {g w r : ℝ} (hg : 0 < g) (hw : 0 < w) (hr : 0 < r)
    (N : ℕ) : (finiteHankelMatrix (scaledGammaMoment g w r) N).PosDef := by
  rw [scaledGammaHankel_eq]
  have hA : (finiteHankelMatrix (gammaShapeMoment r) N).PosDef :=
    gammaShapeMoment_momentHankelMatrix_posDef hr N
  have hD : Function.Injective (diagonal (fun i : Fin N => w ^ i.val)).mulVec := by
    intro a b h
    funext i
    have hi := congrFun h i
    simp only [Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (pow_ne_zero _ hw.ne') hi
  have h := hA.conjTranspose_mul_mul_same hD
  simpa only [diagonal_conjTranspose, star_trivial] using h.smul hg

/-- Exact all-order Schur reserve of the scaled Gamma source. -/
theorem scaledGamma_successorSchur {g w r : ℝ} (hg : 0 < g) (hw : 0 < w) (hr : 0 < r)
    (N : ℕ) :
    finiteHankelSuccessorSchur (scaledGammaMoment g w r) N =
      g * w ^ (2 * N) * (N.factorial : ℝ) * gammaShapeMoment r N := by
  have hhead := scaledGammaHankel_posDef hg hw hr N
  have h := finiteHankelMatrix_succ_det_eq_schur hhead
  rw [det_scaledGammaHankel, det_scaledGammaHankel, Fin.prod_univ_castSucc] at h
  have hdet : (∏ i : Fin N,
      g * w ^ (2 * i.val) * (i.val.factorial : ℝ) * gammaShapeMoment r i.val) ≠ 0 := by
    rw [← det_scaledGammaHankel]
    exact hhead.det_pos.ne'
  exact (mul_left_cancel₀ hdet h).symm

/-- Relative to the new diagonal, source mass and scale cancel from the exact reserve. -/
theorem scaledGamma_successorSchur_div_diagonal {g w r : ℝ}
    (hg : 0 < g) (hw : 0 < w) (hr : 0 < r) (N : ℕ) :
    finiteHankelSuccessorSchur (scaledGammaMoment g w r) N /
        scaledGammaMoment g w r (2 * N) =
      (N.factorial : ℝ) / gammaShapeMoment (r + N) N := by
  have hmoment := gammaShapeMoment_add r N N
  rw [show N + N = 2 * N by omega] at hmoment
  rw [scaledGamma_successorSchur hg hw hr, scaledGammaMoment, hmoment]
  field_simp [hg.ne', pow_ne_zero _ hw.ne', (gammaShapeMoment_pos hr N).ne',
    (gammaShapeMoment_pos (add_pos_of_pos_of_nonneg hr (Nat.cast_nonneg N)) N).ne']

private theorem factorial_reserve_le_shifted_moment {r : ℝ} (hr : 1 / 2 ≤ r) (N : ℕ) :
    (3 / 2 : ℝ) ^ N * (N.factorial : ℝ) ≤ gammaShapeMoment (r + N) N := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hprod : ∀ j, j ≤ N →
      (3 / 2 : ℝ) ^ j * (j.factorial : ℝ) ≤ gammaShapeMoment (r + N) j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjr : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
      have hstep : (3 / 2 : ℝ) * ((j : ℝ) + 1) ≤ r + N + j := by
        linarith only [hr, hjr, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        gammaShapeMoment_succ]
      calc
        _ = ((3 / 2 : ℝ) ^ j * (j.factorial : ℝ)) *
            ((3 / 2 : ℝ) * ((j : ℝ) + 1)) := by ring
        _ ≤ gammaShapeMoment (r + N) j * (r + N + j) :=
          mul_le_mul (ih (by omega)) hstep (by positivity)
            (gammaShapeMoment_pos (add_pos_of_pos_of_nonneg hr0 (Nat.cast_nonneg N)) j).le
  exact hprod N le_rfl

/-- Even the positive Gamma model loses an exponential fraction of each new diagonal. -/
theorem gamma_successor_relative_reserve_le {r : ℝ} (hr : 1 / 2 ≤ r) (N : ℕ) :
    (N.factorial : ℝ) / gammaShapeMoment (r + N) N ≤ (2 / 3 : ℝ) ^ N := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hpos := gammaShapeMoment_pos (add_pos_of_pos_of_nonneg hr0 (Nat.cast_nonneg N)) N
  apply (div_le_iff₀ hpos).mpr
  have hcancel : (2 / 3 : ℝ) ^ N * (3 / 2 : ℝ) ^ N = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (N.factorial : ℝ) = (2 / 3 : ℝ) ^ N * ((3 / 2 : ℝ) ^ N * (N.factorial : ℝ)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (2 / 3 : ℝ) ^ N * gammaShapeMoment (r + N) N :=
      mul_le_mul_of_nonneg_left (factorial_reserve_le_shifted_moment hr N) (by positivity)

#print axioms det_gammaShapeHankel
#print axioms scaledGamma_successorSchur
#print axioms gamma_successor_relative_reserve_le

end GaloisForLFunctions.CompletedArithmeticForms
