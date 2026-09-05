import Mathlib
import GaloisForLFunctions.HTGeometry.Arxiv2607PiecewiseSymmetric

/-!
# Quantitative algebra for Lamé--Stokes homogenization

This file formalizes the finite-dimensional coercivity engine used by arXiv:2606.05098,
*Quantitative Homogenization for Lamé--Stokes Systems*.  The paper permits negative first Lamé
parameter `lambda`, subject to `mu > 0` and `d * lambda + 2 * mu > 0`.  The sharp elementary lower
bound therefore splits at the sign of `lambda` and uses
`trace(M)^2 ≤ d * ‖M‖_F^2` only in the negative branch.

The resulting theorem is valid for every finite square real matrix.  It supplies a positive
coercivity constant, strict positivity away from zero, symmetry of the constitutive stress, and the
square-law consequence of the paper's `O(sqrt epsilon)` homogenization estimate.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section Frobenius

variable {ι : Type*} [Fintype ι]

/-- Squared Frobenius norm, written entrywise to avoid choosing a matrix norm instance. -/
def matrixFrobeniusSq (M : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, M i j ^ 2

/-- Squared Frobenius norm is nonnegative. -/
theorem matrixFrobeniusSq_nonneg (M : Matrix ι ι ℝ) :
    0 ≤ matrixFrobeniusSq M := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Squared Frobenius norm vanishes exactly on the zero matrix. -/
theorem matrixFrobeniusSq_eq_zero_iff (M : Matrix ι ι ℝ) :
    matrixFrobeniusSq M = 0 ↔ M = 0 := by
  classical
  constructor
  · intro hM
    ext i j
    have hi : ∑ j, M i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hM i (Finset.mem_univ i)
    have hij : M i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hi j (Finset.mem_univ j)
    simpa using hij
  · rintro rfl
    simp [matrixFrobeniusSq]

/-- Finite-dimensional trace--Frobenius inequality `(tr M)^2 ≤ d ‖M‖_F^2`. -/
theorem trace_sq_le_card_mul_matrixFrobeniusSq (M : Matrix ι ι ℝ) :
    Matrix.trace M ^ 2 ≤ (Fintype.card ι : ℝ) * matrixFrobeniusSq M := by
  classical
  rw [Matrix.trace]
  calc
    (∑ i, M i i) ^ 2 ≤ ((Finset.univ : Finset ι).card : ℝ) * ∑ i, M i i ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ ((Finset.univ : Finset ι).card : ℝ) * matrixFrobeniusSq M := by
      gcongr
      exact Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (fun j _ => sq_nonneg (M i j)) (Finset.mem_univ i)
    _ = (Fintype.card ι : ℝ) * matrixFrobeniusSq M := by simp

end Frobenius

section LamePair

variable (ι : Type*) [Fintype ι]

/-- Lamé parameters satisfying the paper's admissibility inequalities in dimension `card ι`. -/
structure AdmissibleLamePair where
  lambda : ℝ
  mu : ℝ
  mu_pos : 0 < mu
  bulk_pos : 0 < (Fintype.card ι : ℝ) * lambda + 2 * mu

variable {ι}

/-- Coercivity constant selected by the two possible signs of `lambda`. -/
def AdmissibleLamePair.coercivityConstant (P : AdmissibleLamePair ι) : ℝ :=
  min ((Fintype.card ι : ℝ) * P.lambda + 2 * P.mu) (2 * P.mu)

/-- The selected Lamé coercivity constant is strictly positive. -/
theorem AdmissibleLamePair.coercivityConstant_pos (P : AdmissibleLamePair ι) :
    0 < P.coercivityConstant := by
  apply lt_min P.bulk_pos
  nlinarith [P.mu_pos]

/-- Pointwise quadratic elastic energy. -/
def lameEnergy (P : AdmissibleLamePair ι) (M : Matrix ι ι ℝ) : ℝ :=
  P.lambda * Matrix.trace M ^ 2 + 2 * P.mu * matrixFrobeniusSq M

/-- Sharp elementary coercivity bound used in the Lamé--Stokes homogenization argument. -/
theorem lameEnergy_lower (P : AdmissibleLamePair ι) (M : Matrix ι ι ℝ) :
    P.coercivityConstant * matrixFrobeniusSq M ≤ lameEnergy P M := by
  have hF := matrixFrobeniusSq_nonneg M
  have htr := trace_sq_le_card_mul_matrixFrobeniusSq M
  by_cases hlambda : 0 ≤ P.lambda
  · have hc : P.coercivityConstant ≤ 2 * P.mu := min_le_right _ _
    have h1 := mul_le_mul_of_nonneg_right hc hF
    have h2 : 0 ≤ P.lambda * Matrix.trace M ^ 2 :=
      mul_nonneg hlambda (sq_nonneg _)
    unfold lameEnergy
    linarith
  · have hlambda' : P.lambda ≤ 0 := le_of_not_ge hlambda
    have htrace : P.lambda * ((Fintype.card ι : ℝ) * matrixFrobeniusSq M) ≤
        P.lambda * Matrix.trace M ^ 2 := mul_le_mul_of_nonpos_left htr hlambda'
    have hc : P.coercivityConstant ≤
        (Fintype.card ι : ℝ) * P.lambda + 2 * P.mu := min_le_left _ _
    have h1 := mul_le_mul_of_nonneg_right hc hF
    unfold lameEnergy
    nlinarith

/-- Elastic energy is nonnegative for every matrix. -/
theorem lameEnergy_nonneg (P : AdmissibleLamePair ι) (M : Matrix ι ι ℝ) :
    0 ≤ lameEnergy P M := by
  exact le_trans (mul_nonneg P.coercivityConstant_pos.le (matrixFrobeniusSq_nonneg M))
    (lameEnergy_lower P M)

/-- Elastic energy is strictly positive away from the zero matrix. -/
theorem lameEnergy_pos (P : AdmissibleLamePair ι) {M : Matrix ι ι ℝ} (hM : M ≠ 0) :
    0 < lameEnergy P M := by
  have hFne : matrixFrobeniusSq M ≠ 0 := fun h => hM ((matrixFrobeniusSq_eq_zero_iff M).mp h)
  have hFpos : 0 < matrixFrobeniusSq M :=
    lt_of_le_of_ne (matrixFrobeniusSq_nonneg M) (Ne.symm hFne)
  exact lt_of_lt_of_le (mul_pos P.coercivityConstant_pos hFpos) (lameEnergy_lower P M)

end LamePair

section FiniteCellHomogenization

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]

/-- Discrete Jensen estimate for a mean-zero matrix corrector on a finite periodic cell. -/
theorem sum_matrixFrobeniusSq_add_ge_card
    (A : Matrix ι ι ℝ) (corrector : κ → Matrix ι ι ℝ)
    (hmean : ∑ q, corrector q = 0) :
    (Fintype.card κ : ℝ) * matrixFrobeniusSq A ≤
      ∑ q, matrixFrobeniusSq (A + corrector q) := by
  classical
  have hentry (i j : ι) : ∑ q, corrector q i j = 0 := by
    let ev : Matrix ι ι ℝ →+ ℝ :=
      { toFun := fun M => M i j
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change ∑ q, ev (corrector q) = 0
    rw [← map_sum, hmean, map_zero]
  have hpoint (i j : ι) :
      (Fintype.card κ : ℝ) * A i j ^ 2 ≤ ∑ q, (A + corrector q) i j ^ 2 := by
    have hsum : ∑ q, (A + corrector q) i j = (Fintype.card κ : ℝ) * A i j := by
      simp only [Matrix.add_apply, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, hentry, add_zero]
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset κ)) (f := fun q => (A + corrector q) i j)
    rw [hsum] at hcs
    simp only [Finset.card_univ] at hcs
    have hcard : 0 < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
    nlinarith
  rw [matrixFrobeniusSq]
  simp_rw [matrixFrobeniusSq]
  calc
    (Fintype.card κ : ℝ) * ∑ i, ∑ j, A i j ^ 2 =
        ∑ i, ∑ j, (Fintype.card κ : ℝ) * A i j ^ 2 := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ∑ q, (A + corrector q) i j ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
    _ = ∑ q, ∑ i, ∑ j, (A + corrector q) i j ^ 2 := by
      calc
        (∑ i, ∑ j, ∑ q, (A + corrector q) i j ^ 2) =
            ∑ i, ∑ q, ∑ j, (A + corrector q) i j ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = ∑ q, ∑ i, ∑ j, (A + corrector q) i j ^ 2 := by
          rw [Finset.sum_comm]

/-- Finite-cell analogue of homogenized Lamé coercivity: every mean-zero corrector preserves the
original coercivity constant after cell averaging. -/
theorem finiteCell_lameEnergy_coercive
    (P : AdmissibleLamePair ι) (A : Matrix ι ι ℝ)
    (corrector : κ → Matrix ι ι ℝ) (hmean : ∑ q, corrector q = 0) :
    (Fintype.card κ : ℝ) * P.coercivityConstant * matrixFrobeniusSq A ≤
      ∑ q, lameEnergy P (A + corrector q) := by
  have hJ := sum_matrixFrobeniusSq_add_ge_card A corrector hmean
  calc
    (Fintype.card κ : ℝ) * P.coercivityConstant * matrixFrobeniusSq A =
        P.coercivityConstant * ((Fintype.card κ : ℝ) * matrixFrobeniusSq A) := by ring
    _ ≤ P.coercivityConstant * ∑ q, matrixFrobeniusSq (A + corrector q) :=
      mul_le_mul_of_nonneg_left hJ P.coercivityConstant_pos.le
    _ = ∑ q, P.coercivityConstant * matrixFrobeniusSq (A + corrector q) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ q, lameEnergy P (A + corrector q) :=
      Finset.sum_le_sum fun q _ => lameEnergy_lower P (A + corrector q)

end FiniteCellHomogenization

section ConstitutiveStress

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Isotropic Lamé stress `lambda tr(epsilon) I + 2 mu epsilon`, with symmetric strain. -/
def lameStress (P : AdmissibleLamePair ι) (gradient : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (P.lambda * Matrix.trace (matrixSymPart gradient)) • (1 : Matrix ι ι ℝ) +
    (2 * P.mu) • matrixSymPart gradient

/-- Constitutive Lamé stress is symmetric, even for a nonsymmetric input gradient. -/
theorem lameStress_transpose (P : AdmissibleLamePair ι) (gradient : Matrix ι ι ℝ) :
    (lameStress P gradient).transpose = lameStress P gradient := by
  unfold lameStress
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_one, matrixSymPart_transpose]

/-- Zero gradient produces zero Lamé stress. -/
@[simp] theorem lameStress_zero (P : AdmissibleLamePair ι) :
    lameStress P (0 : Matrix ι ι ℝ) = 0 := by
  ext i j
  simp [lameStress, matrixSymPart]

end ConstitutiveStress

section SquareRootRate

/-- Certified pointwise `O(sqrt epsilon)` error estimate. -/
structure SqrtHomogenizationBound (X : Type*) where
  error : ℝ → X → ℝ
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  error_nonneg : ∀ ε x, 0 ≤ error ε x
  bound : ∀ {ε}, 0 ≤ ε → ∀ x, error ε x ≤ constant * Real.sqrt ε

/-- Squaring the paper's `O(sqrt epsilon)` estimate gives an `O(epsilon)` energy error. -/
theorem SqrtHomogenizationBound.sq_le (H : SqrtHomogenizationBound X)
    {ε : ℝ} (hε : 0 ≤ ε) (x : X) :
    H.error ε x ^ 2 ≤ H.constant ^ 2 * ε := by
  have hbound := H.bound hε x
  have hsqrt : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  nlinarith [H.error_nonneg ε x, Real.sq_sqrt hε]

end SquareRootRate

end GaloisForLFunctions.HTGeometry
