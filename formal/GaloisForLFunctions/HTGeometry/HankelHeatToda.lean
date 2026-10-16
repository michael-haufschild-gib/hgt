import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCausticQSystem
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The differential condensation identity for heat Hankel determinants

For a moment flow `s'ₖ = -sₖ₊₁`, differentiating a consecutive-row
determinant leaves only its last row. Differentiating that border along
columns leaves only its last column. Two-border condensation then gives
the Toda identity without differentiating an inverse matrix.
-/

open Matrix
open scoped BigOperators

namespace HTGeometry
noncomputable section

/-- Replace the last index `n` by `n+r`. -/
def hankelBorderIndex (n r : ℕ) (i : Fin (n + 1)) : ℕ :=
  if i = Fin.last n then n + r else i

@[simp] theorem hankelBorderIndex_last (n r : ℕ) :
    hankelBorderIndex n r (Fin.last n) = n + r := by
  simp [hankelBorderIndex]

@[simp] theorem hankelBorderIndex_castSucc (n r : ℕ) (i : Fin n) :
    hankelBorderIndex n r i.castSucc = i := by
  simp [hankelBorderIndex]

@[simp] theorem hankelBorderIndex_zero (n : ℕ) (i : Fin (n + 1)) :
    hankelBorderIndex n 0 i = i := by
  by_cases h : i = Fin.last n <;> simp [hankelBorderIndex, h]

/-- The four terminal minors used in condensation. -/
def hankelBorderMatrix (s : ℕ → ℝ) (n r c : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => s (hankelBorderIndex n r i + hankelBorderIndex n c j)

@[simp] theorem hankelBorderMatrix_zero_zero (s : ℕ → ℝ) (n : ℕ) :
    hankelBorderMatrix s n 0 0 = momentHankelMatrix s (n + 1) := by
  ext i j
  simp [hankelBorderMatrix, momentHankelMatrix]

theorem hankelBorderMatrix_transpose (s : ℕ → ℝ) (n r c : ℕ) :
    (hankelBorderMatrix s n r c)ᵀ = hankelBorderMatrix s n c r := by
  ext i j
  simp [hankelBorderMatrix, add_comm]

private def realDetRows (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ where
  toMultilinearMap := (Matrix.detRowAlternating :
    (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap
  cont := continuous_id.matrix_det

/-- Consecutive rows collapse the determinant derivative to one terminal border. -/
theorem hasDerivAt_consecutiveHankelRows
    {s : ℝ → ℕ → ℝ} {a : ℝ} (hs : ∀ k,
      HasDerivAt (fun t => s t k) (-s a (k + 1)) a)
    (n : ℕ) (c : Fin (n + 1) → ℕ) :
    HasDerivAt (fun t => Matrix.det (fun i j : Fin (n + 1) => s t (i + c j)))
      (-Matrix.det (fun i j : Fin (n + 1) => s a (hankelBorderIndex n 1 i + c j))) a := by
  classical
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j => s a (i + c j)
  have hM : HasDerivAt (fun t (i j : Fin (n + 1)) => s t (i + c j))
      (fun i j => -s a (i + c j + 1)) a :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hs (i + c j)
  have h := ((realDetRows (n + 1)).hasFDerivAt A).comp_hasDerivAt a hM
  change HasDerivAt _
    ((realDetRows (n + 1)).linearDeriv A (fun i j => -s a (i + c j + 1))) a at h
  refine h.congr_deriv ?_
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i : Fin (n + 1), (A.updateRow i (fun j => -s a (i + c j + 1))).det) = _
  have hrow (i : Fin (n + 1)) :
      (A.updateRow i (fun j => -s a (i + c j + 1))).det =
        -(A.updateRow i (fun j => s a (i + c j + 1))).det := by
    simpa only [Pi.smul_def, smul_eq_mul, neg_one_mul] using
      Matrix.det_updateRow_smul A i (-1 : ℝ) (fun j => s a (i + c j + 1))
  simp_rw [hrow]
  rw [Finset.sum_eq_single (Fin.last n)]
  · congr 2
    ext i j
    by_cases hi : i = Fin.last n
    · subst i
      simp [Matrix.updateRow, hankelBorderIndex, add_assoc, add_comm, add_left_comm]
    · simp [Matrix.updateRow, hankelBorderIndex, hi, A]
  · intro i _ hi
    let u : Fin (n + 1) := ⟨i + 1, by
      have hlt := i.isLt
      have hne : (i : ℕ) ≠ n := fun he => hi (Fin.ext he)
      omega⟩
    have hui : u ≠ i := by
      intro he
      have := congrArg Fin.val he
      dsimp [u] at this
      omega
    have he : (fun j => s a (i + c j + 1)) = A u := by
      funext j
      simp [A, u, add_assoc, add_comm, add_left_comm]
    rw [he, Matrix.det_updateRow_eq_zero hui, neg_zero]
  · simp

theorem hasDerivAt_hankelBorderMatrix_zero
    {s : ℝ → ℕ → ℝ} {a : ℝ} (hs : ∀ k,
      HasDerivAt (fun t => s t k) (-s a (k + 1)) a) (n c : ℕ) :
    HasDerivAt (fun t => (hankelBorderMatrix (s t) n 0 c).det)
      (-(hankelBorderMatrix (s a) n 1 c).det) a := by
  change HasDerivAt (fun t => Matrix.det (fun i j : Fin (n + 1) =>
    s t (hankelBorderIndex n 0 i + hankelBorderIndex n c j)))
    (-Matrix.det (fun i j : Fin (n + 1) =>
      s a (hankelBorderIndex n 1 i + hankelBorderIndex n c j))) a
  simpa only [hankelBorderMatrix, hankelBorderIndex_zero] using
    hasDerivAt_consecutiveHankelRows hs n (hankelBorderIndex n c)

theorem hasDerivAt_hankelBorderMatrix_one_zero
    {s : ℝ → ℕ → ℝ} {a : ℝ} (hs : ∀ k,
      HasDerivAt (fun t => s t k) (-s a (k + 1)) a) (n : ℕ) :
    HasDerivAt (fun t => (hankelBorderMatrix (s t) n 1 0).det)
      (-(hankelBorderMatrix (s a) n 1 1).det) a := by
  have he (t : ℝ) : (hankelBorderMatrix (s t) n 1 0).det =
      (hankelBorderMatrix (s t) n 0 1).det := by
    rw [← hankelBorderMatrix_transpose, Matrix.det_transpose]
  simpa only [he] using hasDerivAt_hankelBorderMatrix_zero hs n 1

/-- Algebraic condensation at a regular preceding head. The heat specialization
extends this identity to singular heads by continuity. -/
theorem hankelBorder_condensation (s : ℕ → ℝ) (n : ℕ)
    (hn : (momentHankelMatrix s n).det ≠ 0) :
    (momentHankelMatrix s (n + 1)).det * (hankelBorderMatrix s n 1 1).det -
        (hankelBorderMatrix s n 1 0).det ^ 2 =
      (momentHankelMatrix s n).det * (momentHankelMatrix s (n + 2)).det := by
  classical
  let D := momentHankelMatrix s n
  let B : Matrix (Fin n) (Fin 2) ℝ := fun i j => s (i + (n + j))
  let C : Matrix (Fin 2) (Fin n) ℝ := fun i j => s ((n + i) + j)
  let E : Matrix (Fin 2) (Fin 2) ℝ := fun i j => s ((n + i) + (n + j))
  letI : Invertible D := Matrix.invertibleOfIsUnitDet D (isUnit_iff_ne_zero.mpr hn)
  have hfull : Matrix.fromBlocks D B C E =
      (momentHankelMatrix s (n + 2)).submatrix finSumFinEquiv finSumFinEquiv := by
    ext (i | i) (j | j) <;>
      simp [D, B, C, E, momentHankelMatrix, finSumFinEquiv]
  have hminor (i j : Fin 2) :
      GaloisForLFunctions.HTGeometry.twoBorderMinor D B C E i j =
        (hankelBorderMatrix s n i j).submatrix
          (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) finSumFinEquiv := by
    have hcast (u : Fin n) : Fin.castAdd 1 u ≠ Fin.last n := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_last] at hv
      exact (Nat.ne_of_lt u.isLt) hv
    have hnat : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext (by simp)
    ext (u | u) (v | v)
    · simp [GaloisForLFunctions.HTGeometry.twoBorderMinor, D,
        hankelBorderMatrix, momentHankelMatrix, finSumFinEquiv, hankelBorderIndex, hcast]
    · have hv : v = 0 := Subsingleton.elim _ _
      subst v
      simp [GaloisForLFunctions.HTGeometry.twoBorderMinor, B,
        hankelBorderMatrix, finSumFinEquiv, hankelBorderIndex, hcast, hnat]
    · have hu : u = 0 := Subsingleton.elim _ _
      subst u
      simp [GaloisForLFunctions.HTGeometry.twoBorderMinor, C,
        hankelBorderMatrix, finSumFinEquiv, hankelBorderIndex, hcast, hnat]
    · have hu : u = 0 := Subsingleton.elim _ _
      have hv : v = 0 := Subsingleton.elim _ _
      subst u
      subst v
      simp [GaloisForLFunctions.HTGeometry.twoBorderMinor, E,
        hankelBorderMatrix, finSumFinEquiv, hankelBorderIndex, hnat]
  have h := GaloisForLFunctions.HTGeometry.det_fromBlocks_twoBorder_mul_center D B C E
  rw [hfull, Matrix.det_submatrix_equiv_self] at h
  simp only [hminor, Matrix.det_submatrix_equiv_self, Fin.val_zero, Fin.val_one,
    hankelBorderMatrix_zero_zero] at h
  have hc : (hankelBorderMatrix s n 0 1).det =
      (hankelBorderMatrix s n 1 0).det := by
    rw [← hankelBorderMatrix_transpose, Matrix.det_transpose]
  rw [hc] at h
  simpa only [D, pow_two, mul_comm] using h.symm

end
end HTGeometry
