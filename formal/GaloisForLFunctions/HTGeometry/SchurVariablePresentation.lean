import GaloisForLFunctions.HTGeometry.RectangularSchurTopEntry
import Mathlib.Algebra.MvPolynomial.Division
import GaloisForLFunctions.HTGeometry.MvLinearIrreducible

/-!
# Presenting the complete homogeneous coefficients with the top one first

The rectangular section of parameters `m` and `n` involves the coefficients of index at most
`n + m - 1`.  Indexing them in reverse — the largest first — presents the section over a polynomial
ring in which the corner entry is the first variable and every other entry is free of it.

That is the presentation the corner criterion for irreducibility consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K]

/-- The complete homogeneous coefficients as variables, largest index first, with the convention
that the zeroth coefficient is one. -/
noncomputable def schurVar (K : Type*) [Field K] (L : ℕ) (k : ℕ) : MvPolynomial (Fin L) K :=
  if k = 0 then 1 else if h : L - k < L then MvPolynomial.X ⟨L - k, h⟩ else 0

theorem schurVar_top {L : ℕ} (hL : 0 < L) :
    schurVar K L L = MvPolynomial.X (⟨0, hL⟩ : Fin L) := by
  rw [schurVar, if_neg (by omega), dif_pos (by omega : L - L < L)]
  congr 1
  refine Fin.ext ?_
  show L - L = 0
  omega

/-- **Every coefficient below the top is free of the first variable.** -/
theorem degreeOf_zero_schurVar {L k : ℕ} (hL : 0 < L) (hkL : k ≤ L) (hk : k ≠ L) :
    MvPolynomial.degreeOf (⟨0, hL⟩ : Fin L) (schurVar K L k) = 0 := by
  rw [schurVar]
  by_cases h0 : k = 0
  · rw [if_pos h0, MvPolynomial.degreeOf_one]
  · rw [if_neg h0]
    by_cases hlt : L - k < L
    · refine (dif_pos hlt) ▸ MvPolynomial.degreeOf_X_of_ne ?_
      intro hcon
      rw [Fin.mk.injEq] at hcon
      omega
    · rw [dif_neg hlt, MvPolynomial.degreeOf_zero]

/-- **The presentation shifts by two when the rectangle shrinks.**  The corner expansion drops the
top two coefficient indices, so a coefficient of index at most `L'` is the same variable read two
places later. -/
theorem schurVar_shift {L' k : ℕ} (hk : k ≤ L') :
    schurVar K (L' + 2) k =
      MvPolynomial.rename (fun j : Fin L' => (j.succ).succ) (schurVar K L' k) := by
  rw [schurVar, schurVar]
  by_cases h0 : k = 0
  · rw [if_pos h0, if_pos h0, map_one]
  · rw [if_neg h0, if_neg h0]
    by_cases hlt : L' - k < L'
    · rw [dif_pos hlt, dif_pos (by omega : L' + 2 - k < L' + 2), MvPolynomial.rename_X]
      congr 1
      refine Fin.ext ?_
      show L' + 2 - k = (L' - k) + 1 + 1
      omega
    · rw [dif_neg hlt, dif_neg ?_, map_zero]
      have hkL : k = L' := by omega
      omega

/-! ## The base rectangle -/

/-- **A rectangle of height one is a single coefficient.** -/
theorem det_rectangularSchurToeplitz_one {n : ℕ} (hn : 0 < n) :
    (rectangularSchurToeplitz (schurVar K n) n 1).det =
      MvPolynomial.X (⟨0, hn⟩ : Fin n) := by
  rw [Matrix.det_fin_one, rectangularSchurToeplitz]
  have hidx : ((0 : Fin 1) : ℕ) = 0 := rfl
  rw [hidx, if_pos (by omega : (0 : ℕ) ≤ n + 0), show n + 0 - 0 = n by omega]
  exact schurVar_top hn

/-- **Hence it is irreducible**, being a variable. -/
theorem irreducible_det_rectangularSchurToeplitz_one {n : ℕ} (hn : 0 < n) :
    Irreducible (rectangularSchurToeplitz (schurVar K n) n 1).det := by
  rw [det_rectangularSchurToeplitz_one hn]
  exact (MvPolynomial.X_prime (R := K) (i := (⟨0, hn⟩ : Fin n))).irreducible

/-! ## The degenerate rectangle -/

/-- **At shift zero the section is lower triangular with unit diagonal.** -/
theorem rectangularSchurToeplitz_zero_shift_upper {L m : ℕ} (r i : Fin m) (hri : r < i) :
    rectangularSchurToeplitz (schurVar K L) 0 m r i = 0 := by
  rw [rectangularSchurToeplitz, if_neg]
  show ¬ (i : ℕ) ≤ 0 + (r : ℕ)
  have : (r : ℕ) < (i : ℕ) := hri
  omega

/-- **Hence its determinant is one, so a rectangle of shift zero contributes a unit.** -/
theorem det_rectangularSchurToeplitz_zero_shift {L m : ℕ} :
    (rectangularSchurToeplitz (schurVar K L) 0 m).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i j h => rectangularSchurToeplitz_zero_shift_upper i j h)]
  refine Finset.prod_eq_one fun r _ => ?_
  rw [rectangularSchurToeplitz, if_pos (by omega : (r : ℕ) ≤ 0 + (r : ℕ)), schurVar,
    if_pos (by omega : 0 + (r : ℕ) - (r : ℕ) = 0)]

/-! ## The corner minor -/

/-- **The corner minor of a rectangle is the smaller rectangle, shifted.**  Deleting the last row and
the first column of the `(m'+1, n'+1)` section leaves the `(m', n')` section, read two variables
later. -/
theorem submatrix_rectangularSchurToeplitz {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') :
    ((rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).submatrix
        (Fin.last m').succAbove Fin.succ) =
      (rectangularSchurToeplitz (schurVar K (n' + m' - 1)) n' m').map
        (MvPolynomial.rename (fun j : Fin (n' + m' - 1) => (j.succ).succ)) := by
  refine Matrix.ext fun r i => ?_
  rw [Matrix.submatrix_apply, Matrix.map_apply, Fin.succAbove_last,
    rectangularSchurToeplitz, rectangularSchurToeplitz]
  have hcast : ((Fin.castSucc r : Fin (m' + 1)) : ℕ) = (r : ℕ) := rfl
  have hsucc : ((Fin.succ i : Fin (m' + 1)) : ℕ) = (i : ℕ) + 1 := rfl
  rw [hcast, hsucc]
  have hr := r.isLt
  by_cases hg : (i : ℕ) ≤ n' + (r : ℕ)
  · rw [if_pos (by omega : (i : ℕ) + 1 ≤ n' + 1 + (r : ℕ)), if_pos hg,
      show n' + 1 + (r : ℕ) - ((i : ℕ) + 1) = n' + (r : ℕ) - (i : ℕ) by omega]
    exact schurVar_shift (by omega)
  · rw [if_neg (by omega : ¬ ((i : ℕ) + 1 ≤ n' + 1 + (r : ℕ))), if_neg hg, map_zero]

/-- **The determinant of the corner minor is the smaller determinant, shifted.** -/
theorem det_submatrix_rectangularSchurToeplitz {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') :
    ((rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).submatrix
        (Fin.last m').succAbove Fin.succ).det =
      MvPolynomial.rename (fun j : Fin (n' + m' - 1) => (j.succ).succ)
        ((rectangularSchurToeplitz (schurVar K (n' + m' - 1)) n' m').det) := by
  rw [submatrix_rectangularSchurToeplitz hn hm]
  exact (AlgHom.map_det
    (MvPolynomial.rename (R := K) (fun j : Fin (n' + m' - 1) => (j.succ).succ)) _).symm

/-- **The corner minor in the form the criterion consumes.**  It is `rename Fin.succ` of the
once-shifted smaller determinant. -/
theorem det_submatrix_eq_rename_succ {n' m' : ℕ} (hn : 0 < n') (hm : 0 < m') :
    ((rectangularSchurToeplitz (schurVar K (n' + m' - 1 + 2)) (n' + 1) (m' + 1)).submatrix
        (Fin.last m').succAbove Fin.succ).det =
      MvPolynomial.rename Fin.succ
        (MvPolynomial.rename Fin.succ
          ((rectangularSchurToeplitz (schurVar K (n' + m' - 1)) n' m').det)) := by
  rw [det_submatrix_rectangularSchurToeplitz hn hm, MvPolynomial.rename_rename]
  rfl

/-! ## Evaluating at the unit tail -/

/-- The unit tail as a specialisation of the reversed presentation. -/
noncomputable def unitTailEval (K : Type*) [Field K] (L n : ℕ) :
    MvPolynomial (Fin L) K →ₐ[K] K :=
  MvPolynomial.aeval (fun j : Fin L => if L - (j : ℕ) = n then (1 : K) else 0)

/-- **A coefficient of positive index evaluates to its unit-tail value.** -/
theorem unitTailEval_schurVar {L n k : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L) :
    unitTailEval K L n (schurVar K L k) = if k = n then 1 else 0 := by
  rw [unitTailEval, schurVar, if_neg (by omega : ¬ k = 0),
    dif_pos (by omega : L - k < L), MvPolynomial.aeval_X]
  show (if L - (L - k) = n then (1 : K) else 0) = if k = n then 1 else 0
  rw [show L - (L - k) = k by omega]

/-- **The zeroth coefficient evaluates to one, not to its unit-tail value.**  The convention that the
zeroth complete homogeneous coefficient is one is not a variable, so no specialisation can set it to
zero; the unit tail is a separating point only when the index zero does not occur in the section,
that is when the shift is at least the height. -/
theorem unitTailEval_schurVar_zero {L n : ℕ} :
    unitTailEval K L n (schurVar K L 0) = 1 := by
  rw [unitTailEval, schurVar, if_pos rfl, map_one]

/-- **In the valid regime the unit tail sends the section to the identity.**  When the shift is at
least the height, no entry has index zero, so every entry evaluates to its unit-tail value. -/
theorem map_unitTailEval_rectangularSchurToeplitz [DecidableEq K] {n m : ℕ} (hnm : m ≤ n) :
    (rectangularSchurToeplitz (schurVar K (n + m - 1)) n m).map (unitTailEval K (n + m - 1) n) =
      rectangularSchurToeplitz (fun k => if k = n then (1 : K) else 0) n m := by
  refine Matrix.ext fun r i => ?_
  rw [Matrix.map_apply, rectangularSchurToeplitz, rectangularSchurToeplitz]
  have hr := r.isLt
  have hi := i.isLt
  by_cases hg : (i : ℕ) ≤ n + (r : ℕ)
  · rw [if_pos hg, if_pos hg]
    exact unitTailEval_schurVar (by omega) (by omega)
  · rw [if_neg hg, if_neg hg, map_zero]

/-- **Hence the determinant evaluates to one there.** -/
theorem unitTailEval_det_rectangularSchurToeplitz [DecidableEq K] {n m : ℕ} (hnm : m ≤ n) :
    unitTailEval K (n + m - 1) n
      ((rectangularSchurToeplitz (schurVar K (n + m - 1)) n m).det) = 1 := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply,
    map_unitTailEval_rectangularSchurToeplitz hnm,
    rectangularSchurToeplitz_unit_tail, Matrix.det_one]

/-- **The unit-tail evaluation is compatible with adding a variable.**  Reading a polynomial one
variable later and evaluating at the unit tail is evaluating at the unit tail of the smaller
presentation. -/
theorem unitTailEval_rename_succ {L n : ℕ} (p : MvPolynomial (Fin L) K) :
    unitTailEval K (L + 1) n (MvPolynomial.rename Fin.succ p) = unitTailEval K L n p := by
  have hfun : ((fun j : Fin (L + 1) => if L + 1 - (j : ℕ) = n then (1 : K) else 0) ∘ Fin.succ)
      = fun j : Fin L => if L - (j : ℕ) = n then (1 : K) else 0 := by
    refine _root_.funext fun j => ?_
    show (if L + 1 - ((j.succ : Fin (L + 1)) : ℕ) = n then (1 : K) else 0) =
      if L - (j : ℕ) = n then (1 : K) else 0
    rw [show ((j.succ : Fin (L + 1)) : ℕ) = (j : ℕ) + 1 from rfl,
      show L + 1 - ((j : ℕ) + 1) = L - (j : ℕ) by omega]
  rw [unitTailEval, unitTailEval, MvPolynomial.aeval_rename, hfun]

end GaloisForLFunctions.HTGeometry
