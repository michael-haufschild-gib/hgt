import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelLocalizedRetraction
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Localized Hazewinkel coordinate equivalence

After inverting the leading Hankel determinant, the universal rank-`n` Hankel stage is isomorphic
to the localization of the polynomial ring in its first `2n - 1` nonconstant coefficients. The
proof reconstructs every later coefficient from the unique linear recurrence and proves both
composites of the coordinate maps are identities. Consequently the localized universal stage is
an integral domain.
-/

open scoped BigOperators

theorem bottom_eq_schur_sum_of_block_det_zero
    {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (b z : Fin n → R) (a : R)
    (hunit : IsUnit M.det)
    (hdet : (Matrix.fromBlocks M (fun i (_ : Fin 1) => b i)
      (fun (_ : Fin 1) j => z j) (fun _ _ => a)).det = 0) :
    a = ∑ j : Fin n, z j * (M⁻¹.mulVec b) j := by
  let B : Matrix (Fin n) (Fin 1) R := fun i _ => b i
  let C : Matrix (Fin 1) (Fin n) R := fun _ j => z j
  let D : Matrix (Fin 1) (Fin 1) R := fun _ _ => a
  change (Matrix.fromBlocks M B C D).det = 0 at hdet
  cases (M.isUnit_iff_isUnit_det.mpr hunit).nonempty_invertible
  rw [Matrix.det_fromBlocks₁₁] at hdet
  have hschur : Matrix.det (D - C * ⅟M * B) = 0 := by
    exact hunit.mul_right_inj.mp (by simpa using hdet)
  rw [Matrix.det_fin_one] at hschur
  simp only [D, C, B, Matrix.sub_apply, Matrix.mul_apply] at hschur
  rw [Matrix.invOf_eq_nonsing_inv] at hschur
  simp only [Matrix.mulVec, dotProduct]
  change a - (∑ x, (∑ j, z j * M⁻¹ j x) * b x) = 0 at hschur
  rw [sub_eq_zero] at hschur
  rw [hschur]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

namespace RHTower
noncomputable section

def deningerHazewinkelStageLocalizationEval (n : ℕ) :
    MvPolynomial ℕ ℤ →+* DeningerHazewinkelStageLocalization n :=
  (algebraMap (DeningerHazewinkelStageQuotient n)
    (DeningerHazewinkelStageLocalization n)).comp
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n))

def deningerHazewinkelStageLocalizedSequence (n s : ℕ) :
    DeningerHazewinkelStageLocalization n :=
  deningerHazewinkelStageLocalizationEval n
    (deningerHazewinkelUniversalCoeff s)

def deningerHazewinkelStageLocalizedMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (DeningerHazewinkelStageLocalization n) :=
  fun i j => deningerHazewinkelStageLocalizedSequence n (i.val + j.val)

def deningerHazewinkelStageLocalizedRhs (n : ℕ) :
    Fin n → DeningerHazewinkelStageLocalization n :=
  fun i => deningerHazewinkelStageLocalizedSequence n (i.val + n)

def deningerHazewinkelStageLocalizedRecurrence (n : ℕ) :
    Fin n → DeningerHazewinkelStageLocalization n :=
  (deningerHazewinkelStageLocalizedMatrix n)⁻¹.mulVec
    (deningerHazewinkelStageLocalizedRhs n)

theorem deningerHazewinkelStageLocalizedMatrix_det_isUnit (n : ℕ) :
    IsUnit (deningerHazewinkelStageLocalizedMatrix n).det := by
  have hdet : (deningerHazewinkelStageLocalizedMatrix n).det =
      algebraMap _ _
        (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
          (deningerHazewinkelLeadingDeterminant n)) := by
    change Matrix.det (fun i j : Fin n =>
        deningerHazewinkelStageLocalizedSequence n (i.val + j.val)) =
      algebraMap _ _
        (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
          (Matrix.det fun i j : Fin n =>
            deningerHazewinkelUniversalCoeff (i.val + j.val)))
    rw [(Ideal.Quotient.mk (deningerHazewinkelIdeal n)).map_det,
      (algebraMap (DeningerHazewinkelStageQuotient n)
        (DeningerHazewinkelStageLocalization n)).map_det]
    congr 1
  rw [hdet]
  exact IsLocalization.Away.algebraMap_isUnit _

theorem deningerHazewinkelStageLocalizedRecurrence_solve (n : ℕ) :
    (deningerHazewinkelStageLocalizedMatrix n).mulVec
      (deningerHazewinkelStageLocalizedRecurrence n) =
    deningerHazewinkelStageLocalizedRhs n := by
  rw [deningerHazewinkelStageLocalizedRecurrence, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (deningerHazewinkelStageLocalizedMatrix_det_isUnit n),
    Matrix.one_mulVec]

theorem deningerHazewinkelStageLocalized_rankLT (n : ℕ) :
    ∀ rows cols : Fin (n + 1) → ℕ,
      (Matrix.submatrix
        (fun i j => deningerHazewinkelStageLocalizedSequence n (i + j))
        rows cols).det = 0 := by
  let f : MvPolynomial ℕ ℤ →+* DeningerHazewinkelStageLocalization n :=
    deningerHazewinkelStageLocalizationEval n
  have hf : deningerHazewinkelIdeal n ≤ RingHom.ker f := by
    intro p hp
    apply RingHom.mem_ker.mpr
    change deningerHazewinkelStageLocalizationEval n p = 0
    rw [deningerHazewinkelStageLocalizationEval, RingHom.comp_apply]
    change algebraMap _ _
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n) p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have h := deningerHazewinkelUniversalWitt_map_rankLT n f hf
  intro rows cols
  have hr := h rows cols
  convert hr using 1
  congr 1
  funext i j
  simp [deningerBigWittHankel, deningerHazewinkelStageLocalizedSequence,
    f, deningerHazewinkelStageLocalizationEval, deningerHazewinkelUniversalWitt]

theorem deningerHazewinkelStageLocalizedSequence_recurrence (n i : ℕ) :
    deningerHazewinkelStageLocalizedSequence n (i + n) =
      ∑ j : Fin n, deningerHazewinkelStageLocalizedSequence n (i + j.val) *
        deningerHazewinkelStageLocalizedRecurrence n j := by
  let M := deningerHazewinkelStageLocalizedMatrix n
  let b := deningerHazewinkelStageLocalizedRhs n
  let z : Fin n → DeningerHazewinkelStageLocalization n := fun j =>
    deningerHazewinkelStageLocalizedSequence n (i + j.val)
  let a := deningerHazewinkelStageLocalizedSequence n (i + n)
  let B : Matrix (Fin n) (Fin 1) (DeningerHazewinkelStageLocalization n) :=
    fun r _ => b r
  let C : Matrix (Fin 1) (Fin n) (DeningerHazewinkelStageLocalization n) :=
    fun _ j => z j
  let D : Matrix (Fin 1) (Fin 1) (DeningerHazewinkelStageLocalization n) :=
    fun _ _ => a
  let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
  let rowsSum : Fin n ⊕ Fin 1 → ℕ := Sum.elim (fun r => r.val) (fun _ => i)
  let colsSum : Fin n ⊕ Fin 1 → ℕ := Sum.elim (fun j => j.val) (fun _ => n)
  let rows : Fin (n + 1) → ℕ := rowsSum ∘ e.symm
  let cols : Fin (n + 1) → ℕ := colsSum ∘ e.symm
  have hz := deningerHazewinkelStageLocalized_rankLT n rows cols
  have hblock : Matrix.fromBlocks M B C D =
      (Matrix.submatrix
        (fun r c => deningerHazewinkelStageLocalizedSequence n (r + c))
        rows cols).submatrix e e := by
    ext r c
    rcases r with r | r <;> rcases c with c | c <;>
      simp [M, B, C, D, b, z, a, rows, cols, rowsSum, colsSum, e,
        deningerHazewinkelStageLocalizedMatrix,
        deningerHazewinkelStageLocalizedRhs]
  have hdet : (Matrix.fromBlocks M B C D).det = 0 := by
    rw [hblock, Matrix.det_submatrix_equiv_self]
    exact hz
  have hbottom := bottom_eq_schur_sum_of_block_det_zero M b z a
    (deningerHazewinkelStageLocalizedMatrix_det_isUnit n) hdet
  simpa [M, b, z, a, deningerHazewinkelStageLocalizedRecurrence, mul_comm] using hbottom

theorem deningerHazewinkelParameterToStageLocalization_initialCoeff
    (n : ℕ) {s : ℕ} (hs : s < 2 * n) :
    deningerHazewinkelParameterToStageLocalization n
        (algebraMap _ _ (deningerHazewinkelParameterCoeff n s)) =
      deningerHazewinkelStageLocalizedSequence n s := by
  rw [deningerHazewinkelParameterToStageLocalization,
    IsLocalization.Away.lift_eq,
    deningerHazewinkelParameterToStageLocalizationBase_coeff n hs]
  rfl

theorem deningerHazewinkelParameterToStageLocalization_recurrence (n : ℕ) :
    (fun j => deningerHazewinkelParameterToStageLocalization n
      (deningerHazewinkelLocalizedRecurrence n j)) =
    deningerHazewinkelStageLocalizedRecurrence n := by
  let g := deningerHazewinkelParameterToStageLocalization n
  have hmatrix (i j : Fin n) :
      g (deningerHazewinkelLocalizedMatrix n i j) =
        deningerHazewinkelStageLocalizedMatrix n i j := by
    change g (algebraMap _ _
        (deningerHazewinkelParameterCoeff n (i.val + j.val))) =
      deningerHazewinkelStageLocalizedSequence n (i.val + j.val)
    exact deningerHazewinkelParameterToStageLocalization_initialCoeff n (by omega)
  have hrhs (i : Fin n) :
      g (deningerHazewinkelLocalizedRhs n i) =
        deningerHazewinkelStageLocalizedRhs n i := by
    change g (algebraMap _ _
        (deningerHazewinkelParameterCoeff n (i.val + n))) =
      deningerHazewinkelStageLocalizedSequence n (i.val + n)
    exact deningerHazewinkelParameterToStageLocalization_initialCoeff n (by omega)
  have hmapSolve : (deningerHazewinkelStageLocalizedMatrix n).mulVec
      (fun j => g (deningerHazewinkelLocalizedRecurrence n j)) =
      deningerHazewinkelStageLocalizedRhs n := by
    funext i
    have hi := congrArg g
      (congrFun (deningerHazewinkelLocalizedRecurrence_solve n) i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at hi
    rw [Matrix.mulVec, dotProduct]
    calc
      (∑ j, deningerHazewinkelStageLocalizedMatrix n i j *
          g (deningerHazewinkelLocalizedRecurrence n j)) =
          ∑ j, g (deningerHazewinkelLocalizedMatrix n i j) *
            g (deningerHazewinkelLocalizedRecurrence n j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hmatrix]
      _ = g (deningerHazewinkelLocalizedRhs n i) := hi
      _ = deningerHazewinkelStageLocalizedRhs n i := hrhs i
  have h := congrArg
    (deningerHazewinkelStageLocalizedMatrix n)⁻¹.mulVec
    (hmapSolve.trans (deningerHazewinkelStageLocalizedRecurrence_solve n).symm)
  simpa only [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (deningerHazewinkelStageLocalizedMatrix_det_isUnit n),
    Matrix.one_mulVec] using h

theorem deningerHazewinkelParameterToStageLocalization_localizedSequence
    (n : ℕ) (hn : 0 < n) (s : ℕ) :
    deningerHazewinkelParameterToStageLocalization n
        (deningerHazewinkelLocalizedSequence n hn s) =
      deningerHazewinkelStageLocalizedSequence n s := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
      by_cases hs : s < 2 * n
      · rw [deningerHazewinkelLocalizedSequence_of_lt n hn hs]
        exact deningerHazewinkelParameterToStageLocalization_initialCoeff n hs
      · have hs2n : 2 * n ≤ s := Nat.le_of_not_gt hs
        rw [deningerHazewinkelLocalizedSequence_of_ge n hn hs2n, map_sum]
        simp_rw [map_mul]
        rw [show s = (s - n) + n by omega,
          deningerHazewinkelStageLocalizedSequence_recurrence]
        apply Finset.sum_congr rfl
        intro j hj
        have hrecj := congrFun
          (deningerHazewinkelParameterToStageLocalization_recurrence n) j
        rw [hrecj]
        have hidx : s - n + n - n + j.val = s - n + j.val := by omega
        rw [hidx, ih (s - n + j.val) (by omega)]
        ring

theorem deningerHazewinkelParameterToStage_comp_localizedStageToParameter
    (n : ℕ) (hn : 0 < n) :
    (deningerHazewinkelParameterToStageLocalization n).comp
        (deningerHazewinkelLocalizedStageToParameter n hn) =
      RingHom.id (DeningerHazewinkelStageLocalization n) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
        (deningerHazewinkelLeadingDeterminant n)))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [deningerHazewinkelLocalizedStageToParameter,
      deningerHazewinkelStageLocalizationToParameter,
      deningerHazewinkelUniversalToLocalizedParameter,
      deningerHazewinkelParameterToStageLocalization]
  · intro j
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [deningerHazewinkelLocalizedStageToParameter,
      IsLocalization.Away.lift_eq]
    change deningerHazewinkelParameterToStageLocalization n
        (deningerHazewinkelUniversalToLocalizedParameter n hn
          (MvPolynomial.X j)) = _
    rw [deningerHazewinkelUniversalToLocalizedParameter,
      MvPolynomial.eval₂Hom_X']
    rw [deningerHazewinkelParameterToStageLocalization_localizedSequence]
    rfl

def deningerHazewinkelLocalizedStageEquivParameter (n : ℕ) (hn : 0 < n) :
    DeningerHazewinkelStageLocalization n ≃+*
      DeningerHazewinkelParameterLocalization n :=
  RingEquiv.ofRingHom
    (deningerHazewinkelLocalizedStageToParameter n hn)
    (deningerHazewinkelParameterToStageLocalization n)
    (deningerHazewinkelLocalizedStageToParameter_comp_parameterToStage n hn)
    (deningerHazewinkelParameterToStage_comp_localizedStageToParameter n hn)

theorem deningerHazewinkelStageLocalization_isDomain (n : ℕ) (hn : 0 < n) :
    IsDomain (DeningerHazewinkelStageLocalization n) := by
  letI : IsDomain (DeningerHazewinkelParameterLocalization n) :=
    deningerHazewinkelParameterLocalization_isDomain n hn
  exact (deningerHazewinkelLocalizedStageEquivParameter n hn).toMulEquiv.isDomain _

end
end RHTower
