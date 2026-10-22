import GaloisForLFunctions.HTGeometry.Critical.Reciprocal.NumeratorLastCoordinate
import GaloisForLFunctions.HTGeometry.Critical.Source.ReciprocalNumeratorCanonical
import GaloisForLFunctions.HTGeometry.MvPolynomialAwayComplexPoints

/-!
# Raw-coordinate assignments for critical source meridians

Two explicit assignments vary either marked torus coordinate while keeping the other nonzero.
When the raw and reciprocal marked indices coincide, the reciprocal-numerator affine law gives
the compensating value directly; when they differ, the last coordinate is solved uniquely.  A
unit-disk bound proves the complete source-chart denominator stays nonzero in both cases.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

def criticalRawZeroIndex : Fin (m + n) := ⟨0, by
  have hm : 1 < m := Fact.out
  have hn : 1 < n := Fact.out
  omega⟩
def criticalRawMarkedIndex : Fin (m + n) := ⟨m, by
  have hn : 1 < n := Fact.out
  omega⟩
def criticalRecipMarkedIndex : Fin (m + n) := ⟨n, by
  have hm : 1 < m := Fact.out
  omega⟩

theorem criticalRawZeroIndex_ne_rawMarked :
    criticalRawZeroIndex (m := m) (n := n) ≠ criticalRawMarkedIndex := by
  intro h
  have := congrArg Fin.val h
  simp [criticalRawZeroIndex, criticalRawMarkedIndex] at this
  have hm : 1 < m := Fact.out
  omega

theorem criticalRawZeroIndex_ne_recipMarked :
    criticalRawZeroIndex (m := m) (n := n) ≠ criticalRecipMarkedIndex := by
  intro h
  have := congrArg Fin.val h
  simp [criticalRawZeroIndex, criticalRecipMarkedIndex] at this
  have hn : 1 < n := Fact.out
  omega

theorem criticalRecipMarkedIndex_ne_rawMarked (h : n ≠ m) :
    criticalRecipMarkedIndex (m := m) (n := n) ≠ criticalRawMarkedIndex := by
  intro heq
  apply h
  exact congrArg Fin.val heq

def criticalFirstMeridianBase (z : ℂ) : Fin (m + n) → ℂ :=
  Function.update (criticalReciprocalTestPoint ℂ) criticalRawMarkedIndex z

def criticalSecondMeridianBase : Fin (m + n) → ℂ :=
  Function.update (criticalReciprocalTestPoint ℂ) criticalRawMarkedIndex 1

def criticalFirstMeridianRaw (z : ℂ) : Fin (m + n) → ℂ :=
  if n = m then criticalFirstMeridianBase z
  else
    let base := criticalFirstMeridianBase z
    let R := MvPolynomial.eval base (criticalReciprocalNumerator ℂ (m + n) n)
    Function.update base criticalRecipMarkedIndex (R - 1)

def criticalSecondMeridianRaw (z : ℂ) : Fin (m + n) → ℂ :=
  if n = m then
    Function.update (criticalReciprocalTestPoint ℂ) criticalRawMarkedIndex
      ((-1 : ℂ) ^ m - z)
  else
    let base := criticalSecondMeridianBase (m := m) (n := n)
    let R := MvPolynomial.eval base (criticalReciprocalNumerator ℂ (m + n) n)
    Function.update base criticalRecipMarkedIndex (R - z)

theorem criticalFirstMeridianRaw_zero (z : ℂ) :
    criticalFirstMeridianRaw (m := m) (n := n) z criticalRawZeroIndex = 1 := by
  unfold criticalFirstMeridianRaw
  split_ifs with h
  · change Function.update (criticalReciprocalTestPoint ℂ)
        (criticalRawMarkedIndex (m := m) (n := n)) z
          (criticalRawZeroIndex (m := m) (n := n)) = 1
    rw [show Function.update (criticalReciprocalTestPoint ℂ)
        (criticalRawMarkedIndex (m := m) (n := n)) z
          (criticalRawZeroIndex (m := m) (n := n)) =
          criticalReciprocalTestPoint ℂ
            (criticalRawZeroIndex (m := m) (n := n)) by
      simp [Function.update,
        criticalRawZeroIndex_ne_rawMarked (m := m) (n := n)]]
    simp [criticalRawZeroIndex, criticalReciprocalTestPoint]
  · dsimp only
    rw [show Function.update (criticalFirstMeridianBase z)
        (criticalRecipMarkedIndex (m := m) (n := n)) _
          (criticalRawZeroIndex (m := m) (n := n)) =
          criticalFirstMeridianBase z
            (criticalRawZeroIndex (m := m) (n := n)) by
      simp [Function.update,
        criticalRawZeroIndex_ne_recipMarked (m := m) (n := n)]]
    rw [show criticalFirstMeridianBase z
        (criticalRawZeroIndex (m := m) (n := n)) =
          criticalReciprocalTestPoint ℂ
            (criticalRawZeroIndex (m := m) (n := n)) by
      simp [criticalFirstMeridianBase, Function.update,
        criticalRawZeroIndex_ne_rawMarked (m := m) (n := n)]]
    simp [criticalRawZeroIndex, criticalReciprocalTestPoint]

theorem criticalSecondMeridianRaw_zero (z : ℂ) :
    criticalSecondMeridianRaw (m := m) (n := n) z criticalRawZeroIndex = 1 := by
  unfold criticalSecondMeridianRaw
  split_ifs with h
  · rw [show Function.update (criticalReciprocalTestPoint ℂ)
        (criticalRawMarkedIndex (m := m) (n := n)) ((-1 : ℂ) ^ m - z)
          (criticalRawZeroIndex (m := m) (n := n)) =
          criticalReciprocalTestPoint ℂ
            (criticalRawZeroIndex (m := m) (n := n)) by
      simp [Function.update,
        criticalRawZeroIndex_ne_rawMarked (m := m) (n := n)]]
    simp [criticalRawZeroIndex, criticalReciprocalTestPoint]
  · dsimp only
    rw [show Function.update (criticalSecondMeridianBase (m := m) (n := n))
        (criticalRecipMarkedIndex (m := m) (n := n)) _
          (criticalRawZeroIndex (m := m) (n := n)) =
          criticalSecondMeridianBase (m := m) (n := n)
            (criticalRawZeroIndex (m := m) (n := n)) by
      simp [Function.update,
        criticalRawZeroIndex_ne_recipMarked (m := m) (n := n)]]
    simp [criticalSecondMeridianBase, Function.update,
      criticalRawZeroIndex_ne_rawMarked (m := m) (n := n), criticalRawZeroIndex,
      criticalReciprocalTestPoint]

theorem criticalFirstMeridianRaw_marked (z : ℂ) :
    criticalFirstMeridianRaw (m := m) (n := n) z criticalRawMarkedIndex = z := by
  rw [criticalFirstMeridianRaw]
  split_ifs with h
  · simp [criticalFirstMeridianBase]
  · dsimp only
    rw [show Function.update (criticalFirstMeridianBase z)
        (criticalRecipMarkedIndex (m := m) (n := n)) _
          (criticalRawMarkedIndex (m := m) (n := n)) =
          criticalFirstMeridianBase z
            (criticalRawMarkedIndex (m := m) (n := n)) by
      simp [Function.update,
        (criticalRecipMarkedIndex_ne_rawMarked (m := m) (n := n) h).symm]]
    simp [criticalFirstMeridianBase, Function.update]

theorem criticalSecondMeridianRaw_marked (z : ℂ) :
    criticalSecondMeridianRaw (m := m) (n := n) z criticalRawMarkedIndex =
      if n = m then (-1 : ℂ) ^ m - z else 1 := by
  rw [criticalSecondMeridianRaw]
  split_ifs with h
  · simp [criticalRawMarkedIndex]
  · dsimp only
    rw [show Function.update (criticalSecondMeridianBase (m := m) (n := n))
        (criticalRecipMarkedIndex (m := m) (n := n)) _
          (criticalRawMarkedIndex (m := m) (n := n)) =
          criticalSecondMeridianBase (m := m) (n := n)
            (criticalRawMarkedIndex (m := m) (n := n)) by
      simp [Function.update,
        (criticalRecipMarkedIndex_ne_rawMarked (m := m) (n := n) h).symm]]
    simp [criticalSecondMeridianBase, Function.update]

theorem continuous_criticalFirstMeridianBase :
    Continuous (criticalFirstMeridianBase (m := m) (n := n)) := by
  apply continuous_pi
  intro i
  by_cases hi : i = criticalRawMarkedIndex
  · subst i
    simp [criticalFirstMeridianBase, Function.update]
    exact continuous_id
  · simp [criticalFirstMeridianBase, Function.update, hi]
    exact continuous_const

theorem continuous_criticalFirstMeridianRaw :
    Continuous (criticalFirstMeridianRaw (m := m) (n := n)) := by
  apply continuous_pi
  intro i
  unfold criticalFirstMeridianRaw
  split_ifs with h
  · simp only [criticalFirstMeridianBase]
    by_cases hi : i = criticalRawMarkedIndex
    · subst i
      simp
      exact continuous_id
    · simp [Function.update, hi]
      exact continuous_const
  · dsimp only
    by_cases hin : i = criticalRecipMarkedIndex
    · subst i
      simp [Function.update]
      exact (AlgSpec.continuous_mvPolynomial_eval _).comp
        continuous_criticalFirstMeridianBase |>.sub continuous_const
    · simp only [Function.update, hin, ↓reduceIte]
      simp only [criticalFirstMeridianBase]
      by_cases him : i = criticalRawMarkedIndex
      · subst i
        simp
        exact continuous_id
      · simp [Function.update, him]
        exact continuous_const

theorem continuous_criticalSecondMeridianRaw :
    Continuous (criticalSecondMeridianRaw (m := m) (n := n)) := by
  apply continuous_pi
  intro i
  unfold criticalSecondMeridianRaw
  split_ifs with h
  · by_cases hi : i = criticalRawMarkedIndex
    · subst i
      simp
      exact continuous_const.sub continuous_id
    · simp [Function.update, hi]
      exact continuous_const
  · dsimp only
    by_cases hin : i = criticalRecipMarkedIndex
    · subst i
      simp [Function.update]
      exact continuous_const.sub continuous_id
    · simp only [Function.update, hin, ↓reduceIte]
      simp only [criticalSecondMeridianBase]
      simp
      exact continuous_const

theorem criticalFirstMeridianBase_zero (z : ℂ) :
    criticalFirstMeridianBase (m := m) (n := n) z criticalRawZeroIndex = 1 := by
  rw [show criticalFirstMeridianBase z
      (criticalRawZeroIndex (m := m) (n := n)) =
        criticalReciprocalTestPoint ℂ
          (criticalRawZeroIndex (m := m) (n := n)) by
    simp [criticalFirstMeridianBase, Function.update,
      criticalRawZeroIndex_ne_rawMarked (m := m) (n := n)]]
  simp [criticalRawZeroIndex, criticalReciprocalTestPoint]

theorem criticalSecondMeridianBase_zero :
    criticalSecondMeridianBase (m := m) (n := n) criticalRawZeroIndex = 1 := by
  rw [show criticalSecondMeridianBase (m := m) (n := n)
      (criticalRawZeroIndex (m := m) (n := n)) =
        criticalReciprocalTestPoint ℂ
          (criticalRawZeroIndex (m := m) (n := n)) by
    simp [criticalSecondMeridianBase, Function.update,
      criticalRawZeroIndex_ne_rawMarked (m := m) (n := n)]]
  simp [criticalRawZeroIndex, criticalReciprocalTestPoint]

theorem criticalFirstMeridianBase_recipMarked_of_ne (h : n ≠ m) (z : ℂ) :
    criticalFirstMeridianBase (m := m) (n := n) z criticalRecipMarkedIndex = 0 := by
  rw [criticalFirstMeridianBase]
  rw [show Function.update (criticalReciprocalTestPoint ℂ)
      (criticalRawMarkedIndex (m := m) (n := n)) z
        (criticalRecipMarkedIndex (m := m) (n := n)) =
        criticalReciprocalTestPoint ℂ
          (criticalRecipMarkedIndex (m := m) (n := n)) by
    simp [Function.update, criticalRecipMarkedIndex_ne_rawMarked h]]
  simp [criticalRecipMarkedIndex, criticalReciprocalTestPoint]
  have hn : 1 < n := Fact.out
  omega

theorem criticalSecondMeridianBase_recipMarked_of_ne (h : n ≠ m) :
    criticalSecondMeridianBase (m := m) (n := n) criticalRecipMarkedIndex = 0 := by
  rw [criticalSecondMeridianBase]
  rw [show Function.update (criticalReciprocalTestPoint ℂ)
      (criticalRawMarkedIndex (m := m) (n := n)) 1
        (criticalRecipMarkedIndex (m := m) (n := n)) =
        criticalReciprocalTestPoint ℂ
          (criticalRecipMarkedIndex (m := m) (n := n)) by
    simp [Function.update, criticalRecipMarkedIndex_ne_rawMarked h]]
  simp [criticalRecipMarkedIndex, criticalReciprocalTestPoint]
  have hn : 1 < n := Fact.out
  omega

theorem criticalFirstMeridianRaw_reciprocal (z : ℂ) :
    MvPolynomial.eval (criticalFirstMeridianRaw (m := m) (n := n) z)
      (criticalReciprocalNumerator ℂ (m + n) n) =
        if n = m then (-1 : ℂ) ^ m - z else 1 := by
  unfold criticalFirstMeridianRaw
  split_ifs with h
  · subst n
    simpa [criticalFirstMeridianBase, criticalRawMarkedIndex] using
      (eval_criticalReciprocalNumerator_update_testPoint
        (L := m + m) (k := m) (Fact.out : 1 < m) (by
          have hm : 1 < m := Fact.out
          omega) z)
  · dsimp only
    exact eval_criticalReciprocalNumerator_update_to
      (k := n) (L := m + n) (by have : 1 < n := Fact.out; omega) (by
        have : 1 < m := Fact.out
        omega)
      (criticalFirstMeridianBase z)
      (criticalFirstMeridianBase_zero (m := m) (n := n) z)
      (criticalFirstMeridianBase_recipMarked_of_ne h z) 1

theorem criticalSecondMeridianRaw_reciprocal (z : ℂ) :
    MvPolynomial.eval (criticalSecondMeridianRaw (m := m) (n := n) z)
      (criticalReciprocalNumerator ℂ (m + n) n) = z := by
  unfold criticalSecondMeridianRaw
  split_ifs with h
  · subst n
    calc
      MvPolynomial.eval
          (Function.update (criticalReciprocalTestPoint ℂ) criticalRawMarkedIndex
            ((-1 : ℂ) ^ m - z))
          (criticalReciprocalNumerator ℂ (m + m) m) =
          (-1 : ℂ) ^ m - ((-1 : ℂ) ^ m - z) := by
            simpa [criticalRawMarkedIndex] using
              (eval_criticalReciprocalNumerator_update_testPoint
                (L := m + m) (k := m) (Fact.out : 1 < m) (by
                  have hm : 1 < m := Fact.out
                  omega)
                ((-1 : ℂ) ^ m - z))
      _ = z := by ring
  · dsimp only
    exact eval_criticalReciprocalNumerator_update_to
      (k := n) (L := m + n) (by have : 1 < n := Fact.out; omega) (by
        have : 1 < m := Fact.out
        omega)
      criticalSecondMeridianBase
      (criticalSecondMeridianBase_zero (m := m) (n := n))
      (criticalSecondMeridianBase_recipMarked_of_ne h) z

theorem neg_one_pow_sub_ne_zero_of_norm_lt_one (k : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) : (-1 : ℂ) ^ k - z ≠ 0 := by
  intro hzero
  have heq : (-1 : ℂ) ^ k = z := sub_eq_zero.mp hzero
  have hnorm : ‖z‖ = 1 := by
    rw [← heq, norm_pow]
    simp
  linarith

theorem criticalFirstMeridianRaw_chartPoly_ne_zero {z : ℂ}
    (hz : z ≠ 0) (hsmall : ‖z‖ < 1) :
    MvPolynomial.eval (criticalFirstMeridianRaw (m := m) (n := n) z)
      (criticalSourceChartPoly ℂ m n) ≠ 0 := by
  rw [criticalSourceChartPoly_eq_canonical, criticalCanonicalSourceChartPoly]
  simp only [map_mul, MvPolynomial.eval_X]
  apply mul_ne_zero
  · apply mul_ne_zero
    · simpa [criticalRawZeroIndex] using
        (show criticalFirstMeridianRaw (m := m) (n := n) z criticalRawZeroIndex ≠ 0
          from (criticalFirstMeridianRaw_zero (m := m) (n := n) z).symm ▸ one_ne_zero)
    · change criticalFirstMeridianRaw (m := m) (n := n) z
          criticalRawMarkedIndex ≠ 0
      rw [criticalFirstMeridianRaw_marked]
      exact hz
  · rw [criticalFirstMeridianRaw_reciprocal]
    split_ifs
    · exact neg_one_pow_sub_ne_zero_of_norm_lt_one m hsmall
    · exact one_ne_zero

theorem criticalSecondMeridianRaw_chartPoly_ne_zero {z : ℂ}
    (hz : z ≠ 0) (hsmall : ‖z‖ < 1) :
    MvPolynomial.eval (criticalSecondMeridianRaw (m := m) (n := n) z)
      (criticalSourceChartPoly ℂ m n) ≠ 0 := by
  rw [criticalSourceChartPoly_eq_canonical, criticalCanonicalSourceChartPoly]
  simp only [map_mul, MvPolynomial.eval_X]
  apply mul_ne_zero
  · apply mul_ne_zero
    · simpa [criticalRawZeroIndex] using
        (show criticalSecondMeridianRaw (m := m) (n := n) z criticalRawZeroIndex ≠ 0
          from (criticalSecondMeridianRaw_zero (m := m) (n := n) z).symm ▸ one_ne_zero)
    · change criticalSecondMeridianRaw (m := m) (n := n) z
          criticalRawMarkedIndex ≠ 0
      rw [criticalSecondMeridianRaw_marked]
      split_ifs
      · exact neg_one_pow_sub_ne_zero_of_norm_lt_one m hsmall
      · exact one_ne_zero
  · rw [criticalSecondMeridianRaw_reciprocal]
    exact hz

end
end GaloisForLFunctions.HTGeometry
