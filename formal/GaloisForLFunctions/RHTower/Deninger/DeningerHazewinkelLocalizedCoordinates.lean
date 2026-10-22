import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelPrimeReduction
import GaloisForLFunctions.RHTower.Deninger.DeningerHazewinkelLeadingLocalization
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Localized coordinates for universal Hazewinkel stages

For every positive stage, this module constructs the finite parameter chart behind Hazewinkel's
localization argument. It inverts the leading Hankel determinant, solves the universal recurrence
by the nonsingular inverse, extends finite initial coordinates to an infinite Hankel sequence,
and proves all J_n relations vanish on that sequence. Consequently it constructs the canonical
map from the localization of Z[X]/J_n at the leading determinant to a localization of a finite
integer polynomial ring, without assuming primeness or regularity of J_n.
-/

namespace RHTower
noncomputable section
open scoped BigOperators

abbrev DeningerHazewinkelParameterIndex (n : ℕ) :=
  { k : ℕ // 0 < k ∧ k < 2 * n }

abbrev DeningerHazewinkelParameterRing (n : ℕ) :=
  MvPolynomial (DeningerHazewinkelParameterIndex n) ℤ

def deningerHazewinkelParameterCoeff (n s : ℕ) :
    DeningerHazewinkelParameterRing n :=
  if hs0 : s = 0 then 1 else
    if hs : s < 2 * n then MvPolynomial.X ⟨s, Nat.pos_of_ne_zero hs0, hs⟩ else 0

@[simp] theorem deningerHazewinkelParameterCoeff_zero (n : ℕ) :
    deningerHazewinkelParameterCoeff n 0 = 1 := by
  simp [deningerHazewinkelParameterCoeff]

@[simp] theorem deningerHazewinkelParameterCoeff_pos {n s : ℕ} (hs0 : 0 < s) (hs : s < 2 * n) :
    deningerHazewinkelParameterCoeff n s =
      MvPolynomial.X (⟨s, hs0, hs⟩ : DeningerHazewinkelParameterIndex n) := by
  simp [deningerHazewinkelParameterCoeff, hs0.ne', hs]

def deningerHazewinkelParameterLeadingDeterminant (n : ℕ) :
    DeningerHazewinkelParameterRing n :=
  Matrix.det fun i j : Fin n => deningerHazewinkelParameterCoeff n (i.val + j.val)

def deningerHazewinkelParameterMomentEval (n : ℕ) :
    DeningerHazewinkelParameterRing n →+* ℚ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℚ) fun k =>
    deningerHazewinkelRationalMoment n k.val

theorem deningerHazewinkelParameterLeading_eval (n : ℕ) (hn : 0 < n) :
    deningerHazewinkelParameterMomentEval n
      (deningerHazewinkelParameterLeadingDeterminant n) =
    deningerHazewinkelRationalMomentEval n
      (deningerHazewinkelLeadingDeterminant n) := by
  rw [deningerHazewinkelParameterLeadingDeterminant,
    deningerHazewinkelLeadingDeterminant,
    (deningerHazewinkelParameterMomentEval n).map_det,
    (deningerHazewinkelRationalMomentEval n).map_det]
  congr 1
  funext i j
  change deningerHazewinkelParameterMomentEval n
      (deningerHazewinkelParameterCoeff n (i.val + j.val)) =
    deningerHazewinkelRationalMomentEval n
      (deningerHazewinkelUniversalCoeff (i.val + j.val))
  by_cases hzero : i.val + j.val = 0
  · rw [hzero]
    simp [deningerHazewinkelParameterMomentEval,
      deningerHazewinkelRationalMoment_zero n hn,
      deningerHazewinkelRationalMomentEval_universalCoeff n 0 hn]
  · have hpos : 0 < i.val + j.val := Nat.pos_of_ne_zero hzero
    have hlt : i.val + j.val < 2 * n := by omega
    rw [deningerHazewinkelParameterCoeff_pos hpos hlt]
    rw [deningerHazewinkelRationalMomentEval_universalCoeff n _ hn]
    rw [deningerHazewinkelParameterMomentEval, MvPolynomial.eval₂Hom_X']

theorem deningerHazewinkelParameterLeading_ne_zero (n : ℕ) (hn : 0 < n) :
    deningerHazewinkelParameterLeadingDeterminant n ≠ 0 := by
  intro hzero
  have hmap := congrArg (deningerHazewinkelParameterMomentEval n) hzero
  rw [map_zero, deningerHazewinkelParameterLeading_eval n hn] at hmap
  exact deningerHazewinkelRationalMomentEval_leading_ne_zero n hn hmap

abbrev DeningerHazewinkelParameterLocalization (n : ℕ) :=
  Localization.Away (deningerHazewinkelParameterLeadingDeterminant n)

/-- The finite parameter chart remains an integral domain after inverting its leading
determinant. -/
theorem deningerHazewinkelParameterLocalization_isDomain
    (n : ℕ) (hn : 0 < n) :
    IsDomain (DeningerHazewinkelParameterLocalization n) := by
  exact IsLocalization.isDomain_of_le_nonZeroDivisors
    (DeningerHazewinkelParameterLocalization n)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (deningerHazewinkelParameterLeading_ne_zero n hn))

def deningerHazewinkelParameterMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (DeningerHazewinkelParameterRing n) :=
  fun i j => deningerHazewinkelParameterCoeff n (i.val + j.val)

def deningerHazewinkelParameterRhs (n : ℕ) :
    Fin n → DeningerHazewinkelParameterRing n :=
  fun i => deningerHazewinkelParameterCoeff n (i.val + n)

def deningerHazewinkelLocalizedMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (DeningerHazewinkelParameterLocalization n) :=
  (algebraMap _ _).mapMatrix (deningerHazewinkelParameterMatrix n)

def deningerHazewinkelLocalizedRhs (n : ℕ) :
    Fin n → DeningerHazewinkelParameterLocalization n :=
  fun i => algebraMap _ _ (deningerHazewinkelParameterRhs n i)

def deningerHazewinkelLocalizedRecurrence (n : ℕ) :
    Fin n → DeningerHazewinkelParameterLocalization n :=
  (deningerHazewinkelLocalizedMatrix n)⁻¹.mulVec
    (deningerHazewinkelLocalizedRhs n)

theorem deningerHazewinkelLocalizedMatrix_det_isUnit (n : ℕ) :
    IsUnit (deningerHazewinkelLocalizedMatrix n).det := by
  rw [deningerHazewinkelLocalizedMatrix, ← RingHom.map_det]
  change IsUnit (algebraMap _ _ (deningerHazewinkelParameterLeadingDeterminant n))
  exact IsLocalization.Away.algebraMap_isUnit _

theorem deningerHazewinkelLocalizedRecurrence_solve (n : ℕ) :
    (deningerHazewinkelLocalizedMatrix n).mulVec
      (deningerHazewinkelLocalizedRecurrence n) =
    deningerHazewinkelLocalizedRhs n := by
  rw [deningerHazewinkelLocalizedRecurrence, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (deningerHazewinkelLocalizedMatrix_det_isUnit n), Matrix.one_mulVec]

def deningerHazewinkelLocalizedSequence (n : ℕ) (hn : 0 < n) (s : ℕ) :
    DeningerHazewinkelParameterLocalization n :=
  if _hs : s < 2 * n then
    algebraMap _ _ (deningerHazewinkelParameterCoeff n s)
  else
    ∑ j : Fin n, deningerHazewinkelLocalizedRecurrence n j *
      deningerHazewinkelLocalizedSequence n hn (s - n + j.val)
termination_by s
decreasing_by omega

@[simp] theorem deningerHazewinkelLocalizedSequence_of_lt
    (n : ℕ) (hn : 0 < n) {s : ℕ} (hs : s < 2 * n) :
    deningerHazewinkelLocalizedSequence n hn s =
      algebraMap _ _ (deningerHazewinkelParameterCoeff n s) := by
  rw [deningerHazewinkelLocalizedSequence]
  simp [hs]

theorem deningerHazewinkelLocalizedSequence_of_ge
    (n : ℕ) (hn : 0 < n) {s : ℕ} (hs : 2 * n ≤ s) :
    deningerHazewinkelLocalizedSequence n hn s =
      ∑ j : Fin n, deningerHazewinkelLocalizedRecurrence n j *
        deningerHazewinkelLocalizedSequence n hn (s - n + j.val) := by
  rw [deningerHazewinkelLocalizedSequence]
  simp [Nat.not_lt.mpr hs]

theorem deningerHazewinkelLocalizedSequence_recurrence_initial
    (n : ℕ) (hn : 0 < n) {s : ℕ} (hns : n ≤ s) (hs2n : s < 2 * n) :
    deningerHazewinkelLocalizedSequence n hn s =
      ∑ j : Fin n, deningerHazewinkelLocalizedRecurrence n j *
        deningerHazewinkelLocalizedSequence n hn (s - n + j.val) := by
  let i : Fin n := ⟨s - n, by omega⟩
  have hsolve := congrFun (deningerHazewinkelLocalizedRecurrence_solve n) i
  rw [Matrix.mulVec, dotProduct] at hsolve
  change (∑ j, deningerHazewinkelLocalizedMatrix n i j *
      deningerHazewinkelLocalizedRecurrence n j) =
    algebraMap _ _ (deningerHazewinkelParameterRhs n i) at hsolve
  rw [deningerHazewinkelLocalizedSequence_of_lt n hn hs2n]
  rw [show s = i.val + n by dsimp [i]; omega]
  change algebraMap _ _ (deningerHazewinkelParameterRhs n i) = _
  rw [← hsolve]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show i.val + n - n + j.val = i.val + j.val by omega]
  have hidx : i.val + j.val < 2 * n := by omega
  rw [deningerHazewinkelLocalizedSequence_of_lt n hn hidx]
  change algebraMap _ _ (deningerHazewinkelParameterCoeff n (i.val + j.val)) *
      deningerHazewinkelLocalizedRecurrence n j =
    deningerHazewinkelLocalizedRecurrence n j *
      algebraMap _ _ (deningerHazewinkelParameterCoeff n (i.val + j.val))
  rw [mul_comm]

theorem deningerHazewinkelLocalizedSequence_recurrence
    (n : ℕ) (hn : 0 < n) {s : ℕ} (hns : n ≤ s) :
    deningerHazewinkelLocalizedSequence n hn s =
      ∑ j : Fin n, deningerHazewinkelLocalizedRecurrence n j *
        deningerHazewinkelLocalizedSequence n hn (s - n + j.val) := by
  by_cases hs2n : s < 2 * n
  · exact deningerHazewinkelLocalizedSequence_recurrence_initial n hn hns hs2n
  · exact deningerHazewinkelLocalizedSequence_of_ge n hn (Nat.le_of_not_gt hs2n)

theorem hankelColumnGenerated_of_forwardRecurrence
    {A : Type*} [CommRing A] (a : ℕ → A) (c : Fin n → A)
    (hrec : ∀ s : ℕ, n ≤ s →
      a s = ∑ r : Fin n, c r * a (s - n + r.val)) :
    DeningerHankelColumnGenerated a n := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hj : j < n
      · let tj : Fin n := ⟨j, hj⟩
        refine ⟨fun t => if t = tj then 1 else 0, ?_⟩
        intro i
        simp [tj]
      · have hnj : n ≤ j := Nat.le_of_not_gt hj
        have hprev : ∀ r : Fin n, ∃ d : Fin n → A, ∀ i : ℕ,
            a (i + (j - n + r.val)) =
              ∑ u : Fin n, a (i + u.val) * d u := by
          intro r
          apply ih (j - n + r.val)
          omega
        choose d hd using hprev
        refine ⟨fun u => ∑ r : Fin n, c r * d r u, ?_⟩
        intro i
        rw [hrec (i + j) (by omega)]
        have hidx (r : Fin n) : i + j - n + r.val = i + (j - n + r.val) := by
          omega
        simp_rw [hidx, hd]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro r hr
        ring

def deningerHazewinkelUniversalToLocalizedParameter
    (n : ℕ) (hn : 0 < n) :
    MvPolynomial ℕ ℤ →+* DeningerHazewinkelParameterLocalization n :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) fun j =>
    deningerHazewinkelLocalizedSequence n hn (j + 1)

@[simp] theorem deningerHazewinkelUniversalToLocalizedParameter_coeff
    (n : ℕ) (hn : 0 < n) (s : ℕ) :
    deningerHazewinkelUniversalToLocalizedParameter n hn
      (deningerHazewinkelUniversalCoeff s) =
    deningerHazewinkelLocalizedSequence n hn s := by
  cases s with
  | zero =>
      simp [deningerHazewinkelUniversalCoeff,
        deningerHazewinkelUniversalToLocalizedParameter,
        deningerHazewinkelLocalizedSequence_of_lt n hn (by omega : 0 < 2 * n),
        deningerHazewinkelParameterCoeff]
  | succ s =>
      rw [deningerHazewinkelUniversalCoeff,
        deningerHazewinkelUniversalToLocalizedParameter,
        MvPolynomial.eval₂Hom_X']

theorem deningerHazewinkelUniversalToLocalizedParameter_ideal_le_ker
    (n : ℕ) (hn : 0 < n) :
    deningerHazewinkelIdeal n ≤
      RingHom.ker (deningerHazewinkelUniversalToLocalizedParameter n hn) := by
  rw [deningerHazewinkelIdeal, deningerMatrixMinorIdeal, Ideal.span_le]
  rintro z ⟨rows, cols, rfl⟩
  apply RingHom.mem_ker.mpr
  rw [(deningerHazewinkelUniversalToLocalizedParameter n hn).map_det]
  let a : ℕ → DeningerHazewinkelParameterLocalization n :=
    deningerHazewinkelLocalizedSequence n hn
  let c : Fin n → DeningerHazewinkelParameterLocalization n :=
    deningerHazewinkelLocalizedRecurrence n
  have hcol : DeningerHankelColumnGenerated a n := by
    exact hankelColumnGenerated_of_forwardRecurrence a c
      (fun s hs => deningerHazewinkelLocalizedSequence_recurrence n hn hs)
  have hdet := hankelRankLT_succ_of_columnGenerated a n hcol rows cols
  convert hdet using 1
  congr 1
  funext i j
  change deningerHazewinkelUniversalToLocalizedParameter n hn
      (deningerHazewinkelUniversalCoeff (rows i + cols j)) =
    deningerHazewinkelLocalizedSequence n hn (rows i + cols j)
  rw [deningerHazewinkelUniversalToLocalizedParameter_coeff]

def deningerHazewinkelStageLocalizationToParameter
    (n : ℕ) (hn : 0 < n) :
    DeningerHazewinkelStageQuotient n →+*
      DeningerHazewinkelParameterLocalization n :=
  Ideal.Quotient.lift (deningerHazewinkelIdeal n)
    (deningerHazewinkelUniversalToLocalizedParameter n hn)
    (deningerHazewinkelUniversalToLocalizedParameter_ideal_le_ker n hn)

theorem deningerHazewinkelStageLocalizationToParameter_leading
    (n : ℕ) (hn : 0 < n) :
    deningerHazewinkelStageLocalizationToParameter n hn
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
        (deningerHazewinkelLeadingDeterminant n)) =
    algebraMap _ _ (deningerHazewinkelParameterLeadingDeterminant n) := by
  change deningerHazewinkelUniversalToLocalizedParameter n hn
      (Matrix.det fun i j : Fin n =>
        deningerHazewinkelUniversalCoeff (i.val + j.val)) =
    algebraMap _ _ (Matrix.det fun i j : Fin n =>
      deningerHazewinkelParameterCoeff n (i.val + j.val))
  rw [(deningerHazewinkelUniversalToLocalizedParameter n hn).map_det,
    (algebraMap (DeningerHazewinkelParameterRing n)
      (DeningerHazewinkelParameterLocalization n)).map_det]
  congr 1
  funext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [deningerHazewinkelUniversalToLocalizedParameter_coeff]
  exact deningerHazewinkelLocalizedSequence_of_lt n hn (by omega)

def deningerHazewinkelLocalizedStageToParameter
    (n : ℕ) (hn : 0 < n) :
    Localization.Away
        (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
          (deningerHazewinkelLeadingDeterminant n)) →+*
      DeningerHazewinkelParameterLocalization n :=
  IsLocalization.Away.lift _
    (show IsUnit
        (deningerHazewinkelStageLocalizationToParameter n hn
          (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
            (deningerHazewinkelLeadingDeterminant n))) by
      rw [deningerHazewinkelStageLocalizationToParameter_leading]
      exact IsLocalization.Away.algebraMap_isUnit _)

end
end RHTower
