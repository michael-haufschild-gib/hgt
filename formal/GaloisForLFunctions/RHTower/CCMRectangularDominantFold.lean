import GaloisForLFunctions.RHTower.CCMShiftedXiLandauPoleContradiction

/-!
# Folding the full rectangular dominant carrier onto the right Xi divisor

Functional-equation reflection pairs the negative transverse divisor with
the positive transverse divisor, while the critical-line part contributes
zero.  At logarithmic aperture the complete dominant Xi sum is therefore
exactly the real right-divisor Dirichlet coefficient.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- Multiplicity copies strictly to the left of the critical line in the
literal centered Xi coordinate. -/
abbrev XiLeftZeroCopy :=
  {q : XiZeroCopy // (I * xiSpectralPoint q).re < 0}

/-- Functional-equation reflection is an equivalence between the right and
left transverse multiplicity copies. -/
def xiRightLeftReflectEquiv : XiRightZeroCopy ≃ XiLeftZeroCopy :=
  Equiv.subtypeEquiv xiZeroCopyReflectEquiv (fun q => by
    rw [xiSpectralPoint_reflect]
    simp)

/-- The reflected left dominant sum equals the right dominant sum. -/
theorem tsum_xiRectangularTwoEdgeDominant_left_eq_right
    (L a : ℝ) :
    (∑' q : XiLeftZeroCopy,
      xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1)) =
    ∑' q : XiRightZeroCopy,
      xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1) := by
  calc
    (∑' q : XiLeftZeroCopy,
        xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1)) =
      ∑' q : XiRightZeroCopy,
        xiRectangularTwoEdgeDominant L a
          (xiSpectralPoint (xiRightLeftReflectEquiv q).1) :=
      (xiRightLeftReflectEquiv.tsum_eq
        (fun q : XiLeftZeroCopy =>
          xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1))).symm
    _ = ∑' q : XiRightZeroCopy,
        xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1) := by
      apply tsum_congr
      intro q
      exact xiRectangularTwoEdgeDominant_reflect L a q.1

/-- The full dominant Xi sum folds exactly to twice its positive-transverse
half. -/
theorem tsum_xiRectangularTwoEdgeDominant_eq_two_mul_right
    (L a : ℝ) :
    (∑' q : XiZeroCopy,
      xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)) =
    2 * ∑' q : XiRightZeroCopy,
      xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1) := by
  let f : XiZeroCopy → ℂ := fun q =>
    xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)
  let P : Set XiZeroCopy := {q | 0 < (I * xiSpectralPoint q).re}
  let M : Set XiZeroCopy := {q | (I * xiSpectralPoint q).re < 0}
  have hsum : Summable f := xiRectangularTwoEdgeDominant_summable L a
  have hpoint : f = P.indicator f + M.indicator f := by
    funext q
    rcases lt_trichotomy (I * xiSpectralPoint q).re 0 with hneg | hzero | hpos
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_mem]
      · simp only [zero_add]
      · exact hneg
      · exact not_lt.mpr hneg.le
    · rw [Pi.add_apply, Set.indicator_of_notMem, Set.indicator_of_notMem,
        add_zero]
      · dsimp only [f, xiRectangularTwoEdgeDominant]
        rw [rectangularTwoEdgeDominant, if_neg (by linarith),
          if_neg (by linarith)]
      · exact not_lt.mpr hzero.le
      · exact not_lt.mpr (by linarith)
    · rw [Pi.add_apply, Set.indicator_of_mem, Set.indicator_of_notMem,
        add_zero]
      · exact not_lt.mpr hpos.le
      · exact hpos
  calc
    (∑' q : XiZeroCopy,
        xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)) =
      ∑' q : XiZeroCopy, f q := rfl
    _ = ∑' q : XiZeroCopy, (P.indicator f q + M.indicator f q) := by
      rw [hpoint]
      rfl
    _ = (∑' q : XiZeroCopy, P.indicator f q) +
        ∑' q : XiZeroCopy, M.indicator f q :=
      (hsum.indicator P).tsum_add (hsum.indicator M)
    _ = (∑' q : P, f q.1) + ∑' q : M, f q.1 := by
      rw [tsum_subtype, tsum_subtype]
    _ = (∑' q : XiRightZeroCopy,
          xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1)) +
        ∑' q : XiLeftZeroCopy,
          xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1) := rfl
    _ = (∑' q : XiRightZeroCopy,
          xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1)) +
        ∑' q : XiRightZeroCopy,
          xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1) := by
      rw [tsum_xiRectangularTwoEdgeDominant_left_eq_right]
    _ = 2 * ∑' q : XiRightZeroCopy,
        xiRectangularTwoEdgeDominant L a (xiSpectralPoint q.1) := by ring

/-- At logarithmic aperture the complete dominant carrier is the real
right-divisor Dirichlet coefficient. -/
theorem tsum_xiRectangularTwoEdgeDominant_logSample_eq_rightCoefficient
    (L : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∑' q : XiZeroCopy,
      xiRectangularTwoEdgeDominant L (Real.log n / 2)
        (xiSpectralPoint q)) =
      xiRectangularRightDirichletComplex L n := by
  rw [tsum_xiRectangularTwoEdgeDominant_eq_two_mul_right,
    xiRectangularRightDirichletComplex]
  congr 1
  apply tsum_congr
  intro q
  exact xiRectangularTwoEdgeDominant_logSample_of_right hn q

theorem tsum_xiRectangularTwoEdgeDominant_logSample_eq_ofReal_rightCoefficient
    (L : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∑' q : XiZeroCopy,
      xiRectangularTwoEdgeDominant L (Real.log n / 2)
        (xiSpectralPoint q)) =
      (xiRectangularRightDirichletCoefficientReal L n : ℂ) := by
  rw [tsum_xiRectangularTwoEdgeDominant_logSample_eq_rightCoefficient L hn,
    ofReal_xiRectangularRightDirichletCoefficientReal]

end

end RHTower
