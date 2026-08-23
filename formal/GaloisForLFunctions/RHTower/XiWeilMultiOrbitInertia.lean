import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryPadeContactParity
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion

/-!
# Multi-orbit negative inertia of the complete Xi Weil form

Off-real Xi sign tests supported on distinct conjugation folds are exactly orthogonal for the
complete Weil polarization. Their diagonal masses retain full multiplicity of each conjugate
orbit. Consequently, `k` distinct off-real folds produce a strictly negative `k`-dimensional
coefficient Gram block.
-/

namespace RHTower

open scoped ComplexConjugate BigOperators
open Complex Matrix

noncomputable section

/-- Sign tests on distinct conjugation folds are orthogonal for the complete Xi Weil form. -/
theorem xiWeilPolarization_offRealSignTest_cross_eq_zero
    {alpha beta : ℂ}
    (hfold : complexConjugationFold alpha ≠ complexConjugationFold beta) :
    xiWeilPolarization (xiOffRealSignTest alpha) (xiOffRealSignTest beta) = 0 := by
  have hab : alpha ≠ beta := by
    intro h
    exact hfold (congrArg complexConjugationFold h)
  have habc : alpha ≠ (starRingEnd ℂ) beta := by
    intro h
    apply hfold
    rw [h, complexConjugationFold_conj]
  have hcab : (starRingEnd ℂ) alpha ≠ beta := by
    intro h
    apply habc
    have hc := congrArg (starRingEnd ℂ) h
    simpa using hc
  have hcc : (starRingEnd ℂ) alpha ≠ (starRingEnd ℂ) beta := by
    exact fun h => hab (Complex.conjCLE.injective h)
  rw [xiWeilPolarization]
  have hterm : (fun q : XiZeroCopy =>
      xiOffRealSignTest alpha (xiSpectralPoint q) *
        xiWeilSharp (xiOffRealSignTest beta) (xiSpectralPoint q)) = 0 := by
    funext q
    let z := xiSpectralPoint q
    change xiOffRealSignTest alpha z *
      xiWeilSharp (xiOffRealSignTest beta) z = 0
    by_cases hza : z = alpha
    · rw [hza]
      simp [xiOffRealSignTest, xiWeilSharp, hcab, hcc]
    · by_cases hzca : z = (starRingEnd ℂ) alpha
      · rw [hzca]
        simp [xiOffRealSignTest, xiWeilSharp, hab, habc]
      · rw [xiOffRealSignTest_eq_zero hza hzca, zero_mul]
  rw [hterm]
  exact tsum_zero

/-- Total Xi-zero multiplicity carried by conjugation orbit of `q`. -/
def xiWeilOffRealOrbitMultiplicity (q : XiZeroCopy) : ℕ :=
  ((finite_xiSpectralPoint_fiber (xiSpectralPoint q)).toFinset ∪
    (finite_xiSpectralPoint_fiber
      ((starRingEnd ℂ) (xiSpectralPoint q))).toFinset).card

theorem xiWeilOffRealOrbitMultiplicity_pos (q : XiZeroCopy) :
    0 < xiWeilOffRealOrbitMultiplicity q := by
  apply Finset.card_pos.mpr
  refine ⟨q, Finset.mem_union_left _ ?_⟩
  simp

/-- Complete Xi Weil Gram matrix on a finite family of off-real sign tests. -/
def xiWeilOffRealSignGram {k : ℕ} (s : Fin k → XiZeroCopy) :
    Matrix (Fin k) (Fin k) ℂ := fun j l =>
  xiWeilPolarization
    (xiOffRealSignTest (xiSpectralPoint (s j)))
    (xiOffRealSignTest (xiSpectralPoint (s l)))

/-- Exact multiplicity-weighted diagonalization for fold-distinct off-real Xi sign tests. -/
theorem xiWeilOffRealSignGram_eq_diagonal
    {k : ℕ} (s : Fin k → XiZeroCopy)
    (hfold : Function.Injective (fun j =>
      complexConjugationFold (xiSpectralPoint (s j))))
    (him : ∀ j, (xiSpectralPoint (s j)).im ≠ 0) :
    xiWeilOffRealSignGram s = Matrix.diagonal (fun j =>
      -((xiWeilOffRealOrbitMultiplicity (s j) : ℕ) : ℂ)) := by
  ext j l
  by_cases hjl : j = l
  · subst l
    rw [Matrix.diagonal_apply_eq]
    simpa only [xiWeilOffRealSignGram, xiWeilOffRealOrbitMultiplicity] using
      xiWeilPolarization_offRealSignTest (xiSpectralPoint (s j))
        (Complex.conj_eq_iff_im.not.mpr (him j))
  · rw [Matrix.diagonal_apply_ne _ hjl]
    exact xiWeilPolarization_offRealSignTest_cross_eq_zero
      (hfold.ne hjl)

/-- Every nonzero coefficient vector sees a strictly negative complete Xi Weil Gram value. -/
theorem xiWeilOffRealSignGram_negDef
    {k : ℕ} (s : Fin k → XiZeroCopy)
    (hfold : Function.Injective (fun j =>
      complexConjugationFold (xiSpectralPoint (s j))))
    (him : ∀ j, (xiSpectralPoint (s j)).im ≠ 0)
    (x : Fin k → ℂ) (hx : x ≠ 0) :
    (star x ⬝ᵥ (xiWeilOffRealSignGram s).mulVec x).re < 0 := by
  rw [xiWeilOffRealSignGram_eq_diagonal s hfold him]
  have hform :
      star x ⬝ᵥ
          (Matrix.diagonal (fun j =>
            -((xiWeilOffRealOrbitMultiplicity (s j) : ℕ) : ℂ))).mulVec x =
        ∑ j, -((xiWeilOffRealOrbitMultiplicity (s j) : ℕ) : ℂ) *
          (starRingEnd ℂ) (x j) * x j := by
    simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro j _hj
    change (starRingEnd ℂ) (x j) *
      (-((xiWeilOffRealOrbitMultiplicity (s j) : ℕ) : ℂ) * x j) = _
    ring
  rw [hform, Complex.re_sum]
  obtain ⟨j0, hj0⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
  have hterm_re : ∀ j,
      (-((xiWeilOffRealOrbitMultiplicity (s j) : ℕ) : ℂ) *
        (starRingEnd ℂ) (x j) * x j).re =
        -(xiWeilOffRealOrbitMultiplicity (s j) : ℝ) *
          Complex.normSq (x j) := by
    intro j
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]
    norm_num
  have hnonpos : ∀ j,
      (-((xiWeilOffRealOrbitMultiplicity (s j) : ℕ) : ℂ) *
        (starRingEnd ℂ) (x j) * x j).re ≤ 0 := by
    intro j
    rw [hterm_re]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by positivity)) (Complex.normSq_nonneg _)
  have hjneg :
      (-((xiWeilOffRealOrbitMultiplicity (s j0) : ℕ) : ℂ) *
        (starRingEnd ℂ) (x j0) * x j0).re < 0 := by
    rw [hterm_re]
    exact mul_neg_of_neg_of_pos
      (neg_neg_of_pos (by exact_mod_cast xiWeilOffRealOrbitMultiplicity_pos (s j0)))
      (Complex.normSq_pos.mpr hj0)
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun j => (-((xiWeilOffRealOrbitMultiplicity (s j) : ℕ) : ℂ) *
      (starRingEnd ℂ) (x j) * x j).re) (Finset.mem_univ j0)
  have hrest : ∑ j ∈ Finset.univ.erase j0,
      (-((xiWeilOffRealOrbitMultiplicity (s j) : ℕ) : ℂ) *
        (starRingEnd ℂ) (x j) * x j).re ≤ 0 :=
    Finset.sum_nonpos fun j _ => hnonpos j
  rw [← hsplit]
  linarith

end

end RHTower
