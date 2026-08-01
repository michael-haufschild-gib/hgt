import GaloisForLFunctions.RHTower.CCMPublishedSourceSineCoefficient
import GaloisForLFunctions.RHTower.CCMSourceResponseDeterminantDichotomy

/-!
# The source-locked published CCM restricted-Weil matrix

This module instantiates the finite matrix of Connes--Consani--Moscovici with the literal
finite-aperture Weil distribution.  The diagonal is the Weil value of the tent--cosine
autocorrelation and the off-diagonal source is the published sine coefficient.  Consequently the
generic divided-difference, reflection, displacement, boundary-completion, and real-rooted
source/response machinery applies to the actual arithmetic matrix rather than to free data.

Nothing here asserts positivity of the restricted Weil form, convergence of spectral floors, or
convergence of the completed determinants to `XiC`.  Those are the source-level Route O gates.
-/

open scoped BigOperators Matrix ComplexOrder
open MeasureTheory Set Matrix

noncomputable section

namespace RHTower

/-- The finite archimedean distribution `W_ℝ#` on the logarithmic aperture `(0,2a]`.

The endpoint correction is written in the exact form used in equation (4.4) of the published CCM
matrix calculation. -/
def ccmPublishedRestrictedArchimedeanPairing (a : ℝ) (F : ℝ → ℝ) : ℝ :=
  F 0 / 2 *
      (Real.eulerMascheroniConstant +
        Real.log
          (4 * Real.pi *
            ((Real.exp (2 * a) - 1) / (Real.exp (2 * a) + 1)))) +
    ∫ h in Ioc (0 : ℝ) (2 * a),
      (Real.exp (h / 2) * F h - F 0) /
        (Real.exp h - Real.exp (-h))

/-- The literal one-sided restricted Weil functional
`Ψ# = W₀,₂# - W_ℝ# - Σₚ Wₚ#` on real logarithmic tests.  The polar and prime terms are already
assembled by `criticalMellinStieltjesPairing`. -/
def ccmPublishedRestrictedWeilPairing (a : ℝ) (F : ℝ → ℝ) : ℝ :=
  (criticalMellinStieltjesPairing a (fun h => (F h : ℂ))).re -
    ccmPublishedRestrictedArchimedeanPairing a F

/-- The restricted Weil functional is real-linear under negation. -/
theorem ccmPublishedRestrictedWeilPairing_neg (a : ℝ) (F : ℝ → ℝ) :
    ccmPublishedRestrictedWeilPairing a (fun h => -F h) =
      -ccmPublishedRestrictedWeilPairing a F := by
  have hcritical :
      criticalMellinStieltjesPairing a (fun h => ((-F h : ℝ) : ℂ)) =
        -criticalMellinStieltjesPairing a (fun h => (F h : ℂ)) := by
    rw [criticalMellinStieltjesPairing, criticalMellinStieltjesPairing]
    have hint :
        (∫ h in Ioc (0 : ℝ) (2 * a),
            ((-F h : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ)) =
          -(∫ h in Ioc (0 : ℝ) (2 * a),
            (F h : ℂ) * (2 * Real.cosh (h / 2) : ℂ)) := by
      rw [← integral_neg]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with h
      push_cast
      ring
    have hsum :
        (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
            (criticalMellinAtomWeight k : ℂ) * ((-F (Real.log k) : ℝ) : ℂ)) =
          -(∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
            (criticalMellinAtomWeight k : ℂ) * (F (Real.log k) : ℂ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    rw [hint, hsum]
    ring
  have harch :
      ccmPublishedRestrictedArchimedeanPairing a (fun h => -F h) =
        -ccmPublishedRestrictedArchimedeanPairing a F := by
    rw [ccmPublishedRestrictedArchimedeanPairing,
      ccmPublishedRestrictedArchimedeanPairing]
    have hint :
        (∫ h in Ioc (0 : ℝ) (2 * a),
            (Real.exp (h / 2) * -F h - -F 0) /
              (Real.exp h - Real.exp (-h))) =
          -(∫ h in Ioc (0 : ℝ) (2 * a),
            (Real.exp (h / 2) * F h - F 0) /
              (Real.exp h - Real.exp (-h))) := by
      rw [← integral_neg]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with h
      ring
    rw [hint]
    ring
  rw [ccmPublishedRestrictedWeilPairing,
    ccmPublishedRestrictedWeilPairing, hcritical, harch]
  simp only [Complex.neg_re]
  ring

/-- The sine test in the literal restricted Weil functional is exactly the already formalized
published odd CCM source coordinate. -/
theorem neg_inv_pi_mul_ccmPublishedRestrictedWeilPairing_sine
    (a ξ : ℝ) :
    -(1 / Real.pi) *
        ccmPublishedRestrictedWeilPairing a (fun h => Real.sin (ξ * h)) =
      ccmPublishedSourceSineCoefficient a ξ := by
  have harch :
      ccmPublishedRestrictedArchimedeanPairing a
          (fun h => Real.sin (ξ * h)) =
        ∫ h in Ioc (0 : ℝ) (2 * a),
          Real.sin (ξ * h) * ccmPublishedArchimedeanDensity h := by
    rw [ccmPublishedRestrictedArchimedeanPairing]
    simp only [Real.sin_zero, mul_zero, zero_div, zero_mul, zero_add, sub_zero,
      ccmPublishedArchimedeanDensity]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with h
    ring
  rw [ccmPublishedRestrictedWeilPairing, harch,
    ccmPublishedSourceSineCoefficient,
    ccmPublishedArchimedeanSineCoefficient,
    ccmPublishedPolarPrimeSineCoefficient]
  ring

/-- Integer mode centered on the odd-dimensional packet `{-N,...,N}`. -/
def ccmPublishedCenteredMode (N : ℕ) (i : Fin (2 * N + 1)) : ℤ :=
  (i.val : ℤ) - N

/-- The clock of the published finite matrix.  It is dimensionless, exactly as the denominator
`i-j` in CCM equation (5.2). -/
def ccmPublishedCenteredClock (N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  ccmPublishedCenteredMode N i

/-- Physical Fourier frequency `πn/a = 2πn/L`, where `L=2a`. -/
def ccmPublishedCenteredFrequency (a : ℝ) (N : ℕ)
    (i : Fin (2 * N + 1)) : ℝ :=
  Real.pi * ccmPublishedCenteredClock N i / a

/-- Actual published off-diagonal source coordinate at a centered mode. -/
def ccmPublishedCenteredSource (a : ℝ) (N : ℕ)
    (i : Fin (2 * N + 1)) : ℝ :=
  -(1 / Real.pi) *
    ccmPublishedRestrictedWeilPairing a
      (fun h => Real.sin (ccmPublishedCenteredFrequency a N i * h))

/-- Actual published diagonal coordinate: the restricted Weil value of
`2(1-h/(2a)) cos(πnh/a)`. -/
def ccmPublishedCenteredDiagonal (a : ℝ) (N : ℕ)
    (i : Fin (2 * N + 1)) : ℝ :=
  ccmPublishedRestrictedWeilPairing a
    (fun h =>
      2 * (1 - h / (2 * a)) *
        Real.cos (ccmPublishedCenteredFrequency a N i * h))

/-- The exact finite restricted-Weil matrix in the centered Fourier packet. -/
def ccmPublishedRestrictedWeilMatrix (a : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmDividedDifferenceMatrix
    (ccmPublishedCenteredClock N)
    (ccmPublishedCenteredSource a N)
    (ccmPublishedCenteredDiagonal a N)

/-- Source-lock identification with the pre-existing published coefficient. -/
theorem ccmPublishedCenteredSource_eq_sourceSineCoefficient
    (a : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmPublishedCenteredSource a N i =
      ccmPublishedSourceSineCoefficient a
        (ccmPublishedCenteredFrequency a N i) := by
  exact neg_inv_pi_mul_ccmPublishedRestrictedWeilPairing_sine _ _

/-- Diagonal entries are literal tent--cosine restricted-Weil values. -/
theorem ccmPublishedRestrictedWeilMatrix_apply_self
    (a : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmPublishedRestrictedWeilMatrix a N i i =
      ccmPublishedCenteredDiagonal a N i := by
  simp [ccmPublishedRestrictedWeilMatrix, ccmDividedDifferenceMatrix]

/-- Off-diagonal entries are literal divided differences of the published source coordinate. -/
theorem ccmPublishedRestrictedWeilMatrix_apply_of_ne
    (a : ℝ) (N : ℕ) {i j : Fin (2 * N + 1)} (hij : i ≠ j) :
    ccmPublishedRestrictedWeilMatrix a N i j =
      (ccmPublishedCenteredSource a N i -
          ccmPublishedCenteredSource a N j) /
        (ccmPublishedCenteredClock N i -
          ccmPublishedCenteredClock N j) := by
  simp [ccmPublishedRestrictedWeilMatrix, ccmDividedDifferenceMatrix, hij]

/-- Reversal of the finite packet is integer negation of its centered mode. -/
theorem ccmPublishedCenteredMode_rev (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmPublishedCenteredMode N (Fin.revPerm i) =
      -ccmPublishedCenteredMode N i := by
  simp only [ccmPublishedCenteredMode, Fin.revPerm_apply, Fin.val_rev]
  omega

/-- The centered real clock is reflection-odd. -/
theorem ccmPublishedCenteredClock_rev (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmPublishedCenteredClock N (Fin.revPerm i) =
      -ccmPublishedCenteredClock N i := by
  rw [ccmPublishedCenteredClock, ccmPublishedCenteredClock,
    ccmPublishedCenteredMode_rev]
  exact_mod_cast rfl

/-- The centered clock is injective. -/
theorem ccmPublishedCenteredClock_injective (N : ℕ) :
    Function.Injective (ccmPublishedCenteredClock N) := by
  intro i j hij
  apply Fin.ext
  unfold ccmPublishedCenteredClock at hij
  have hz : ccmPublishedCenteredMode N i = ccmPublishedCenteredMode N j := by
    exact_mod_cast hij
  unfold ccmPublishedCenteredMode at hz
  omega

/-- Physical frequency is reflection-odd. -/
theorem ccmPublishedCenteredFrequency_rev
    (a : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmPublishedCenteredFrequency a N (Fin.revPerm i) =
      -ccmPublishedCenteredFrequency a N i := by
  unfold ccmPublishedCenteredFrequency
  rw [ccmPublishedCenteredClock_rev]
  ring

/-- The actual published source vector is reflection-odd. -/
theorem ccmPublishedCenteredSource_rev
    (a : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmPublishedCenteredSource a N (Fin.revPerm i) =
      -ccmPublishedCenteredSource a N i := by
  unfold ccmPublishedCenteredSource
  rw [ccmPublishedCenteredFrequency_rev]
  have hsin :
      (fun h : ℝ => Real.sin (-ccmPublishedCenteredFrequency a N i * h)) =
        fun h : ℝ => -Real.sin (ccmPublishedCenteredFrequency a N i * h) := by
    funext h
    rw [neg_mul, Real.sin_neg]
  rw [hsin, ccmPublishedRestrictedWeilPairing_neg]
  ring

/-- The actual published diagonal vector is reflection-even. -/
theorem ccmPublishedCenteredDiagonal_rev
    (a : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) :
    ccmPublishedCenteredDiagonal a N (Fin.revPerm i) =
      ccmPublishedCenteredDiagonal a N i := by
  rw [ccmPublishedCenteredDiagonal, ccmPublishedCenteredFrequency_rev]
  congr 1
  funext h
  rw [neg_mul, Real.cos_neg]

/-- The exact published matrix is real symmetric. -/
theorem ccmPublishedRestrictedWeilMatrix_transpose (a : ℝ) (N : ℕ) :
    (ccmPublishedRestrictedWeilMatrix a N).transpose =
      ccmPublishedRestrictedWeilMatrix a N := by
  exact ccmDividedDifferenceMatrix_transpose _ _ _

/-- The exact published matrix commutes with centered reflection. -/
theorem ccmPublishedRestrictedWeilMatrix_commutes_reflection
    (a : ℝ) (N : ℕ) :
    ccmPublishedRestrictedWeilMatrix a N *
        ccmReflectionMatrix (Fin.revPerm (n := 2 * N + 1)) =
      ccmReflectionMatrix (Fin.revPerm (n := 2 * N + 1)) *
        ccmPublishedRestrictedWeilMatrix a N := by
  apply ccmReflectionMatrix_commutes_dividedDifference
  · intro i
    simp
  · exact ccmPublishedCenteredClock_rev N
  · exact ccmPublishedCenteredSource_rev a N
  · exact ccmPublishedCenteredDiagonal_rev a N

/-- Exact rank-two displacement law for the source-locked published matrix. -/
theorem ccmPublishedRestrictedWeilMatrix_displacement
    (a : ℝ) (N : ℕ) :
    ccmDiagonalClock (ccmPublishedCenteredClock N) *
          ccmPublishedRestrictedWeilMatrix a N -
        ccmPublishedRestrictedWeilMatrix a N *
          ccmDiagonalClock (ccmPublishedCenteredClock N) =
      Matrix.vecMulVec (ccmPublishedCenteredSource a N) ccmConstantBoundary -
        Matrix.vecMulVec ccmConstantBoundary
          (ccmPublishedCenteredSource a N) := by
  exact ccmDividedDifference_displacement _ _ _
    (ccmPublishedCenteredClock_injective N)

/-- Every scalar shift of the exact published matrix has an unconditional radical-preserving
rank-one boundary completion.  No simple-even premise is used. -/
theorem ccmPublishedRestrictedWeilMatrix_boundaryCompletion_exists
    (a mu : ℝ) (N : ℕ) :
    let T := ccmScalarShift (ccmPublishedRestrictedWeilMatrix a N) mu
    ∃ A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ,
      T * A = A.transpose * T ∧
      ∀ k : Fin (2 * N + 1) → ℝ,
        T *ᵥ k = 0 → T *ᵥ (A *ᵥ k) = 0 := by
  dsimp only
  apply ccmDividedDifferenceShift_boundaryCompletion_exists
      (Fin.revPerm (n := 2 * N + 1))
  · intro i
    simp
  · exact ccmPublishedCenteredClock_injective N
  · exact ccmPublishedCenteredClock_rev N
  · exact ccmPublishedCenteredSource_rev a N
  · exact ccmPublishedCenteredDiagonal_rev a N

/-- If a scalar shift of the exact published matrix is positive semidefinite and singular, its
source/response completion has full characteristic polynomial supported on the real line.  The
only premises are the two spectral facts that selecting a genuine finite ground shift supplies. -/
theorem ccmPublishedRestrictedWeilMatrix_hasSourceResponseCompletion
    (a mu : ℝ) (N : ℕ)
    (hT : ((ccmScalarShift (ccmPublishedRestrictedWeilMatrix a N) mu).map
      (algebraMap ℝ ℂ)).PosSemidef)
    (hkernel : ∃ k : Fin (2 * N + 1) → ℂ,
      (ccmScalarShift (ccmPublishedRestrictedWeilMatrix a N) mu).map
        (algebraMap ℝ ℂ) *ᵥ k = 0 ∧ k ≠ 0) :
    HasCCMSourceResponseCompletion
      ((ccmScalarShift (ccmPublishedRestrictedWeilMatrix a N) mu).map
        (algebraMap ℝ ℂ))
      (Matrix.diagonal (fun i => (ccmPublishedCenteredClock N i : ℂ)))
      (fun i => (ccmPublishedCenteredSource a N i : ℂ)) := by
  apply ccmDividedDifferenceShift_hasSourceResponseCompletion
      (Fin.revPerm (n := 2 * N + 1))
  · intro i
    simp
  · exact ccmPublishedCenteredClock_injective N
  · exact ccmPublishedCenteredClock_rev N
  · exact ccmPublishedCenteredSource_rev a N
  · exact ccmPublishedCenteredDiagonal_rev a N
  · simpa [ccmPublishedRestrictedWeilMatrix] using hT
  · simpa [ccmPublishedRestrictedWeilMatrix] using hkernel

/-- **Automatic finite ground shift.**  Every exact published finite restricted-Weil matrix has a
real spectral-floor shift whose source/response completion is metric-adjoint and whose full
characteristic polynomial has only real zeros.  Thus finite ground selection, positivity,
singularity, reflection, and completion are all closed unconditionally; no simple-even hypothesis
survives. -/
theorem exists_ccmPublishedRestrictedWeilMatrix_groundShift_completion
    (a : ℝ) (N : ℕ) :
    ∃ mu : ℝ,
      HasCCMSourceResponseCompletion
        ((ccmScalarShift (ccmPublishedRestrictedWeilMatrix a N) mu).map
          (algebraMap ℝ ℂ))
        (Matrix.diagonal (fun i => (ccmPublishedCenteredClock N i : ℂ)))
        (fun i => (ccmPublishedCenteredSource a N i : ℂ)) := by
  let Q := ccmPublishedRestrictedWeilMatrix a N
  let QC := Q.map (algebraMap ℝ ℂ)
  have hQC : QC.IsHermitian := by
    exact realSymmetric_complexification_isHermitian Q
      (ccmPublishedRestrictedWeilMatrix_transpose a N)
  obtain ⟨i0, _hi0, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (2 * N + 1)))
      hQC.eigenvalues Finset.univ_nonempty
  let mu : ℝ := hQC.eigenvalues i0
  let U : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
    hQC.eigenvectorUnitary
  let d : Fin (2 * N + 1) → ℂ :=
    fun i => ((hQC.eigenvalues i - mu : ℝ) : ℂ)
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    exact RCLike.ofReal_nonneg.mpr
      (sub_nonneg.mpr (hmin i (Finset.mem_univ i)))
  have hdiag : (Matrix.diagonal d).PosSemidef :=
    Matrix.PosSemidef.diagonal hdnonneg
  have hspec :
      QC = U * Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) * Uᴴ := by
    simpa [U, Function.comp_def, Matrix.star_eq_conjTranspose] using
      hQC.spectral_theorem
  have hUunit : U * Uᴴ = 1 := by
    change
      (hQC.eigenvectorUnitary : Matrix (Fin (2 * N + 1))
          (Fin (2 * N + 1)) ℂ) *
        (hQC.eigenvectorUnitary : Matrix (Fin (2 * N + 1))
          (Fin (2 * N + 1)) ℂ)ᴴ = 1
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self hQC.eigenvectorUnitary
  have hmuConj :
      U * ((mu : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)) * Uᴴ =
        (mu : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ) := by
    calc
      U * ((mu : ℂ) • 1) * Uᴴ = (mu : ℂ) • (U * Uᴴ) := by
        simp
      _ = (mu : ℂ) • 1 := by rw [hUunit]
  have hdiagShift :
      Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) -
          (mu : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ) =
        Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d]
    · simp [Matrix.diagonal, hij]
  have hshiftSpectral :
      QC - (mu : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ) =
        U * Matrix.diagonal d * Uᴴ := by
    have hspecSub := congrArg
      (fun M : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ =>
        M - (mu : ℂ) • 1) hspec
    calc
      QC - (mu : ℂ) • (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ) =
          U * Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) * Uᴴ -
            (mu : ℂ) • 1 := hspecSub
      _ = U * Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) * Uᴴ -
            U * ((mu : ℂ) • 1) * Uᴴ := by rw [hmuConj]
      _ = U *
          (Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) -
            (mu : ℂ) • 1) * Uᴴ := by noncomm_ring
      _ = U * Matrix.diagonal d * Uᴴ := by rw [hdiagShift]
  have hmapShift :
      (ccmScalarShift Q mu).map (algebraMap ℝ ℂ) =
        QC - (mu : ℂ) •
          (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [ccmScalarShift, Q, QC]
    · simp [ccmScalarShift, Q, QC, hij]
  have hT :
      ((ccmScalarShift Q mu).map (algebraMap ℝ ℂ)).PosSemidef := by
    rw [hmapShift, hshiftSpectral]
    exact hdiag.mul_mul_conjTranspose_same U
  let c : Fin (2 * N + 1) → ℂ := ⇑(hQC.eigenvectorBasis i0)
  have hcne : c ≠ 0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.mpr
      (hQC.eigenvectorBasis.orthonormal.ne_zero i0)
  have hTc :
      (QC - (mu : ℂ) •
        (1 : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ)) *ᵥ c = 0 := by
    rw [Matrix.sub_mulVec, hQC.mulVec_eigenvectorBasis,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    simp [c, mu]
  have hkernel : ∃ k : Fin (2 * N + 1) → ℂ,
      (ccmScalarShift Q mu).map (algebraMap ℝ ℂ) *ᵥ k = 0 ∧ k ≠ 0 := by
    exact ⟨c, by rw [hmapShift]; exact hTc, hcne⟩
  refine ⟨mu, ?_⟩
  apply ccmPublishedRestrictedWeilMatrix_hasSourceResponseCompletion
  · simpa [Q] using hT
  · simpa [Q] using hkernel

end RHTower
