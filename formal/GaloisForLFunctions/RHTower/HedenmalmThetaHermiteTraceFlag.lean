import GaloisForLFunctions.RHTower.HedenmalmThetaArithmeticGreenFlag
import GaloisForLFunctions.RHTower.UnweightedTraceHankelConverse
import GaloisForLFunctions.HTGeometry.SchurCharpoly

/-!
# Root-free theta arithmetic Hermite flag

The modal Green flag quantifies over eigenvectors.  This module replaces that spectral interface
by a literal source-coordinate form.  At stage `k`, coefficients of a real polynomial are paired
against power traces of the actual finite theta source matrix:

`sum_{r,s} a_r a_s tr(M_k^(r+s))`.

No eigenvalue, determinant zero, Xi zero, or spectral branch occurs in this definition.  Schur
triangulation is used only afterward to prove the exact finite-dimensional classification:
universal nonnegativity of this Hermite form is equivalent to a real stage divisor, hence to exact
modewise Green neutrality.  Existing Hilbert--Schmidt and compact-open theorems then provide the
unconditional completion of the same stages.
-/

open Complex Filter Metric Polynomial
open scoped BigOperators Matrix

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmHilbertSchmidt

noncomputable section

/-- Canonically reindexed actual finite theta matrix.  Reindexing changes neither traces nor its
ordinary determinant. -/
def thetaSourceSignedStageFinMatrix (k : ℕ) :
    Matrix (Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
      (Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) ℂ :=
  blockFin (thetaSourceSignedKernel k) (thetaSourceSignedCutoff k)

/-- Root-free arithmetic Hermite form of one actual theta stage. -/
def thetaSourceSignedStageHermiteTrace (k : ℕ) (p : Polynomial ℝ) : ℂ :=
  finiteMatrixUnweightedTraceHankel (thetaSourceSignedStageFinMatrix k) p

/-- Source-coordinate arithmetic property at one stage: every real-polynomial Hermite trace is
nonnegative. -/
def ThetaSourceArithmeticHermiteStageProperty (k : ℕ) : Prop :=
  ∀ p : Polynomial ℝ, 0 ≤ (thetaSourceSignedStageHermiteTrace k p).re

/-- Cofinal root-free theta arithmetic flag. -/
def ThetaSourceArithmeticHermiteFlag : Prop :=
  ∀ k : ℕ, ThetaSourceArithmeticHermiteStageProperty k

/-- Finite arithmetic window at stage `k`.  A matrix of size `n` needs trace moments only through
degree `4n+2`, arising from polynomial tests of degree at most `2n+1`. -/
def ThetaSourceArithmeticHermiteWindowStageProperty (k : ℕ) : Prop :=
  ∀ p : Polynomial ℝ,
    p.natDegree ≤ 2 * Fintype.card ↥(thetaSourceSignedCutoff k) + 1 →
    0 ≤ (thetaSourceSignedStageHermiteTrace k p).re

/-- Cofinal finite-window theta arithmetic flag. -/
def ThetaSourceArithmeticHermiteWindowFlag : Prop :=
  ∀ k : ℕ, ThetaSourceArithmeticHermiteWindowStageProperty k

private theorem thetaSourceSignedStage_entireDet2_eq_finiteDet2
    (k : ℕ) (z : ℂ) :
    entireDet2 (thetaSourceSignedKernel k) z =
      finiteDet2 (-(thetaSourceSignedStageFinMatrix k)) z := by
  rw [thetaSourceSignedStageFinMatrix, finiteDet2_neg_blockFin]
  exact congrFun (entireDet2_eq_finiteDet2_of_support
    (isHS_thetaSourceSignedKernel k) (thetaSourceSignedKernel_support k)) z

private theorem thetaSourceSignedStage_det_eq_zero_of_schur_diagonal
    (k : ℕ)
    {U T : Matrix (Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
      (Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) ℂ}
    (hU2 : U * Uᴴ = 1) (hT : T.BlockTriangular id)
    (hMT : Uᴴ * thetaSourceSignedStageFinMatrix k * U = T)
    {i : Fin (Fintype.card ↥(thetaSourceSignedCutoff k))}
    (hi : T i i ≠ 0) :
    thetaSourceSignedOrdinaryDet k (T i i)⁻¹ = 0 := by
  have hprod := det_one_add_smul_eq_prod hU2 hT hMT (-(T i i)⁻¹)
  have hfactor : 1 + (-(T i i)⁻¹) * T i i = 0 := by
    field_simp [hi]
    ring
  have hdet :
      ((1 : Matrix (Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
        (Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) ℂ) +
        (-(T i i)⁻¹) • thetaSourceSignedStageFinMatrix k).det = 0 := by
    rw [hprod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hfactor
  have hfinite : finiteDet2 (-(thetaSourceSignedStageFinMatrix k)) (T i i)⁻¹ = 0 := by
    rw [finiteDet2]
    have hmatrix :
        (1 : Matrix (Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
          (Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) ℂ) +
            (T i i)⁻¹ • (-(thetaSourceSignedStageFinMatrix k)) =
          1 + (-(T i i)⁻¹) • thetaSourceSignedStageFinMatrix k := by module
    rw [hmatrix, hdet, zero_mul]
  rw [thetaSourceSignedOrdinaryDet_eq_entireDet2,
    thetaSourceSignedStage_entireDet2_eq_finiteDet2]
  exact hfinite

/-- Root-free Hermite positivity at one stage forces its ordinary divisor to be real. -/
theorem thetaSourceArithmeticHermiteStage_realDivisor
    (k : ℕ) (hhermite : ThetaSourceArithmeticHermiteStageProperty k) :
    ThetaSourceSignedStageRealDivisor k := by
  let M := thetaSourceSignedStageFinMatrix k
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ :=
    GaloisForLFunctions.HTGeometry.exists_schur_triangulation
      (Fintype.card ↥(thetaSourceSignedCutoff k)) M
  have hdiag : ∀ i, (T i i).im = 0 := by
    apply finiteMatrix_unweightedTraceHankel_nonneg_implies_schur_real
      hU1 hU2 hT hMT
    intro p
    exact hhermite p
  intro z hz
  have hdet2 : entireDet2 (thetaSourceSignedKernel k) z = 0 := by
    rw [← thetaSourceSignedOrdinaryDet_eq_entireDet2 k z]
    exact hz
  have hfinite : finiteDet2 (-M) z = 0 := by
    rw [← thetaSourceSignedStage_entireDet2_eq_finiteDet2 k z]
    exact hdet2
  have hdet : ((1 : Matrix (Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
      (Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) ℂ) + z • (-M)).det = 0 := by
    rw [finiteDet2] at hfinite
    exact (mul_eq_zero.mp hfinite).resolve_right (Complex.exp_ne_zero _)
  have hprod : ∏ i, (1 + (-z) * T i i) = 0 := by
    rw [← det_one_add_smul_eq_prod hU2 hT hMT (-z)]
    simpa only [smul_neg, neg_smul] using hdet
  obtain ⟨i, hi, hfactor⟩ := Finset.prod_eq_zero_iff.mp hprod
  have htii : T i i ≠ 0 := by
    intro hzero
    simp [hzero] at hfactor
  have htre : (T i i).re ≠ 0 := by
    intro hre
    apply htii
    apply Complex.ext hre (hdiag i)
  have him := congrArg Complex.im hfactor
  simp only [Complex.add_im, Complex.one_im, zero_add, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, hdiag i, mul_zero] at him
  exact neg_eq_zero.mp ((mul_eq_zero.mp him).resolve_right htre)

/-- Conversely, a real stage divisor makes every source power-trace Hermite form nonnegative. -/
theorem thetaSourceArithmeticHermiteStage_of_realDivisor
    (k : ℕ) (hreal : ThetaSourceSignedStageRealDivisor k) :
    ThetaSourceArithmeticHermiteStageProperty k := by
  let M := thetaSourceSignedStageFinMatrix k
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ :=
    GaloisForLFunctions.HTGeometry.exists_schur_triangulation
      (Fintype.card ↥(thetaSourceSignedCutoff k)) M
  have hdiag : ∀ i, (T i i).im = 0 := by
    intro i
    by_cases hi : T i i = 0
    · simp [hi]
    · have hzero := thetaSourceSignedStage_det_eq_zero_of_schur_diagonal
        k hU2 hT hMT hi
      have hinvIm : ((T i i)⁻¹).im = 0 := hreal _ hzero
      rw [Complex.inv_im] at hinvIm
      have hnorm : Complex.normSq (T i i) ≠ 0 := by
        simpa [Complex.normSq_eq_zero] using hi
      have hneg : -(T i i).im = 0 :=
        (div_eq_zero_iff).mp hinvIm |>.resolve_right hnorm
      linarith
  intro p
  change 0 ≤ (finiteMatrixUnweightedTraceHankel M p).re
  rw [finiteMatrixUnweightedTraceHankel_eq_schur hU1 hU2 hT hMT]
  have hsum : (∑ i, evalRealPolynomial p (T i i) ^ 2).re =
      ∑ i, (evalRealPolynomial p (T i i) ^ 2).re := by simp
  rw [hsum]
  apply Finset.sum_nonneg
  intro i hi
  let x : ℝ := (T i i).re
  have htx : T i i = (x : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [x] using hdiag i
  rw [htx, evalRealPolynomial_ofReal]
  rw [pow_two, Complex.mul_re]
  simpa only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    mul_self_nonneg (Polynomial.eval x p)

/-- At each actual theta stage, the root-free source trace condition, real divisor, and exact
modewise Green neutrality are the same theorem. -/
theorem thetaSourceArithmeticHermiteStage_iff_greenStage (k : ℕ) :
    ThetaSourceArithmeticHermiteStageProperty k ↔
      ThetaSourceArithmeticGreenStageProperty k := by
  rw [thetaSourceArithmeticGreenStage_iff_realDivisor]
  exact ⟨thetaSourceArithmeticHermiteStage_realDivisor k,
    thetaSourceArithmeticHermiteStage_of_realDivisor k⟩

/-- The explicit finite degree window is already complete: it is equivalent to unrestricted
Hermite positivity at the same actual theta stage. -/
theorem thetaSourceArithmeticHermiteWindowStage_iff_hermiteStage (k : ℕ) :
    ThetaSourceArithmeticHermiteWindowStageProperty k ↔
      ThetaSourceArithmeticHermiteStageProperty k := by
  constructor
  · intro hwindow
    let M := thetaSourceSignedStageFinMatrix k
    obtain ⟨U, T, hU1, hU2, hT, hMT⟩ :=
      GaloisForLFunctions.HTGeometry.exists_schur_triangulation
        (Fintype.card ↥(thetaSourceSignedCutoff k)) M
    have hdiag : ∀ i, (T i i).im = 0 := by
      apply finiteMatrix_unweightedTraceHankel_nonneg_degree_le_implies_schur_real
        hU1 hU2 hT hMT
      intro p hp
      apply hwindow p
      simpa using hp
    intro p
    change 0 ≤ (finiteMatrixUnweightedTraceHankel M p).re
    rw [finiteMatrixUnweightedTraceHankel_eq_schur hU1 hU2 hT hMT]
    have hsum : (∑ i, evalRealPolynomial p (T i i) ^ 2).re =
        ∑ i, (evalRealPolynomial p (T i i) ^ 2).re := by simp
    rw [hsum]
    apply Finset.sum_nonneg
    intro i hi
    let x : ℝ := (T i i).re
    have htx : T i i = (x : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa [x] using hdiag i
    rw [htx, evalRealPolynomial_ofReal, pow_two, Complex.mul_re]
    simpa only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      mul_self_nonneg (Polynomial.eval x p)
  · intro h p hp
    exact h p

/-- Finite trace window, real stage divisor, and exact modal Green cancellation are equivalent. -/
theorem thetaSourceArithmeticHermiteWindowStage_iff_greenStage (k : ℕ) :
    ThetaSourceArithmeticHermiteWindowStageProperty k ↔
      ThetaSourceArithmeticGreenStageProperty k := by
  rw [thetaSourceArithmeticHermiteWindowStage_iff_hermiteStage,
    thetaSourceArithmeticHermiteStage_iff_greenStage]

/-- Global root-free Hermite flag is exactly the previous modal Green flag. -/
theorem thetaSourceArithmeticHermiteFlag_iff_greenFlag :
    ThetaSourceArithmeticHermiteFlag ↔ ThetaSourceArithmeticGreenFlag := by
  constructor
  · intro h k
    exact (thetaSourceArithmeticHermiteStage_iff_greenStage k).mp (h k)
  · intro h k
    exact (thetaSourceArithmeticHermiteStage_iff_greenStage k).mpr (h k)

/-- The cofinal finite-window flag is exactly the modal Green flag. -/
theorem thetaSourceArithmeticHermiteWindowFlag_iff_greenFlag :
    ThetaSourceArithmeticHermiteWindowFlag ↔ ThetaSourceArithmeticGreenFlag := by
  constructor
  · intro h k
    exact (thetaSourceArithmeticHermiteWindowStage_iff_greenStage k).mp (h k)
  · intro h k
    exact (thetaSourceArithmeticHermiteWindowStage_iff_greenStage k).mpr (h k)

/-- Root-free theta source arithmetic flag closes RH. -/
theorem riemannHypothesis_of_thetaSourceArithmeticHermiteFlag
    (h : ThetaSourceArithmeticHermiteFlag) : RiemannHypothesis :=
  riemannHypothesis_of_thetaSourceArithmeticGreenFlag
    (thetaSourceArithmeticHermiteFlag_iff_greenFlag.mp h)

/-- Finite-window source arithmetic positivity closes RH. -/
theorem riemannHypothesis_of_thetaSourceArithmeticHermiteWindowFlag
    (h : ThetaSourceArithmeticHermiteWindowFlag) : RiemannHypothesis :=
  riemannHypothesis_of_thetaSourceArithmeticGreenFlag
    (thetaSourceArithmeticHermiteWindowFlag_iff_greenFlag.mp h)

/-- Unconditional completion belongs to exactly the same source matrices whose power traces define
the Hermite flag. -/
theorem thetaSourceArithmeticHermiteStages_completion :
    Tendsto (fun k => HilbertSchmidt.hsNorm
      (thetaSourceSignedKernel k - (-thetaKernelMatrix))) atTop (nhds 0) ∧
    TendstoLocallyUniformly thetaSourceSignedOrdinaryDet
      (fun z => XiC z / XiC 0) atTop :=
  ⟨thetaSourceSignedKernel_tendsto_source,
    thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC⟩

/-- Same finite-window stages converge in Hilbert--Schmidt topology and their ordinary
determinants converge compact-open to normalized Xi. -/
theorem thetaSourceArithmeticHermiteWindowStages_completion :
    Tendsto (fun k => HilbertSchmidt.hsNorm
      (thetaSourceSignedKernel k - (-thetaKernelMatrix))) atTop (nhds 0) ∧
    TendstoLocallyUniformly thetaSourceSignedOrdinaryDet
      (fun z => XiC z / XiC 0) atTop :=
  thetaSourceArithmeticHermiteStages_completion

end

end RHTower.HedenmalmThetaSource
