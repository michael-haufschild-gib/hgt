import GaloisForLFunctions.RHTower.BVPrimeWindowDivisorTomography
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinDivisorTomography
import GaloisForLFunctions.RHTower.CCM.CCMRectangularFullObservableDivisorTomography
import GaloisForLFunctions.RHTower.CCM.CCMRectangularObservableDivisorTomography
import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowDivisorTomography
import GaloisForLFunctions.RHTower.CCM.CCMSimplePrimeDivisorSource

/-!
# Xi CCM multi-observable divisor universality

Nine independently constructed prime/Mellin/rectangular observables recover one local Xi-divisor
datum. After the explicit translation from the critical-Mellin chart, their poles have one common
coordinate and are simple. Eight normalized residues equal the analytic Xi multiplicity; the
elementary prime source has its exact negative.
-/

open Complex Filter Function Set WithTop

namespace RHTower

noncomputable section

/-- The elementary prime source's meromorphic trailing coefficient is its punctured-limit
residue, hence the negative Xi multiplicity. -/
theorem meromorphicTrailingCoeffAt_simplePrimeDivisorContinuedSource
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt simplePrimeDivisorContinuedSource
        (xiRightShiftedPole q) = -(xiRightMultiplicity q : ℂ) := by
  let p : ℂ := xiRightShiftedPole q
  let shift : ℂ → ℂ := fun s => s - 1 / 2
  have hshift : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hbase : MeromorphicAt (logDeriv regularizedRiemannZeta) (shift p) :=
    meromorphicAt_logDeriv_regularizedRiemannZeta (shift p)
  have hlog : MeromorphicAt
      (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2)) p := by
    simpa only [shift, Function.comp_apply] using!
      MeromorphicAt.comp_analyticAt hbase hshift
  have hdsGlobal : Differentiable ℂ
      (fun s : ℂ => dslope regularizedRiemannZeta 1 (s - 1 / 2)) := by
    have hds : Differentiable ℂ (dslope regularizedRiemannZeta 1) := by
      rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
      exact differentiable_regularizedRiemannZeta.differentiableOn
    exact hds.comp (differentiable_id.sub_const (1 / 2))
  have hds : AnalyticAt ℂ
      (fun s : ℂ => dslope regularizedRiemannZeta 1 (s - 1 / 2)) p :=
    (hdsGlobal.differentiableOn.analyticOnNhd isOpen_univ) p (Set.mem_univ p)
  have hmero : MeromorphicAt simplePrimeDivisorContinuedSource p := by
    unfold simplePrimeDivisorContinuedSource
    exact hlog.neg.sub hds.meromorphicAt
  have htrail := hmero.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [show meromorphicOrderAt simplePrimeDivisorContinuedSource p =
      ((-1 : ℤ) : WithTop ℤ) by
        simpa only [p] using
          meromorphicOrderAt_simplePrimeDivisorContinuedSource_eq_neg_one q] at htrail
  simp only [WithTop.untop₀_coe, neg_neg, zpow_one, smul_eq_mul] at htrail
  have hres := tendsto_simplePrimeDivisorContinuedSource_residue q
  simpa only [p] using tendsto_nhds_unique htrail hres

/-- Every noncensoring compact-BV prime window has normalized residue equal to the analytic Xi
multiplicity at the underlying right divisor copy. -/
theorem normalizedBVPrimeWindowResidue_eq_xiRightMultiplicity
    (W : CompactBVPrimeWindow) (q : XiRightZeroCopy)
    (hM : W.mellinTransform (inverseTiltedXiPole q.1.1) ≠ 0) :
    meromorphicTrailingCoeffAt W.continuedSource
          (inverseTiltedXiPole q.1.1) /
        (2 * W.mellinTransform (inverseTiltedXiPole q.1.1)) =
      (xiRightMultiplicity q : ℂ) := by
  let rho : ℂ := (q.1.1 : ℂ)
  let p : ℂ := inverseTiltedXiPole q.1.1
  have hrho : 0 < rho.re := by
    dsimp only [rho]
    linarith [(xi_divisor_support_re_mem_open_unit q.1.1).1]
  have hp : p = rho + 1 / 2 := by
    simp only [p, rho, inverseTiltedXiPole]
  have hzero : regularizedRiemannZeta rho = 0 := by
    have h := regularizedRiemannZeta_eq_zero_at_inverseTiltedXiPole q.1.1
    convert h using 1
    dsimp only [rho, inverseTiltedXiPole]
    ring
  have hmero : MeromorphicAt W.continuedSource p :=
    W.meromorphicOn_continuedSource_rightHalf p (by
      dsimp only [p]
      exact inverseTiltedXiPole_re_gt_half q.1.1)
  have horder : meromorphicOrderAt W.continuedSource p =
      ((-1 : ℤ) : WithTop ℤ) := by
    rw [hp]
    exact W.meromorphicOrderAt_continuedSource_eq_neg_one_of_mellin_ne_zero
      hrho hzero (by simpa only [p, hp] using hM)
  have htrail := hmero.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [horder] at htrail
  simp only [WithTop.untop₀_coe, neg_neg, zpow_one, smul_eq_mul] at htrail
  have hres := W.tendsto_continuedSource_residue_of_regularizedZeta_zero hrho hzero
  rw [analyticOrderAt_regularizedRiemannZeta_eq_xi_of_support q.1.1] at hres
  have hcoeff : meromorphicTrailingCoeffAt W.continuedSource p =
      2 * W.mellinTransform p * (xiRightMultiplicity q : ℂ) := by
    simpa only [hp, rho, p, xiRightMultiplicity] using
      tendsto_nhds_unique htrail hres
  rw [show inverseTiltedXiPole q.1.1 = p by rfl, hcoeff]
  field_simp [show W.mellinTransform p ≠ 0 by simpa only [p] using hM]

/-- Pointwise nine-chart tomography of one right-half Xi divisor copy. -/
structure XiCCMMultiObservableDivisorUniversalCertificate
    (W : CompactBVPrimeWindow) (L : ℝ) (N : ℕ) (q : XiRightZeroCopy) : Prop where
  criticalMellinPole_eq_common :
    criticalMellinXiPole q.1.1 + 3 / 2 = xiRightShiftedPole q
  inverseTiltedPole_eq_common :
    inverseTiltedXiPole q.1.1 = xiRightShiftedPole q
  criticalMellinSimplePole :
    meromorphicOrderAt regularizedCriticalMellinDefect
        (criticalMellinXiPole q.1.1) = ((-1 : ℤ) : WithTop ℤ)
  inverseTiltedSimplePole :
    meromorphicOrderAt inverseTiltedDyadicContinuedSource
        (inverseTiltedXiPole q.1.1) = ((-1 : ℤ) : WithTop ℤ)
  shiftedLogDerivSimplePole :
    meromorphicOrderAt
        (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2))
        (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ)
  dyadicSharpSimplePole :
    meromorphicOrderAt dyadicSharpPrimeContinuedSource
        (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ)
  simplePrimeSimplePole :
    meromorphicOrderAt simplePrimeDivisorContinuedSource
        (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ)
  bvPrimeWindowSimplePole :
    meromorphicOrderAt W.continuedSource
        (inverseTiltedXiPole q.1.1) = ((-1 : ℤ) : WithTop ℤ)
  rectangularCarrierSimplePole :
    meromorphicOrderAt (xiRectangularRightDirichletContinuation L)
        (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ)
  rectangularTailSimplePole :
    meromorphicOrderAt (xiRectangularWeilTailContinuation L N)
        (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ)
  fullObservableSimplePole :
    meromorphicOrderAt (xiRectangularWeilFullContinuation L)
        (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ)
  criticalMellinResidue_eq_multiplicity :
    meromorphicTrailingCoeffAt regularizedCriticalMellinDefect
        (criticalMellinXiPole q.1.1) = (xiRightMultiplicity q : ℂ)
  inverseTiltedResidue_eq_multiplicity :
    meromorphicTrailingCoeffAt inverseTiltedDyadicContinuedSource
          (inverseTiltedXiPole q.1.1) /
        (2 * inverseTiltedDyadicMellin (inverseTiltedXiPole q.1.1)) =
      (xiRightMultiplicity q : ℂ)
  shiftedLogDerivResidue_eq_multiplicity :
    meromorphicTrailingCoeffAt
        (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2))
        (xiRightShiftedPole q) = (xiRightMultiplicity q : ℂ)
  dyadicSharpResidue_eq_multiplicity :
    meromorphicTrailingCoeffAt dyadicSharpPrimeContinuedSource
          (xiRightShiftedPole q) /
        (2 * sharpPrimeWindowMellin (Real.log 2) (xiRightShiftedPole q)) =
      (xiRightMultiplicity q : ℂ)
  simplePrimeResidue_eq_neg_multiplicity :
    meromorphicTrailingCoeffAt simplePrimeDivisorContinuedSource
        (xiRightShiftedPole q) = -(xiRightMultiplicity q : ℂ)
  bvPrimeWindowResidue_eq_multiplicity :
    meromorphicTrailingCoeffAt W.continuedSource
          (inverseTiltedXiPole q.1.1) /
        (2 * W.mellinTransform (inverseTiltedXiPole q.1.1)) =
      (xiRightMultiplicity q : ℂ)
  rectangularCarrierResidue_eq_multiplicity :
    meromorphicTrailingCoeffAt (xiRectangularRightDirichletContinuation L)
          (xiRightShiftedPole q) /
        xiRectangularRightCoefficient L q = (xiRightMultiplicity q : ℂ)
  rectangularTailResidue_eq_multiplicity :
    meromorphicTrailingCoeffAt (xiRectangularWeilTailContinuation L N)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L q) = (xiRightMultiplicity q : ℂ)
  fullObservableResidue_eq_multiplicity :
    meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation L)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L q) = (xiRightMultiplicity q : ℂ)
  criticalMellinResidue_eq_inverseTiltedResidue :
    meromorphicTrailingCoeffAt regularizedCriticalMellinDefect
          (criticalMellinXiPole q.1.1) =
      meromorphicTrailingCoeffAt inverseTiltedDyadicContinuedSource
          (inverseTiltedXiPole q.1.1) /
        (2 * inverseTiltedDyadicMellin (inverseTiltedXiPole q.1.1))
  inverseTiltedResidue_eq_shiftedLogDerivResidue :
    meromorphicTrailingCoeffAt inverseTiltedDyadicContinuedSource
          (inverseTiltedXiPole q.1.1) /
        (2 * inverseTiltedDyadicMellin (inverseTiltedXiPole q.1.1)) =
      meromorphicTrailingCoeffAt
        (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2))
        (xiRightShiftedPole q)
  shiftedLogDerivResidue_eq_dyadicSharpResidue :
    meromorphicTrailingCoeffAt
        (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2))
          (xiRightShiftedPole q) =
      meromorphicTrailingCoeffAt dyadicSharpPrimeContinuedSource
          (xiRightShiftedPole q) /
        (2 * sharpPrimeWindowMellin (Real.log 2) (xiRightShiftedPole q))
  dyadicSharpResidue_eq_bvPrimeWindowResidue :
    meromorphicTrailingCoeffAt dyadicSharpPrimeContinuedSource
          (xiRightShiftedPole q) /
        (2 * sharpPrimeWindowMellin (Real.log 2) (xiRightShiftedPole q)) =
      meromorphicTrailingCoeffAt W.continuedSource
          (inverseTiltedXiPole q.1.1) /
        (2 * W.mellinTransform (inverseTiltedXiPole q.1.1))
  bvPrimeWindowResidue_eq_rectangularCarrierResidue :
    meromorphicTrailingCoeffAt W.continuedSource
          (inverseTiltedXiPole q.1.1) /
        (2 * W.mellinTransform (inverseTiltedXiPole q.1.1)) =
      meromorphicTrailingCoeffAt (xiRectangularRightDirichletContinuation L)
          (xiRightShiftedPole q) /
        xiRectangularRightCoefficient L q
  rectangularCarrierResidue_eq_tailResidue :
    meromorphicTrailingCoeffAt (xiRectangularRightDirichletContinuation L)
          (xiRightShiftedPole q) /
        xiRectangularRightCoefficient L q =
      meromorphicTrailingCoeffAt (xiRectangularWeilTailContinuation L N)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L q)
  rectangularTailResidue_eq_fullObservableResidue :
    meromorphicTrailingCoeffAt (xiRectangularWeilTailContinuation L N)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L q) =
      meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation L)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L q)
  neg_simplePrimeResidue_eq_fullObservableResidue :
    -meromorphicTrailingCoeffAt simplePrimeDivisorContinuedSource
          (xiRightShiftedPole q) =
      meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation L)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L q)

/-- Every positive rectangular width, admissible tail cutoff, noncensoring compact-BV window, and
right Xi divisor copy carries the same nine-chart simple-pole coordinate and multiplicity. -/
theorem xiRightZero_ccmMultiObservableDivisorUniversalCertificate
    (W : CompactBVPrimeWindow) {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (q : XiRightZeroCopy)
    (hM : W.mellinTransform (inverseTiltedXiPole q.1.1) ≠ 0) :
    XiCCMMultiObservableDivisorUniversalCertificate W L N q := by
  have hcriticalCoord :
      criticalMellinXiPole q.1.1 + 3 / 2 = xiRightShiftedPole q := by
    rw [criticalMellinXiPole, xiRightShiftedPole,
      xiRightCenteredZero_eq_support_sub_half]
    ring
  have hinverseCoord :
      inverseTiltedXiPole q.1.1 = xiRightShiftedPole q := by
    rw [inverseTiltedXiPole, xiRightShiftedPole,
      xiRightCenteredZero_eq_support_sub_half]
    ring
  have hcriticalResidue :
      meromorphicTrailingCoeffAt regularizedCriticalMellinDefect
          (criticalMellinXiPole q.1.1) = (xiRightMultiplicity q : ℂ) := by
    simpa only [inverseTiltedXiMultiplicity, xiRightMultiplicity] using
      meromorphicTrailingCoeffAt_regularizedCriticalMellinDefect q.1.1
  have hinverseResidue :
      meromorphicTrailingCoeffAt inverseTiltedDyadicContinuedSource
            (inverseTiltedXiPole q.1.1) /
          (2 * inverseTiltedDyadicMellin (inverseTiltedXiPole q.1.1)) =
        (xiRightMultiplicity q : ℂ) := by
    simpa only [inverseTiltedXiMultiplicity, xiRightMultiplicity] using
      normalizedInverseTiltedDyadicResidue_eq_multiplicity q.1.1
  have hlogResidue :
      meromorphicTrailingCoeffAt
          (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2))
          (xiRightShiftedPole q) = (xiRightMultiplicity q : ℂ) :=
    meromorphicTrailingCoeffAt_shiftedRegularizedZeta_logDeriv q
  have hsharpResidue :
      meromorphicTrailingCoeffAt dyadicSharpPrimeContinuedSource
            (xiRightShiftedPole q) /
          (2 * sharpPrimeWindowMellin (Real.log 2) (xiRightShiftedPole q)) =
        (xiRightMultiplicity q : ℂ) :=
    normalizedDyadicSharpPrimeSourceResidue_eq_xiRightMultiplicity q
  have hsimpleResidue :
      meromorphicTrailingCoeffAt simplePrimeDivisorContinuedSource
          (xiRightShiftedPole q) = -(xiRightMultiplicity q : ℂ) :=
    meromorphicTrailingCoeffAt_simplePrimeDivisorContinuedSource q
  have hbVResidue :
      meromorphicTrailingCoeffAt W.continuedSource
            (inverseTiltedXiPole q.1.1) /
          (2 * W.mellinTransform (inverseTiltedXiPole q.1.1)) =
        (xiRightMultiplicity q : ℂ) :=
    normalizedBVPrimeWindowResidue_eq_xiRightMultiplicity W q hM
  have hcarrierResidue :
      meromorphicTrailingCoeffAt (xiRectangularRightDirichletContinuation L)
            (xiRightShiftedPole q) /
          xiRectangularRightCoefficient L q = (xiRightMultiplicity q : ℂ) := by
    rw [meromorphicTrailingCoeffAt_xiRectangularRightDirichletContinuation hL q]
    field_simp [xiRectangularRightCoefficient_ne_zero hL q]
  have htailResidue :
      meromorphicTrailingCoeffAt (xiRectangularWeilTailContinuation L N)
            (xiRightShiftedPole q) /
          (2 * xiRectangularRightCoefficient L q) =
        (xiRightMultiplicity q : ℂ) :=
    normalizedObservableResidue_eq_xiRightMultiplicity hL hN q
  have hfullResidue :
      meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation L)
            (xiRightShiftedPole q) /
          (2 * xiRectangularRightCoefficient L q) =
        (xiRightMultiplicity q : ℂ) :=
    normalizedFullObservableResidue_eq_xiRightMultiplicity hL q
  have hrho : 0 < ((q.1.1 : XiDivisorSupport) : ℂ).re :=
    (xi_divisor_support_re_mem_open_unit q.1.1).1
  have hzero : regularizedRiemannZeta (q.1.1 : ℂ) = 0 := by
    have h := regularizedRiemannZeta_eq_zero_at_inverseTiltedXiPole q.1.1
    convert h using 1
    rw [inverseTiltedXiPole]
    ring
  have hbVOrder : meromorphicOrderAt W.continuedSource
      (inverseTiltedXiPole q.1.1) = ((-1 : ℤ) : WithTop ℤ) := by
    simpa only [inverseTiltedXiPole] using
      W.meromorphicOrderAt_continuedSource_eq_neg_one_of_mellin_ne_zero
        hrho hzero (by simpa only [inverseTiltedXiPole] using hM)
  exact {
    criticalMellinPole_eq_common := hcriticalCoord
    inverseTiltedPole_eq_common := hinverseCoord
    criticalMellinSimplePole :=
      meromorphicOrderAt_regularizedCriticalMellinDefect_eq_neg_one q.1.1
    inverseTiltedSimplePole :=
      meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one q.1.1
    shiftedLogDerivSimplePole :=
      meromorphicOrderAt_shiftedRegularizedZeta_logDeriv_eq_neg_one q
    dyadicSharpSimplePole :=
      meromorphicOrderAt_dyadicSharpPrimeContinuedSource_eq_neg_one q
    simplePrimeSimplePole :=
      meromorphicOrderAt_simplePrimeDivisorContinuedSource_eq_neg_one q
    bvPrimeWindowSimplePole := hbVOrder
    rectangularCarrierSimplePole :=
      meromorphicOrderAt_xiRectangularRightDirichletContinuation_eq_neg_one hL q
    rectangularTailSimplePole :=
      meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one hL hN q
    fullObservableSimplePole :=
      meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one hL q
    criticalMellinResidue_eq_multiplicity := hcriticalResidue
    inverseTiltedResidue_eq_multiplicity := hinverseResidue
    shiftedLogDerivResidue_eq_multiplicity := hlogResidue
    dyadicSharpResidue_eq_multiplicity := hsharpResidue
    simplePrimeResidue_eq_neg_multiplicity := hsimpleResidue
    bvPrimeWindowResidue_eq_multiplicity := hbVResidue
    rectangularCarrierResidue_eq_multiplicity := hcarrierResidue
    rectangularTailResidue_eq_multiplicity := htailResidue
    fullObservableResidue_eq_multiplicity := hfullResidue
    criticalMellinResidue_eq_inverseTiltedResidue :=
      hcriticalResidue.trans hinverseResidue.symm
    inverseTiltedResidue_eq_shiftedLogDerivResidue :=
      hinverseResidue.trans hlogResidue.symm
    shiftedLogDerivResidue_eq_dyadicSharpResidue :=
      hlogResidue.trans hsharpResidue.symm
    dyadicSharpResidue_eq_bvPrimeWindowResidue :=
      hsharpResidue.trans hbVResidue.symm
    bvPrimeWindowResidue_eq_rectangularCarrierResidue :=
      hbVResidue.trans hcarrierResidue.symm
    rectangularCarrierResidue_eq_tailResidue :=
      hcarrierResidue.trans htailResidue.symm
    rectangularTailResidue_eq_fullObservableResidue :=
      htailResidue.trans hfullResidue.symm
    neg_simplePrimeResidue_eq_fullObservableResidue := by
      rw [hsimpleResidue, hfullResidue]
      ring }

end

end RHTower
