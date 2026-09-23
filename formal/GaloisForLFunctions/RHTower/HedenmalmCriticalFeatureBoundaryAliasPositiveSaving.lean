import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureBoundaryAliasVarianceSaving

/-!
# Positive boundary-alias variance saving for HCF

The HCF covariance subtracts its compact source boundary.  Its useful quantitative phase is
therefore a phase where the boundary alias is positive.  The earlier variance selector produced
the opposite orientation.  This module uses the two-sided `37/200` ripple envelope to construct
the required positive selector, including the zero-envelope case.
-/

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators Interval

namespace RHTower

noncomputable section

/-- A continuous zero-mean reporter with a two-sided envelope rises above variance divided by
that envelope.  Division by a zero envelope is interpreted as zero; the bound then forces the
reporter and its variance to vanish. -/
theorem exists_mem_Icc_intervalVariance_div_le_of_zeroMean_of_abs_le
    (f : ℝ → ℝ) (hf : Continuous f) (M : ℝ) (hM : 0 ≤ M)
    (habs : ∀ theta ∈ Icc (0 : ℝ) 1, |f theta| ≤ M)
    (hmean : (∫ theta in (0 : ℝ)..1, f theta) = 0) :
    ∃ theta ∈ Icc (0 : ℝ) 1,
      (∫ t in (0 : ℝ)..1, (f t) ^ (2 : ℕ)) / M ≤ f theta := by
  by_cases hMpos : 0 < M
  · obtain ⟨theta, htheta, hthetaBound⟩ :=
      exists_mem_Icc_le_neg_intervalVariance_div_of_zeroMean
        (fun t => -f t) hf.neg M hMpos
        (fun t ht => by
          have htBound := abs_le.mp (habs t ht)
          linarith)
        (by
          rw [intervalIntegral.integral_neg, hmean, neg_zero])
    have hvariance :
        (∫ t in (0 : ℝ)..1, (-f t) ^ (2 : ℕ)) =
          ∫ t in (0 : ℝ)..1, (f t) ^ (2 : ℕ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    rw [hvariance] at hthetaBound
    have hnegDiv :
        (-(∫ t in (0 : ℝ)..1, (f t) ^ (2 : ℕ))) / M =
          -((∫ t in (0 : ℝ)..1, (f t) ^ (2 : ℕ)) / M) := by ring
    rw [hnegDiv] at hthetaBound
    exact ⟨theta, htheta, by linarith⟩
  · have hMzero : M = 0 := le_antisymm (le_of_not_gt hMpos) hM
    have hfzero : ∀ theta ∈ Icc (0 : ℝ) 1, f theta = 0 := by
      intro theta htheta
      have h := habs theta htheta
      rw [hMzero] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hvariance : (∫ t in (0 : ℝ)..1, (f t) ^ (2 : ℕ)) = 0 := by
      calc
        (∫ t in (0 : ℝ)..1, (f t) ^ (2 : ℕ)) =
            ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' : t ∈ Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
          change f t ^ (2 : ℕ) = 0
          rw [hfzero t ht']
          norm_num
        _ = 0 := by simp
    refine ⟨0, by norm_num, ?_⟩
    rw [hMzero, hvariance, hfzero 0 (by norm_num)]
    norm_num

/-- The compact boundary alias obeys the full two-sided `37/200` source envelope. -/
theorem abs_criticalFeatureCompactSourceBoundaryAliasAtPhase_le_upperEnvelope
    (cutoff : ℕ) (theta : ℝ) :
    |criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta| ≤
      criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff := by
  obtain ⟨Gamma, _hGamma, hzero, hfull⟩ :=
    exists_criticalFeatureCompactSourceBoundaryPhaseFamily_eq_realZeroSums cutoff
  have hformula :
      criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta =
        ∑ gamma ∈ Gamma,
          (((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma) *
              (criticalFeatureRealBoundaryPeriodization (gamma + theta) - 2 * Real.pi) := by
    rw [criticalFeatureCompactSourceBoundaryAliasAtPhase, hfull theta, hzero]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro gamma hgamma
    unfold criticalFeatureFullBoundaryCutoffWeight
      criticalFeatureZeroModeBoundaryCutoffWeight
    ring
  rw [hformula]
  calc
    |∑ gamma ∈ Gamma,
        (((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
          SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma) *
            (criticalFeatureRealBoundaryPeriodization (gamma + theta) - 2 * Real.pi)| ≤
      ∑ gamma ∈ Gamma,
        |(((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
          SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma) *
            (criticalFeatureRealBoundaryPeriodization (gamma + theta) - 2 * Real.pi)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ gamma ∈ Gamma,
        (((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
          SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma) * ((37 : ℝ) / 200) := by
      apply Finset.sum_le_sum
      intro gamma hgamma
      have hweight : 0 ≤
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) gamma :=
        mul_nonneg (Nat.cast_nonneg _)
          (SchwartzMap.realCompactIntervalCutoff_nonnegative _ _)
      rw [abs_mul, abs_of_nonneg hweight]
      exact mul_le_mul_of_nonneg_left
        (abs_criticalFeatureRealBoundaryPeriodization_sub_two_pi_le (gamma + theta))
        hweight
    _ = criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff := by
      rw [criticalFeatureCompactSourceBoundaryAliasUpperEnvelope, hzero]
      simp only [criticalFeatureZeroModeBoundaryCutoffWeight]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro gamma hgamma
      field_simp [Real.pi_ne_zero]

/-- Quantitative boundary-first phase in the covariance-saving orientation. -/
theorem exists_criticalFeatureCompactBoundaryAliasPhase_variance_div_le
    (cutoff : ℕ) :
    ∃ theta ∈ Icc (0 : ℝ) 1,
      criticalFeatureCompactSourceBoundaryAliasRealVariance cutoff /
          criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff ≤
        criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff theta := by
  simpa only [criticalFeatureCompactSourceBoundaryAliasRealVariance] using
    exists_mem_Icc_intervalVariance_div_le_of_zeroMean_of_abs_le
      (criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff)
      (continuous_criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff)
      (criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff)
      (criticalFeatureCompactSourceBoundaryAliasUpperEnvelope_nonnegative cutoff)
      (fun theta _htheta =>
        abs_criticalFeatureCompactSourceBoundaryAliasAtPhase_le_upperEnvelope cutoff theta)
      (intervalIntegral_criticalFeatureCompactSourceBoundaryAliasAtPhase_eq_zero cutoff)

/-- Canonical boundary phase maximizing the quantitative covariance saving. -/
def criticalFeatureCompactBoundaryVarianceSavingPhase (cutoff : ℕ) : ℝ :=
  Classical.choose (exists_criticalFeatureCompactBoundaryAliasPhase_variance_div_le cutoff)

theorem criticalFeatureCompactBoundaryVarianceSavingPhase_mem (cutoff : ℕ) :
    criticalFeatureCompactBoundaryVarianceSavingPhase cutoff ∈ Icc (0 : ℝ) 1 :=
  (Classical.choose_spec
    (exists_criticalFeatureCompactBoundaryAliasPhase_variance_div_le cutoff)).1

theorem criticalFeatureCompactBoundaryVarianceSavingPhase_spec (cutoff : ℕ) :
    criticalFeatureCompactSourceBoundaryAliasRealVariance cutoff /
        criticalFeatureCompactSourceBoundaryAliasUpperEnvelope cutoff ≤
      criticalFeatureCompactSourceBoundaryAliasAtPhase cutoff
        (criticalFeatureCompactBoundaryVarianceSavingPhase cutoff) :=
  (Classical.choose_spec
    (exists_criticalFeatureCompactBoundaryAliasPhase_variance_div_le cutoff)).2

/-- Positive boundary-alias saving survives replacement of both source boundary limits by
finite positive-displacement pole--Gamma observables.  The only loss is the sum of the two
approximation errors. -/
theorem neg_criticalFeatureCompactFullPoleGammaObservableAtVarianceSavingPhase_sub_zeroMode_lt
    (n : ℕ) {eta eps : ℝ}
    (hfull :
      |criticalFeatureCompactFullPoleGammaObservableAtPhase
          (criticalFeatureCompactBoundaryVarianceSavingPhase n) n eta -
        criticalFeatureCompactFullSourceBoundaryLimitAtPhase n
          (criticalFeatureCompactBoundaryVarianceSavingPhase n)| < eps)
    (hzero :
      |criticalFeatureCompactZeroModePoleGammaObservable n eta -
        criticalFeatureCompactZeroModeSourceBoundaryLimit n| < eps) :
    -(criticalFeatureCompactFullPoleGammaObservableAtPhase
        (criticalFeatureCompactBoundaryVarianceSavingPhase n) n eta -
      criticalFeatureCompactZeroModePoleGammaObservable n eta) <
      -(criticalFeatureCompactSourceBoundaryAliasRealVariance n /
        criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n) + 2 * eps := by
  have hphase := criticalFeatureCompactBoundaryVarianceSavingPhase_spec n
  rw [criticalFeatureCompactSourceBoundaryAliasAtPhase] at hphase
  rw [abs_lt] at hfull hzero
  linarith

private theorem eventually_abs_sub_lt_of_tendsto_positiveBoundarySaving
    {alpha : Type*} {l : Filter alpha} {f : alpha → ℝ} {a eps : ℝ}
    (h : Tendsto f l (nhds a)) (heps : 0 < eps) :
    ∀ᶠ x in l, |f x - a| < eps := by
  have hlo : ∀ᶠ x in l, a - eps < f x :=
    (tendsto_order.1 h).1 _ (by linarith)
  have hhi : ∀ᶠ x in l, f x < a + eps :=
    (tendsto_order.1 h).2 _ (by linarith)
  filter_upwards [hlo, hhi] with x hxlo hxhi
  rw [abs_lt]
  constructor <;> linarith

/-- Boundary-variance phase, outer cutoff, and positive displacement selected in source-first
order.  Unlike `CriticalFeatureCanonicalBoundarySelectedData`, this record carries the
quantitative positive-alias phase needed to lower the covariance. -/
structure CriticalFeatureCanonicalBoundaryVarianceSelectedData (n : ℕ) where
  cutoff : ℕ
  cutoff_ge : n ≤ cutoff
  displacement : ℝ
  displacement_pos : 0 < displacement
  displacement_lt_half : displacement < 1 / 2
  displacement_lt_reciprocal : displacement < 1 / ((n : ℝ) + 1)
  covariance_error_lt :
    |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n cutoff
          displacement (criticalFeatureCompactBoundaryVarianceSavingPhase n) -
        criticalFeatureTranslatedPoleGammaPlemeljCovariance
          (-(criticalFeatureCompactBoundaryVarianceSavingPhase n))
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1)
  full_boundary_error_lt :
    |criticalFeatureCompactFullPoleGammaObservableAtPhase
          (criticalFeatureCompactBoundaryVarianceSavingPhase n) n displacement -
        criticalFeatureCompactFullSourceBoundaryLimitAtPhase n
          (criticalFeatureCompactBoundaryVarianceSavingPhase n)| <
      1 / ((n : ℝ) + 1)
  zero_boundary_error_lt :
    |criticalFeatureCompactZeroModePoleGammaObservable n displacement -
        criticalFeatureCompactZeroModeSourceBoundaryLimit n| <
      1 / ((n : ℝ) + 1)

/-- Quantitative positive-alias boundary data exist unconditionally.  Phase is fixed before both
outer cutoff and displacement, so no moving-phase limit interchange is used. -/
theorem exists_criticalFeatureCanonicalBoundaryVarianceSelectedData (n : ℕ) :
    Nonempty (CriticalFeatureCanonicalBoundaryVarianceSelectedData n) := by
  let K := criticalFeatureCanonicalLatticeWindow n
  let theta := criticalFeatureCompactBoundaryVarianceSavingPhase n
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have heps : 0 < eps := by positivity
  have houter : Tendsto
      (criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K)
      atTop
      (nhds (criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K)) := by
    have h :=
      tendsto_criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K
    convert h using 1
    rw [criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget_eq_sourceCovariance_add_vm]
    ring_nf
  have houterNear : ∀ᶠ cutoff : ℕ in atTop,
      |criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K cutoff -
        criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K| < eps / 2 :=
    eventually_abs_sub_lt_of_tendsto_positiveBoundarySaving houter (half_pos heps)
  obtain ⟨cutoff, hcutoffNear, hcutoffGe⟩ :=
    (houterNear.and (eventually_ge_atTop n)).exists
  have hinner :=
    tendsto_criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
      n cutoff theta
  have hinnerNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
          n cutoff eta theta -
        criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K cutoff| <
        eps / 2 :=
    eventually_abs_sub_lt_of_tendsto_positiveBoundarySaving hinner (half_pos heps)
  have hfullNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      |criticalFeatureCompactFullPoleGammaObservableAtPhase theta n eta -
        criticalFeatureCompactFullSourceBoundaryLimitAtPhase n theta| < eps :=
    eventually_abs_sub_lt_of_tendsto_positiveBoundarySaving
      (tendsto_criticalFeatureCompactFullPoleGammaObservableAtPhase theta n) heps
  have hzeroNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      |criticalFeatureCompactZeroModePoleGammaObservable n eta -
        criticalFeatureCompactZeroModeSourceBoundaryLimit n| < eps :=
    eventually_abs_sub_lt_of_tendsto_positiveBoundarySaving
      (tendsto_criticalFeatureCompactZeroModePoleGammaObservable n) heps
  have hpos : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < eta :=
    self_mem_nhdsWithin
  have hhalf : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  have hepsNear : ∀ᶠ eta : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), eta < eps :=
    (eventually_lt_nhds heps).filter_mono inf_le_left
  obtain ⟨eta, hetaPos, hetaHalf, hetaEps, hetaInner, hetaFull, hetaZero⟩ :=
    (hpos.and (hhalf.and (hepsNear.and
      (hinnerNear.and (hfullNear.and hzeroNear))))).exists
  refine ⟨{
    cutoff := cutoff
    cutoff_ge := hcutoffGe
    displacement := eta
    displacement_pos := hetaPos
    displacement_lt_half := hetaHalf
    displacement_lt_reciprocal := ?_
    covariance_error_lt := ?_
    full_boundary_error_lt := ?_
    zero_boundary_error_lt := ?_ }⟩
  · simpa only [eps] using hetaEps
  · have htriangle :
        |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
              n cutoff eta theta -
            criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K| ≤
          |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
              n cutoff eta theta -
            criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K cutoff| +
          |criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta) K cutoff -
            criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K| := by
        rw [show
          criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
                n cutoff eta theta -
              criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K =
            (criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
                n cutoff eta theta -
              criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff
                (-theta) K cutoff) +
            (criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff
                (-theta) K cutoff -
              criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K) by ring]
        exact abs_add_le _ _
    change
      |criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
            n cutoff eta theta -
          criticalFeatureTranslatedPoleGammaPlemeljCovariance (-theta) K| < eps
    exact htriangle.trans_lt (by linarith)
  · simpa only [theta, eps] using hetaFull
  · simpa only [eps] using hetaZero

/-- Canonical source-first data at the quantitative covariance-saving boundary phase. -/
def criticalFeatureCanonicalBoundaryVarianceSelectedData (n : ℕ) :
    CriticalFeatureCanonicalBoundaryVarianceSelectedData n :=
  Classical.choice (exists_criticalFeatureCanonicalBoundaryVarianceSelectedData n)

/-- Finite pole--Gamma source majorant with the boundary-alias variance saving subtracted
explicitly.  Its definition contains no zero or divisor index. -/
def criticalFeatureCanonicalBoundaryVarianceFiniteSourceMajorant (n : ℕ) : ℝ :=
  let data := criticalFeatureCanonicalBoundaryVarianceSelectedData n
  let theta := criticalFeatureCompactBoundaryVarianceSavingPhase n
  (criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
      (criticalFeatureCanonicalLatticeWindow n) -
    criticalFeatureCompactZeroModePoleGammaObservable n data.displacement) -
  criticalFeatureCompactSourceBoundaryAliasRealVariance n /
    criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n +
  |criticalFeatureCompactTranslatedBaseOmittedCenters n data.displacement theta| +
  |criticalFeatureCanonicalBoundarySelectedExteriorIncrement
    n data.cutoff data.displacement theta| +
  2 * (1 / ((n : ℝ) + 1))

/-- The selected finite covariance receives the full normalized boundary variance as a genuine
source-side saving. -/
theorem criticalFeatureCanonicalBoundaryVarianceSelectedFiniteCovariance_le_majorant (n : ℕ) :
    criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n
        (criticalFeatureCanonicalBoundaryVarianceSelectedData n).cutoff
        (criticalFeatureCanonicalBoundaryVarianceSelectedData n).displacement
        (criticalFeatureCompactBoundaryVarianceSavingPhase n) ≤
      criticalFeatureCanonicalBoundaryVarianceFiniteSourceMajorant n := by
  let data := criticalFeatureCanonicalBoundaryVarianceSelectedData n
  let theta := criticalFeatureCompactBoundaryVarianceSavingPhase n
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have halias :=
    neg_criticalFeatureCompactFullPoleGammaObservableAtVarianceSavingPhase_sub_zeroMode_lt
      n data.full_boundary_error_lt data.zero_boundary_error_lt
  have homit := le_abs_self
    (criticalFeatureCompactTranslatedBaseOmittedCenters n data.displacement theta)
  have hext := neg_le_abs
    (criticalFeatureCanonicalBoundarySelectedExteriorIncrement
      n data.cutoff data.displacement theta)
  dsimp only [data, theta, eps] at halias homit hext
  rw [criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance_eq_boundaryPieces]
  simp only [criticalFeatureCanonicalBoundaryVarianceFiniteSourceMajorant]
  linarith

/-- Infinite translated Plemelj majorant after paying the selected finite-covariance error.
This is the zero-independent height-local pole--Gamma object to estimate asymptotically. -/
def criticalFeatureCanonicalBoundaryVariancePlemeljSourceMajorant (n : ℕ) : ℝ :=
  let data := criticalFeatureCanonicalBoundaryVarianceSelectedData n
  let theta := criticalFeatureCompactBoundaryVarianceSavingPhase n
  (criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
      (criticalFeatureCanonicalLatticeWindow n) -
    criticalFeatureCompactZeroModePoleGammaObservable n data.displacement) -
  criticalFeatureCompactSourceBoundaryAliasRealVariance n /
    criticalFeatureCompactSourceBoundaryAliasUpperEnvelope n +
  |criticalFeatureCompactTranslatedBaseOmittedCenters n data.displacement theta| +
  |criticalFeatureCanonicalBoundarySelectedExteriorIncrement
    n data.cutoff data.displacement theta| +
  3 * (1 / ((n : ℝ) + 1))

/-- Exact finite-to-infinite transfer: translated Plemelj covariance is strictly below the
variance-saved source majorant. -/
theorem criticalFeatureTranslatedPoleGammaPlemeljCovariance_lt_boundaryVarianceSourceMajorant
    (n : ℕ) :
    criticalFeatureTranslatedPoleGammaPlemeljCovariance
        (-(criticalFeatureCompactBoundaryVarianceSavingPhase n))
        (criticalFeatureCanonicalLatticeWindow n) <
      criticalFeatureCanonicalBoundaryVariancePlemeljSourceMajorant n := by
  let data := criticalFeatureCanonicalBoundaryVarianceSelectedData n
  let theta := criticalFeatureCompactBoundaryVarianceSavingPhase n
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have hfinite :=
    criticalFeatureCanonicalBoundaryVarianceSelectedFiniteCovariance_le_majorant n
  have hclose := data.covariance_error_lt
  rw [abs_lt] at hclose
  dsimp only [data, theta, eps] at hclose
  simp only [criticalFeatureCanonicalBoundaryVarianceFiniteSourceMajorant] at hfinite
  simp only [criticalFeatureCanonicalBoundaryVariancePlemeljSourceMajorant]
  linarith

end

end RHTower
