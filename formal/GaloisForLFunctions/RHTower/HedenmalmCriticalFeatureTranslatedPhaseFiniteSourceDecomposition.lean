import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureTranslatedCellAverage
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureTranslatedSourcePlemeljCovariance

/-!
# Source-selected translated finite HCF covariance

The source Fourier alias has a phase with the sign needed by the HCF covariance, while the
translated three-center receiver is uniform in that phase.  This module fuses the translated
finite feature lattice before scalarization and proves the missing finite-window decomposition at
the source-selected phase.

The resulting upper bound pays no nonzero Fourier-alias norm.  Its only losses are the literal
omitted-center term and the compact-cutoff exterior tail.  No zero or divisor index occurs in any
definition below.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open RHTower.RealBoundaryDivisor
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Compact-cutoff HCF weight with geometric centers `k - theta`. -/
def criticalFeatureTranslatedLatticeBoundaryCutoffWeight
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ K, criticalFeatureBoundaryCutoffWeight ((k : ℝ) - theta) cutoff x

theorem continuous_criticalFeatureTranslatedLatticeBoundaryCutoffWeight
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) :
    Continuous (criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta K cutoff) := by
  unfold criticalFeatureTranslatedLatticeBoundaryCutoffWeight
  exact continuous_finsetSum K fun k _hk =>
    continuous_criticalFeatureBoundaryCutoffWeight ((k : ℝ) - theta) cutoff

theorem criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_zero_of_not_mem
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) {x : ℝ}
    (hx : x ∉ Ioo (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3)) :
    criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta K cutoff x = 0 := by
  rw [criticalFeatureTranslatedLatticeBoundaryCutoffWeight]
  apply Finset.sum_eq_zero
  intro k hk
  exact criticalFeatureBoundaryCutoffWeight_eq_zero_of_not_mem
    ((k : ℝ) - theta) cutoff hx

/-- On the canonical core, a dominating cutoff removes only the compact cutoff and preserves the
translated finite lattice exactly. -/
theorem criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_finiteWeight_on_core
    {n cutoff : ℕ} (hcutoff : n ≤ cutoff) (theta : ℝ) {x : ℝ}
    (hx : x ∈ criticalFeatureCanonicalCore n) :
    criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta
        (criticalFeatureCanonicalLatticeWindow n) cutoff x =
      criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta
        (criticalFeatureCanonicalLatticeWindow n) x := by
  have hxabs : |x| ≤ (n : ℝ) + 1 := by
    rw [abs_le]
    simpa only [criticalFeatureCanonicalCore, mem_Icc] using hx
  have hncutoff : (n : ℝ) ≤ cutoff := by exact_mod_cast hcutoff
  have hchi : SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) x = 1 := by
    apply SchwartzMap.realCompactIntervalCutoff_apply_of_abs_le_add_one
    have hcutoffAbs : |(cutoff : ℝ)| = (cutoff : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg cutoff)
    rw [hcutoffAbs]
    linarith
  rw [criticalFeatureTranslatedLatticeBoundaryCutoffWeight,
    criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [criticalFeatureBoundaryCutoffWeight, hchi, mul_one]

/-- One fused compact pole--Gamma observable for a translated finite HCF lattice. -/
def criticalFeatureTranslatedCompactLatticeBoundaryObservable
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
    criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta K cutoff x *
      boundaryDensity XiC eta x

def criticalFeatureTranslatedCompactLatticePoleGammaObservable
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
    criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta K cutoff x *
      criticalFeaturePositiveShiftPoleGammaDensity eta x

theorem criticalFeatureTranslatedCompactLatticeBoundaryObservable_eq_poleGamma
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) {eta : ℝ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2) :
    criticalFeatureTranslatedCompactLatticeBoundaryObservable theta K cutoff eta =
      criticalFeatureTranslatedCompactLatticePoleGammaObservable theta K cutoff eta := by
  rw [criticalFeatureTranslatedCompactLatticeBoundaryObservable,
    criticalFeatureTranslatedCompactLatticePoleGammaObservable]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards
    [ae_boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity heta0 hetaHalf]
    with x hx
  rw [hx]
  intro _hx
  rfl

/-- The fused translated source has the expected fixed-phase Plemelj boundary value. -/
theorem tendsto_criticalFeatureTranslatedCompactLatticeBoundaryObservable
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) :
    Tendsto (criticalFeatureTranslatedCompactLatticeBoundaryObservable theta K cutoff)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k ∈ K,
        criticalLineCriticalFeatureCutoffTrace ((k : ℝ) - theta) cutoff)) := by
  have hr : 0 ≤ (cutoff : ℝ) + 3 := by positivity
  have hrR : (cutoff : ℝ) + 3 < (cutoff : ℝ) + 4 := by linarith
  obtain ⟨Gamma, hGamma, hlim⟩ :=
    XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral
      (c := 0) (r := (cutoff : ℝ) + 3) (R := (cutoff : ℝ) + 4)
      hr hrR
      (continuous_criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta K cutoff)
      (fun x hx => by
        apply criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_zero_of_not_mem
          theta K cutoff
        simpa only [zero_sub, zero_add] using hx)
  have hterm (k : ℤ) :
      criticalLineCriticalFeatureCutoffTrace ((k : ℝ) - theta) cutoff =
        ∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureBoundaryCutoffWeight ((k : ℝ) - theta) cutoff gamma := by
    obtain ⟨Gamma', hGamma', hsum⟩ :=
      exists_criticalFeatureCompactSourceBoundaryLimit_eq_realZeroSum
        ((k : ℝ) - theta) cutoff
    have hGG : Gamma' = Gamma := by
      ext gamma
      rw [hGamma', hGamma]
      simp
    rw [← criticalFeatureCompactSourceBoundaryLimit_eq_cutoffTrace,
      hsum, hGG]
  have htarget :
      (∑ gamma ∈ Gamma,
        ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
          criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta K cutoff gamma) =
        ∑ k ∈ K,
          criticalLineCriticalFeatureCutoffTrace ((k : ℝ) - theta) cutoff := by
    simp only [criticalFeatureTranslatedLatticeBoundaryCutoffWeight, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    exact (hterm k).symm
  rw [← htarget]
  have hlower : (0 : ℝ) - ((cutoff : ℝ) + 3) =
      -((cutoff : ℝ) + 3) := by ring
  have hupper : (0 : ℝ) + ((cutoff : ℝ) + 3) =
      (cutoff : ℝ) + 3 := by ring
  rw [hlower, hupper] at hlim
  change Tendsto
    (fun eta : ℝ =>
      ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
        criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta K cutoff x *
          boundaryDensity XiC eta x)
    (𝓝[>] (0 : ℝ))
    (𝓝 (∑ gamma ∈ Gamma,
      ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
        criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta K cutoff gamma))
  exact hlim

/-- Fixed-phase pole--Gamma source convergence follows without a zero-free horizontal line. -/
theorem tendsto_criticalFeatureTranslatedCompactLatticePoleGammaObservable
    (theta : ℝ) (K : Finset ℤ) (cutoff : ℕ) :
    Tendsto (criticalFeatureTranslatedCompactLatticePoleGammaObservable theta K cutoff)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k ∈ K,
        criticalLineCriticalFeatureCutoffTrace ((k : ℝ) - theta) cutoff)) := by
  have hsource :=
    tendsto_criticalFeatureTranslatedCompactLatticeBoundaryObservable theta K cutoff
  apply hsource.congr'
  have hhalf : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hhalf] with eta heta0 hetaHalf
  exact criticalFeatureTranslatedCompactLatticeBoundaryObservable_eq_poleGamma
    theta K cutoff heta0 hetaHalf

/-- The translated canonical core is the restriction of the fused compact observable's integrand. -/
theorem criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable_eq_cutoffWeight
    {n cutoff : ℕ} (hcutoff : n ≤ cutoff) (eta theta : ℝ) :
    criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable n eta theta =
      ∫ x in criticalFeatureCanonicalCore n,
        criticalFeatureTranslatedLatticeBoundaryCutoffWeight theta
            (criticalFeatureCanonicalLatticeWindow n) cutoff x *
          criticalFeaturePositiveShiftPoleGammaDensity eta x := by
  rw [criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards with x
  intro hx
  rw [criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_finiteWeight_on_core
    hcutoff theta hx]

/-- Literal exterior tail of the translated fused compact source observable. -/
def criticalFeatureCanonicalTranslatedExteriorPoleGammaTail
    (n cutoff : ℕ) (eta theta : ℝ) : ℝ :=
  criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
      (criticalFeatureCanonicalLatticeWindow n) cutoff eta -
    criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable n eta theta

/-- Finite-displacement translated covariance, formed after fusing every feature center into one
source test.  The sign `-theta` matches centers `k - theta` with the receiver convention `k + θ`. -/
def criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
    (n cutoff : ℕ) (eta theta : ℝ) : ℝ :=
  criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
      (criticalFeatureCanonicalLatticeWindow n) -
    criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
      (criticalFeatureCanonicalLatticeWindow n) cutoff eta

/-- For every fixed source phase, the fused finite-displacement covariance lands on the translated
Plemelj covariance at that same geometric lattice. -/
theorem tendsto_criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
    (n cutoff : ℕ) (theta : ℝ) :
    Tendsto
      (fun eta : ℝ =>
        criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
          n cutoff eta theta)
      (𝓝[>] (0 : ℝ))
      (𝓝 (criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta)
        (criticalFeatureCanonicalLatticeWindow n) cutoff)) := by
  have h : Tendsto
      (fun eta : ℝ =>
        criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
            (criticalFeatureCanonicalLatticeWindow n) -
          criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
            (criticalFeatureCanonicalLatticeWindow n) cutoff eta)
      (𝓝[>] (0 : ℝ))
      (𝓝 (criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
          (criticalFeatureCanonicalLatticeWindow n) -
        ∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
          criticalLineCriticalFeatureCutoffTrace ((k : ℝ) - theta) cutoff)) :=
    tendsto_const_nhds.sub
      (tendsto_criticalFeatureTranslatedCompactLatticePoleGammaObservable theta
        (criticalFeatureCanonicalLatticeWindow n) cutoff)
  have htarget :
      criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
          (criticalFeatureCanonicalLatticeWindow n) -
        (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
          criticalLineCriticalFeatureCutoffTrace ((k : ℝ) - theta) cutoff) =
      criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff (-theta)
        (criticalFeatureCanonicalLatticeWindow n) cutoff := by
    rw [criticalFeatureTranslatedPoleGammaPlemeljCovarianceAtCutoff]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hlim := tendsto_criticalFeatureCompactPoleGammaObservable
      ((k : ℝ) - theta) cutoff
    simpa only [sub_eq_add_neg] using hlim.limUnder_eq.symm
  rw [← htarget]
  exact h

/-- Exact zero-mode/core/exterior decomposition of the translated finite covariance. -/
theorem criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance_eq_sourcePieces
    (n cutoff : ℕ) (eta theta : ℝ) :
    criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance
        n cutoff eta theta =
      (criticalFeatureTranslatedPoleGammaLatticeBudget (-theta)
          (criticalFeatureCanonicalLatticeWindow n) -
        criticalFeatureCanonicalCorePoleGammaZeroMode n eta) -
      (criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable n eta theta -
        criticalFeatureCanonicalCorePoleGammaZeroMode n eta) -
      criticalFeatureCanonicalTranslatedExteriorPoleGammaTail n cutoff eta theta := by
  rw [criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance,
    criticalFeatureCanonicalTranslatedExteriorPoleGammaTail]
  ring

/-- At the source-selected phase, the translated finite covariance pays no nonzero Fourier alias. -/
theorem criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance_le_dealiased
    (n : ℕ) :
    criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
        (criticalFeatureCanonicalDealiasingPhase n) ≤
      (criticalFeatureTranslatedPoleGammaLatticeBudget
          (-(criticalFeatureCanonicalDealiasingPhase n))
          (criticalFeatureCanonicalLatticeWindow n) -
        criticalFeatureCanonicalCorePoleGammaZeroMode n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement) +
      |criticalFeatureCanonicalTranslatedInteriorOmittedAlias n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
        (criticalFeatureCanonicalDealiasingPhase n)| +
      |criticalFeatureCanonicalTranslatedExteriorPoleGammaTail n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
        (criticalFeatureCanonicalDealiasingPhase n)| := by
  rw [criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance_eq_sourcePieces]
  have hcore :=
    neg_criticalFeatureCanonicalCoreTranslatedFinitePoleGammaObservable_sub_zeroMode_le_omitted n
  have htail := neg_le_abs
    (criticalFeatureCanonicalTranslatedExteriorPoleGammaTail n
      (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
      (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
      (criticalFeatureCanonicalDealiasingPhase n))
  linarith

/-- Dealiased finite source majorant.  Unlike the unshifted majorants, it has no Fourier-alias or
`L¹` ripple term. -/
def criticalFeatureCanonicalDealiasedFiniteSourcePieceMajorant (n : ℕ) : ℝ :=
  (criticalFeatureTranslatedPoleGammaLatticeBudget
      (-(criticalFeatureCanonicalDealiasingPhase n))
      (criticalFeatureCanonicalLatticeWindow n) -
    criticalFeatureCanonicalCorePoleGammaZeroMode n
      (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement) +
  |criticalFeatureCanonicalTranslatedInteriorOmittedAlias n
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
    (criticalFeatureCanonicalDealiasingPhase n)| +
  |criticalFeatureCanonicalTranslatedExteriorPoleGammaTail n
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
    (criticalFeatureCanonicalDealiasingPhase n)|

theorem criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance_le_dealiasedMajorant
    (n : ℕ) :
    criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
        (criticalFeatureCanonicalDealiasingPhase n) ≤
      criticalFeatureCanonicalDealiasedFiniteSourcePieceMajorant n := by
  simpa only [criticalFeatureCanonicalDealiasedFiniteSourcePieceMajorant] using
    criticalFeatureCanonicalTranslatedFiniteDisplacementPoleGammaCovariance_le_dealiased n

end

end RHTower
