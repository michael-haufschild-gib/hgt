import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureCanonicalFiniteDisplacement

/-!
# Canonical lattice-summed finite-displacement source gate for HCF

The pointwise finite-displacement gate still scalarizes one compact boundary observable per
feature center and only then adds over the height lattice.  This module fuses the entire finite
lattice into one compact test weight before the sole Lebesgue scalarization.  The resulting
observable is literal continued pole--Gamma--von-Mangoldt data, with no zero or divisor index.

A direct Plemelj argument for the fused weight proves convergence to the sum of the individual
critical-line cutoff traces.  A diagonal cutoff/displacement selection then gives a canonical
positive submicroscopic source covariance differing from the infinite HCF Plemelj covariance by
`o(N)`.  This is a source reduction, not the remaining quantitative ceiling.
-/

open Complex Filter Topology Set MeasureTheory
open RHTower.RealBoundaryDivisor
open scoped BigOperators

namespace RHTower

noncomputable section

def criticalFeatureLatticeBoundaryCutoffWeight
    (K : Finset ℤ) (cutoff : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ K, criticalFeatureBoundaryCutoffWeight (k : ℝ) cutoff x

theorem continuous_criticalFeatureLatticeBoundaryCutoffWeight
    (K : Finset ℤ) (cutoff : ℕ) :
    Continuous (criticalFeatureLatticeBoundaryCutoffWeight K cutoff) := by
  unfold criticalFeatureLatticeBoundaryCutoffWeight
  exact continuous_finsetSum K fun k _hk =>
    continuous_criticalFeatureBoundaryCutoffWeight (k : ℝ) cutoff

theorem criticalFeatureLatticeBoundaryCutoffWeight_eq_zero_of_not_mem
    (K : Finset ℤ) (cutoff : ℕ) {x : ℝ}
    (hx : x ∉ Ioo (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3)) :
    criticalFeatureLatticeBoundaryCutoffWeight K cutoff x = 0 := by
  rw [criticalFeatureLatticeBoundaryCutoffWeight]
  apply Finset.sum_eq_zero
  intro k hk
  exact criticalFeatureBoundaryCutoffWeight_eq_zero_of_not_mem (k : ℝ) cutoff hx

def criticalFeatureCompactLatticeBoundaryObservable
    (K : Finset ℤ) (cutoff : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
    criticalFeatureLatticeBoundaryCutoffWeight K cutoff x *
      boundaryDensity XiC eta x

def criticalFeatureCompactLatticePoleGammaObservable
    (K : Finset ℤ) (cutoff : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in Icc (-((cutoff : ℝ) + 3)) ((cutoff : ℝ) + 3),
    criticalFeatureLatticeBoundaryCutoffWeight K cutoff x *
      criticalFeaturePositiveShiftPoleGammaDensity eta x

theorem criticalFeatureCompactLatticeBoundaryObservable_eq_poleGamma
    (K : Finset ℤ) (cutoff : ℕ) {eta : ℝ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2) :
    criticalFeatureCompactLatticeBoundaryObservable K cutoff eta =
      criticalFeatureCompactLatticePoleGammaObservable K cutoff eta := by
  rw [criticalFeatureCompactLatticeBoundaryObservable,
    criticalFeatureCompactLatticePoleGammaObservable]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards
    [ae_boundaryDensity_XiC_eq_positiveShiftPoleGammaDensity heta0 hetaHalf]
    with x hx
  rw [hx]
  intro _hx
  rfl

theorem tendsto_criticalFeatureCompactLatticeBoundaryObservable
    (K : Finset ℤ) (cutoff : ℕ) :
    Tendsto (criticalFeatureCompactLatticeBoundaryObservable K cutoff)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k ∈ K, criticalLineCriticalFeatureCutoffTrace (k : ℝ) cutoff)) := by
  have hr : 0 ≤ (cutoff : ℝ) + 3 := by positivity
  have hrR : (cutoff : ℝ) + 3 < (cutoff : ℝ) + 4 := by linarith
  obtain ⟨Gamma, hGamma, hlim⟩ :=
    XiRealBoundary.tendsto_xiBoundaryDensity_setIntegral
      (c := 0) (r := (cutoff : ℝ) + 3) (R := (cutoff : ℝ) + 4)
      hr hrR (continuous_criticalFeatureLatticeBoundaryCutoffWeight K cutoff)
      (fun x hx => by
        apply criticalFeatureLatticeBoundaryCutoffWeight_eq_zero_of_not_mem K cutoff
        simpa only [zero_sub, zero_add] using hx)
  have hterm (k : ℤ) :
      criticalLineCriticalFeatureCutoffTrace (k : ℝ) cutoff =
        ∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            criticalFeatureBoundaryCutoffWeight (k : ℝ) cutoff gamma := by
    obtain ⟨Gamma', hGamma', hsum⟩ :=
      exists_criticalFeatureCompactSourceBoundaryLimit_eq_realZeroSum
        (k : ℝ) cutoff
    have hGG : Gamma' = Gamma := by
      ext gamma
      rw [hGamma', hGamma]
      simp
    rw [← criticalFeatureCompactSourceBoundaryLimit_eq_cutoffTrace,
      hsum, hGG]
  have htarget :
      (∑ gamma ∈ Gamma,
        ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
          criticalFeatureLatticeBoundaryCutoffWeight K cutoff gamma) =
        ∑ k ∈ K, criticalLineCriticalFeatureCutoffTrace (k : ℝ) cutoff := by
    simp only [criticalFeatureLatticeBoundaryCutoffWeight, Finset.mul_sum]
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
        criticalFeatureLatticeBoundaryCutoffWeight K cutoff x *
          boundaryDensity XiC eta x)
    (𝓝[>] (0 : ℝ))
    (𝓝 (∑ gamma ∈ Gamma,
      ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
        criticalFeatureLatticeBoundaryCutoffWeight K cutoff gamma))
  exact hlim

theorem tendsto_criticalFeatureCompactLatticePoleGammaObservable
    (K : Finset ℤ) (cutoff : ℕ) :
    Tendsto (criticalFeatureCompactLatticePoleGammaObservable K cutoff)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k ∈ K, criticalLineCriticalFeatureCutoffTrace (k : ℝ) cutoff)) := by
  have hsource := tendsto_criticalFeatureCompactLatticeBoundaryObservable K cutoff
  apply hsource.congr'
  have hhalf : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hhalf] with eta heta0 hetaHalf
  exact criticalFeatureCompactLatticeBoundaryObservable_eq_poleGamma
    K cutoff heta0 hetaHalf

/-- One lattice-summed source covariance: feature aggregation occurs inside a single boundary
integral, before scalarization. -/
def criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance
    (K : Finset ℤ) (cutoff : ℕ) (eta : ℝ) : ℝ :=
  criticalFeaturePoleGammaLatticeBudget K -
    criticalFeatureCompactLatticePoleGammaObservable K cutoff eta

theorem tendsto_criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance
    (K : Finset ℤ) (cutoff : ℕ) :
    Tendsto
      (criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance K cutoff)
      (𝓝[>] (0 : ℝ))
      (𝓝 (criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff)) := by
  have h : Tendsto
      (fun eta : ℝ => criticalFeaturePoleGammaLatticeBudget K -
        criticalFeatureCompactLatticePoleGammaObservable K cutoff eta)
      (𝓝[>] (0 : ℝ))
      (𝓝 (criticalFeaturePoleGammaLatticeBudget K -
        (∑ k ∈ K, criticalLineCriticalFeatureCutoffTrace (k : ℝ) cutoff))) :=
    tendsto_const_nhds.sub
      (tendsto_criticalFeatureCompactLatticePoleGammaObservable K cutoff)
  have htarget :
      criticalFeaturePoleGammaLatticeBudget K -
          (∑ k ∈ K, criticalLineCriticalFeatureCutoffTrace (k : ℝ) cutoff) =
        criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff := by
    rw [criticalFeaturePoleGammaPlemeljCovarianceAtCutoff]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact (tendsto_criticalFeatureCompactPoleGammaObservable
      (k : ℝ) cutoff).limUnder_eq.symm
  rw [← htarget]
  change Tendsto
    (fun eta : ℝ => criticalFeaturePoleGammaLatticeBudget K -
      criticalFeatureCompactLatticePoleGammaObservable K cutoff eta)
    (𝓝[>] (0 : ℝ))
    (𝓝 (criticalFeaturePoleGammaLatticeBudget K -
      (∑ k ∈ K, criticalLineCriticalFeatureCutoffTrace (k : ℝ) cutoff)))
  exact h

private theorem eventually_abs_sub_lt_of_tendsto_latticeSummed
    {α : Type*} {l : Filter α} {f : α → ℝ} {a eps : ℝ}
    (h : Tendsto f l (𝓝 a)) (heps : 0 < eps) :
    ∀ᶠ x in l, |f x - a| < eps := by
  have hlo : ∀ᶠ x in l, a - eps < f x :=
    (tendsto_order.1 h).1 _ (by linarith)
  have hhi : ∀ᶠ x in l, f x < a + eps :=
    (tendsto_order.1 h).2 _ (by linarith)
  filter_upwards [hlo, hhi] with x hxlo hxhi
  rw [abs_lt]
  constructor <;> linarith

/-- Source-selected simultaneous compact cutoff and positive displacement for the genuinely
lattice-summed observable. -/
structure CriticalFeatureCanonicalLatticeSummedDisplacementData (n : ℕ) where
  cutoff : ℕ
  cutoff_ge : n ≤ cutoff
  displacement : ℝ
  displacement_pos : 0 < displacement
  displacement_lt_half : displacement < 1 / 2
  displacement_lt_reciprocal : displacement < 1 / ((n : ℝ) + 1)
  error_lt :
    |criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance
          (criticalFeatureCanonicalLatticeWindow n) cutoff displacement -
        criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1)

theorem exists_criticalFeatureCanonicalLatticeSummedDisplacementData (n : ℕ) :
    Nonempty (CriticalFeatureCanonicalLatticeSummedDisplacementData n) := by
  let K := criticalFeatureCanonicalLatticeWindow n
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have heps : 0 < eps := by positivity
  have houter : Tendsto
      (criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K) atTop
      (𝓝 (criticalFeaturePoleGammaPlemeljCovariance K)) := by
    convert tendsto_criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K using 1
    rw [criticalFeaturePrimeGammaOffLineLatticeBudget_eq_plemeljCovariance_add_vm]
    ring_nf
  have houterNear : ∀ᶠ cutoff : ℕ in atTop,
      |criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff -
        criticalFeaturePoleGammaPlemeljCovariance K| < eps / 2 :=
    eventually_abs_sub_lt_of_tendsto_latticeSummed houter (half_pos heps)
  obtain ⟨cutoff, hcutoff, hcutoffGe⟩ :=
    (houterNear.and (eventually_ge_atTop n)).exists
  have hinner :=
    tendsto_criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance K cutoff
  have hinnerNear : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ),
      |criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance K cutoff eta -
        criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff| < eps / 2 :=
    eventually_abs_sub_lt_of_tendsto_latticeSummed hinner (half_pos heps)
  have hpos : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), 0 < eta := self_mem_nhdsWithin
  have hhalf : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  have hepsNear : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta < eps :=
    (eventually_lt_nhds heps).filter_mono inf_le_left
  obtain ⟨eta, hetaPos, hetaHalf, hetaEps, hetaNear⟩ :=
    (hpos.and (hhalf.and (hepsNear.and hinnerNear))).exists
  refine ⟨{
    cutoff := cutoff
    cutoff_ge := hcutoffGe
    displacement := eta
    displacement_pos := hetaPos
    displacement_lt_half := hetaHalf
    displacement_lt_reciprocal := ?_
    error_lt := ?_ }⟩
  · simpa [eps] using hetaEps
  · have htriangle :
        |criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance K cutoff eta -
            criticalFeaturePoleGammaPlemeljCovariance K| ≤
          |criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance K cutoff eta -
              criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff| +
            |criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff -
              criticalFeaturePoleGammaPlemeljCovariance K| := by
        rw [show
          criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance K cutoff eta -
                criticalFeaturePoleGammaPlemeljCovariance K =
              (criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance K cutoff eta -
                criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff) +
              (criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff -
                criticalFeaturePoleGammaPlemeljCovariance K) by ring]
        exact abs_add_le _ _
    change
      |criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance K cutoff eta -
          criticalFeaturePoleGammaPlemeljCovariance K| < eps
    exact htriangle.trans_lt (by linarith)

def criticalFeatureCanonicalLatticeSummedDisplacementData (n : ℕ) :
    CriticalFeatureCanonicalLatticeSummedDisplacementData n :=
  Classical.choice (exists_criticalFeatureCanonicalLatticeSummedDisplacementData n)

/-- Canonical finite source covariance with the entire feature lattice fused before the sole
Lebesgue scalarization. -/
def criticalFeatureCanonicalLatticeSummedDisplacementCovariance (n : ℕ) : ℝ :=
  criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance
    (criticalFeatureCanonicalLatticeWindow n)
    (criticalFeatureCanonicalLatticeSummedDisplacementData n).cutoff
    (criticalFeatureCanonicalLatticeSummedDisplacementData n).displacement

theorem criticalFeatureCanonicalLatticeSummedDisplacement_pos_lt (n : ℕ) :
    0 < (criticalFeatureCanonicalLatticeSummedDisplacementData n).displacement ∧
      (criticalFeatureCanonicalLatticeSummedDisplacementData n).displacement < 1 / 2 ∧
      (criticalFeatureCanonicalLatticeSummedDisplacementData n).displacement <
        1 / ((n : ℝ) + 1) :=
  ⟨(criticalFeatureCanonicalLatticeSummedDisplacementData n).displacement_pos,
    (criticalFeatureCanonicalLatticeSummedDisplacementData n).displacement_lt_half,
    (criticalFeatureCanonicalLatticeSummedDisplacementData n).displacement_lt_reciprocal⟩

theorem tendsto_criticalFeatureCanonicalLatticeSummedDisplacement_cutoff :
    Tendsto
      (fun n : ℕ => (criticalFeatureCanonicalLatticeSummedDisplacementData n).cutoff)
      atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun n =>
      (criticalFeatureCanonicalLatticeSummedDisplacementData n).cutoff_ge)
    tendsto_id

theorem tendsto_criticalFeatureCanonicalLatticeSummedDisplacement_displacement :
    Tendsto
      (fun n : ℕ => (criticalFeatureCanonicalLatticeSummedDisplacementData n).displacement)
      atTop (𝓝 0) := by
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      (criticalFeatureCanonicalLatticeSummedDisplacementData n).displacement_pos.le)
    (Filter.Eventually.of_forall fun n =>
      (criticalFeatureCanonicalLatticeSummedDisplacementData n).displacement_lt_reciprocal.le)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem criticalFeatureCanonicalLatticeSummedDisplacementCovariance_error_lt (n : ℕ) :
    |criticalFeatureCanonicalLatticeSummedDisplacementCovariance n -
        criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1) :=
  (criticalFeatureCanonicalLatticeSummedDisplacementData n).error_lt

theorem tendsto_canonicalLatticeSummedDisplacement_sub_plemeljCovariance_div :
    Tendsto
      (fun n : ℕ =>
        (criticalFeatureCanonicalLatticeSummedDisplacementCovariance n -
            criticalFeaturePoleGammaPlemeljCovariance
              (criticalFeatureCanonicalLatticeWindow n)) /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun n => norm_nonneg _)
    ?_ tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_criticalFeatureCanonicalZeroCount_pos] with n hN
  have hN_one : 1 ≤ criticalFeatureCanonicalZeroCount n := by
    dsimp [criticalFeatureCanonicalZeroCount] at hN ⊢
    have hN_int : (0 : ℤ) < xiZeroCount (n : ℝ) := by exact_mod_cast hN
    have hN_int_one : (1 : ℤ) ≤ xiZeroCount (n : ℝ) := by omega
    exact_mod_cast hN_int_one
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hN]
  calc
    |criticalFeatureCanonicalLatticeSummedDisplacementCovariance n -
          criticalFeaturePoleGammaPlemeljCovariance
            (criticalFeatureCanonicalLatticeWindow n)| /
          criticalFeatureCanonicalZeroCount n
        ≤ (1 / ((n : ℝ) + 1)) /
            criticalFeatureCanonicalZeroCount n :=
      div_le_div_of_nonneg_right
        (criticalFeatureCanonicalLatticeSummedDisplacementCovariance_error_lt n).le hN.le
    _ ≤ 1 / ((n : ℝ) + 1) := div_le_self (by positivity) hN_one

theorem canonicalLatticeSummedDisplacement_ceiling_iff_plemeljCovariance_ceiling
    (c : ℝ) :
    CriticalFeatureCanonicalAsymptoticUpper
        criticalFeatureCanonicalLatticeSummedDisplacementCovariance c ↔
      CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n)) c := by
  have hdiff := tendsto_canonicalLatticeSummedDisplacement_sub_plemeljCovariance_div
  have htransfer (X Y : ℕ → ℝ)
      (hXY : Tendsto
        (fun n => (X n - Y n) / criticalFeatureCanonicalZeroCount n)
        atTop (𝓝 0))
      (hY : CriticalFeatureCanonicalAsymptoticUpper Y c) :
      CriticalFeatureCanonicalAsymptoticUpper X c := by
    intro eps heps
    have hY' := hY (eps / 2) (by linarith)
    have herr : ∀ᶠ n : ℕ in atTop,
        (X n - Y n) / criticalFeatureCanonicalZeroCount n < eps / 2 :=
      (tendsto_order.1 hXY).2 _ (by linarith)
    filter_upwards [hY', herr, eventually_criticalFeatureCanonicalZeroCount_pos]
      with n hYn heren hN
    have hdiffn : X n - Y n <
        (eps / 2) * criticalFeatureCanonicalZeroCount n :=
      (div_lt_iff₀ hN).mp heren
    nlinarith
  constructor
  · intro hfused
    apply htransfer _ _ ?_ hfused
    have hneg := hdiff.neg
    simp only [neg_zero] at hneg
    convert hneg using 1
    funext n
    ring
  · exact htransfer _ _ hdiff

theorem canonical_correctedBudget_ceiling_iff_latticeSummedDisplacement_ceiling_reflectedDirectThreeCenter :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n))
        (15872 / 21125) ↔
      CriticalFeatureCanonicalAsymptoticUpper
        criticalFeatureCanonicalLatticeSummedDisplacementCovariance
        (15872 / 21125) :=
  canonical_correctedBudget_ceiling_iff_plemeljCovariance_ceiling_reflectedDirectThreeCenter.trans
    (canonicalLatticeSummedDisplacement_ceiling_iff_plemeljCovariance_ceiling
      (15872 / 21125)).symm

end

end RHTower
