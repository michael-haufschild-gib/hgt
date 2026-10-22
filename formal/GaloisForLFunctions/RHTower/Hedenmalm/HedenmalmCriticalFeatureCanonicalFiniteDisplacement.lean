import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureReflectedPairDirectThreeCenterCharge

/-!
# Canonical finite-displacement source gate for HCF

The source-only Plemelj covariance is defined by a positive-shift boundary limit followed by
compact-cutoff exhaustion.  This module collapses both limits, on every canonical height window,
to one compact pole--Gamma--von-Mangoldt evaluation at a source-selected positive displacement.
The displacement is submicroscopic (`< 1 / (n + 1)`), and the finite evaluation differs from the
infinite Plemelj covariance by `< 1 / (n + 1)`.

No zero or divisor occurs in the finite observable or in the selection predicate.  The theorem
does not assert the remaining quantitative arithmetic ceiling.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Finite, literal pole--Gamma covariance at one compact cutoff and positive displacement. -/
def criticalFeatureFiniteDisplacementPoleGammaCovariance
    (K : Finset ℤ) (cutoff : ℕ) (eta : ℝ) : ℝ :=
  criticalFeaturePoleGammaLatticeBudget K -
    ∑ k ∈ K,
      criticalFeatureCompactPoleGammaObservable (k : ℝ) cutoff eta

/-- At fixed lattice and cutoff, positive finite displacements converge to the compact Plemelj
covariance. -/
theorem tendsto_criticalFeatureFiniteDisplacementPoleGammaCovariance
    (K : Finset ℤ) (cutoff : ℕ) :
    Tendsto
      (criticalFeatureFiniteDisplacementPoleGammaCovariance K cutoff)
      (𝓝[>] (0 : ℝ))
      (𝓝 (criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff)) := by
  have hterm (k : ℤ) : Tendsto
      (criticalFeatureCompactPoleGammaObservable (k : ℝ) cutoff)
      (𝓝[>] (0 : ℝ))
      (𝓝 (limUnder (𝓝[>] (0 : ℝ))
        (criticalFeatureCompactPoleGammaObservable (k : ℝ) cutoff))) := by
    have h := tendsto_criticalFeatureCompactPoleGammaObservable (k : ℝ) cutoff
    simpa only [h.limUnder_eq] using h
  have hsum := tendsto_finsetSum K (fun k _hk => hterm k)
  exact tendsto_const_nhds.sub hsum

private theorem eventually_abs_sub_lt_of_tendsto
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

/-- Source-only data selecting one compact cutoff and one positive displacement at height `n`. -/
structure CriticalFeatureCanonicalFiniteDisplacementData (n : ℕ) where
  cutoff : ℕ
  cutoff_ge : n ≤ cutoff
  displacement : ℝ
  displacement_pos : 0 < displacement
  displacement_lt_half : displacement < 1 / 2
  displacement_lt_reciprocal : displacement < 1 / ((n : ℝ) + 1)
  error_lt :
    |criticalFeatureFiniteDisplacementPoleGammaCovariance
          (criticalFeatureCanonicalLatticeWindow n) cutoff displacement -
        criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1)

/-- Every canonical HCF window admits one source-only, submicroscopic finite-displacement
realization of its infinite Plemelj covariance. -/
theorem exists_criticalFeatureCanonicalFiniteDisplacementData (n : ℕ) :
    Nonempty (CriticalFeatureCanonicalFiniteDisplacementData n) := by
  let K := criticalFeatureCanonicalLatticeWindow n
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have heps : 0 < eps := by positivity
  have houter : Tendsto
      (criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K) atTop
      (𝓝 (criticalFeaturePoleGammaPlemeljCovariance K)) :=
    by
      convert tendsto_criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K using 1
      rw [criticalFeaturePrimeGammaOffLineLatticeBudget_eq_plemeljCovariance_add_vm]
      ring_nf
  have houterNear : ∀ᶠ cutoff : ℕ in atTop,
      |criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff -
        criticalFeaturePoleGammaPlemeljCovariance K| < eps / 2 :=
    eventually_abs_sub_lt_of_tendsto houter (half_pos heps)
  obtain ⟨cutoff, hcutoff, hcutoffGe⟩ :=
    (houterNear.and (eventually_ge_atTop n)).exists
  have hinner :=
    tendsto_criticalFeatureFiniteDisplacementPoleGammaCovariance K cutoff
  have hinnerNear : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ),
      |criticalFeatureFiniteDisplacementPoleGammaCovariance K cutoff eta -
        criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff| < eps / 2 :=
    eventually_abs_sub_lt_of_tendsto hinner (half_pos heps)
  have hpos : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), 0 < eta :=
    self_mem_nhdsWithin
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
        |criticalFeatureFiniteDisplacementPoleGammaCovariance K cutoff eta -
            criticalFeaturePoleGammaPlemeljCovariance K| ≤
          |criticalFeatureFiniteDisplacementPoleGammaCovariance K cutoff eta -
              criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff| +
            |criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff -
              criticalFeaturePoleGammaPlemeljCovariance K| := by
        rw [show
          criticalFeatureFiniteDisplacementPoleGammaCovariance K cutoff eta -
                criticalFeaturePoleGammaPlemeljCovariance K =
              (criticalFeatureFiniteDisplacementPoleGammaCovariance K cutoff eta -
                criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff) +
              (criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff -
                criticalFeaturePoleGammaPlemeljCovariance K) by ring]
        exact abs_add_le _ _
    change
      |criticalFeatureFiniteDisplacementPoleGammaCovariance K cutoff eta -
          criticalFeaturePoleGammaPlemeljCovariance K| < eps
    exact htriangle.trans_lt (by linarith)

/-- Canonical source-selected cutoff/displacement pair. -/
def criticalFeatureCanonicalFiniteDisplacementData (n : ℕ) :
    CriticalFeatureCanonicalFiniteDisplacementData n :=
  Classical.choice (exists_criticalFeatureCanonicalFiniteDisplacementData n)

/-- Single-scale, finite, zero-independent canonical HCF source covariance. -/
def criticalFeatureCanonicalFiniteDisplacementCovariance (n : ℕ) : ℝ :=
  criticalFeatureFiniteDisplacementPoleGammaCovariance
    (criticalFeatureCanonicalLatticeWindow n)
    (criticalFeatureCanonicalFiniteDisplacementData n).cutoff
    (criticalFeatureCanonicalFiniteDisplacementData n).displacement

/-- The selected displacement is positive and submicroscopic. -/
theorem criticalFeatureCanonicalFiniteDisplacement_pos_lt (n : ℕ) :
    0 < (criticalFeatureCanonicalFiniteDisplacementData n).displacement ∧
      (criticalFeatureCanonicalFiniteDisplacementData n).displacement < 1 / 2 ∧
      (criticalFeatureCanonicalFiniteDisplacementData n).displacement <
        1 / ((n : ℝ) + 1) :=
  ⟨(criticalFeatureCanonicalFiniteDisplacementData n).displacement_pos,
    (criticalFeatureCanonicalFiniteDisplacementData n).displacement_lt_half,
    (criticalFeatureCanonicalFiniteDisplacementData n).displacement_lt_reciprocal⟩

/-- Selected compact cutoffs exhaust the height axis. -/
theorem tendsto_criticalFeatureCanonicalFiniteDisplacement_cutoff :
    Tendsto
      (fun n : ℕ => (criticalFeatureCanonicalFiniteDisplacementData n).cutoff)
      atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun n =>
      (criticalFeatureCanonicalFiniteDisplacementData n).cutoff_ge)
    tendsto_id

/-- Selected positive real displacements shrink to the critical boundary. -/
theorem tendsto_criticalFeatureCanonicalFiniteDisplacement_displacement :
    Tendsto
      (fun n : ℕ => (criticalFeatureCanonicalFiniteDisplacementData n).displacement)
      atTop (𝓝 0) := by
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      (criticalFeatureCanonicalFiniteDisplacementData n).displacement_pos.le)
    (Filter.Eventually.of_forall fun n =>
      (criticalFeatureCanonicalFiniteDisplacementData n).displacement_lt_reciprocal.le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Uniform vanishing error between the single-scale source covariance and infinite Plemelj
covariance. -/
theorem criticalFeatureCanonicalFiniteDisplacementCovariance_error_lt (n : ℕ) :
    |criticalFeatureCanonicalFiniteDisplacementCovariance n -
        criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1) :=
  (criticalFeatureCanonicalFiniteDisplacementData n).error_lt

/-- The finite-displacement replacement differs from infinite Plemelj covariance by `o(N)`. -/
theorem tendsto_canonicalFiniteDisplacement_sub_plemeljCovariance_div :
    Tendsto
      (fun n : ℕ =>
        (criticalFeatureCanonicalFiniteDisplacementCovariance n -
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
    |criticalFeatureCanonicalFiniteDisplacementCovariance n -
          criticalFeaturePoleGammaPlemeljCovariance
            (criticalFeatureCanonicalLatticeWindow n)| /
          criticalFeatureCanonicalZeroCount n
        ≤ (1 / ((n : ℝ) + 1)) /
            criticalFeatureCanonicalZeroCount n :=
      div_le_div_of_nonneg_right
        (criticalFeatureCanonicalFiniteDisplacementCovariance_error_lt n).le hN.le
    _ ≤ 1 / ((n : ℝ) + 1) := div_le_self (by positivity) hN_one

/-- Every canonical asymptotic ceiling is unchanged when the infinite Plemelj covariance is
replaced by the selected finite-displacement source covariance. -/
theorem canonicalFiniteDisplacement_ceiling_iff_plemeljCovariance_ceiling (c : ℝ) :
    CriticalFeatureCanonicalAsymptoticUpper
        criticalFeatureCanonicalFiniteDisplacementCovariance c ↔
      CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n)) c := by
  have hdiff := tendsto_canonicalFiniteDisplacement_sub_plemeljCovariance_div
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
  · intro hfinite
    apply htransfer _ _ ?_ hfinite
    have hneg := hdiff.neg
    simp only [neg_zero] at hneg
    convert hneg using 1
    funext n
    ring
  · exact htransfer _ _ hdiff

/-- Reflected direct-three-center 75% gate with no infinite trace or nested source limit in its
quantitative premise. -/
theorem canonical_correctedBudget_ceiling_iff_finiteDisplacement_ceiling_reflectedDirectThreeCenter :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n))
        (15872 / 21125) ↔
      CriticalFeatureCanonicalAsymptoticUpper
        criticalFeatureCanonicalFiniteDisplacementCovariance
        (15872 / 21125) :=
  canonical_correctedBudget_ceiling_iff_plemeljCovariance_ceiling_reflectedDirectThreeCenter.trans
    (canonicalFiniteDisplacement_ceiling_iff_plemeljCovariance_ceiling
      (15872 / 21125)).symm

end

end RHTower
