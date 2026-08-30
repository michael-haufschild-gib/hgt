import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureFiniteWindowAliasDecomposition
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureReflectedPairDirectThreeCenterCharge
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorAdmissibleContour

/-!
# Regular canonical finite-window HCF source decomposition

The canonical finite-displacement selector can be refined to avoid every Xi zero on its compact
horizontal segment.  Zero-free displacements are frequent at the critical boundary: a compact
rectangle contains only finitely many zeros, so every positive displacement interval contains an
admissible horizontal slice.  Intersecting this frequent set with the eventual Plemelj
approximation gives one positive submicroscopic, zero-free displacement at every height.

Consequently the finite-window alias decomposition applies to a canonical covariance with no
integrability premise left.  The observable still contains only finite pole--Gamma source
evaluations; the nonvanishing certificate is used to justify ordinary compact Lebesgue
integrability, not to insert a divisor trace.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Zero-free positive displacement lines through the canonical core occur frequently as the
displacement tends to zero from above. -/
theorem frequently_criticalFeatureCanonicalCore_zeroFree_displacement (n : ℕ) :
    ∃ᶠ eta : ℝ in 𝓝[>] (0 : ℝ),
      ∀ x ∈ criticalFeatureCanonicalCore n,
        XiC ((x : ℂ) + (eta : ℂ) * I) ≠ 0 := by
  rw [frequently_iff]
  intro s hs
  obtain ⟨eps, heps, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hs
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcore : -((n : ℝ) + 1) < (n : ℝ) + 1 := by linarith
  obtain ⟨eta, heta, _eta₂, _heta₂, hzero, _hzero₂⟩ :=
    exists_horizontal_slices_avoiding_entire_zeros
      (f := XiC) XiC_analytic ⟨0, XiC_zero_ne⟩ hcore
      (show eps / 5 < 2 * eps / 5 by linarith)
      (show 2 * eps / 5 < 3 * eps / 5 by linarith)
      (show 3 * eps / 5 < 4 * eps / 5 by linarith)
  have heta0 : 0 < eta := by linarith [heta.1]
  have hetaeps : eta < eps := by linarith [heta.2]
  refine ⟨eta, hsub ?_, ?_⟩
  · constructor
    · rw [Metric.mem_ball, Real.dist_eq]
      simpa [abs_of_pos heta0] using hetaeps
    · exact heta0
  · intro x hx
    apply hzero x
    simpa only [criticalFeatureCanonicalCore, uIcc_of_le hcore.le] using hx

private theorem eventually_abs_sub_lt_of_tendsto_regular
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

/-- Canonical finite source data with a zero-free compact displacement line. -/
structure CriticalFeatureCanonicalRegularLatticeSummedDisplacementData (n : ℕ) where
  cutoff : ℕ
  cutoff_ge : n ≤ cutoff
  displacement : ℝ
  displacement_pos : 0 < displacement
  displacement_lt_half : displacement < 1 / 2
  displacement_lt_reciprocal : displacement < 1 / ((n : ℝ) + 1)
  zeroFreeCore :
    ∀ x ∈ criticalFeatureCanonicalCore n,
      XiC ((x : ℂ) + (displacement : ℂ) * I) ≠ 0
  error_lt :
    |criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance
          (criticalFeatureCanonicalLatticeWindow n) cutoff displacement -
        criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1)

/-- At every height, one can select a regular, positive, submicroscopic source displacement while
retaining the canonical `1/(n+1)` approximation to the Plemelj covariance. -/
theorem exists_criticalFeatureCanonicalRegularLatticeSummedDisplacementData (n : ℕ) :
    Nonempty (CriticalFeatureCanonicalRegularLatticeSummedDisplacementData n) := by
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
    eventually_abs_sub_lt_of_tendsto_regular houter (half_pos heps)
  obtain ⟨cutoff, hcutoff, hcutoffGe⟩ :=
    (houterNear.and (eventually_ge_atTop n)).exists
  have hinner :=
    tendsto_criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance K cutoff
  have hinnerNear : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ),
      |criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance K cutoff eta -
        criticalFeaturePoleGammaPlemeljCovarianceAtCutoff K cutoff| < eps / 2 :=
    eventually_abs_sub_lt_of_tendsto_regular hinner (half_pos heps)
  have hpos : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), 0 < eta :=
    self_mem_nhdsWithin
  have hhalf : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  have hepsNear : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), eta < eps :=
    (eventually_lt_nhds heps).filter_mono inf_le_left
  have hregular :=
    (frequently_criticalFeatureCanonicalCore_zeroFree_displacement n).and_eventually
      (hpos.and (hhalf.and (hepsNear.and hinnerNear)))
  obtain ⟨eta, hzero, hetaPos, hetaHalf, hetaEps, hetaNear⟩ := hregular.exists
  refine ⟨{
    cutoff := cutoff
    cutoff_ge := hcutoffGe
    displacement := eta
    displacement_pos := hetaPos
    displacement_lt_half := hetaHalf
    displacement_lt_reciprocal := ?_
    zeroFreeCore := hzero
    error_lt := ?_ }⟩
  · simpa only [eps] using hetaEps
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

/-- Chosen regular finite-window source data. -/
def criticalFeatureCanonicalRegularLatticeSummedDisplacementData (n : ℕ) :
    CriticalFeatureCanonicalRegularLatticeSummedDisplacementData n :=
  Classical.choice
    (exists_criticalFeatureCanonicalRegularLatticeSummedDisplacementData n)

/-- Canonical regular finite source covariance. -/
def criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance (n : ℕ) : ℝ :=
  criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance
    (criticalFeatureCanonicalLatticeWindow n)
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement

theorem criticalFeatureCanonicalRegularLatticeSummedDisplacement_pos_lt (n : ℕ) :
    0 < (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement ∧
      (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement < 1 / 2 ∧
      (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement <
        1 / ((n : ℝ) + 1) :=
  ⟨(criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement_pos,
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement_lt_half,
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement_lt_reciprocal⟩

theorem criticalFeatureCanonicalRegularLatticeSummedDisplacement_zeroFreeCore (n : ℕ) :
    ∀ x ∈ criticalFeatureCanonicalCore n,
      XiC ((x : ℂ) +
        ((criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement : ℂ) * I) ≠
          0 :=
  (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).zeroFreeCore

theorem integrableOn_criticalFeatureCanonicalRegularPoleGammaDensity (n : ℕ) :
    IntegrableOn
      (criticalFeaturePositiveShiftPoleGammaDensity
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement)
      (criticalFeatureCanonicalCore n) := by
  have hpos := criticalFeatureCanonicalRegularLatticeSummedDisplacement_pos_lt n
  apply integrableOn_criticalFeaturePositiveShiftPoleGammaDensity_of_noZero
    hpos.1 hpos.2.1
  exact criticalFeatureCanonicalRegularLatticeSummedDisplacement_zeroFreeCore n

theorem criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance_error_lt (n : ℕ) :
    |criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance n -
        criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n)| <
      1 / ((n : ℝ) + 1) :=
  (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).error_lt

/-- The regular finite-window covariance still differs from the source Plemelj covariance by
`o(N)` on the canonical height scale. -/
theorem tendsto_canonicalRegularLatticeSummedDisplacement_sub_plemeljCovariance_div :
    Tendsto
      (fun n : ℕ =>
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance n -
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
    |criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance n -
          criticalFeaturePoleGammaPlemeljCovariance
            (criticalFeatureCanonicalLatticeWindow n)| /
          criticalFeatureCanonicalZeroCount n
        ≤ (1 / ((n : ℝ) + 1)) /
            criticalFeatureCanonicalZeroCount n :=
      div_le_div_of_nonneg_right
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance_error_lt n).le hN.le
    _ ≤ 1 / ((n : ℝ) + 1) := div_le_self (by positivity) hN_one

/-- Unconditional source-piece estimate for the canonical regular covariance. -/
theorem criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance_le_sourcePieces
    (n : ℕ) :
    criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance n ≤
      (criticalFeaturePoleGammaLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n) -
        criticalFeatureCanonicalCorePoleGammaZeroMode n
          (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement) +
      (37 : ℝ) / 200 *
        (∫ x in criticalFeatureCanonicalCore n,
          |criticalFeaturePositiveShiftPoleGammaDensity
            (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement x|) +
      |criticalFeatureCanonicalInteriorOmittedAlias n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement| +
      |criticalFeatureCanonicalExteriorPoleGammaTail n
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement| := by
  exact criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance_le_sourcePieces
    n
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement
    (integrableOn_criticalFeatureCanonicalRegularPoleGammaDensity n)

/-- Explicit finite pole--Gamma source majorant selected at canonical height `n`.  Its four terms
are respectively zero-mode mismatch, sharp nonzero Poisson aliases, interior omitted aliases, and
the compact-cutoff exterior tail. -/
def criticalFeatureCanonicalRegularSourcePieceMajorant (n : ℕ) : ℝ :=
  (criticalFeaturePoleGammaLatticeBudget
      (criticalFeatureCanonicalLatticeWindow n) -
    criticalFeatureCanonicalCorePoleGammaZeroMode n
      (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement) +
  (37 : ℝ) / 200 *
    (∫ x in criticalFeatureCanonicalCore n,
      |criticalFeaturePositiveShiftPoleGammaDensity
        (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement x|) +
  |criticalFeatureCanonicalInteriorOmittedAlias n
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement| +
  |criticalFeatureCanonicalExteriorPoleGammaTail n
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).cutoff
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementData n).displacement|

theorem criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance_le_sourcePieceMajorant
    (n : ℕ) :
    criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance n ≤
      criticalFeatureCanonicalRegularSourcePieceMajorant n := by
  simpa only [criticalFeatureCanonicalRegularSourcePieceMajorant] using
    criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance_le_sourcePieces n

/-- Replacing the Plemelj limit by the selected regular finite-window source covariance preserves
every canonical asymptotic ceiling. -/
theorem canonicalRegularLatticeSummedDisplacement_ceiling_iff_plemeljCovariance_ceiling
    (c : ℝ) :
    CriticalFeatureCanonicalAsymptoticUpper
        criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance c ↔
      CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n)) c := by
  have hdiff :=
    tendsto_canonicalRegularLatticeSummedDisplacement_sub_plemeljCovariance_div
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
  · intro hregular
    apply htransfer _ _ ?_ hregular
    have hneg := hdiff.neg
    simp only [neg_zero] at hneg
    convert hneg using 1
    funext n
    ring
  · exact htransfer _ _ hdiff

/-- Any asymptotic ceiling for the explicit source-piece majorant transfers to the selected regular
finite covariance with no constant loss. -/
theorem canonicalRegularLatticeSummedDisplacement_ceiling_of_sourcePieceMajorant
    {c : ℝ}
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularSourcePieceMajorant c) :
    CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance c := by
  intro eps heps
  filter_upwards [hsource eps heps] with n hn
  exact
    (criticalFeatureCanonicalRegularLatticeSummedDisplacementCovariance_le_sourcePieceMajorant n).trans
      hn

/-- Strongest current source-to-75%-receiver connector: it is enough to prove the explicit regular
finite source-piece majorant has canonical ceiling `15872/21125`. -/
theorem canonical_correctedBudget_ceiling_of_regularSourcePieceMajorant_reflectedDirectThreeCenter
    (hsource : CriticalFeatureCanonicalAsymptoticUpper
      criticalFeatureCanonicalRegularSourcePieceMajorant (15872 / 21125)) :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n))
        (15872 / 21125) := by
  apply
    canonical_correctedBudget_ceiling_iff_plemeljCovariance_ceiling_reflectedDirectThreeCenter.mpr
  exact
    (canonicalRegularLatticeSummedDisplacement_ceiling_iff_plemeljCovariance_ceiling
      (15872 / 21125)).mp
      (canonicalRegularLatticeSummedDisplacement_ceiling_of_sourcePieceMajorant hsource)

end

end RHTower
