import GaloisForLFunctions.HTGeometry.FiniteMatrixSchurPositiveQuarticSpectralSplit
import GaloisForLFunctions.RHTower.HedenmalmThetaSchurQuarticAsymptoticZeroTransfer

/-!
# Theta Schur quartic spectral-decay equivalence

Positive quartic charge on the actual corrected finite theta stages tends uniformly to zero over
all Schur triangularizations if and only if RH holds.

The forward implication from RH does not label eigenvalues.  A uniform Hilbert--Schmidt ceiling
puts every Schur diagonal in one bounded window.  For fixed positive thresholds `δ, η`, inversion
maps the compact set of nodes satisfying `normSq ≥ δ` and `Im² ≥ η` to a compact set on which
normalized Xi is zero-free under RH.  Compact-open determinant convergence then excludes all such
nodes at sufficiently late stages.  The dimension-free finite spectral split converts this
transverse localization into uniform quartic-charge decay.  Conversely, uniform decay implies the
previously proved cofinal-smallness endpoint and hence RH.
-/

open Complex Filter Metric Set Topology Matrix
open scoped BigOperators Matrix

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmHilbertSchmidt

noncomputable section

/-- A locally uniformly convergent sequence is eventually zero-free on a compact set where its
continuous limit is zero-free.  Holomorphy is not needed. -/
theorem eventually_forall_ne_zero_on_compact_of_tendstoLocallyUniformly
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (hnz : ∀ z ∈ K, f z ≠ 0)
    (hconv : TendstoLocallyUniformly F f atTop) :
    ∀ᶠ k in atTop, ∀ z ∈ K, F k z ≠ 0 := by
  by_cases hKne : K.Nonempty
  · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne hf.norm
    have hminPos : 0 < ‖f z₀‖ := norm_pos_iff.mpr (hnz z₀ hz₀)
    have huniform : TendstoUniformlyOn F f atTop K :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
        hconv.tendstoLocallyUniformlyOn
    have hclose : ∀ᶠ k in atTop, ∀ z ∈ K,
        dist (F k z) (f z) < ‖f z₀‖ / 2 := by
      simpa only [dist_comm] using
        (Metric.tendstoUniformlyOn_iff.mp huniform) (‖f z₀‖ / 2)
          (half_pos hminPos)
    filter_upwards [hclose] with k hk
    intro z hz hzero
    have hminZ : ‖f z₀‖ ≤ ‖f z‖ := hmin hz
    have hdist : dist (F k z) (f z) = ‖f z‖ := by simp [hzero]
    have hkz := hk z hz
    rw [hdist] at hkz
    linarith
  · have hempty : K = ∅ := not_nonempty_iff_eq_empty.mp hKne
    filter_upwards [] with k
    simp [hempty]

/-- Compact window of bounded, non-small, transversely separated spectral nodes. -/
def thetaSchurBadSpectralWindow (R δ η : ℝ) : Set ℂ :=
  (closedBall (0 : ℂ) R ∩ {z | δ ≤ Complex.normSq z}) ∩
    {z | η ≤ z.im ^ 2}

theorem thetaSchurBadSpectralWindow_isCompact (R δ η : ℝ) :
    IsCompact (thetaSchurBadSpectralWindow R δ η) := by
  unfold thetaSchurBadSpectralWindow
  exact ((isCompact_closedBall (0 : ℂ) R).inter_right
    (isClosed_le continuous_const Complex.continuous_normSq)).inter_right
      (isClosed_le continuous_const (Complex.continuous_im.pow 2))

theorem continuousOn_inv_thetaSchurBadSpectralWindow
    {R δ η : ℝ} (hδ : 0 < δ) :
    ContinuousOn (fun z : ℂ => z⁻¹) (thetaSchurBadSpectralWindow R δ η) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    have hnorm : δ ≤ Complex.normSq z := hz.1.2
    exact Complex.normSq_pos.mp (hδ.trans_le hnorm)
  exact (continuousAt_id.inv₀ hz0).continuousWithinAt

theorem thetaSchurBadReciprocalWindow_isCompact
    (R δ η : ℝ) (hδ : 0 < δ) :
    IsCompact ((fun z : ℂ => z⁻¹) '' thetaSchurBadSpectralWindow R δ η) :=
  (thetaSchurBadSpectralWindow_isCompact R δ η).image_of_continuousOn
    (continuousOn_inv_thetaSchurBadSpectralWindow hδ)

theorem normalizedXi_ne_zero_on_thetaSchurBadReciprocalWindow
    (hRH : RiemannHypothesis) {R δ η : ℝ} (hη : 0 < η) :
    ∀ z ∈ (fun w : ℂ => w⁻¹) '' thetaSchurBadSpectralWindow R δ η,
      XiC z / XiC 0 ≠ 0 := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hwim : w.im ≠ 0 := by
    intro hwzero
    have htrans : η ≤ w.im ^ 2 := hw.2
    rw [hwzero] at htrans
    norm_num at htrans
    linarith
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    exact hwim (by simp)
  have hinvim : (w⁻¹).im ≠ 0 := by
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr hwim)
      (Complex.normSq_pos.mpr hw0).ne'
  apply div_ne_zero
  · intro hzero
    exact hinvim ((_root_.RHTower.riemannHypothesis_iff_XiC_zeros_real.mp hRH) _ hzero)
  · exact XiC_zero_ne

/-- Under RH, honest corrected theta determinants are eventually zero-free on reciprocals of every
bounded non-small spectral node separated from the real axis. -/
theorem eventually_thetaSourceSignedOrdinaryDet_ne_zero_on_badReciprocalWindow_of_rh
    (hRH : RiemannHypothesis) {R δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∀ᶠ k in atTop,
      ∀ z ∈ (fun w : ℂ => w⁻¹) '' thetaSchurBadSpectralWindow R δ η,
        thetaSourceSignedOrdinaryDet k z ≠ 0 := by
  apply eventually_forall_ne_zero_on_compact_of_tendstoLocallyUniformly
    (thetaSchurBadReciprocalWindow_isCompact R δ η hδ)
  · exact (XiC_analytic.continuous.div_const (XiC 0)).continuousOn
  · exact normalizedXi_ne_zero_on_thetaSchurBadReciprocalWindow hRH hη
  · exact thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC

/-- Uniform Hilbert--Schmidt norm ceiling for all actual corrected theta stages. -/
def thetaSourceSignedHSCeiling : ℝ :=
  1 + HilbertSchmidt.hsNorm (-thetaKernelMatrix)

theorem thetaSourceSignedHSCeiling_pos : 0 < thetaSourceSignedHSCeiling := by
  unfold thetaSourceSignedHSCeiling
  have := HilbertSchmidt.hsNorm_nonneg (-thetaKernelMatrix)
  linarith

theorem hsNorm_thetaSourceSignedKernel_le_ceiling (k : ℕ) :
    HilbertSchmidt.hsNorm (thetaSourceSignedKernel k) ≤ thetaSourceSignedHSCeiling := by
  have hdiffHS : HilbertSchmidt.IsHS
      (thetaSourceSignedKernel k - (-thetaKernelMatrix)) :=
    HilbertSchmidt.isHS_sub (isHS_thetaSourceSignedKernel k)
      isHS_neg_thetaKernelMatrix
  have hsum := HilbertSchmidt.hsNorm_add_le hdiffHS isHS_neg_thetaKernelMatrix
  have heq :
      thetaSourceSignedKernel k =
        (thetaSourceSignedKernel k - (-thetaKernelMatrix)) + (-thetaKernelMatrix) := by
    funext p
    simp
  have hfrac : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    norm_num
  calc
    HilbertSchmidt.hsNorm (thetaSourceSignedKernel k) =
        HilbertSchmidt.hsNorm ((thetaSourceSignedKernel k - (-thetaKernelMatrix)) +
          (-thetaKernelMatrix)) := congrArg HilbertSchmidt.hsNorm heq
    _ ≤ HilbertSchmidt.hsNorm (thetaSourceSignedKernel k - (-thetaKernelMatrix)) +
        HilbertSchmidt.hsNorm (-thetaKernelMatrix) := hsum
    _ ≤ 1 + HilbertSchmidt.hsNorm (-thetaKernelMatrix) := by
      have hdiff := (hsNorm_thetaSourceSignedKernel_sub_lt k).le.trans hfrac
      linarith
    _ = thetaSourceSignedHSCeiling := rfl

/-- Every actual finite theta-stage matrix has Hilbert--Schmidt energy below the fixed source
ceiling squared. -/
theorem matHSNormSq_thetaSourceSignedStageFinMatrix_le_ceiling (k : ℕ) :
    matHSNormSq (thetaSourceSignedStageFinMatrix k) ≤ thetaSourceSignedHSCeiling ^ 2 := by
  have hblock :
      matHSNormSq (thetaSourceSignedStageFinMatrix k) ≤
        HilbertSchmidt.hsNormSq (thetaSourceSignedKernel k) := by
    rw [thetaSourceSignedStageFinMatrix, blockFin, matHSNormSq_submatrix]
    exact HilbertSchmidt.matHSNormSq_blockMatrix_le (isHS_thetaSourceSignedKernel k)
      (thetaSourceSignedCutoff k)
  have hsq :
      HilbertSchmidt.hsNormSq (thetaSourceSignedKernel k) =
        HilbertSchmidt.hsNorm (thetaSourceSignedKernel k) ^ 2 := by
    rw [HilbertSchmidt.hsNorm,
      Real.sq_sqrt (HilbertSchmidt.hsNormSq_nonneg _)]
  rw [hsq] at hblock
  have hnorm := hsNorm_thetaSourceSignedKernel_le_ceiling k
  have hnonneg := HilbertSchmidt.hsNorm_nonneg (thetaSourceSignedKernel k)
  have hceiling := thetaSourceSignedHSCeiling_pos.le
  nlinarith

theorem norm_thetaSourceStageSchurDiagonal_le_ceiling
    {k : ℕ} (S : ThetaSourceStageSchurPacket k)
    (i : Fin (Fintype.card ↥(thetaSourceSignedCutoff k))) :
    ‖S.T i i‖ ≤ thetaSourceSignedHSCeiling := by
  have hdiag := norm_diag_le_of_schur S.unitary_right S.conjugates_stage i
  have hsqrt :
      Real.sqrt (matHSNormSq (thetaSourceSignedStageFinMatrix k)) ≤
        Real.sqrt (thetaSourceSignedHSCeiling ^ 2) :=
    Real.sqrt_le_sqrt (matHSNormSq_thetaSourceSignedStageFinMatrix_le_ceiling k)
  rw [Real.sqrt_sq_eq_abs, abs_of_pos thetaSourceSignedHSCeiling_pos] at hsqrt
  exact hdiag.trans hsqrt

/-- Every nonzero Schur diagonal of an actual theta stage contributes its reciprocal as a zero of
the stage's honest ordinary determinant. -/
theorem thetaSourceSignedOrdinaryDet_inv_schurDiagonal_eq_zero
    {k : ℕ} (S : ThetaSourceStageSchurPacket k)
    (i : Fin (Fintype.card ↥(thetaSourceSignedCutoff k)))
    (hi : S.T i i ≠ 0) :
    thetaSourceSignedOrdinaryDet k (S.T i i)⁻¹ = 0 := by
  rw [thetaSourceSignedOrdinaryDet_eq_stageFinDet]
  have hprod := det_one_add_smul_eq_prod S.unitary_right S.triangular
    S.conjugates_stage (-(S.T i i)⁻¹)
  have hfactor : 1 + (-(S.T i i)⁻¹) * S.T i i = 0 := by
    field_simp [hi]
    ring
  have hzprod : ∏ j, (1 + (-(S.T i i)⁻¹) * S.T j j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hfactor
  rw [← hprod] at hzprod
  simpa only [neg_smul, sub_eq_add_neg] using hzprod

/-- **Uniform transverse localization.** Under RH, for every positive size and transverse
threshold, all sufficiently late Schur packets have every diagonal node above the size threshold
strictly inside the transverse threshold. -/
theorem eventually_thetaSourceStageSchurDiagonal_im_sq_lt_of_rh
    (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ (S : ThetaSourceStageSchurPacket k) i,
      δ < Complex.normSq (S.T i i) → (S.T i i).im ^ 2 < η := by
  have hfree :=
    eventually_thetaSourceSignedOrdinaryDet_ne_zero_on_badReciprocalWindow_of_rh
      hRH hδ hη (R := thetaSourceSignedHSCeiling)
  filter_upwards [hfree] with k hk
  intro S i hlarge
  by_contra hnot
  have him : η ≤ (S.T i i).im ^ 2 := le_of_not_gt hnot
  have hi : S.T i i ≠ 0 := Complex.normSq_pos.mp (hδ.trans hlarge)
  have hmem :
      S.T i i ∈ thetaSchurBadSpectralWindow thetaSourceSignedHSCeiling δ η := by
    refine ⟨⟨?_, hlarge.le⟩, him⟩
    rw [mem_closedBall, dist_zero_right]
    exact norm_thetaSourceStageSchurDiagonal_le_ceiling S i
  exact hk (S.T i i)⁻¹ ⟨S.T i i, hmem, rfl⟩
    (thetaSourceSignedOrdinaryDet_inv_schurDiagonal_eq_zero S i hi)

/-- Under RH, positive quartic charge is eventually below every positive tolerance uniformly over
all Schur packets of the actual corrected theta stage. -/
theorem eventually_thetaSourceStageSchurPositiveQuarticCharge_lt_of_rh
    (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ S : ThetaSourceStageSchurPacket k,
      thetaSourceStageSchurPositiveQuarticCharge S < ε := by
  let C : ℝ := thetaSourceSignedHSCeiling
  let t : ℝ := ε / (9200 * (C ^ 2 + 1))
  have hC : 0 < C := thetaSourceSignedHSCeiling_pos
  have hden : 0 < 9200 * (C ^ 2 + 1) := by positivity
  have ht : 0 < t := div_pos hε hden
  have him := eventually_thetaSourceStageSchurDiagonal_im_sq_lt_of_rh hRH ht ht
  have hnumeric : 2300 * (t + t) * C ^ 2 < ε := by
    have hsmallDen : 0 < 2 * (C ^ 2 + 1) := by positivity
    calc
      2300 * (t + t) * C ^ 2 = ε * C ^ 2 / (2 * (C ^ 2 + 1)) := by
        dsimp [t]
        field_simp
        ring
      _ < ε := by
        rw [div_lt_iff₀ hsmallDen]
        nlinarith [sq_nonneg C]
  filter_upwards [him] with k hk
  intro S
  have hsplit :=
    finiteMatrixSchurPositiveQuarticCharge_le_of_large_im_sq_le
      t t ht.le ht.le S.toFiniteMatrixSchurPacket
      (fun i hi => (hk S i hi).le)
  change thetaSourceStageSchurPositiveQuarticCharge S ≤
    2300 * (t + t) * matHSNormSq (thetaSourceSignedStageFinMatrix k) at hsplit
  have henergy : matHSNormSq (thetaSourceSignedStageFinMatrix k) ≤ C ^ 2 := by
    exact matHSNormSq_thetaSourceSignedStageFinMatrix_le_ceiling k
  have hcoeff : 0 ≤ 2300 * (t + t) := by positivity
  exact hsplit.trans_lt <|
    (mul_le_mul_of_nonneg_left henergy hcoeff).trans_lt hnumeric

/-- Uniform decay of positive quartic charge over every Schur realization at each late actual
theta stage. -/
def ThetaSourceSchurPositiveQuarticChargeUniformDecay : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ S : ThetaSourceStageSchurPacket k,
    thetaSourceStageSchurPositiveQuarticCharge S < ε

theorem thetaSourceSchurPositiveQuarticChargeUniformDecay_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ThetaSourceSchurPositiveQuarticChargeUniformDecay := by
  intro ε hε
  exact eventually_thetaSourceStageSchurPositiveQuarticCharge_lt_of_rh hRH hε

theorem thetaSourceSchurPositiveQuarticChargeCofinallySmall_of_uniformDecay
    (hdecay : ThetaSourceSchurPositiveQuarticChargeUniformDecay) :
    ThetaSourceSchurPositiveQuarticChargeCofinallySmall := by
  intro ε hε N
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hdecay ε hε)
  let k : ℕ := max N N₀
  let S : ThetaSourceStageSchurPacket k :=
    Classical.choice (nonempty_thetaSourceStageSchurPacket k)
  refine ⟨k, le_max_left _ _, S, ?_⟩
  exact hN₀ k (le_max_right _ _) S

/-- **Exact GTA asymptotic classification.** RH holds exactly when positive quartic charge tends
uniformly to zero across every Schur packet of the actual corrected finite theta stages. -/
theorem riemannHypothesis_iff_thetaSourceSchurPositiveQuarticChargeUniformDecay :
    RiemannHypothesis ↔ ThetaSourceSchurPositiveQuarticChargeUniformDecay := by
  constructor
  · exact thetaSourceSchurPositiveQuarticChargeUniformDecay_of_riemannHypothesis
  · intro h
    exact riemannHypothesis_of_thetaSourceSchurPositiveQuarticChargeCofinallySmall
      (thetaSourceSchurPositiveQuarticChargeCofinallySmall_of_uniformDecay h)

end

end RHTower.HedenmalmThetaSource
