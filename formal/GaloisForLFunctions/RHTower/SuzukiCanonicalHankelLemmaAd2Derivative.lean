import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelBoundarySourceDerivative
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelApertureDerivative

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

def suzukiFixedWindowPhiContinuous
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) (ha0 : 0 < a) (haB : a ≤ B) :
    C(ClosedInterval 0 B, ℂ) :=
  suzukiHankelKernelContinuousRow omega B homega ⟨a, ⟨ha0.le, haB⟩⟩ -
    epsilon.coeff • suzukiCompressedHankelContinuousOutput omega B (by linarith) hB
      (suzukiApertureCutoff a B
        (suzukiFixedWindowPhi epsilon omega B (by linarith) hB a))

@[simp] theorem suzukiFixedWindowPhiContinuous_apply
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) (ha0 : 0 < a) (haB : a ≤ B)
    (x : ClosedInterval 0 B) :
    suzukiFixedWindowPhiContinuous epsilon omega B homega hB a ha0 haB x =
      suzukiFixedWindowPhiPoint epsilon omega B homega hB a x := by
  rw [suzukiFixedWindowPhiContinuous, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, suzukiFixedWindowPhiPoint,
    suzukiHankelKernelContinuousRow_apply]
  simp only [smul_eq_mul]
  rw [mul_comm (x : ℝ) a]

theorem suzukiCompressedHankelContinuousOutput_toLp_eq
    (omega B : ℝ) (homega : 1 < omega) (hB : 1 < B) (f : IntervalL2 0 B) :
    ContinuousMap.toLp 2 volume ℂ
        (suzukiCompressedHankelContinuousOutput omega B (by linarith) hB f) =
      suzukiCompressedHankelOperator omega B (by linarith) f := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (ClosedInterval 0 B)))
      (suzukiCompressedHankelContinuousOutput omega B (by linarith) hB f),
    suzukiCompressedHankelOperator_coeFn omega B (by linarith) (by linarith) f] with x hcont hop
  rw [hcont, hop, suzukiCompressedHankelContinuousOutput_eq_integral]

theorem suzukiFixedWindowPhiContinuous_toLp_two_eq
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) (ha0 : 0 < a) (haB : a ≤ B) :
    ContinuousMap.toLp 2 volume ℂ
        (suzukiFixedWindowPhiContinuous epsilon omega B homega hB a ha0 haB) =
      suzukiFixedWindowPhi epsilon omega B (by linarith) hB a := by
  have heq := suzukiFixedWindowPhi_equation_expanded
    (omega := omega) (B := B) epsilon (by linarith) hB a
  have hsource : ContinuousMap.toLp 2 volume ℂ
        (suzukiHankelKernelContinuousRow omega B homega ⟨a, ⟨ha0.le, haB⟩⟩) =
      suzukiFixedWindowBoundarySource omega B (by linarith) hB a := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
        (μ := (volume : Measure (ClosedInterval 0 B)))
        (suzukiHankelKernelContinuousRow omega B homega ⟨a, ⟨ha0.le, haB⟩⟩),
      suzukiCompressedHankelRow_ae (omega := omega) (a := B) (x := a)
        (by linarith) hB ha0 haB] with x hcont hrow
    rw [hcont]
    unfold suzukiFixedWindowBoundarySource
    rw [hrow, suzukiHankelKernelContinuousRow_apply]
    rw [mul_comm]
  rw [suzukiFixedWindowPhiContinuous, map_sub, map_smul, hsource,
    suzukiCompressedHankelContinuousOutput_toLp_eq omega B homega hB]
  exact (eq_sub_of_add_eq heq).symm

theorem suzukiFixedWindowPhiContinuous_toLp_one_eq
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) (ha0 : 0 < a) (haB : a ≤ B) :
    ContinuousMap.toLp 1 volume ℂ
        (suzukiFixedWindowPhiContinuous epsilon omega B homega hB a ha0 haB) =
      suzukiIntervalL2AsL1 B
        (suzukiFixedWindowPhi epsilon omega B (by linarith) hB a) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (1 : ENNReal))
      (μ := (volume : Measure (ClosedInterval 0 B)))
      (suzukiFixedWindowPhiContinuous epsilon omega B homega hB a ha0 haB),
    suzukiIntervalL2AsL1_ae B
      (suzukiFixedWindowPhi epsilon omega B (by linarith) hB a),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (ClosedInterval 0 B)))
      (suzukiFixedWindowPhiContinuous epsilon omega B homega hB a ha0 haB),
    show (ContinuousMap.toLp 2 volume ℂ
        (suzukiFixedWindowPhiContinuous epsilon omega B homega hB a ha0 haB) :
          ClosedInterval 0 B → ℂ) =ᵐ[volume]
        (suzukiFixedWindowPhi epsilon omega B (by linarith) hB a :
          ClosedInterval 0 B → ℂ) by
      rw [suzukiFixedWindowPhiContinuous_toLp_two_eq]] with
      x hL1 hright hL2 hEq
  rw [hL1, hright]
  exact hL2.symm.trans hEq

def suzukiFixedWindowPhiL1
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) : IntervalL1 0 B :=
  suzukiIntervalL2AsL1 B
    (suzukiFixedWindowPhi epsilon omega B (by linarith) hB a)

theorem suzukiFixedWindowPhiL1_equation
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) :
    suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a
        (suzukiFixedWindowPhiL1 epsilon omega B homega hB a) =
      suzukiFixedWindowBoundarySourceL1 omega B homega hB a := by
  have heq := suzukiFixedWindowPhi_equation_expanded
    (omega := omega) (B := B) epsilon (by linarith) hB a
  rw [suzukiFixedWindowResolventOperatorL1, add_apply, one_apply_eq_self,
    suzukiFixedWindowPhiL1, suzukiFixedWindowBoundarySourceL1,
    suzukiFixedWindowSignedSectionL1_asL1 epsilon omega a B homega hB]
  have heq' : suzukiFixedWindowPhi epsilon omega B (by linarith) hB a +
      suzukiFixedWindowSignedSection epsilon omega B (by linarith) a
        (suzukiFixedWindowPhi epsilon omega B (by linarith) hB a) =
      suzukiFixedWindowBoundarySource omega B (by linarith) hB a := by
    simpa [suzukiFixedWindowSignedSection] using heq
  have h := congrArg (suzukiIntervalL2ToL1 B) heq'
  rw [map_add] at h
  exact h

def suzukiFixedWindowSignedSectionDerivativeAtPhiL1
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) (ha0 : 0 < a) (haB : a < B) :
    IntervalL1 0 B :=
  suzukiFixedWindowL1Lift epsilon B
    (ContinuousMap.toLp 2 volume ℂ
      (suzukiSmoothedApertureProfileIntegrand omega B homega (by linarith)
        (suzukiFixedWindowPhiContinuous epsilon omega B homega hB a ha0 haB.le) a))

theorem hasDerivAt_suzukiFixedWindowSignedSectionL1_apply_phi
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    HasDerivAt
      (fun b : ℝ => suzukiFixedWindowSignedSectionL1 epsilon omega B homega b
        (suzukiFixedWindowPhiL1 epsilon omega B homega hB a))
      (suzukiFixedWindowSignedSectionDerivativeAtPhiL1
        epsilon omega B homega hB a ha0 haB) a := by
  let f := suzukiFixedWindowPhiContinuous epsilon omega B homega hB a ha0 haB.le
  have hphi : suzukiFixedWindowPhiL1 epsilon omega B homega hB a =
      ContinuousMap.toLp 1 volume ℂ f :=
    (suzukiFixedWindowPhiContinuous_toLp_one_eq
      epsilon omega B homega hB a ha0 haB.le).symm
  have hH := hasDerivAt_suzukiCompressedHankelL1ToL2_aperture_continuousMap
    omega B homega a ha0 haB f
  have hlift := ((suzukiFixedWindowL1Lift epsilon B).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    a hH
  rw [hphi]
  change HasDerivAt
    (fun b : ℝ => suzukiFixedWindowL1Lift epsilon B
      (suzukiCompressedHankelL1ToL2 omega B homega
        (suzukiApertureCutoffL1 b B (ContinuousMap.toLp 1 volume ℂ f)))) _ a
  exact hlift

theorem norm_suzukiApertureCutoffL1_apply_le
    (a B : ℝ) (f : IntervalL1 0 B) :
    ‖suzukiApertureCutoffL1 a B f‖ ≤ ‖f‖ := by
  change ‖lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ)
      (volume : Measure (ClosedInterval 0 B)) 1
      (suzukiApertureSet a B) (measurableSet_suzukiApertureSet a B)
      (LpToLpRestrictCLM (ClosedInterval 0 B) ℂ ℂ
        (volume : Measure (ClosedInterval 0 B)) 1
        (suzukiApertureSet a B) f)‖ ≤ ‖f‖
  rw [show lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ)
      (volume : Measure (ClosedInterval 0 B)) 1
      (suzukiApertureSet a B) (measurableSet_suzukiApertureSet a B)
      (LpToLpRestrictCLM (ClosedInterval 0 B) ℂ ℂ
        (volume : Measure (ClosedInterval 0 B)) 1
        (suzukiApertureSet a B) f) =
      lpExtendByZero (F := ℂ) (volume : Measure (ClosedInterval 0 B)) 1
        (suzukiApertureSet a B) (measurableSet_suzukiApertureSet a B)
        (LpToLpRestrictCLM (ClosedInterval 0 B) ℂ ℂ
          (volume : Measure (ClosedInterval 0 B)) 1
          (suzukiApertureSet a B) f) by rfl,
    norm_lpExtendByZero]
  exact norm_Lp_toLp_restrict_le (suzukiApertureSet a B) f

theorem continuous_suzukiApertureCutoffL1_apply (B : ℝ) (f : IntervalL1 0 B) :
    Continuous fun a : ℝ => suzukiApertureCutoffL1 a B f := by
  rw [continuous_iff_seqContinuous]
  intro u a hu
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  let F : ℕ → ClosedInterval 0 B → ℂ := fun n =>
    (suzukiApertureSet (u n) B).indicator f
  let G : ClosedInterval 0 B → ℂ :=
    (suzukiApertureSet a B).indicator f
  have hF (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    (Lp.memLp f).1.indicator (measurableSet_suzukiApertureSet (u n) B)
  have hG : MemLp G 1 volume :=
    (Lp.memLp f).indicator (measurableSet_suzukiApertureSet a B)
  have hui : UnifIntegrable F 1 volume := by
    intro epsilon hepsilon
    obtain ⟨delta, hdelta, hbound⟩ :=
      (unifIntegrable_const (ι := ℕ) (p := (1 : ℝ≥0∞)) (by norm_num)
        (by norm_num) (Lp.memLp f)) hepsilon
    refine ⟨delta, hdelta, fun n s hs hmeasure => ?_⟩
    calc
      eLpNorm (s.indicator (F n)) 1 volume =
          eLpNorm ((s ∩ suzukiApertureSet (u n) B).indicator f) 1 volume := by
        change eLpNorm (s.indicator ((suzukiApertureSet (u n) B).indicator f))
          1 volume = _
        rw [Set.indicator_indicator]
      _ ≤ eLpNorm (s.indicator f) 1 volume := by
        apply eLpNorm_mono
        intro x
        by_cases hxs : x ∈ s
        · by_cases hxa : x ∈ suzukiApertureSet (u n) B <;> simp [hxs, hxa]
        · simp [hxs]
      _ ≤ ENNReal.ofReal epsilon := hbound n s hs hmeasure
  have hmp : MeasurePreserving ((↑) : ClosedInterval 0 B → ℝ)
      (volume : Measure (ClosedInterval 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hne : ∀ᵐ x : ClosedInterval 0 B ∂volume, (x : ℝ) ≠ a :=
    hmp.quasiMeasurePreserving.ae
      (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne a))
  have hpoint : ∀ᵐ x : ClosedInterval 0 B ∂volume,
      Tendsto (fun n => F n x) atTop (𝓝 (G x)) := by
    filter_upwards [hne] with x hx
    rcases lt_or_gt_of_ne hx with hxa | hax
    · have hevent : ∀ᶠ n in atTop, (x : ℝ) < u n :=
        (tendsto_order.mp hu).1 (x : ℝ) hxa
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      filter_upwards [hevent] with n hn
      simp [F, G, suzukiApertureSet, hn.le, hxa.le]
    · have hevent : ∀ᶠ n in atTop, u n < (x : ℝ) :=
        (tendsto_order.mp hu).2 (x : ℝ) hax
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      filter_upwards [hevent] with n hn
      simp [F, G, suzukiApertureSet, not_le.mpr hn, not_le.mpr hax]
  have hLp : Tendsto (fun n => eLpNorm (F n - G) 1 volume) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hF hG hui hpoint
  have hnorm : (fun n => eLpNorm
      ((suzukiApertureCutoffL1 (u n) B f : ClosedInterval 0 B → ℂ) -
        (suzukiApertureCutoffL1 a B f : ClosedInterval 0 B → ℂ)) 1 volume) =
      (fun n => eLpNorm (F n - G) 1 volume) := by
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [suzukiApertureCutoffL1_ae (u n) B f,
      suzukiApertureCutoffL1_ae a B f] with x hleft hright
    simp only [Pi.sub_apply]
    rw [hleft, hright]
  change Tendsto (fun n => eLpNorm
      ((suzukiApertureCutoffL1 (u n) B f : ClosedInterval 0 B → ℂ) -
        (suzukiApertureCutoffL1 a B f : ClosedInterval 0 B → ℂ)) 1 volume) atTop (𝓝 0)
  rw [hnorm]
  exact hLp

theorem norm_suzukiApertureCutoffL1_le_one (a B : ℝ) :
    ‖suzukiApertureCutoffL1 a B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_suzukiApertureCutoffL1_apply_le a B f

theorem norm_suzukiFixedWindowSignedSection_le_hankel
    (epsilon : SuzukiHankelSign) {omega B : ℝ}
    (homega : 1 < omega) (a : ℝ) :
    ‖suzukiFixedWindowSignedSection epsilon omega B (by linarith) a‖ ≤
      ‖suzukiCompressedHankelOperator omega B (by linarith)‖ := by
  rw [suzukiFixedWindowSignedSection, norm_smul]
  have hcoeff : ‖epsilon.coeff‖ = 1 := by
    cases epsilon <;> simp [SuzukiHankelSign.coeff]
  rw [hcoeff, one_mul]
  calc
    ‖suzukiCompressedHankelOperator omega B (by linarith) ∘L
        suzukiApertureCutoff a B‖ ≤
      ‖suzukiCompressedHankelOperator omega B (by linarith)‖ *
        ‖suzukiApertureCutoff a B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖suzukiCompressedHankelOperator omega B (by linarith)‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_suzukiApertureCutoff_le_one a B) (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_suzukiFixedWindowResolventOperatorL2Inverse_le
    (epsilon : SuzukiHankelSign) {omega B : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) :
    ‖suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a‖ ≤
      (1 - ‖suzukiCompressedHankelOperator omega B (by linarith)‖)⁻¹ := by
  let H := suzukiCompressedHankelOperator omega B (by linarith)
  let S := suzukiFixedWindowSignedSection epsilon omega B (by linarith) a
  let R := suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a
  have hq : ‖H‖ < 1 := suzuki2012_lemma_four_four_iii (by linarith) hB
  have hden : 0 < 1 - ‖H‖ := sub_pos.mpr hq
  have hS : ‖S‖ ≤ ‖H‖ :=
    norm_suzukiFixedWindowSignedSection_le_hankel epsilon homega a
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hden.le)
  intro f
  have heq := suzukiFixedWindowResolventOperator_apply_inverseL2
    epsilon omega B homega hB a f
  change R f + S (R f) = f at heq
  have hraw : ‖R f‖ ≤ ‖f‖ + ‖H‖ * ‖R f‖ := by
    have hu : R f = f - S (R f) := eq_sub_of_add_eq heq
    calc
      ‖R f‖ = ‖f - S (R f)‖ := congrArg norm hu
      _ ≤ ‖f‖ + ‖S (R f)‖ := norm_sub_le _ _
      _ ≤ ‖f‖ + ‖S‖ * ‖R f‖ := by
        gcongr
        exact S.le_opNorm _
      _ ≤ ‖f‖ + ‖H‖ * ‖R f‖ := by gcongr
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hden).2
  nlinarith [norm_nonneg (R f)]

def suzukiFixedWindowResolventOperatorL1InverseBound
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) : ℝ :=
  ‖(1 : IntervalL1 0 B →L[ℂ] IntervalL1 0 B)‖ +
    ‖suzukiFixedWindowL1Lift epsilon B‖ *
    (1 - ‖suzukiCompressedHankelOperator omega B (by linarith)‖)⁻¹ *
      ‖suzukiCompressedHankelL1ToL2 omega B homega‖

theorem norm_suzukiFixedWindowResolventOperatorL1Inverse_le
    (epsilon : SuzukiHankelSign) {omega B : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) :
    ‖suzukiFixedWindowResolventOperatorL1Inverse epsilon omega B homega hB a‖ ≤
      suzukiFixedWindowResolventOperatorL1InverseBound epsilon omega B homega := by
  rw [suzukiFixedWindowResolventOperatorL1Inverse,
    suzukiFixedWindowResolventOperatorL1InverseBound]
  calc
    ‖(1 : IntervalL1 0 B →L[ℂ] IntervalL1 0 B) -
        suzukiFixedWindowL1Lift epsilon B ∘L
          suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a ∘L
            suzukiFixedWindowL1Section omega a B homega‖ ≤
      ‖(1 : IntervalL1 0 B →L[ℂ] IntervalL1 0 B)‖ +
        ‖suzukiFixedWindowL1Lift epsilon B ∘L
          suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a ∘L
            suzukiFixedWindowL1Section omega a B homega‖ := by
      exact norm_sub_le
        (1 : IntervalL1 0 B →L[ℂ] IntervalL1 0 B)
        (suzukiFixedWindowL1Lift epsilon B ∘L
          suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a ∘L
            suzukiFixedWindowL1Section omega a B homega)
    _ ≤ ‖(1 : IntervalL1 0 B →L[ℂ] IntervalL1 0 B)‖ +
        ‖suzukiFixedWindowL1Lift epsilon B‖ *
        ‖suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a‖ *
          ‖suzukiFixedWindowL1Section omega a B homega‖ := by
      gcongr
      calc
        ‖suzukiFixedWindowL1Lift epsilon B ∘L
            (suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a ∘L
              suzukiFixedWindowL1Section omega a B homega)‖ ≤
          ‖suzukiFixedWindowL1Lift epsilon B‖ *
            ‖suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a ∘L
              suzukiFixedWindowL1Section omega a B homega‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖suzukiFixedWindowL1Lift epsilon B‖ *
            (‖suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a‖ *
              ‖suzukiFixedWindowL1Section omega a B homega‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
        _ = ‖suzukiFixedWindowL1Lift epsilon B‖ *
            ‖suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a‖ *
              ‖suzukiFixedWindowL1Section omega a B homega‖ := by ring
    _ ≤ ‖(1 : IntervalL1 0 B →L[ℂ] IntervalL1 0 B)‖ +
        ‖suzukiFixedWindowL1Lift epsilon B‖ *
        (1 - ‖suzukiCompressedHankelOperator omega B (by linarith)‖)⁻¹ *
          ‖suzukiCompressedHankelL1ToL2 omega B homega‖ := by
      have hq : ‖suzukiCompressedHankelOperator omega B (by linarith)‖ < 1 :=
        suzuki2012_lemma_four_four_iii (by linarith) hB
      have hrnonneg : 0 ≤
          (1 - ‖suzukiCompressedHankelOperator omega B (by linarith)‖)⁻¹ :=
        inv_nonneg.mpr (sub_nonneg.mpr hq.le)
      have hR := norm_suzukiFixedWindowResolventOperatorL2Inverse_le epsilon homega hB a
      have hV : ‖suzukiFixedWindowL1Section omega a B homega‖ ≤
          ‖suzukiCompressedHankelL1ToL2 omega B homega‖ := by
        change ‖suzukiCompressedHankelL1ToL2 omega B homega ∘L
            suzukiApertureCutoffL1 a B‖ ≤ _
        calc
          _ ≤ ‖suzukiCompressedHankelL1ToL2 omega B homega‖ *
              ‖suzukiApertureCutoffL1 a B‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖suzukiCompressedHankelL1ToL2 omega B homega‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_suzukiApertureCutoffL1_le_one a B) (norm_nonneg _)
          _ = _ := mul_one _
      have hprod : ‖suzukiFixedWindowL1Lift epsilon B‖ *
            ‖suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a‖ *
              ‖suzukiFixedWindowL1Section omega a B homega‖ ≤
          ‖suzukiFixedWindowL1Lift epsilon B‖ *
            (1 - ‖suzukiCompressedHankelOperator omega B (by linarith)‖)⁻¹ *
              ‖suzukiCompressedHankelL1ToL2 omega B homega‖ :=
        mul_le_mul
        (mul_le_mul_of_nonneg_left hR (norm_nonneg _)) hV
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) hrnonneg)
      exact add_le_add (le_refl _) hprod

theorem continuous_suzukiFixedWindowResolventOperatorL1_apply
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (f : IntervalL1 0 B) :
    Continuous fun a : ℝ =>
      suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a f := by
  change Continuous fun a : ℝ =>
    f + suzukiFixedWindowL1Lift epsilon B
      (suzukiCompressedHankelL1ToL2 omega B homega
        (suzukiApertureCutoffL1 a B f))
  exact continuous_const.add
    ((suzukiFixedWindowL1Lift epsilon B).continuous.comp
      ((suzukiCompressedHankelL1ToL2 omega B homega).continuous.comp
        (continuous_suzukiApertureCutoffL1_apply B f)))

theorem continuousAt_suzukiFixedWindowResolventOperatorL1Inverse_apply₂
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B)
    {g : ℝ → IntervalL1 0 B} (hg : ContinuousAt g a) :
    ContinuousAt (fun b : ℝ =>
      suzukiFixedWindowResolventOperatorL1Inverse
        epsilon omega B homega hB b (g b)) a := by
  let A := fun b : ℝ =>
    suzukiFixedWindowResolventOperatorL1 epsilon omega B homega b
  let R := fun b : ℝ =>
    suzukiFixedWindowResolventOperatorL1Inverse epsilon omega B homega hB b
  let C := suzukiFixedWindowResolventOperatorL1InverseBound epsilon omega B homega
  let v := R a (g a)
  have hav : A a v = g a := by
    exact suzukiFixedWindowResolventOperatorL1_apply_inverse
      epsilon omega B homega hB a (g a)
  have hdiff (b : ℝ) :
      R b (g b) - v =
        R b ((g b - g a) + (A a v - A b v)) := by
    have hb : R b (A b v) = v :=
      suzukiFixedWindowResolventOperatorL1_inverse_apply
        epsilon omega B homega hB b v
    calc
      R b (g b) - v = R b (g b) - R b (A b v) := by rw [hb]
      _ = R b (g b - A b v) := by rw [map_sub]
      _ = R b ((g b - g a) + (A a v - A b v)) := by
        congr 1
        rw [hav]
        abel
  have hA : ContinuousAt (fun b : ℝ => A b v) a :=
    (continuous_suzukiFixedWindowResolventOperatorL1_apply
      epsilon omega B homega v).continuousAt
  have hg0 : Tendsto (fun b : ℝ => g b - g a) (𝓝 a) (𝓝 0) := by
    have hgc : ContinuousAt (fun b : ℝ => g b - g a) a :=
      hg.sub continuousAt_const
    change Tendsto (fun b : ℝ => g b - g a) (𝓝 a) (𝓝 (g a - g a)) at hgc
    simpa using hgc
  have hA0 : Tendsto (fun b : ℝ => A a v - A b v) (𝓝 a) (𝓝 0) := by
    have hAc : ContinuousAt (fun b : ℝ => A a v - A b v) a :=
      continuousAt_const.sub hA
    change Tendsto (fun b : ℝ => A a v - A b v) (𝓝 a)
      (𝓝 (A a v - A a v)) at hAc
    simpa using hAc
  have hupper : Tendsto (fun b : ℝ =>
      C * (‖g b - g a‖ + ‖A a v - A b v‖)) (𝓝 a) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hg0.norm.add hA0.norm)
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
    tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun b => norm_nonneg (R b (g b) - v))
    (Eventually.of_forall fun b => ?_) hupper
  rw [hdiff]
  have hR : ‖R b‖ ≤ C :=
    norm_suzukiFixedWindowResolventOperatorL1Inverse_le epsilon homega hB b
  calc
    ‖R b ((g b - g a) + (A a v - A b v))‖ ≤
        ‖R b‖ * ‖(g b - g a) + (A a v - A b v)‖ := (R b).le_opNorm _
    _ ≤ C * (‖g b - g a‖ + ‖A a v - A b v‖) := by
      exact mul_le_mul hR (norm_add_le _ _)
        (norm_nonneg _) (le_trans (norm_nonneg _) hR)

theorem suzukiFixedWindowPhiL1_eq_inverse_source
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) :
    suzukiFixedWindowPhiL1 epsilon omega B homega hB a =
      suzukiFixedWindowResolventOperatorL1Inverse epsilon omega B homega hB a
        (suzukiFixedWindowBoundarySourceL1 omega B homega hB a) := by
  rw [← suzukiFixedWindowPhiL1_equation epsilon omega B homega hB a]
  exact (suzukiFixedWindowResolventOperatorL1_inverse_apply
    epsilon omega B homega hB a
      (suzukiFixedWindowPhiL1 epsilon omega B homega hB a)).symm

def suzukiFixedWindowPhiDerivativeL1
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ)
    (ha0 : 0 < a) (haB : a < B) : IntervalL1 0 B :=
  suzukiFixedWindowResolventOperatorL1Inverse epsilon omega B homega hB a
    (suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a -
      suzukiFixedWindowSignedSectionDerivativeAtPhiL1
        epsilon omega B homega hB a ha0 haB)

/-- Suzuki's fixed-window Fredholm solution has a strong `L¹` derivative at every positive
aperture strictly inside the window.  The derivative is the inverse resolvent applied to the
literal source derivative minus the moving-endpoint Hankel row. -/
theorem hasDerivAt_suzukiFixedWindowPhiL1
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    HasDerivAt (suzukiFixedWindowPhiL1 epsilon omega B homega hB)
      (suzukiFixedWindowPhiDerivativeL1
        epsilon omega B homega hB a ha0 haB) a := by
  let u := suzukiFixedWindowPhiL1 epsilon omega B homega hB
  let s := suzukiFixedWindowBoundarySourceL1 omega B homega hB
  let A := fun b : ℝ =>
    suzukiFixedWindowResolventOperatorL1 epsilon omega B homega b
  let R := fun b : ℝ =>
    suzukiFixedWindowResolventOperatorL1Inverse epsilon omega B homega hB b
  let dS := suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a
  let dA := suzukiFixedWindowSignedSectionDerivativeAtPhiL1
    epsilon omega B homega hB a ha0 haB
  let q := fun b : ℝ =>
    (s b - s a) - (A b (u a) - A a (u a))
  have hs : HasDerivAt s dS a :=
    hasDerivAt_suzukiFixedWindowBoundarySourceL1 homega hB ha0 haB
  have hsection : HasDerivAt
      (fun b : ℝ => suzukiFixedWindowSignedSectionL1 epsilon omega B homega b (u a))
      dA a := by
    exact hasDerivAt_suzukiFixedWindowSignedSectionL1_apply_phi
      epsilon homega hB ha0 haB
  have hAua : HasDerivAt (fun b : ℝ => A b (u a)) dA a := by
    change HasDerivAt (fun b : ℝ =>
      u a + suzukiFixedWindowSignedSectionL1 epsilon omega B homega b (u a)) dA a
    exact hsection.const_add (u a)
  have hq : HasDerivAt q (dS - dA) a := by
    have hq' := (hs.sub_const (s a)).sub (hAua.sub_const (A a (u a)))
    change HasDerivAt
      ((fun b : ℝ => s b - s a) - fun b : ℝ => A b (u a) - A a (u a))
        (dS - dA) a at hq'
    change HasDerivAt
      (fun b : ℝ => (s b - s a) - (A b (u a) - A a (u a)))
        (dS - dA) a
    exact hq'
  have hqa : q a = 0 := by simp [q]
  have hdiff (b : ℝ) : u b - u a = R b (q b) := by
    have hEqb : A b (u b) = s b :=
      suzukiFixedWindowPhiL1_equation epsilon omega B homega hB b
    have hEqa : A a (u a) = s a :=
      suzukiFixedWindowPhiL1_equation epsilon omega B homega hB a
    have hinv : R b (A b (u b - u a)) = u b - u a :=
      suzukiFixedWindowResolventOperatorL1_inverse_apply
        epsilon omega B homega hB b (u b - u a)
    rw [map_sub, hEqb] at hinv
    rw [← hinv]
    congr 1
    change s b - A b (u a) =
      (s b - s a) - (A b (u a) - A a (u a))
    rw [hEqa]
    abel
  let g := Function.update (slope q a) a (dS - dA)
  have hg : ContinuousAt g a := by
    exact continuousAt_update_same.mpr hq.tendsto_slope
  have hRg : ContinuousAt (fun b : ℝ => R b (g b)) a :=
    continuousAt_suzukiFixedWindowResolventOperatorL1Inverse_apply₂
      epsilon homega hB hg
  rw [hasDerivAt_iff_tendsto_slope]
  have hlimit : Tendsto (fun b : ℝ => R b (g b)) (𝓝[≠] a)
      (𝓝 (R a (dS - dA))) := by
    have h : Tendsto (fun b : ℝ => R b (g b)) (𝓝[≠] a)
        (𝓝 (R a (g a))) := hRg.tendsto.mono_left nhdsWithin_le_nhds
    simpa [g] using h
  refine hlimit.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with b hba
  change R b (Function.update (slope q a) a (dS - dA) b) = slope u a b
  rw [Function.update_of_ne hba]
  change R b ((b - a)⁻¹ • (q b - q a)) = (b - a)⁻¹ • (u b - u a)
  rw [hqa, sub_zero, hdiff]
  exact map_smul ((R b).restrictScalars ℝ) (b - a)⁻¹ (q b)

end RHTower
