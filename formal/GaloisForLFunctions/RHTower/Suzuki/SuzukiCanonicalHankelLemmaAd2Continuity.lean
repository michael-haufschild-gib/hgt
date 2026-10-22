import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelApertureContinuity

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

def suzukiFixedWindowSignedSection
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 / 2 < omega) (a : ℝ) :
    IntervalL2 0 B →L[ℂ] IntervalL2 0 B :=
  epsilon.coeff •
    (suzukiCompressedHankelOperator omega B homega ∘L
      suzukiApertureCutoff a B)

theorem norm_suzukiFixedWindowSignedSection_lt_one
    (epsilon : SuzukiHankelSign) {omega B : ℝ}
    (homega : 1 / 2 < omega) (hB : 1 < B) (a : ℝ) :
    ‖suzukiFixedWindowSignedSection epsilon omega B homega a‖ < 1 := by
  rw [suzukiFixedWindowSignedSection, norm_smul]
  have hcoeff : ‖epsilon.coeff‖ = 1 := by
    cases epsilon <;> simp [SuzukiHankelSign.coeff]
  rw [hcoeff, one_mul]
  calc
    ‖suzukiCompressedHankelOperator omega B homega ∘L suzukiApertureCutoff a B‖ ≤
        ‖suzukiCompressedHankelOperator omega B homega‖ *
          ‖suzukiApertureCutoff a B‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖suzukiCompressedHankelOperator omega B homega‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_suzukiApertureCutoff_le_one a B)
        (norm_nonneg _)
    _ < 1 := by
      simpa only [mul_one] using suzuki2012_lemma_four_four_iii homega hB

def suzukiFixedWindowResolventOperator
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 / 2 < omega) (a : ℝ) :
    IntervalL2 0 B →L[ℂ] IntervalL2 0 B :=
  1 + suzukiFixedWindowSignedSection epsilon omega B homega a

theorem suzukiFixedWindowResolventOperator_isUnit
    (epsilon : SuzukiHankelSign) {omega B : ℝ}
    (homega : 1 / 2 < omega) (hB : 1 < B) (a : ℝ) :
    IsUnit (suzukiFixedWindowResolventOperator epsilon omega B homega a) := by
  rw [suzukiFixedWindowResolventOperator, ← sub_neg_eq_add]
  apply isUnit_one_sub_of_norm_lt_one
  rw [norm_neg]
  exact norm_suzukiFixedWindowSignedSection_lt_one epsilon homega hB a

def suzukiFixedWindowBoundarySource
    (omega B : ℝ) (homega : 1 / 2 < omega) (hB : 1 < B) (a : ℝ) :
    IntervalL2 0 B :=
  suzukiCompressedHankelRow omega B homega hB a

def suzukiFixedWindowPhi
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 / 2 < omega) (hB : 1 < B) (a : ℝ) :
    IntervalL2 0 B :=
  let hunit := suzukiFixedWindowResolventOperator_isUnit epsilon homega hB a
  ((↑(hunit.unit⁻¹) : IntervalL2 0 B →L[ℂ] IntervalL2 0 B)
    (suzukiFixedWindowBoundarySource omega B homega hB a))

theorem suzukiFixedWindowPhi_equation
    (epsilon : SuzukiHankelSign) {omega B : ℝ}
    (homega : 1 / 2 < omega) (hB : 1 < B) (a : ℝ) :
    suzukiFixedWindowResolventOperator epsilon omega B homega a
        (suzukiFixedWindowPhi epsilon omega B homega hB a) =
      suzukiFixedWindowBoundarySource omega B homega hB a := by
  let hunit := suzukiFixedWindowResolventOperator_isUnit epsilon homega hB a
  let U := hunit.unit
  have hU : (↑U : IntervalL2 0 B →L[ℂ] IntervalL2 0 B) =
      suzukiFixedWindowResolventOperator epsilon omega B homega a := hunit.unit_spec
  rw [← hU]
  change (↑U : IntervalL2 0 B →L[ℂ] IntervalL2 0 B)
      ((↑(U⁻¹) : IntervalL2 0 B →L[ℂ] IntervalL2 0 B)
        (suzukiFixedWindowBoundarySource omega B homega hB a)) = _
  rw [← mul_apply_eq_comp, Units.mul_inv]
  simp

theorem suzukiFixedWindowPhi_equation_expanded
    (epsilon : SuzukiHankelSign) {omega B : ℝ}
    (homega : 1 / 2 < omega) (hB : 1 < B) (a : ℝ) :
    suzukiFixedWindowPhi epsilon omega B homega hB a +
        epsilon.coeff • suzukiCompressedHankelOperator omega B homega
          (suzukiApertureCutoff a B
            (suzukiFixedWindowPhi epsilon omega B homega hB a)) =
      suzukiFixedWindowBoundarySource omega B homega hB a := by
  simpa [suzukiFixedWindowResolventOperator, suzukiFixedWindowSignedSection]
    using suzukiFixedWindowPhi_equation epsilon homega hB a

theorem norm_suzukiFixedWindowPhi_sub_le
    (epsilon : SuzukiHankelSign) {omega B : ℝ}
    (homega : 1 / 2 < omega) (hB : 1 < B) (a b : ℝ) :
    ‖suzukiFixedWindowPhi epsilon omega B homega hB b -
        suzukiFixedWindowPhi epsilon omega B homega hB a‖ ≤
      (‖suzukiFixedWindowBoundarySource omega B homega hB b -
          suzukiFixedWindowBoundarySource omega B homega hB a‖ +
        ‖suzukiCompressedHankelOperator omega B homega‖ *
          ‖suzukiApertureCutoff b B
              (suzukiFixedWindowPhi epsilon omega B homega hB a) -
            suzukiApertureCutoff a B
              (suzukiFixedWindowPhi epsilon omega B homega hB a)‖) /
        (1 - ‖suzukiCompressedHankelOperator omega B homega‖) := by
  let H := suzukiCompressedHankelOperator omega B homega
  let Pa := suzukiApertureCutoff a B
  let Pb := suzukiApertureCutoff b B
  let ua := suzukiFixedWindowPhi epsilon omega B homega hB a
  let ub := suzukiFixedWindowPhi epsilon omega B homega hB b
  let sa := suzukiFixedWindowBoundarySource omega B homega hB a
  let sb := suzukiFixedWindowBoundarySource omega B homega hB b
  have heqa : ua + epsilon.coeff • H (Pa ua) = sa :=
    suzukiFixedWindowPhi_equation_expanded epsilon homega hB a
  have heqb : ub + epsilon.coeff • H (Pb ub) = sb :=
    suzukiFixedWindowPhi_equation_expanded epsilon homega hB b
  have hua : ua = sa - epsilon.coeff • H (Pa ua) :=
    eq_sub_of_add_eq heqa
  have hub : ub = sb - epsilon.coeff • H (Pb ub) :=
    eq_sub_of_add_eq heqb
  have hcut : Pb ub - Pa ua = Pb (ub - ua) + (Pb ua - Pa ua) := by
    rw [map_sub]
    abel
  have hdiff : ub - ua =
      (sb - sa) - epsilon.coeff • H (Pb ub - Pa ua) := by
    calc
      ub - ua = (sb - epsilon.coeff • H (Pb ub)) -
          (sa - epsilon.coeff • H (Pa ua)) :=
        congrArg₂ (· - ·) hub hua
      _ = (sb - sa) - epsilon.coeff • H (Pb ub - Pa ua) := by
        rw [map_sub, smul_sub]
        abel
  have hcoeff : ‖epsilon.coeff‖ = 1 := by
    cases epsilon <;> simp [SuzukiHankelSign.coeff]
  have hraw : ‖ub - ua‖ ≤
      ‖sb - sa‖ + ‖H‖ * (‖ub - ua‖ + ‖Pb ua - Pa ua‖) := by
    calc
      ‖ub - ua‖ =
          ‖(sb - sa) - epsilon.coeff • H (Pb ub - Pa ua)‖ :=
        congrArg norm hdiff
      _ ≤
          ‖sb - sa‖ + ‖epsilon.coeff • H (Pb ub - Pa ua)‖ :=
        norm_sub_le _ _
      _ = ‖sb - sa‖ + ‖H (Pb ub - Pa ua)‖ := by
        rw [norm_smul, hcoeff, one_mul]
      _ ≤ ‖sb - sa‖ + ‖H‖ * ‖Pb ub - Pa ua‖ := by
        gcongr
        exact H.le_opNorm _
      _ = ‖sb - sa‖ + ‖H‖ * ‖Pb (ub - ua) + (Pb ua - Pa ua)‖ := by
        rw [hcut]
      _ ≤ ‖sb - sa‖ + ‖H‖ *
          (‖Pb (ub - ua)‖ + ‖Pb ua - Pa ua‖) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖sb - sa‖ + ‖H‖ * (‖ub - ua‖ + ‖Pb ua - Pa ua‖) := by
        gcongr
        exact norm_suzukiApertureCutoff_apply_le b B (ub - ua)
  have hq : ‖H‖ < 1 := suzuki2012_lemma_four_four_iii homega hB
  have hden : 0 < 1 - ‖H‖ := sub_pos.mpr hq
  apply (le_div_iff₀ hden).2
  nlinarith [norm_nonneg (ub - ua), norm_nonneg (sb - sa),
    norm_nonneg (Pb ua - Pa ua), norm_nonneg H]

theorem continuousOn_suzukiFixedWindowPhi
    (epsilon : SuzukiHankelSign) {omega B : ℝ}
    (homega : 1 / 2 < omega) (hB : 1 < B) :
    ContinuousOn (suzukiFixedWindowPhi epsilon omega B homega hB) (Icc 0 B) := by
  intro a ha
  let H := suzukiCompressedHankelOperator omega B homega
  let ua := suzukiFixedWindowPhi epsilon omega B homega hB a
  let source : ℝ → IntervalL2 0 B :=
    suzukiFixedWindowBoundarySource omega B homega hB
  have hsource : ContinuousWithinAt source (Icc 0 B) a := by
    exact (continuousOn_suzukiCompressedHankelRow homega hB a ha)
  have hsourceNorm : Tendsto (fun b => ‖source b - source a‖)
      (𝓝[Icc 0 B] a) (𝓝 0) := by
    have hconst : ContinuousWithinAt (fun _ : ℝ => source a) (Icc 0 B) a :=
      continuousWithinAt_const
    have hnorm' := (hsource.sub hconst).norm
    change Tendsto (fun b => ‖source b - source a‖) (𝓝[Icc 0 B] a)
      (𝓝 ‖source a - source a‖) at hnorm'
    simpa only [sub_self, norm_zero] using hnorm'
  have hcut : ContinuousAt (fun b => suzukiApertureCutoff b B ua) a :=
    (continuous_suzukiApertureCutoff_apply B ua).continuousAt
  have hcutNorm : Tendsto (fun b =>
      ‖suzukiApertureCutoff b B ua - suzukiApertureCutoff a B ua‖)
      (𝓝[Icc 0 B] a) (𝓝 0) := by
    have hconst : ContinuousWithinAt
        (fun _ : ℝ => suzukiApertureCutoff a B ua) (Icc 0 B) a :=
      continuousWithinAt_const
    have hnorm' := (hcut.continuousWithinAt.sub hconst).norm
    change Tendsto (fun b =>
      ‖suzukiApertureCutoff b B ua - suzukiApertureCutoff a B ua‖)
      (𝓝[Icc 0 B] a)
      (𝓝 ‖suzukiApertureCutoff a B ua - suzukiApertureCutoff a B ua‖) at hnorm'
    simpa only [sub_self, norm_zero] using hnorm'
  have hq : ‖H‖ < 1 := suzuki2012_lemma_four_four_iii homega hB
  have hden : 1 - ‖H‖ ≠ 0 := (sub_pos.mpr hq).ne'
  have hrhs : Tendsto (fun b =>
      (‖source b - source a‖ + ‖H‖ *
        ‖suzukiApertureCutoff b B ua - suzukiApertureCutoff a B ua‖) /
        (1 - ‖H‖)) (𝓝[Icc 0 B] a) (𝓝 0) := by
    simpa using (hsourceNorm.add
      (tendsto_const_nhds.mul hcutNorm)).div_const (1 - ‖H‖)
  have hnorm : Tendsto (fun b =>
      ‖suzukiFixedWindowPhi epsilon omega B homega hB b - ua‖)
      (𝓝[Icc 0 B] a) (𝓝 0) := by
    apply squeeze_zero
    · exact fun _ => norm_nonneg _
    · intro b
      exact norm_suzukiFixedWindowPhi_sub_le epsilon homega hB a b
    · exact hrhs
  have hdiff : Tendsto (fun b =>
      suzukiFixedWindowPhi epsilon omega B homega hB b - ua)
      (𝓝[Icc 0 B] a) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hadd := hdiff.add (tendsto_const_nhds (x := ua))
  change Tendsto (suzukiFixedWindowPhi epsilon omega B homega hB)
    (𝓝[Icc 0 B] a) (𝓝 ua)
  simpa only [sub_add_cancel, zero_add] using hadd

theorem suzukiApertureCutoff_eq_inclusion_restriction
    (a B : ℝ) (f : IntervalL2 0 B) :
    suzukiApertureCutoff a B f =
      suzukiPhysicalIntervalInclusion a B
        (suzukiPhysicalIntervalRestrictionBetween a B f) := by
  let R : IntervalL2 0 a := suzukiPhysicalIntervalRestrictionBetween a B f
  let EB : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry B f
  have hmpA : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hEBReal := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae f)
  have hEBSubA := hmpA.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hEBReal)
  have hneA := hmpA.quasiMeasurePreserving.ae
    (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0))
  have hRzero : ∀ᵐ x : ClosedInterval 0 a ∂volume,
      suzukiPhysicalIntervalZeroExtendFun R (x : ℝ) =
        suzukiPhysicalIntervalZeroExtendFun f (x : ℝ) := by
    filter_upwards [suzukiPhysicalIntervalRepresentative_ae R,
      suzukiPositiveIntervalRestriction_value_ae EB,
      hEBSubA, hneA] with x hRrep hRval hEB hne
    rw [suzukiPhysicalIntervalZeroExtendFun_apply, hRrep]
    change suzukiPositiveIntervalRestriction a EB x = _
    rw [hRval]
    have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hne)
    exact hEB hxpos
  have hRreal : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc 0 a),
      suzukiPhysicalIntervalZeroExtendFun R x =
        suzukiPhysicalIntervalZeroExtendFun f x :=
    (ae_restrict_iff_subtype measurableSet_Icc).2 hRzero
  have hRwhole := (ae_restrict_iff' measurableSet_Icc).mp hRreal
  have hmpB : MeasurePreserving ((↑) : ClosedInterval 0 B → ℝ)
      (volume : Measure (ClosedInterval 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hRSubB := hmpB.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hRwhole)
  have hposRReal := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae R)
  have hposRSubB := hmpB.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hposRReal)
  have hneB := hmpB.quasiMeasurePreserving.ae
    (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0))
  apply Lp.ext
  filter_upwards [suzukiApertureCutoff_ae a B f,
    suzukiPhysicalIntervalInclusion_ae a B R,
    hposRSubB, hRSubB,
    suzukiPhysicalIntervalRepresentative_ae f, hneB] with
      x hcut hinc hposR hR hfrep hne
  rw [hcut, hinc]
  have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hne)
  rw [hposR hxpos]
  by_cases hxa : (x : ℝ) ≤ a
  · rw [Set.indicator_of_mem (show x ∈ suzukiApertureSet a B from hxa)]
    rw [hR ⟨x.property.1, hxa⟩]
    symm
    rw [suzukiPhysicalIntervalZeroExtendFun_apply, hfrep]
  · rw [Set.indicator_of_notMem
      (show x ∉ suzukiApertureSet a B from hxa)]
    rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem]
    exact fun hx => hxa hx.2

theorem suzukiFixedWindowPhi_eq_extended
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hB : 1 < B) (haB : a ≤ B) :
    suzukiFixedWindowPhi epsilon omega B homega hB a =
      suzukiHankelPhiExtended epsilon omega a B homega ha haB := by
  apply suzukiHankelPhiExtended_unique epsilon homega ha haB
  rw [SuzukiHankelExtendedEquation,
    ← suzukiApertureCutoff_eq_inclusion_restriction a B]
  have hEq := suzukiFixedWindowPhi_equation_expanded epsilon homega hB a
  simpa only [suzukiFixedWindowBoundarySource,
    suzukiHankelExtendedBoundary, suzukiHankelBoundarySourceOn,
    eq_sub_iff_add_eq] using hEq

def suzukiFixedWindowPhiPoint
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ)
    (x : ClosedInterval 0 B) : ℂ :=
  suzukiSourceHFinite omega (a * (x : ℝ)) - epsilon.coeff *
    suzukiCompressedHankelContinuousOutput omega B (by linarith) hB
      (suzukiApertureCutoff a B
        (suzukiFixedWindowPhi epsilon omega B (by linarith) hB a)) x

theorem continuousAt_suzukiFixedWindowPhi
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 / 2 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    ContinuousAt (suzukiFixedWindowPhi epsilon omega B homega hB) a := by
  exact ((continuousOn_suzukiFixedWindowPhi epsilon homega hB).continuousAt
    (Icc_mem_nhds ha0 haB))

theorem continuousAt_suzukiFixedWindowPhiPoint
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B)
    (x : ClosedInterval 0 B) (hx : 0 < (x : ℝ)) :
    ContinuousAt (fun b =>
      suzukiFixedWindowPhiPoint epsilon omega B homega hB b x) a := by
  let u : ℝ → IntervalL2 0 B :=
    suzukiFixedWindowPhi epsilon omega B (by linarith) hB
  have hu : ContinuousAt u a :=
    continuousAt_suzukiFixedWindowPhi epsilon (by linarith) hB ha0 haB
  have hcut : ContinuousAt (fun b => suzukiApertureCutoff b B (u b)) a :=
    continuousAt_suzukiApertureCutoff_apply₂ B a hu
  have hout : ContinuousAt (fun b =>
      suzukiCompressedHankelContinuousOutput omega B (by linarith) hB
        (suzukiApertureCutoff b B (u b)) x) a := by
    change ContinuousAt (fun b =>
      suzukiCompressedHankelFunctionalContinuous omega B (by linarith) hB x
        (suzukiApertureCutoff b B (u b))) a
    exact (suzukiCompressedHankelFunctionalContinuous omega B (by linarith) hB x).continuous
      |>.continuousAt.comp hcut
  have hsource : ContinuousAt
      (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ))) a :=
    let hmul : ContinuousAt (fun b : ℝ => b * (x : ℝ)) a :=
      continuousAt_id.mul continuousAt_const
    (continuousAt_suzukiSourceHFinite homega (mul_pos ha0 hx)).comp_of_eq
      hmul rfl
  exact hsource.sub (continuousAt_const.mul hout)

theorem suzukiFixedWindowPhiPoint_eq_global
    (epsilon : SuzukiHankelSign) {omega a B : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hB : 1 < B) (haB : a ≤ B)
    (x : ClosedInterval 0 B) (hx : 0 < (x : ℝ)) :
    suzukiFixedWindowPhiPoint epsilon omega B homega hB a x =
      suzukiHankelPhiGlobal epsilon omega a homega ha (x : ℝ) := by
  let homegaHalf : 1 / 2 < omega := by linarith
  let phi := suzukiHankelPhi epsilon omega a homegaHalf ha
  let u := suzukiFixedWindowPhi epsilon omega B homegaHalf hB a
  have hcut : suzukiApertureCutoff a B u =
      suzukiPhysicalIntervalInclusion a B phi := by
    rw [suzukiApertureCutoff_eq_inclusion_restriction]
    rw [show u = suzukiHankelPhiExtended epsilon omega a B homegaHalf ha haB from
      suzukiFixedWindowPhi_eq_extended epsilon homegaHalf ha hB haB,
      suzukiHankelPhiExtended_restriction]
  rw [suzukiFixedWindowPhiPoint, suzukiHankelPhiGlobal,
    suzukiCompressedHankelContinuousOutput_eq_integral (by linarith) hB,
    hcut]
  rw [suzukiIntegral_physicalIntervalInclusion homegaHalf (by linarith) hB haB
    phi x hx]

def suzukiHankelPhiGlobalAperture
    (epsilon : SuzukiHankelSign) (omega x : ℝ) (homega : 1 < omega) :
    Ioi (1 : ℝ) → ℂ := fun a =>
  suzukiHankelPhiGlobal epsilon omega (a : ℝ) homega a.property x

theorem continuous_suzukiHankelPhiGlobalAperture
    (epsilon : SuzukiHankelSign) {omega x : ℝ}
    (homega : 1 < omega) (hx : 0 < x) :
    Continuous (suzukiHankelPhiGlobalAperture epsilon omega x homega) := by
  rw [continuous_iff_continuousAt]
  intro a
  let B : ℝ := max (a : ℝ) x + 1
  have haB : (a : ℝ) < B := by
    dsimp only [B]
    linarith [le_max_left (a : ℝ) x]
  have hxB : x < B := by
    dsimp only [B]
    linarith [le_max_right (a : ℝ) x]
  have hB : 1 < B := lt_trans a.property haB
  let xB : ClosedInterval 0 B := ⟨x, ⟨hx.le, hxB.le⟩⟩
  let localPhi : ℝ → ℂ := fun b =>
    suzukiFixedWindowPhiPoint epsilon omega B homega hB b xB
  have hlocal : ContinuousAt localPhi (a : ℝ) :=
    continuousAt_suzukiFixedWindowPhiPoint epsilon homega hB
      (lt_trans zero_lt_one a.property) haB xB hx
  have hlocalSubtype : ContinuousAt (fun b : Ioi (1 : ℝ) => localPhi (b : ℝ)) a :=
    hlocal.comp_of_eq continuousAt_subtype_val rfl
  have hbelow : ∀ᶠ b : Ioi (1 : ℝ) in 𝓝 a, (b : ℝ) < B :=
    continuousAt_subtype_val (Iio_mem_nhds haB)
  have heq : suzukiHankelPhiGlobalAperture epsilon omega x homega =ᶠ[𝓝 a]
      fun b : Ioi (1 : ℝ) => localPhi (b : ℝ) := by
    filter_upwards [hbelow] with b hbB
    change suzukiHankelPhiGlobal epsilon omega (b : ℝ) homega b.property x =
      suzukiFixedWindowPhiPoint epsilon omega B homega hB (b : ℝ) xB
    exact (suzukiFixedWindowPhiPoint_eq_global epsilon homega b.property hB hbB.le xB hx).symm
  exact hlocalSubtype.congr_of_eventuallyEq heq

end RHTower
