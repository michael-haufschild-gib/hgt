import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelL1Smoothing

/-!
# Suzuki canonical Hankel resolvent on `L¹`

This module transfers Suzuki's fixed-window resolvent from `L²` to `L¹` by an exact
Woodbury factorization.  The Hankel kernel smooths `L¹` input into `L²`, while the
finite-measure embedding returns `L²` output to `L¹`.  Hence invertibility of
`1 + V U` on `L²` gives an explicit two-sided inverse of `1 + U V` on `L¹` without
asserting a false `L¹` contraction estimate.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace
set_option maxHeartbeats 1000000

def suzukiIntervalL2ToL1Bound (B : ℝ) : ℝ :=
  ((volume : Measure (ClosedInterval 0 B)) Set.univ ^
    (1 / (1 : ℝ) - 1 / (2 : ℝ))).toReal

theorem norm_suzukiIntervalL2AsL1_le (B : ℝ) (f : IntervalL2 0 B) :
    ‖suzukiIntervalL2AsL1 B f‖ ≤ suzukiIntervalL2ToL1Bound B * ‖f‖ := by
  have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := (volume : Measure (ClosedInterval 0 B)))
    (p := (1 : ENNReal)) (q := (2 : ENNReal))
    (by norm_num : (1 : ENNReal) ≤ 2) (Lp.aestronglyMeasurable f)
  have hrightTop :
      eLpNorm (fun x : ClosedInterval 0 B => f x) 2 volume *
          (volume : Measure (ClosedInterval 0 B)) Set.univ ^
            (1 / (1 : ℝ) - 1 / (2 : ℝ)) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact (Lp.memLp f).eLpNorm_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness)
  have hreal := ENNReal.toReal_mono hrightTop hle
  rw [ENNReal.toReal_mul] at hreal
  rw [mul_comm] at hreal
  rw [suzukiIntervalL2ToL1Bound, Lp.norm_def, Lp.norm_def]
  have hae := suzukiIntervalL2AsL1_ae B f
  rw [eLpNorm_congr_ae hae]
  exact hreal

def suzukiIntervalL2ToL1 (B : ℝ) :
    IntervalL2 0 B →L[ℂ] IntervalL1 0 B :=
  LinearMap.mkContinuous
    { toFun := suzukiIntervalL2AsL1 B
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [suzukiIntervalL2AsL1_ae B (f + g),
          Lp.coeFn_add f g,
          suzukiIntervalL2AsL1_ae B f,
          suzukiIntervalL2AsL1_ae B g,
          Lp.coeFn_add (suzukiIntervalL2AsL1 B f)
            (suzukiIntervalL2AsL1 B g)] with x hfg hadd hf hg haddL1
        rw [hfg, hadd, haddL1]
        simp only [Pi.add_apply]
        rw [hf, hg]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [suzukiIntervalL2AsL1_ae B (c • f),
          Lp.coeFn_smul c f,
          suzukiIntervalL2AsL1_ae B f,
          Lp.coeFn_smul c (suzukiIntervalL2AsL1 B f)] with x hcf hsmul hf hsmulL1
        rw [hcf, hsmul]
        change (c • (f : ClosedInterval 0 B → ℂ)) x =
          ((c • suzukiIntervalL2AsL1 B f : IntervalL1 0 B) :
            ClosedInterval 0 B → ℂ) x
        rw [hsmulL1]
        simp only [Pi.smul_apply]
        rw [hf] }
    (suzukiIntervalL2ToL1Bound B)
    (norm_suzukiIntervalL2AsL1_le B)

@[simp] theorem suzukiIntervalL2ToL1_apply (B : ℝ) (f : IntervalL2 0 B) :
    suzukiIntervalL2ToL1 B f = suzukiIntervalL2AsL1 B f := rfl

def suzukiApertureCutoffL1 (a B : ℝ) :
    IntervalL1 0 B →L[ℂ] IntervalL1 0 B :=
  lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ)
    (volume : Measure (ClosedInterval 0 B)) 1
    (suzukiApertureSet a B) (measurableSet_suzukiApertureSet a B)

theorem suzukiApertureCutoffL1_ae
    (a B : ℝ) (f : IntervalL1 0 B) :
    suzukiApertureCutoffL1 a B f =ᵐ[volume]
      (suzukiApertureSet a B).indicator f := by
  exact lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ)
    (volume : Measure (ClosedInterval 0 B)) 1
    (suzukiApertureSet a B) (measurableSet_suzukiApertureSet a B) f

theorem suzukiApertureCutoffL1_asL1
    (a B : ℝ) (f : IntervalL2 0 B) :
    suzukiApertureCutoffL1 a B (suzukiIntervalL2AsL1 B f) =
      suzukiIntervalL2AsL1 B (suzukiApertureCutoff a B f) := by
  apply Lp.ext
  filter_upwards [suzukiApertureCutoffL1_ae a B (suzukiIntervalL2AsL1 B f),
    suzukiIntervalL2AsL1_ae B f,
    suzukiIntervalL2AsL1_ae B (suzukiApertureCutoff a B f),
    suzukiApertureCutoff_ae a B f] with x hleft hf hright hcut
  rw [hleft, hright, hcut]
  by_cases hx : x ∈ suzukiApertureSet a B <;> simp [hx, hf]

theorem suzukiCompressedHankelL1ToL2_cutoff_asL1
    (omega a B : ℝ) (homega : 1 < omega) (hB : 1 < B)
    (f : IntervalL2 0 B) :
    suzukiCompressedHankelL1ToL2 omega B homega
        (suzukiApertureCutoffL1 a B (suzukiIntervalL2AsL1 B f)) =
      suzukiCompressedHankelOperator omega B (by linarith)
        (suzukiApertureCutoff a B f) := by
  rw [suzukiApertureCutoffL1_asL1,
    suzukiCompressedHankelL1ToL2_asL1 omega B homega hB]

def suzukiFixedWindowSignedSectionL1
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (a : ℝ) :
    IntervalL1 0 B →L[ℂ] IntervalL1 0 B :=
  epsilon.coeff •
    (suzukiIntervalL2ToL1 B ∘L
      suzukiCompressedHankelL1ToL2 omega B homega ∘L
      suzukiApertureCutoffL1 a B)

theorem suzukiFixedWindowSignedSectionL1_asL1
    (epsilon : SuzukiHankelSign) (omega a B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (f : IntervalL2 0 B) :
    suzukiFixedWindowSignedSectionL1 epsilon omega B homega a
        (suzukiIntervalL2AsL1 B f) =
      suzukiIntervalL2AsL1 B
        (suzukiFixedWindowSignedSection epsilon omega B (by linarith) a f) := by
  rw [suzukiFixedWindowSignedSectionL1, suzukiFixedWindowSignedSection,
    smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    suzukiCompressedHankelL1ToL2_cutoff_asL1 omega a B homega hB]
  change epsilon.coeff • suzukiIntervalL2ToL1 B
      (suzukiCompressedHankelOperator omega B (by linarith)
        (suzukiApertureCutoff a B f)) =
    suzukiIntervalL2ToL1 B
      (epsilon.coeff • suzukiCompressedHankelOperator omega B (by linarith)
        (suzukiApertureCutoff a B f))
  rw [map_smul]

def suzukiFixedWindowL1Lift
    (epsilon : SuzukiHankelSign) (B : ℝ) :
    IntervalL2 0 B →L[ℂ] IntervalL1 0 B :=
  epsilon.coeff • suzukiIntervalL2ToL1 B

def suzukiFixedWindowL1Section
    (omega a B : ℝ) (homega : 1 < omega) :
    IntervalL1 0 B →L[ℂ] IntervalL2 0 B :=
  suzukiCompressedHankelL1ToL2 omega B homega ∘L
    suzukiApertureCutoffL1 a B

theorem suzukiFixedWindowL1Section_lift
    (epsilon : SuzukiHankelSign) (omega a B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (f : IntervalL2 0 B) :
    suzukiFixedWindowL1Section omega a B homega
        (suzukiFixedWindowL1Lift epsilon B f) =
      suzukiFixedWindowSignedSection epsilon omega B (by linarith) a f := by
  rw [suzukiFixedWindowL1Section, suzukiFixedWindowL1Lift,
    ContinuousLinearMap.comp_apply, smul_apply, map_smul, map_smul,
    suzukiIntervalL2ToL1_apply,
    suzukiCompressedHankelL1ToL2_cutoff_asL1 omega a B homega hB,
    suzukiFixedWindowSignedSection, smul_apply,
    ContinuousLinearMap.comp_apply]

theorem suzukiFixedWindowSignedSectionL1_eq_lift_section
    (epsilon : SuzukiHankelSign) (omega a B : ℝ)
    (homega : 1 < omega) :
    suzukiFixedWindowSignedSectionL1 epsilon omega B homega a =
      suzukiFixedWindowL1Lift epsilon B ∘L
        suzukiFixedWindowL1Section omega a B homega := by
  rfl

def suzukiFixedWindowResolventOperatorL1
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (a : ℝ) :
    IntervalL1 0 B →L[ℂ] IntervalL1 0 B :=
  1 + suzukiFixedWindowSignedSectionL1 epsilon omega B homega a

def suzukiFixedWindowResolventOperatorL2Inverse
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) :
    IntervalL2 0 B →L[ℂ] IntervalL2 0 B :=
  let hunit := suzukiFixedWindowResolventOperator_isUnit epsilon
    (omega := omega) (B := B) (by linarith) hB a
  ↑(hunit.unit⁻¹)

theorem suzukiFixedWindowResolventOperator_apply_inverseL2
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) (f : IntervalL2 0 B) :
    suzukiFixedWindowResolventOperator epsilon omega B (by linarith) a
        (suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a f) = f := by
  let hunit := suzukiFixedWindowResolventOperator_isUnit epsilon
    (omega := omega) (B := B) (by linarith) hB a
  let U := hunit.unit
  have hU : (↑U : IntervalL2 0 B →L[ℂ] IntervalL2 0 B) =
      suzukiFixedWindowResolventOperator epsilon omega B (by linarith) a :=
    hunit.unit_spec
  rw [← hU]
  change (↑U : IntervalL2 0 B →L[ℂ] IntervalL2 0 B)
      ((↑(U⁻¹) : IntervalL2 0 B →L[ℂ] IntervalL2 0 B) f) = f
  rw [← mul_apply_eq_comp, Units.mul_inv]
  simp

theorem suzukiFixedWindowResolventOperator_inverseL2_apply
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) (f : IntervalL2 0 B) :
    suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a
        (suzukiFixedWindowResolventOperator epsilon omega B (by linarith) a f) = f := by
  let hunit := suzukiFixedWindowResolventOperator_isUnit epsilon
    (omega := omega) (B := B) (by linarith) hB a
  let U := hunit.unit
  have hU : (↑U : IntervalL2 0 B →L[ℂ] IntervalL2 0 B) =
      suzukiFixedWindowResolventOperator epsilon omega B (by linarith) a :=
    hunit.unit_spec
  rw [← hU]
  change (↑(U⁻¹) : IntervalL2 0 B →L[ℂ] IntervalL2 0 B)
      ((↑U : IntervalL2 0 B →L[ℂ] IntervalL2 0 B) f) = f
  rw [← mul_apply_eq_comp, Units.inv_mul]
  simp

def suzukiFixedWindowResolventOperatorL1Inverse
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) :
    IntervalL1 0 B →L[ℂ] IntervalL1 0 B :=
  1 - suzukiFixedWindowL1Lift epsilon B ∘L
    suzukiFixedWindowResolventOperatorL2Inverse epsilon omega B homega hB a ∘L
    suzukiFixedWindowL1Section omega a B homega

theorem suzukiFixedWindowResolventOperatorL1_apply_inverse
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) (g : IntervalL1 0 B) :
    suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a
        (suzukiFixedWindowResolventOperatorL1Inverse
          epsilon omega B homega hB a g) = g := by
  let U := suzukiFixedWindowL1Lift epsilon B
  let V := suzukiFixedWindowL1Section omega a B homega
  let R := suzukiFixedWindowResolventOperatorL2Inverse
    epsilon omega B homega hB a
  have hR := suzukiFixedWindowResolventOperator_apply_inverseL2
    epsilon omega B homega hB a (V g)
  have hVU : V (U (R (V g))) =
      suzukiFixedWindowSignedSection epsilon omega B (by linarith) a (R (V g)) := by
    exact suzukiFixedWindowL1Section_lift epsilon omega a B homega hB (R (V g))
  rw [suzukiFixedWindowResolventOperator, add_apply,
    one_apply_eq_self] at hR
  rw [← hVU] at hR
  have hUR := congrArg U hR
  rw [map_add] at hUR
  rw [suzukiFixedWindowResolventOperatorL1,
    suzukiFixedWindowSignedSectionL1_eq_lift_section,
    suzukiFixedWindowResolventOperatorL1Inverse]
  change ((1 : IntervalL1 0 B →L[ℂ] IntervalL1 0 B) + U ∘L V)
      (((1 : IntervalL1 0 B →L[ℂ] IntervalL1 0 B) - U ∘L R ∘L V) g) = g
  simp only [add_apply, sub_apply,
    one_apply_eq_self, ContinuousLinearMap.comp_apply,
    map_sub]
  rw [← hUR]
  abel

theorem suzukiFixedWindowResolventOperatorL1_inverse_apply
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ) (g : IntervalL1 0 B) :
    suzukiFixedWindowResolventOperatorL1Inverse
        epsilon omega B homega hB a
        (suzukiFixedWindowResolventOperatorL1 epsilon omega B homega a g) = g := by
  let U := suzukiFixedWindowL1Lift epsilon B
  let V := suzukiFixedWindowL1Section omega a B homega
  let R := suzukiFixedWindowResolventOperatorL2Inverse
    epsilon omega B homega hB a
  have hR := suzukiFixedWindowResolventOperator_inverseL2_apply
    epsilon omega B homega hB a (V g)
  have hVU : V (U (V g)) =
      suzukiFixedWindowSignedSection epsilon omega B (by linarith) a (V g) := by
    exact suzukiFixedWindowL1Section_lift epsilon omega a B homega hB (V g)
  rw [suzukiFixedWindowResolventOperator, add_apply,
    one_apply_eq_self] at hR
  rw [← hVU] at hR
  have hR' : R (V (g + U (V g))) = V g := by
    rw [map_add V]
    exact hR
  rw [suzukiFixedWindowResolventOperatorL1,
    suzukiFixedWindowSignedSectionL1_eq_lift_section,
    suzukiFixedWindowResolventOperatorL1Inverse]
  change ((1 : IntervalL1 0 B →L[ℂ] IntervalL1 0 B) - U ∘L R ∘L V)
      (((1 : IntervalL1 0 B →L[ℂ] IntervalL1 0 B) + U ∘L V) g) = g
  simp only [add_apply, sub_apply,
    one_apply_eq_self, ContinuousLinearMap.comp_apply]
  rw [hR']
  abel

end RHTower
