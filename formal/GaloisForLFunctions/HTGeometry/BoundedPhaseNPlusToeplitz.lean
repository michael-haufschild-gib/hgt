import GaloisForLFunctions.HTGeometry.BoundedPhaseHardyHalfToeplitz
import GaloisForLFunctions.HTGeometry.DiskSmirnovRadialL1
import GaloisForLFunctions.HTGeometry.SmirnovToeplitzNPlus

/-!
# Measurable bounded phases at the `N¹` endpoint

Apply the existing half-power construction to half the phase.  Linearity of the Herglotz lift
turns the already proved square-root radial estimate into a genuine `L¹` estimate.  This is the
measurable `p = 1` endpoint needed by the oriented Kapustin collision.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Half of a real circle phase. -/
def halfBoundedPhase (b : Circle → ℝ) (z : Circle) : ℝ := b z / 2

theorem measurable_halfBoundedPhase {b : Circle → ℝ} (hb : Measurable b) :
    Measurable (halfBoundedPhase b) := by
  change Measurable fun z => b z * (2 : ℝ)⁻¹
  exact hb.mul_const _

theorem abs_halfBoundedPhase_le
    {b : Circle → ℝ} (hbound : ∀ z, |b z| ≤ Real.pi / 2) (z : Circle) :
    |halfBoundedPhase b z| ≤ Real.pi / 2 := by
  rw [halfBoundedPhase, abs_div]
  norm_num
  linarith [hbound z, Real.pi_pos]

/-- The Herglotz transform is linear under halving of the boundary datum. -/
theorem hardyFun_boundedPhaseHardy_half
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2)
    {w : ℂ} (hw : ‖w‖ < 1) :
    hardyFun
        (boundedPhaseHardy (halfBoundedPhase b)
          (measurable_halfBoundedPhase hb)
          (abs_halfBoundedPhase_le hbound)) w =
      hardyFun (boundedPhaseHardy b hb hbound) w / 2 := by
  rw [boundedPhaseHardy, boundedPhaseHardy,
    hardyFun_boundedRealHerglotzHardy_eq_integral _ _ _ _ hw,
    hardyFun_boundedRealHerglotzHardy_eq_integral _ _ _ _ hw]
  have hpoint : (fun z : Circle =>
      ((halfBoundedPhase b z : ℝ) : ℂ) * circleHerglotzKernel w z) =
      fun z : Circle => (2 : ℂ)⁻¹ *
        ((b z : ℂ) * circleHerglotzKernel w z) := by
    funext z
    simp only [halfBoundedPhase]
    push_cast
    ring
  rw [hpoint, integral_const_mul]
  ring

/-- The reciprocal quotient for the halved datum is the analytic half-value already constructed
for the original datum. -/
theorem boundedPhaseReciprocal_half_radial_eq_halfValue
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) (n : ℕ) (z : Circle) :
    (boundedPhaseReciprocal (halfBoundedPhase b)
      (measurable_halfBoundedPhase hb)
      (abs_halfBoundedPhase_le hbound)).radialBoundaryFun n z =
        boundedPhaseHalfValue b hb hbound
          ((hardyDiskAbelRadius n : ℂ) * (z : ℂ)) := by
  let w : ℂ := (hardyDiskAbelRadius n : ℂ) * (z : ℂ)
  have hw : ‖w‖ < 1 := by
    change ‖(hardyDiskAbelRadius n : ℂ) * (z : ℂ)‖ < 1
    rw [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hardyDiskAbelRadius_nonneg n), Circle.norm_coe, mul_one]
    exact hardyDiskAbelRadius_lt_one n
  let Hhalf := boundedPhaseHardy (halfBoundedPhase b)
    (measurable_halfBoundedPhase hb) (abs_halfBoundedPhase_le hbound)
  let v := hardyFun Hhalf w
  have hvBound : |v.re| ≤ Real.pi / 2 :=
    boundedPhaseHardy_re_bound (halfBoundedPhase b)
      (measurable_halfBoundedPhase hb) (abs_halfBoundedPhase_le hbound) w hw
  have he : sectorExponential v ≠ 0 := sectorExponential_ne_zero v
  have hden : sectorExponential v + 1 ≠ 0 :=
    add_one_ne_zero_of_re_nonneg (sectorExponential_re_nonneg hvBound)
  have hquot : (1 - sectorCayleyValue v) / (1 + sectorCayleyValue v) =
      (sectorExponential v)⁻¹ := by
    unfold sectorCayleyValue
    field_simp [hden, he]
    ring
  change (1 - sectorCayleyValue v) / (1 + sectorCayleyValue v) =
    Complex.exp (-I * hardyFun (boundedPhaseHardy b hb hbound) w / 2)
  rw [hquot, sectorExponential, ← Complex.exp_neg]
  congr 1
  have hhalf := hardyFun_boundedPhaseHardy_half b hb hbound hw
  change hardyFun Hhalf w = hardyFun (boundedPhaseHardy b hb hbound) w / 2 at hhalf
  change -(I * v) = -I * hardyFun (boundedPhaseHardy b hb hbound) w / 2
  rw [show v = hardyFun (boundedPhaseHardy b hb hbound) w / 2 from hhalf]
  ring

theorem circleIntegral_boundedPhaseReciprocal_half_norm_le
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) (n : ℕ) :
    (∫ z : Circle,
        ‖(boundedPhaseReciprocal (halfBoundedPhase b)
          (measurable_halfBoundedPhase hb)
          (abs_halfBoundedPhase_le hbound)).radialBoundaryFun n z‖
          ∂circleLebesgue) ≤
      (2 * Real.pi)⁻¹ *
        (2 * (((2 * Real.pi : ℂ) * boundedPhaseHalfValue b hb hbound 0).re)) := by
  calc
    (∫ z : Circle,
        ‖(boundedPhaseReciprocal (halfBoundedPhase b)
          (measurable_halfBoundedPhase hb)
          (abs_halfBoundedPhase_le hbound)).radialBoundaryFun n z‖
          ∂circleLebesgue) =
        ∫ z : Circle,
          Real.sqrt ‖(boundedPhaseReciprocal b hb hbound).radialBoundaryFun n z‖
            ∂circleLebesgue := by
      apply integral_congr_ae
      filter_upwards with z
      rw [boundedPhaseReciprocal_half_radial_eq_halfValue b hb hbound n z,
        boundedPhaseReciprocal_radial_sqrt_eq b hb hbound n z]
    _ ≤ _ := circleIntegral_boundedPhaseReciprocal_radial_sqrt_le b hb hbound n

/-- The reciprocal quotient for half the datum has an actual `L¹` circle boundary. -/
theorem integrable_circleBoundary_boundedPhaseReciprocal_half
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    Integrable
      (boundedPhaseReciprocal (halfBoundedPhase b)
        (measurable_halfBoundedPhase hb)
        (abs_halfBoundedPhase_le hbound)).circleBoundary
      circleLebesgue := by
  apply DiskSmirnovBoundary.integrable_circleBoundary_of_uniform_radial_norm
    (C := (2 * Real.pi)⁻¹ *
      (2 * (((2 * Real.pi : ℂ) * boundedPhaseHalfValue b hb hbound 0).re)))
  exact circleIntegral_boundedPhaseReciprocal_half_norm_le b hb hbound

private theorem standardCauchyWeight_le_inv_pi (x : ℝ) :
    standardCauchyWeight x ≤ Real.pi⁻¹ := by
  rw [standardCauchyWeight]
  have hone : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hden : Real.pi ≤ Real.pi * (1 + x ^ 2) := by
    simpa using mul_le_mul_of_nonneg_left hone Real.pi_pos.le
  simpa only [one_div] using one_div_le_one_div_of_le Real.pi_pos hden

/-- The fourth-order Cayley decay transports the circle `L¹` endpoint to Lebesgue measure on the
line. -/
theorem integrable_boundary_boundedPhaseHalfForward_half
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    Integrable
      (boundedPhaseHalfForward (halfBoundedPhase b)
        (measurable_halfBoundedPhase hb)
        (abs_halfBoundedPhase_le hbound)).boundary := by
  let c := halfBoundedPhase b
  let hc := measurable_halfBoundedPhase hb
  let hcbound := abs_halfBoundedPhase_le hbound
  let R := boundedPhaseReciprocal c hc hcbound
  let F := boundedPhaseHalfForward c hc hcbound
  let hCircle : Circle → ℝ := fun z => ‖R.circleBoundary z‖
  have hCircleInt : Integrable hCircle circleLebesgue :=
    (integrable_circleBoundary_boundedPhaseReciprocal_half b hb hbound).norm
  have hWeighted : Integrable (hCircle ∘ circleCayley)
      ((volume : Measure ℝ).withDensity (realDensity standardCauchyWeight)) :=
    (circleCayley_weighted_measurePreserving.integrable_comp
      hCircleInt.aestronglyMeasurable).2 hCircleInt
  have hWeightedLeb : Integrable (fun x : ℝ =>
      hCircle (circleCayley x) * standardCauchyWeight x) volume := by
    have hw := (integrable_withDensity_iff
      (measurable_realDensity measurable_standardCauchyWeight)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hWeighted
    simpa only [Function.comp_apply, realDensity, ENNReal.toReal_ofReal,
      (standardCauchyWeight_pos _).le] using hw
  have hMajorant : Integrable (fun x : ℝ =>
      (16 * Real.pi) *
        (hCircle (circleCayley x) * standardCauchyWeight x)) volume :=
    hWeightedLeb.const_mul (16 * Real.pi)
  have hMul := diskMultiplierLineBoundary_mul_ae
    oneSubDiskMultiplierFourth (boundedPhaseMinus c hc hcbound)
  have hA := diskMultiplierLineBoundary_oneSubDiskMultiplierFourth_ae
  have hR := DiskSmirnovBoundary.boundary_eq_circleBoundary_cayley_ae R
  apply hMajorant.mono'
  · exact F.measurable_boundary.aestronglyMeasurable
  · filter_upwards [hMul, hA, hR] with x hxMul hxA hxR
    have hfactor : F.boundary x =
        diskMultiplierLineBoundary oneSubDiskMultiplierFourth x * R.boundary x := by
      change diskMultiplierLineBoundary
          (oneSubDiskMultiplierFourth.mul (boundedPhaseMinus c hc hcbound)) x /
            diskMultiplierLineBoundary (boundedPhasePlus c hc hcbound) x = _
      rw [hxMul]
      change _ = diskMultiplierLineBoundary oneSubDiskMultiplierFourth x *
        (diskMultiplierLineBoundary (boundedPhaseMinus c hc hcbound) x /
          diskMultiplierLineBoundary (boundedPhasePlus c hc hcbound) x)
      ring
    change ‖F.boundary x‖ ≤
      (16 * Real.pi) *
        (hCircle (circleCayley x) * standardCauchyWeight x)
    rw [hfactor, norm_mul, hxA, norm_pow, hxR]
    have hfourth : ‖1 - realCayley x‖ ^ 4 =
        (4 * Real.pi * standardCauchyWeight x) ^ 2 := by
      rw [show ‖1 - realCayley x‖ ^ 4 =
          (‖1 - realCayley x‖ ^ 2) ^ 2 by ring,
        norm_one_sub_realCayley_sq]
    rw [hfourth]
    have hw0 : 0 ≤ standardCauchyWeight x := (standardCauchyWeight_pos x).le
    have hpiw : Real.pi * standardCauchyWeight x ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (standardCauchyWeight_le_inv_pi x)
        Real.pi_pos.le
      simpa [Real.pi_ne_zero] using h
    have hbase : (4 * Real.pi * standardCauchyWeight x) ^ 2 ≤
        16 * Real.pi * standardCauchyWeight x := by
      have hpw0 : 0 ≤ Real.pi * standardCauchyWeight x :=
        mul_nonneg Real.pi_pos.le hw0
      have hprod : 0 ≤ (Real.pi * standardCauchyWeight x) *
          (1 - Real.pi * standardCauchyWeight x) :=
        mul_nonneg hpw0 (sub_nonneg.mpr hpiw)
      nlinarith
    calc
      (4 * Real.pi * standardCauchyWeight x) ^ 2 *
          ‖R.circleBoundary (circleCayley x)‖ ≤
        (16 * Real.pi * standardCauchyWeight x) *
          ‖R.circleBoundary (circleCayley x)‖ :=
        mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
      _ = (16 * Real.pi) *
          (hCircle (circleCayley x) * standardCauchyWeight x) := by ring

/-- Toeplitz symbol carrying the undoubled bounded phase. -/
def boundedPhaseOneToeplitzSymbol (b : Circle → ℝ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) ((realCayley x) ^ 4) *
    Complex.exp (I * (b (circleCayley x) : ℂ))

theorem boundedPhaseToeplitzSymbol_half_eq
    (b : Circle → ℝ) :
    boundedPhaseToeplitzSymbol (halfBoundedPhase b) =
      boundedPhaseOneToeplitzSymbol b := by
  funext x
  rw [boundedPhaseToeplitzSymbol, boundedPhaseOneToeplitzSymbol]
  congr 2
  simp only [halfBoundedPhase]
  push_cast
  ring

/-- Measurable bounded phase at `p = 1`, packaged in the literal local-`L¹` Smirnov class. -/
noncomputable def boundedPhaseSmirnovToeplitzNPlusOneElement
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    SmirnovToeplitzNPlusElement (boundedPhaseOneToeplitzSymbol b) :=
  ({ toSmirnovToeplitzKernelElement :=
      (boundedPhaseSmirnovToeplitzHalfElement (halfBoundedPhase b)
        (measurable_halfBoundedPhase hb)
        (abs_halfBoundedPhase_le hbound)).toSmirnovToeplitzKernelElement
     forward_locallyIntegrable :=
      (integrable_boundary_boundedPhaseHalfForward_half b hb hbound).locallyIntegrable } :
    SmirnovToeplitzNPlusElement
      (boundedPhaseToeplitzSymbol (halfBoundedPhase b))).congr
        (Filter.Eventually.of_forall fun x =>
          congrFun (boundedPhaseToeplitzSymbol_half_eq b) x)

end

end GaloisForLFunctions.HTGeometry
