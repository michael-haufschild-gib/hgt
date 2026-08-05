import GaloisForLFunctions.HTGeometry.KleinGordonTunedSubband

/-!
# The tuned propagators as scalars on a sub-band

Restating the operator identities against an arbitrary sub-band. Two potentials of different rates
then act as different scalars on one and the same band, which is what makes their composition
computable.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section SubbandOps

variable {b c R : ℝ}

set_option maxHeartbeats 1000000 in
/-- **On a sub-band the shifted cosine propagator is the scalar `cos(ct)`.** -/
theorem kgShiftedCosOp_kgTunedPot_subband (hc0 : 0 < c) (hR : R ≤ Real.sqrt (c ^ 2 - 1 + b))
    (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedCosOp (measurable_kgTunedPot (E := E) b c).neg t (kgLowPassOp R x)
      = ((Real.cos (t * c) : ℝ) : ℂ) • kgLowPassOp R x := by
  have hprod : Measurable fun ξ : E =>
      kgShiftedCos (fun ζ : E => -(kgTunedPot b c ζ)) t ξ * kgLowPass R ξ :=
    (measurable_kgShiftedCos (measurable_kgTunedPot b c).neg t).mul (measurable_kgLowPass R)
  have hprodb : ∀ ξ : E, ‖kgShiftedCos (fun ζ : E => -(kgTunedPot b c ζ)) t ξ
      * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    exact mul_le_one₀ (norm_kgShiftedCos_le _ t ξ) (norm_nonneg _) (norm_kgLowPass_le R ξ)
  have hconst : Measurable fun ξ : E => ((Real.cos (t * c) : ℝ) : ℂ) * kgLowPass R ξ :=
    measurable_const.mul (measurable_kgLowPass R)
  have hconstb : ∀ ξ : E, ‖((Real.cos (t * c) : ℝ) : ℂ) * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_one₀ (Real.abs_cos_le_one _) (norm_nonneg _) (norm_kgLowPass_le R ξ)
  have hcomp : (kgShiftedCosOp (E := E) (measurable_kgTunedPot (E := E) b c).neg t).comp
      (kgLowPassOp R) = fourierMulCLM hprod zero_le_one hprodb := by
    rw [kgShiftedCosOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ zero_le_one hprodb
      (Eventually.of_forall fun _ => rfl)
  have heq : fourierMulCLM hprod zero_le_one hprodb = fourierMulCLM hconst zero_le_one hconstb :=
    fourierMulCLM_congr _ _ _ _ _ _
      (Eventually.of_forall (kgShiftedCos_kgTunedPot_subband (b := b) hc0 hR t))
  have hsmul : fourierMulCLM hconst zero_le_one hconstb
      = ((Real.cos (t * c) : ℝ) : ℂ) • kgLowPassOp (E := E) R := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_smul _ hconst zero_le_one (norm_kgLowPass_le R) zero_le_one hconstb _
      (Eventually.of_forall fun _ => rfl)
  rw [← ContinuousLinearMap.comp_apply, hcomp, heq, hsmul, smul_apply]

set_option maxHeartbeats 1000000 in
/-- **On a sub-band the shifted sine propagator is the scalar `sin(ct)/c`.** -/
theorem kgShiftedSinFreqOp_kgTunedPot_subband (hc0 : 0 < c) (hc1 : 1 ≤ c ^ 2)
    (hR : R ≤ Real.sqrt (c ^ 2 - 1 + b)) (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgShiftedSinFreqOp (measurable_kgTunedPot (E := E) b c).neg t (kgLowPassOp R x)
      = ((Real.sin (t * c) / c : ℝ) : ℂ) • kgLowPassOp R x := by
  have hcge := one_le_of_one_le_sq hc0 hc1
  have hprod : Measurable fun ξ : E =>
      kgShiftedSinOverFreq (fun ζ : E => -(kgTunedPot b c ζ)) t ξ * kgLowPass R ξ :=
    (measurable_kgShiftedSinOverFreq (measurable_kgTunedPot b c).neg t).mul
      (measurable_kgLowPass R)
  have hprodb : ∀ ξ : E, ‖kgShiftedSinOverFreq (fun ζ : E => -(kgTunedPot b c ζ)) t ξ
      * kgLowPass R ξ‖ ≤ |t| := by
    intro ξ
    rw [norm_mul]
    calc ‖kgShiftedSinOverFreq (fun ζ : E => -(kgTunedPot b c ζ)) t ξ‖ * ‖kgLowPass R ξ‖
        ≤ |t| * 1 := mul_le_mul (norm_kgShiftedSinOverFreq_le _ t ξ) (norm_kgLowPass_le R ξ)
          (norm_nonneg _) (abs_nonneg t)
      _ = |t| := mul_one _
  have hconst : Measurable fun ξ : E => ((Real.sin (t * c) / c : ℝ) : ℂ) * kgLowPass R ξ :=
    measurable_const.mul (measurable_kgLowPass R)
  have hconstb : ∀ ξ : E, ‖((Real.sin (t * c) / c : ℝ) : ℂ) * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hq : |Real.sin (t * c) / c| ≤ 1 := by
      rw [abs_div, abs_of_pos hc0, div_le_one hc0]
      exact le_trans (Real.abs_sin_le_one _) hcge
    exact mul_le_one₀ hq (norm_nonneg _) (norm_kgLowPass_le R ξ)
  have hcomp : (kgShiftedSinFreqOp (E := E) (measurable_kgTunedPot (E := E) b c).neg t).comp
      (kgLowPassOp R) = fourierMulCLM hprod (abs_nonneg t) hprodb := by
    rw [kgShiftedSinFreqOp, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ (abs_nonneg t) hprodb
      (Eventually.of_forall fun _ => rfl)
  have heq : fourierMulCLM hprod (abs_nonneg t) hprodb
      = fourierMulCLM hconst zero_le_one hconstb :=
    fourierMulCLM_congr _ _ _ _ _ _
      (Eventually.of_forall (kgShiftedSinOverFreq_kgTunedPot_subband (b := b) hc0 hR t))
  have hsmul : fourierMulCLM hconst zero_le_one hconstb
      = ((Real.sin (t * c) / c : ℝ) : ℂ) • kgLowPassOp (E := E) R := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_smul _ hconst zero_le_one (norm_kgLowPass_le R) zero_le_one hconstb _
      (Eventually.of_forall fun _ => rfl)
  rw [← ContinuousLinearMap.comp_apply, hcomp, heq, hsmul, smul_apply]

end SubbandOps

end GaloisForLFunctions.HTGeometry
