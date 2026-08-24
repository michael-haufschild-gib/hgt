import GaloisForLFunctions.RHTower.ReflectedBiHeatCompletedChannels

/-!
# Phase-side finite-part expansion of the reflected bi-heat pairing

This module assembles the exact regulator-zero Jonquière channels.  The singular--singular finite
part is the logarithmic/digamma anomaly, the two cross terms are exact heat moments, the regular
product is `zeta(z) zeta(1-z)`, and the sharp subtracted remainder tends to zero.  Replacing the two
heat moments by their Gaussian main terms yields the literal displayed small-aperture expansion.
-/

open Complex Filter Topology Set

namespace RHTower

/-- Raw coefficient multiplying the `z-1` full-window heat moment. -/
noncomputable def reflectedBiHeatLeftRawCoefficient (z : ℂ) : ℂ :=
  ((jonquiereLead z + jonquiereLeadNeg z) / 2) * riemannZeta (1 - z)

/-- Raw coefficient multiplying the `-z` full-window heat moment. -/
noncomputable def reflectedBiHeatRightRawCoefficient (z : ℂ) : ℂ :=
  riemannZeta z *
    ((jonquiereLead (1 - z) + jonquiereLeadNeg (1 - z)) / 2)

/-- Universal logarithmic/digamma finite-part anomaly, formula `(7)`. -/
noncomputable def reflectedBiHeatAnomaly (z : ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.sqrt x) : ℂ) *
    ((Real.log (4 * Real.pi * x) : ℂ) -
      (Real.eulerMascheroniConstant : ℂ) -
      Complex.digamma z - Complex.digamma (1 - z))

theorem reflectedBiHeatAnomaly_eq_singularFinitePart (P : ReflectedBiHeatRegulator) :
    reflectedBiHeatAnomaly P.z P.x =
      deriv (reflectedSingularPoleUnit P) 0 := by
  rw [deriv_reflectedSingularPoleUnit_zero_eq_anomaly]
  rfl

/-- Exact phase-side finite part: anomaly, two full-window cross moments, regular product, and the
subtracted Jonquière remainder. -/
noncomputable def reflectedBiHeatPhaseFinitePart
    (P : ReflectedBiHeatRegulator) (x : ℝ) : ℂ :=
  reflectedBiHeatAnomaly P.z x
    + reflectedBiHeatLeftRawCoefficient P.z * heatMoment x (P.z - 1)
    + reflectedBiHeatRightRawCoefficient P.z * heatMoment x (-P.z)
    + riemannZeta P.z * riemannZeta (1 - P.z)
    + reflectedBiHeatSharpRemainder P x

/-- Same four principal channels with exact heat moments replaced by their Gaussian main terms. -/
noncomputable def reflectedBiHeatPhaseGaussianModel
    (P : ReflectedBiHeatRegulator) (x : ℝ) : ℂ :=
  reflectedBiHeatAnomaly P.z x
    + reflectedBiHeatLeftRawCoefficient P.z * heatMomentTerm x (P.z - 1)
    + reflectedBiHeatRightRawCoefficient P.z * heatMomentTerm x (-P.z)
    + riemannZeta P.z * riemannZeta (1 - P.z)

/-- Literal card model in equation `(3)`. -/
noncomputable def reflectedBiHeatCardExpansion
    (P : ReflectedBiHeatRegulator) (x : ℝ) : ℂ :=
  reflectedBiHeatAnomaly P.z x
    + (1 / 2 * reflectedCompletedLambda P.z) *
        ((x : ℂ) ^ ((P.z - 1) / 2))
    + (1 / 2 * reflectedCompletedLambda P.z) *
        ((x : ℂ) ^ (-P.z / 2))
    + riemannZeta P.z * riemannZeta (1 - P.z)

theorem reflectedBiHeatLeftRaw_mul_heatMomentTerm
    (P : ReflectedBiHeatRegulator) {x : ℝ} (hx : 0 < x) :
    reflectedBiHeatLeftRawCoefficient P.z * heatMomentTerm x (P.z - 1) =
      (1 / 2 * reflectedCompletedLambda P.z) *
        ((x : ℂ) ^ ((P.z - 1) / 2)) := by
  have havg := averagedLead_mul_heatMomentTerm (s := P.z) hx
  calc
    reflectedBiHeatLeftRawCoefficient P.z * heatMomentTerm x (P.z - 1) =
        (((jonquiereLead P.z + jonquiereLeadNeg P.z) / 2) *
          heatMomentTerm x (P.z - 1)) * riemannZeta (1 - P.z) := by
            rw [reflectedBiHeatLeftRawCoefficient]
            ring
    _ = heatEchoC P.z * ((x : ℂ) ^ ((P.z - 1) / 2)) *
          riemannZeta (1 - P.z) := by rw [havg]
    _ = reflectedBiHeatLeftCrossCoefficient P.z *
          ((x : ℂ) ^ ((P.z - 1) / 2)) := by
            rw [reflectedBiHeatLeftCrossCoefficient]
            ring
    _ = (1 / 2 * reflectedCompletedLambda P.z) *
          ((x : ℂ) ^ ((P.z - 1) / 2)) := by
            rw [reflectedBiHeatLeftCrossCoefficient_eq_completed P,
              reflectedCompletedLambda_one_sub P]

theorem reflectedBiHeatRightRaw_mul_heatMomentTerm
    (P : ReflectedBiHeatRegulator) {x : ℝ} (hx : 0 < x) :
    reflectedBiHeatRightRawCoefficient P.z * heatMomentTerm x (-P.z) =
      (1 / 2 * reflectedCompletedLambda P.z) *
        ((x : ℂ) ^ (-P.z / 2)) := by
  have havg := averagedLead_mul_heatMomentTerm (s := 1 - P.z) hx
  have harg : (1 - P.z) - 1 = -P.z := by ring
  rw [harg] at havg
  calc
    reflectedBiHeatRightRawCoefficient P.z * heatMomentTerm x (-P.z) =
        riemannZeta P.z *
          (((jonquiereLead (1 - P.z) + jonquiereLeadNeg (1 - P.z)) / 2) *
            heatMomentTerm x (-P.z)) := by
              rw [reflectedBiHeatRightRawCoefficient]
              ring
    _ = riemannZeta P.z *
          (heatEchoC (1 - P.z) * ((x : ℂ) ^ (-P.z / 2))) := by
            rw [havg]
    _ = reflectedBiHeatRightCrossCoefficient P.z *
          ((x : ℂ) ^ (-P.z / 2)) := by
            rw [reflectedBiHeatRightCrossCoefficient]
            ring
    _ = (1 / 2 * reflectedCompletedLambda P.z) *
          ((x : ℂ) ^ (-P.z / 2)) := by
            rw [reflectedBiHeatRightCrossCoefficient_eq_completed P]

theorem reflectedBiHeatPhaseGaussianModel_eq_cardExpansion
    (P : ReflectedBiHeatRegulator) {x : ℝ} (hx : 0 < x) :
    reflectedBiHeatPhaseGaussianModel P x = reflectedBiHeatCardExpansion P x := by
  rw [reflectedBiHeatPhaseGaussianModel, reflectedBiHeatCardExpansion,
    reflectedBiHeatLeftRaw_mul_heatMomentTerm P hx,
    reflectedBiHeatRightRaw_mul_heatMomentTerm P hx]

/-- The exact phase-side finite part has the full small-aperture expansion `(3)`. -/
theorem tendsto_reflectedBiHeatPhaseFinitePart_sub_cardExpansion
    (P : ReflectedBiHeatRegulator) :
    Tendsto (fun x : ℝ =>
      reflectedBiHeatPhaseFinitePart P x - reflectedBiHeatCardExpansion P x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hz : -1 < (P.z - 1).re := by simp; linarith [P.z_re_pos]
  have h1z : -1 < (-P.z).re := by simp; linarith [P.z_re_lt_one]
  have hleft := (tendsto_heatMoment_sub_term_of_neg_one_lt_re hz).const_mul
    (reflectedBiHeatLeftRawCoefficient P.z)
  have hright := (tendsto_heatMoment_sub_term_of_neg_one_lt_re h1z).const_mul
    (reflectedBiHeatRightRawCoefficient P.z)
  rw [mul_zero] at hleft hright
  have hrem := tendsto_reflectedBiHeatSharpRemainder P
  have hsum := (hleft.add hright).add hrem
  rw [zero_add, zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [← reflectedBiHeatPhaseGaussianModel_eq_cardExpansion P hx]
  rw [reflectedBiHeatPhaseFinitePart, reflectedBiHeatPhaseGaussianModel]
  ring

/-- Premise-free phase-expansion capstone. -/
theorem reflectedBiHeatPhaseExpansion_capstone :
    ∀ P : ReflectedBiHeatRegulator,
      Tendsto (fun x : ℝ =>
        reflectedBiHeatPhaseFinitePart P x - reflectedBiHeatCardExpansion P x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro P
  exact tendsto_reflectedBiHeatPhaseFinitePart_sub_cardExpansion P

end RHTower
