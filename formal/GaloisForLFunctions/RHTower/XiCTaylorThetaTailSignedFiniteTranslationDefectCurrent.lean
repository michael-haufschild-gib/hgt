import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSignedFiniteTranslationPacket
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailUniformFiniteTranslationDefectCurrent

/-!
# Uniform signed finite translation defect

The arithmetic crossed channel retains a possibly negative displacement.  The packet, edge, and
mixed current are never replaced by their absolute-displacement analogues; only their analytic
majorants depend on `|a|`.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Exponential envelope for the complete signed value-plus-derivative translation edge. -/
theorem thetaCuspTailPhaseTranslationEdgeIntegratedNorm_le_absExponentialMajorant
    (d R : ℕ) (hR : 1 ≤ R) (a : ℝ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    thetaCuspTailPhaseTranslationEdgeIntegratedNorm d z a ≤
      32 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
        (((2 * d + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ d) *
          Real.exp (((3 * R : ℕ) : ℝ) * |a|) := by
  have hp : 0 < 2 * R := by omega
  have hV :=
    integral_abs_thetaCuspTailSecondDensity_mul_phaseTranslationTopEdge_norm_le_abs
      d R (2 * R) hp a z hz
  have hD :=
    integral_abs_thetaCuspTailSecondDensity_mul_phaseTranslationTopEdgeDerivative_norm_le_abs
      d R (2 * R) hR hp a z hz
  have hratio1 := phaseTranslation_ratio_one_le R d hR
  have hratio2 := phaseTranslation_ratio_two_le R d hR
  have hCnonneg : 0 ≤ thetaCuspTailDerivativeNatExpConstant 2 (3 * R) := by
    unfold thetaCuspTailDerivativeNatExpConstant
    exact mul_nonneg
      (mul_nonneg (thetaCuspCoeffMass_nonneg _) (Real.exp_pos _).le)
      (tsum_nonneg fun _ => mul_nonneg (pow_nonneg (by positivity) _)
        (Real.exp_pos _).le)
  have hexpnonneg : 0 ≤ Real.exp (((3 * R : ℕ) : ℝ) * |a|) :=
    (Real.exp_pos _).le
  unfold thetaCuspTailPhaseTranslationEdgeIntegratedNorm
  have hV' : (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖) ≤
      12 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) * (1 / 4 : ℝ) ^ d *
        Real.exp (((3 * R : ℕ) : ℝ) * |a|) := by
    calc
      _ ≤ 12 * thetaCuspTailDerivativeNatExpConstant 2 (2 * R + R) *
          ((R : ℝ) ^ (2 * d + 1) / ((2 * R : ℕ) : ℝ) ^ (2 * d + 2)) *
            Real.exp (((2 * R + R : ℕ) : ℝ) * |a|) := hV
      _ ≤ _ := by
        norm_num only [show 2 * R + R = 3 * R by omega]
        gcongr
  have hD' : (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖) ≤
      20 * ((2 * d + 2 : ℕ) : ℝ) *
        thetaCuspTailDerivativeNatExpConstant 2 (3 * R) * (1 / 4 : ℝ) ^ d *
          Real.exp (((3 * R : ℕ) : ℝ) * |a|) := by
    calc
      _ ≤ 12 * (2 * d + 1 : ℕ) *
          (thetaCuspTailDerivativeNatExpConstant 2 (2 * R + R) *
            ((R : ℝ) ^ (2 * d + 1) / ((2 * R : ℕ) : ℝ) ^ (2 * d + 2)) *
              Real.exp (((2 * R + R : ℕ) : ℝ) * |a|)) +
        8 * (2 * d + 2 : ℕ) *
          (thetaCuspTailDerivativeNatExpConstant 2 (2 * R + R) *
            ((R : ℝ) ^ (2 * d + 2) / ((2 * R : ℕ) : ℝ) ^ (2 * d + 3)) *
              Real.exp (((2 * R + R : ℕ) : ℝ) * |a|)) := hD
      _ ≤ _ := by
        norm_num only [show 2 * R + R = 3 * R by omega]
        have hdle : ((2 * d + 1 : ℕ) : ℝ) ≤ (2 * d + 2 : ℕ) := by norm_num
        calc
          _ ≤ 12 * ((2 * d + 2 : ℕ) : ℝ) *
                (thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
                  (1 / 4 : ℝ) ^ d * Real.exp (((3 * R : ℕ) : ℝ) * |a|)) +
              8 * ((2 * d + 2 : ℕ) : ℝ) *
                (thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
                  (1 / 4 : ℝ) ^ d * Real.exp (((3 * R : ℕ) : ℝ) * |a|)) := by
            gcongr
          _ = _ := by ring
  calc
    _ ≤ 12 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
          (1 / 4 : ℝ) ^ d * Real.exp (((3 * R : ℕ) : ℝ) * |a|) +
        20 * ((2 * d + 2 : ℕ) : ℝ) *
          thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
          (1 / 4 : ℝ) ^ d * Real.exp (((3 * R : ℕ) : ℝ) * |a|) :=
      add_le_add hV' hD'
    _ ≤ _ := by
      have hdOne : (1 : ℝ) ≤ ((2 * d + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * d + 2 by omega)
      have hnon : 0 ≤ thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
          (1 / 4 : ℝ) ^ d * Real.exp (((3 * R : ℕ) : ℝ) * |a|) := by
        positivity
      nlinarith

/-- Signed edge control uniformly below an absolute logarithmic horizon. -/
theorem thetaCuspTailPhaseTranslationEdgeIntegratedNorm_le_absLogarithmicMajorant_of_le
    (A d R n : ℕ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R)
    (a : ℝ) (hale : |a| ≤ xiCTaylorLogarithmicHaarDisplacement A n) :
    thetaCuspTailPhaseTranslationEdgeIntegratedNorm d z a ≤
      32 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
        (((2 * d + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ d) *
          (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := by
  have hedge := thetaCuspTailPhaseTranslationEdgeIntegratedNorm_le_absExponentialMajorant
    d R hR a z hz
  have hscale : 0 ≤ ((3 * R : ℕ) : ℝ) := by positivity
  have hexpLe : Real.exp (((3 * R : ℕ) : ℝ) * |a|) ≤
      Real.exp (((3 * R : ℕ) : ℝ) * xiCTaylorLogarithmicHaarDisplacement A n) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hale hscale)
  have hexpHorizon :
      Real.exp (((3 * R : ℕ) : ℝ) * xiCTaylorLogarithmicHaarDisplacement A n) ≤
        (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := by
    unfold xiCTaylorLogarithmicHaarDisplacement
    convert exp_logarithmicHaarDepth_le_pow A (6 * R) n using 1
    push_cast
    ring
  have hCnonneg : 0 ≤ thetaCuspTailDerivativeNatExpConstant 2 (3 * R) := by
    unfold thetaCuspTailDerivativeNatExpConstant
    exact mul_nonneg
      (mul_nonneg (thetaCuspCoeffMass_nonneg _) (Real.exp_pos _).le)
      (tsum_nonneg fun _ => mul_nonneg (pow_nonneg (by positivity) _)
        (Real.exp_pos _).le)
  have hcoef : 0 ≤ 32 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
      (((2 * d + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ d) := by
    exact mul_nonneg (mul_nonneg (by positivity) hCnonneg) (by positivity)
  calc
    _ ≤ 32 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
        (((2 * d + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ d) *
          Real.exp (((3 * R : ℕ) : ℝ) * |a|) := hedge
    _ ≤ _ := mul_le_mul_of_nonneg_left (hexpLe.trans hexpHorizon) hcoef

/-- The signed complete phase packet has a uniform absolute logarithmic-horizon majorant. -/
theorem thetaCuspTailPhaseTranslationPacketIntegratedNorm_le_absLogarithmicMajorant_of_le
    (A d R n : ℕ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R)
    (a : ℝ) (hale : |a| ≤ xiCTaylorLogarithmicHaarDisplacement A n) :
    thetaCuspTailPhaseTranslationPacketIntegratedNorm d z a ≤
      4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
        ((R : ℝ) + 1) *
          (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (2 * (R + 1))) := by
  have hpacket := thetaCuspTailPhaseTranslationPacketIntegratedNorm_le_abs
    d R hR a z hz
  have hscale : 0 ≤ ((1 + R : ℕ) : ℝ) := by positivity
  have hexpLe : Real.exp (((1 + R : ℕ) : ℝ) * |a|) ≤
      Real.exp (((1 + R : ℕ) : ℝ) * xiCTaylorLogarithmicHaarDisplacement A n) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hale hscale)
  have hexpHorizon :
      Real.exp (((1 + R : ℕ) : ℝ) * xiCTaylorLogarithmicHaarDisplacement A n) ≤
        (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (2 * (R + 1))) := by
    unfold xiCTaylorLogarithmicHaarDisplacement
    convert exp_logarithmicHaarDepth_le_pow A (2 * (R + 1)) n using 1
    push_cast
    ring
  have hCnonneg : 0 ≤ thetaCuspTailDerivativeNatExpConstant 2 (1 + R) := by
    unfold thetaCuspTailDerivativeNatExpConstant
    exact mul_nonneg
      (mul_nonneg (thetaCuspCoeffMass_nonneg _) (Real.exp_pos _).le)
      (tsum_nonneg fun _ => mul_nonneg (pow_nonneg (by positivity) _)
        (Real.exp_pos _).le)
  have hcoef : 0 ≤ 4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
      ((R : ℝ) + 1) := by
    exact mul_nonneg (mul_nonneg (by positivity) hCnonneg) (by positivity)
  calc
    _ ≤ 4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
        ((R : ℝ) + 1) * Real.exp (((1 + R : ℕ) : ℝ) * |a|) := hpacket
    _ ≤ _ := mul_le_mul_of_nonneg_left (hexpLe.trans hexpHorizon) hcoef

/-- The signed edge beats every prescribed mesh power under an absolute logarithmic horizon. -/
theorem tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero_of_abs_le
    (A M R : ℕ) (hR : 1 ≤ R) (d : ℕ → ℕ) (hd : ∀ n, n ≤ d n)
    (z : ℕ → ℂ) (hz : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ R)
    (a : ℕ → ℝ)
    (hale : ∀ n, |a n| ≤ xiCTaylorLogarithmicHaarDisplacement A n) :
    Tendsto (fun n : ℕ =>
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm (d n) (z n) (a n) *
        (((n + 1 : ℕ) : ℝ) ^ M)) atTop (nhds 0) := by
  let C : ℝ := 32 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
    (2 : ℝ) ^ (A * (6 * R))
  have hbase := tendsto_degree_factor_geometric_mul_succ_pow d hd
    (A * (6 * R) + M)
  have hmajor : Tendsto (fun n : ℕ => C *
      ((((2 * d n + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ d n) *
        (((n + 1 : ℕ) : ℝ) ^ (A * (6 * R) + M)))) atTop (nhds 0) := by
    simpa using hbase.const_mul C
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg
      (thetaCuspTailPhaseTranslationEdgeIntegratedNorm_nonneg _ _ _)
      (pow_nonneg (by positivity) _)
  · filter_upwards [hz] with n hzn
    have hedge :=
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm_le_absLogarithmicMajorant_of_le
        A (d n) R n hR (z n) hzn (a n) (hale n)
    have hq : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ M) := by positivity
    calc
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm (d n) (z n) (a n) *
          ((n + 1 : ℕ) : ℝ) ^ M ≤
        (32 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
          (((2 * d n + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ d n) *
            (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R))) *
              ((n + 1 : ℕ) : ℝ) ^ M :=
        mul_le_mul_of_nonneg_right hedge hq
      _ = C * ((((2 * d n + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ d n) *
          (((n + 1 : ℕ) : ℝ) ^ (A * (6 * R) + M))) := by
        dsimp [C]
        rw [mul_pow, pow_add]
        ring
  · exact hmajor

/-- **Signed complete-defect theorem.**  The exact crossed finite translation defect, including
both mixed currents, beats every prescribed mesh power whenever the absolute displacement stays
below the logarithmic horizon. -/
theorem tendsto_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_mul_pow_zero_of_abs_le
    (A M R : ℕ) (hR : 1 ≤ R) (d : ℕ → ℕ) (hd : ∀ n, n ≤ d n)
    (z : ℕ → ℂ) (hz : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ R)
    (a : ℕ → ℝ)
    (hale : ∀ n, |a n| ≤ xiCTaylorLogarithmicHaarDisplacement A n) :
    Tendsto (fun n : ℕ =>
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
          (d n) (z n) (a n)| * (((n + 1 : ℕ) : ℝ) ^ M)) atTop (nhds 0) := by
  let E : ℕ → ℝ := fun n =>
    thetaCuspTailPhaseTranslationEdgeIntegratedNorm (d n) (z n) (a n)
  let Q : ℕ → ℝ := fun n =>
    thetaCuspTailPhaseTranslationPacketIntegratedNorm (d n) (z n) (a n)
  let K : ℕ := A * (2 * (R + 1))
  let C : ℝ := 4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
    ((R : ℝ) + 1) * (2 : ℝ) ^ K
  have hEM : Tendsto (fun n => E n * (((n + 1 : ℕ) : ℝ) ^ M))
      atTop (nhds 0) := by
    simpa only [E] using
      tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero_of_abs_le
        A M R hR d hd z hz a hale
  have hEKM : Tendsto (fun n => E n * (((n + 1 : ℕ) : ℝ) ^ (K + M)))
      atTop (nhds 0) := by
    simpa only [E] using
      tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero_of_abs_le
        A (K + M) R hR d hd z hz a hale
  have hE0 : Tendsto E atTop (nhds 0) := by
    simpa only [E, pow_zero, mul_one] using
      tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero_of_abs_le
        A 0 R hR d hd z hz a hale
  have hcrossMajor : Tendsto (fun n => C *
      (E n * (((n + 1 : ℕ) : ℝ) ^ (K + M)))) atTop (nhds 0) := by
    simpa using hEKM.const_mul C
  have hcross : Tendsto (fun n =>
      (Q n * E n) * (((n + 1 : ℕ) : ℝ) ^ M)) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n => mul_nonneg
        (mul_nonneg
          (by
            dsimp [Q]
            exact thetaCuspTailPhaseTranslationPacketIntegratedNorm_nonneg _ _ _)
          (thetaCuspTailPhaseTranslationEdgeIntegratedNorm_nonneg _ _ _))
        (pow_nonneg (by positivity) _)
    · filter_upwards [hz] with n hzn
      have hQ :=
        thetaCuspTailPhaseTranslationPacketIntegratedNorm_le_absLogarithmicMajorant_of_le
          A (d n) R n hR (z n) hzn (a n) (hale n)
      have hE0n : 0 ≤ E n := by
        dsimp [E]
        exact thetaCuspTailPhaseTranslationEdgeIntegratedNorm_nonneg _ _ _
      have hq : Q n ≤ C * (((n + 1 : ℕ) : ℝ) ^ K) := by
        calc
          Q n ≤ 4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
              ((R : ℝ) + 1) *
                (2 * ((n + 1 : ℕ) : ℝ)) ^ K := by
            simpa only [Q, K] using hQ
          _ = C * (((n + 1 : ℕ) : ℝ) ^ K) := by
            dsimp [C]
            rw [mul_pow]
            ring
      calc
        (Q n * E n) * ((n + 1 : ℕ) : ℝ) ^ M ≤
            ((C * ((n + 1 : ℕ) : ℝ) ^ K) * E n) *
              ((n + 1 : ℕ) : ℝ) ^ M := by gcongr
        _ = C * (E n * ((n + 1 : ℕ) : ℝ) ^ (K + M)) := by
          rw [pow_add]
          ring
    · exact hcrossMajor
  have hself : Tendsto (fun n => E n *
      (E n * (((n + 1 : ℕ) : ℝ) ^ M))) atTop (nhds 0) := by
    simpa using hE0.mul hEM
  have hmajor : Tendsto (fun n =>
      (Q n * E n) * (((n + 1 : ℕ) : ℝ) ^ M) +
        E n * (E n * (((n + 1 : ℕ) : ℝ) ^ M))) atTop (nhds 0) := by
    simpa using hcross.add hself
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (abs_nonneg _)
      (pow_nonneg (by positivity) _)
  · filter_upwards [] with n
    have hdef := abs_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_le
      (d n) (z n) (a n)
    have hpow : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ M) := by positivity
    calc
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent (d n) (z n) (a n)| *
          ((n + 1 : ℕ) : ℝ) ^ M ≤
        (Q n * E n + E n ^ 2) * ((n + 1 : ℕ) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right hdef hpow
      _ = (Q n * E n) * ((n + 1 : ℕ) : ℝ) ^ M +
          E n * (E n * ((n + 1 : ℕ) : ℝ) ^ M) := by ring
  · exact hmajor

end


end RHTower
