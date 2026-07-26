import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationDefectCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSignedFiniteTranslationPacket

/-!
# Uniform finite translation defect below the logarithmic horizon

The existing logarithmic theorem controls the complete finite cosine--sine translation defect at
one cofinal displacement.  Primitive-ray and valuation-box assemblies need the same estimate for
a displacement which may vary with the mesh point, subject only to lying between zero and that
cofinal horizon.

The estimates below are applied only after the exact value, derivative, and mixed-current
cancellations have been combined into
`thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent`; no window or top-edge current is
assigned a sign separately.
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

/-- Exponential envelope for the complete value-plus-derivative finite translation edge at an
arbitrary nonnegative displacement. -/
theorem thetaCuspTailPhaseTranslationEdgeIntegratedNorm_le_exponentialMajorant
    (d R : ℕ) (hR : 1 ≤ R) (a : ℝ) (ha : 0 ≤ a) (z : ℂ) (hz : ‖z‖ ≤ R) :
    thetaCuspTailPhaseTranslationEdgeIntegratedNorm d z a ≤
      32 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
        (((2 * d + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ d) *
          Real.exp (((3 * R : ℕ) : ℝ) * a) := by
  have h := thetaCuspTailPhaseTranslationEdgeIntegratedNorm_le_absExponentialMajorant
    d R hR a z hz
  rwa [abs_of_nonneg ha] at h
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

/-- The same cached logarithmic majorant controls every nonnegative displacement below the
cofinal logarithmic horizon. -/
theorem thetaCuspTailPhaseTranslationEdgeIntegratedNorm_le_logarithmicMajorant_of_le
    (A d R n : ℕ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R)
    (a : ℝ) (ha : 0 ≤ a) (hale : a ≤ xiCTaylorLogarithmicHaarDisplacement A n) :
    thetaCuspTailPhaseTranslationEdgeIntegratedNorm d z a ≤
      32 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
        (((2 * d + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ d) *
          (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := by
  exact thetaCuspTailPhaseTranslationEdgeIntegratedNorm_le_absLogarithmicMajorant_of_le
    A d R n hR z hz a (by rwa [abs_of_nonneg ha])
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

/-- The complete finite phase packet admits the same uniform logarithmic-horizon majorant. -/
theorem thetaCuspTailPhaseTranslationPacketIntegratedNorm_le_logarithmicMajorant_of_le
    (A d R n : ℕ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R)
    (a : ℝ) (ha : 0 ≤ a) (hale : a ≤ xiCTaylorLogarithmicHaarDisplacement A n) :
    thetaCuspTailPhaseTranslationPacketIntegratedNorm d z a ≤
      4 * thetaCuspTailDerivativeNatExpConstant 2 (1 + R) *
        ((R : ℝ) + 1) *
          (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (2 * (R + 1))) := by
  exact thetaCuspTailPhaseTranslationPacketIntegratedNorm_le_absLogarithmicMajorant_of_le
    A d R n hR z hz a (by rwa [abs_of_nonneg ha])
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

/-- Uniform super-polynomial decay of the finite translation edge for any mesh-dependent shift
below the logarithmic horizon. -/
theorem tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero_of_le
    (A M R : ℕ) (hR : 1 ≤ R) (d : ℕ → ℕ) (hd : ∀ n, n ≤ d n)
    (z : ℕ → ℂ) (hz : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ R)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hale : ∀ n, a n ≤ xiCTaylorLogarithmicHaarDisplacement A n) :
    Tendsto (fun n : ℕ =>
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm (d n) (z n) (a n) *
        (((n + 1 : ℕ) : ℝ) ^ M)) atTop (nhds 0) := by
  exact tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero_of_abs_le
    A M R hR d hd z hz a (fun n => by rw [abs_of_nonneg (ha n)]; exact hale n)
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

/-- **Uniform complete-defect theorem.**  The exact finite cosine--sine translation defect,
including both mixed currents, beats every prescribed power for any mesh-dependent displacement
below the logarithmic horizon. -/
theorem tendsto_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_mul_pow_zero_of_le
    (A M R : ℕ) (hR : 1 ≤ R) (d : ℕ → ℕ) (hd : ∀ n, n ≤ d n)
    (z : ℕ → ℂ) (hz : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ R)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hale : ∀ n, a n ≤ xiCTaylorLogarithmicHaarDisplacement A n) :
    Tendsto (fun n : ℕ =>
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
          (d n) (z n) (a n)| * (((n + 1 : ℕ) : ℝ) ^ M)) atTop (nhds 0) := by
  exact tendsto_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_mul_pow_zero_of_abs_le
    A M R hR d hd z hz a (fun n => by rw [abs_of_nonneg (ha n)]; exact hale n)
/-- Scheduled positive-channel specialization at twice the local Xi order. -/
theorem tendsto_scheduled_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_localOrder_of_le
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hale : ∀ n, a n ≤ xiCTaylorLogarithmicHaarDisplacement A n) :
    Tendsto (fun n : ℕ =>
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n) (a n)| *
        (((n + 1 : ℕ) : ℝ) ^
          (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  exact
    tendsto_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_mul_pow_zero_of_le
      A (2 * (analyticOrderAt xi sigma).toNat) R hR
        (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (le_xiCTaylorScheduledThetaTailDepth hD sigma)
        (xiCTaylorAnisotropicCenteredPoint sigma) hz a ha hale

/-- Scheduled negative-channel specialization; reflection preserves the uniform horizon. -/
theorem tendsto_scheduled_thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_localOrder_of_le
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hale : ∀ n, a n ≤ xiCTaylorLogarithmicHaarDisplacement A n) :
    Tendsto (fun n : ℕ =>
      |thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n) (a n)| *
        (((n + 1 : ℕ) : ℝ) ^
          (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  have hzneg : ∀ᶠ n : ℕ in atTop,
      ‖-xiCTaylorAnisotropicCenteredPoint sigma n‖ ≤ R := by
    simpa only [norm_neg] using hz
  have hpos :=
    tendsto_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_mul_pow_zero_of_le
      A (2 * (analyticOrderAt xi sigma).toNat) R hR
        (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (le_xiCTaylorScheduledThetaTailDepth hD sigma)
        (fun n => -xiCTaylorAnisotropicCenteredPoint sigma n) hzneg a ha hale
  convert hpos using 1
  funext n
  rw [thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_eq_neg_positive_neg]
  simp

/-- Uniform positive-channel joint defect is `o(n)|P|^2` on the anisotropic mesh. -/
theorem eventually_abs_scheduled_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_lt_scaled_normSq_of_le
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hale : ∀ n, a n ≤ xiCTaylorLogarithmicHaarDisplacement A n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n) (a n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  apply eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
    hD sigma (fun n =>
      |thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent
        (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (xiCTaylorAnisotropicCenteredPoint sigma n) (a n)|)
  · exact
      tendsto_scheduled_thetaCuspTailPhaseTranslationFullDefectIntegratedCurrent_localOrder_of_le
        hD A sigma a ha hale
  · exact hepsilon

/-- Uniform negative-channel joint defect is `o(n)|P|^2` on the same mesh. -/
theorem eventually_abs_scheduled_thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_lt_scaled_normSq_of_le
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hale : ∀ n, a n ≤ xiCTaylorLogarithmicHaarDisplacement A n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n) (a n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  apply eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
    hD sigma (fun n =>
      |thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent
        (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (xiCTaylorAnisotropicCenteredPoint sigma n) (a n)|)
  · exact
      tendsto_scheduled_thetaCuspTailNegativePhaseTranslationFullDefectIntegratedCurrent_localOrder_of_le
        hD A sigma a ha hale
  · exact hepsilon

end

end RHTower
