import GaloisForLFunctions.RHTower.XiCTaylorAnisotropicRelativeRemainder
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationTopRow

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

/-- A logarithmic cofinal Haar depth. -/
def xiCTaylorLogarithmicHaarDepth (A n : ℕ) : ℕ :=
  A * Nat.clog 2 (n + 1)

/-- The remote dyadic row is translated back by twice its logarithmic depth. -/
def xiCTaylorLogarithmicHaarDisplacement (A n : ℕ) : ℝ :=
  2 * (xiCTaylorLogarithmicHaarDepth A n : ℝ) * Real.log 2

lemma two_pow_clog_two_le_two_mul (n : ℕ) :
    (2 : ℝ) ^ Nat.clog 2 (n + 1) ≤ 2 * (n + 1 : ℝ) := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hx : 1 < n + 1 + 1 := by omega
      have hpred := Nat.pow_pred_clog_lt_self (b := 2) (by omega) hx
      have hpos := Nat.clog_pos (b := 2) (n := n + 1 + 1) (by omega) hx
      have hsucc : (Nat.clog 2 (n + 1 + 1)).pred + 1 =
          Nat.clog 2 (n + 1 + 1) := Nat.succ_pred_eq_of_pos hpos
      rw [← hsucc, pow_succ]
      have hr : (2 : ℝ) ^ (Nat.clog 2 (n + 1 + 1)).pred ≤
          (n + 1 + 1 : ℕ) := by exact_mod_cast hpred.le
      push_cast at hr ⊢
      nlinarith

lemma exp_logarithmicHaarDepth_le_pow
    (A c n : ℕ) :
    Real.exp ((c : ℝ) * ((xiCTaylorLogarithmicHaarDepth A n : ℕ) : ℝ) *
        Real.log 2) ≤
      (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * c) := by
  rw [show (c : ℝ) * (xiCTaylorLogarithmicHaarDepth A n : ℝ) * Real.log 2 =
      ((A * c * Nat.clog 2 (n + 1) : ℕ) : ℝ) * Real.log 2 by
        simp only [xiCTaylorLogarithmicHaarDepth]
        push_cast
        ring]
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [show A * c * Nat.clog 2 (n + 1) =
      Nat.clog 2 (n + 1) * (A * c) by ac_rfl, pow_mul]
  simpa only [Nat.cast_add, Nat.cast_one] using
    pow_le_pow_left₀ (by positivity) (two_pow_clog_two_le_two_mul n) (A * c)

lemma succ_le_two_pow_succ (d : ℕ) : d + 1 ≤ 2 ^ (d + 1) := by
  exact (Nat.lt_pow_self (n := d + 1) (a := 2) (by omega)).le

lemma degree_factor_geometric_le
    (D n : ℕ) (hnD : n ≤ D) :
    ((2 * D + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ D ≤
      4 * (1 / 2 : ℝ) ^ n := by
  have hsucc : ((D + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (D + 1) := by
    exact_mod_cast succ_le_two_pow_succ D
  have hpow : (1 / 2 : ℝ) ^ D ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_of_le_one (by positivity) (by norm_num) hnD
  calc
    ((2 * D + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ D =
        2 * (D + 1 : ℝ) * (1 / 4 : ℝ) ^ D := by push_cast; ring
    _ ≤ 2 * (2 : ℝ) ^ (D + 1) * (1 / 4 : ℝ) ^ D := by
      have hsucc' : (D : ℝ) + 1 ≤ (2 : ℝ) ^ (D + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hsucc
      gcongr
    _ = 4 * (1 / 2 : ℝ) ^ D := by
      rw [pow_succ]
      ring_nf
      rw [← mul_pow]
      norm_num
    _ ≤ 4 * (1 / 2 : ℝ) ^ n := by gcongr

lemma tendsto_succ_pow_mul_half_pow (M : ℕ) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ M) * (1 / 2 : ℝ) ^ n)
      atTop (nhds 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_lt_one M
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp
      (tendsto_add_atTop_nat 1)
  have htwo := h.const_mul (2 : ℝ)
  convert htwo using 1
  · funext n
    change ((n + 1 : ℕ) : ℝ) ^ M * (1 / 2 : ℝ) ^ n =
      2 * (((n + 1 : ℕ) : ℝ) ^ M * (1 / 2 : ℝ) ^ (n + 1))
    rw [pow_succ]
    ring
  · ring

lemma tendsto_degree_factor_geometric_mul_succ_pow
    (D : ℕ → ℕ) (hD : ∀ n, n ≤ D n) (M : ℕ) :
    Tendsto (fun n : ℕ =>
      (((2 * D n + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ D n) *
        (((n + 1 : ℕ) : ℝ) ^ M)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (by positivity) (by positivity)
  · filter_upwards [] with n
    have h := degree_factor_geometric_le (D n) n (hD n)
    calc
      ((2 * D n + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ D n *
          ((n + 1 : ℕ) ^ M) ≤
        (4 * (1 / 2 : ℝ) ^ n) * ((n + 1 : ℕ) ^ M) := by gcongr
      _ = 4 * (((n + 1 : ℕ) : ℝ) ^ M * (1 / 2 : ℝ) ^ n) := by ring
  · simpa using (tendsto_succ_pow_mul_half_pow M).const_mul 4

lemma phaseTranslation_ratio_one_le (R d : ℕ) (hR : 1 ≤ R) :
    (R : ℝ) ^ (2 * d + 1) / (2 * R : ℕ) ^ (2 * d + 2) ≤
      (1 / 4 : ℝ) ^ d := by
  have hRR : (0 : ℝ) < R := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hEq : (R : ℝ) ^ (2 * d + 1) / (2 * R : ℕ) ^ (2 * d + 2) =
      (1 / 4 : ℝ) ^ d / (4 * R) := by
    have hpow : (1 / 4 : ℝ) ^ d * 2 ^ (d * 2) = 1 := by
      rw [show d * 2 = 2 * d by omega, pow_mul]
      norm_num
      rw [← mul_pow]
      norm_num
    push_cast
    field_simp
    ring_nf
    rw [show (R : ℝ) ^ (2 : ℕ) * R ^ (d * 2) * (1 / 4) ^ d * 2 ^ (d * 2) * 4 =
      R ^ (2 : ℕ) * R ^ (d * 2) * ((1 / 4) ^ d * 2 ^ (d * 2)) * 4 by ring,
      hpow]
    ring
  rw [hEq]
  exact div_le_self (pow_nonneg (by norm_num) _)
    (by exact_mod_cast (show 1 ≤ 4 * R by omega))

lemma phaseTranslation_ratio_two_le (R d : ℕ) (hR : 1 ≤ R) :
    (R : ℝ) ^ (2 * d + 2) / (2 * R : ℕ) ^ (2 * d + 3) ≤
      (1 / 4 : ℝ) ^ d := by
  have hRR : (0 : ℝ) < R := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hEq : (R : ℝ) ^ (2 * d + 2) / (2 * R : ℕ) ^ (2 * d + 3) =
      (1 / 4 : ℝ) ^ d / (8 * R) := by
    have hpow : (1 / 4 : ℝ) ^ d * 2 ^ (d * 2) = 1 := by
      rw [show d * 2 = 2 * d by omega, pow_mul]
      norm_num
      rw [← mul_pow]
      norm_num
    push_cast
    field_simp
    ring_nf
    rw [show (R : ℝ) ^ (3 : ℕ) * R ^ (d * 2) * (1 / 4) ^ d * 2 ^ (d * 2) * 8 =
      R ^ (3 : ℕ) * R ^ (d * 2) * ((1 / 4) ^ d * 2 ^ (d * 2)) * 8 by ring,
      hpow]
    ring
  rw [hEq]
  exact div_le_self (pow_nonneg (by norm_num) _)
    (by exact_mod_cast (show 1 ≤ 8 * R by omega))

/-- Sum of the two exact density-integrated phase-edge norm envelopes. -/
def thetaCuspTailPhaseTranslationEdgeIntegratedNorm
    (d : ℕ) (z : ℂ) (a : ℝ) : ℝ :=
  (∫ x : ℝ in Ioi 0,
    |thetaCuspTailSecondDensity x| *
      ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖) +
  (∫ x : ℝ in Ioi 0,
    |thetaCuspTailSecondDensity x| *
      ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖)

lemma thetaCuspTailPhaseTranslationEdgeIntegratedNorm_nonneg
    (d : ℕ) (z : ℂ) (a : ℝ) :
    0 ≤ thetaCuspTailPhaseTranslationEdgeIntegratedNorm d z a := by
  unfold thetaCuspTailPhaseTranslationEdgeIntegratedNorm
  apply add_nonneg
  · exact MeasureTheory.integral_nonneg fun x => mul_nonneg (abs_nonneg _)
      (norm_nonneg _)
  · exact MeasureTheory.integral_nonneg fun x => mul_nonneg (abs_nonneg _)
      (norm_nonneg _)

/-- At logarithmic Haar depth the complete value-plus-derivative phase edge is bounded by one
geometric degree factor times a fixed polynomial in the mesh resolution. -/
theorem thetaCuspTailPhaseTranslationEdgeIntegratedNorm_le_logarithmicMajorant
    (A d R n : ℕ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    thetaCuspTailPhaseTranslationEdgeIntegratedNorm d z
        (xiCTaylorLogarithmicHaarDisplacement A n) ≤
      32 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
        (((2 * d + 2 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ d) *
          (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := by
  have ha : 0 ≤ xiCTaylorLogarithmicHaarDisplacement A n := by
    unfold xiCTaylorLogarithmicHaarDisplacement
    positivity
  have hp : 0 < 2 * R := by omega
  have hV := integral_abs_thetaCuspTailSecondDensity_mul_phaseTranslationTopEdge_norm_le
    d R (2 * R) hp ha z hz
  have hD := integral_abs_thetaCuspTailSecondDensity_mul_phaseTranslationTopEdgeDerivative_norm_le
    d R (2 * R) hR hp ha z hz
  have hratio1 := phaseTranslation_ratio_one_le R d hR
  have hratio2 := phaseTranslation_ratio_two_le R d hR
  have hexp : Real.exp ((((2 * R + R : ℕ) : ℝ) *
      xiCTaylorLogarithmicHaarDisplacement A n)) ≤
      (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := by
    unfold xiCTaylorLogarithmicHaarDisplacement
    convert exp_logarithmicHaarDepth_le_pow A (6 * R) n using 1
    push_cast
    ring
  have hexp' : Real.exp ((((3 * R : ℕ) : ℝ) *
      xiCTaylorLogarithmicHaarDisplacement A n)) ≤
      (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := by
    simpa only [show 2 * R + R = 3 * R by omega] using hexp
  have hCnonneg : 0 ≤ thetaCuspTailDerivativeNatExpConstant 2 (3 * R) := by
    unfold thetaCuspTailDerivativeNatExpConstant
    exact mul_nonneg
      (mul_nonneg (thetaCuspCoeffMass_nonneg _) (Real.exp_pos _).le)
      (tsum_nonneg fun _ => mul_nonneg (pow_nonneg (by positivity) _)
        (Real.exp_pos _).le)
  have hpow : 0 ≤ (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := by positivity
  unfold thetaCuspTailPhaseTranslationEdgeIntegratedNorm
  have hV' : (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x
          (xiCTaylorLogarithmicHaarDisplacement A n)).eval z‖) ≤
      12 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) * (1 / 4 : ℝ) ^ d *
        (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := by
    calc
      _ ≤ 12 * thetaCuspTailDerivativeNatExpConstant 2 (2 * R + R) *
          ((R : ℝ) ^ (2 * d + 1) / ((2 * R : ℕ) : ℝ) ^ (2 * d + 2)) *
            Real.exp (((2 * R + R : ℕ) : ℝ) *
              xiCTaylorLogarithmicHaarDisplacement A n) := hV
      _ ≤ _ := by
        norm_num only [show 2 * R + R = 3 * R by omega]
        gcongr
  have hD' : (∫ x : ℝ in Ioi 0,
      |thetaCuspTailSecondDensity x| *
        ‖(finitePositivePhaseTranslationTopEdge d x
          (xiCTaylorLogarithmicHaarDisplacement A n)).derivative.eval z‖) ≤
      20 * ((2 * d + 2 : ℕ) : ℝ) *
        thetaCuspTailDerivativeNatExpConstant 2 (3 * R) * (1 / 4 : ℝ) ^ d *
        (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := by
    calc
      _ ≤ 12 * (2 * d + 1 : ℕ) *
          (thetaCuspTailDerivativeNatExpConstant 2 (2 * R + R) *
            ((R : ℝ) ^ (2 * d + 1) / ((2 * R : ℕ) : ℝ) ^ (2 * d + 2)) *
              Real.exp (((2 * R + R : ℕ) : ℝ) *
                xiCTaylorLogarithmicHaarDisplacement A n)) +
        8 * (2 * d + 2 : ℕ) *
          (thetaCuspTailDerivativeNatExpConstant 2 (2 * R + R) *
            ((R : ℝ) ^ (2 * d + 2) / ((2 * R : ℕ) : ℝ) ^ (2 * d + 3)) *
              Real.exp (((2 * R + R : ℕ) : ℝ) *
                xiCTaylorLogarithmicHaarDisplacement A n)) := hD
      _ ≤ _ := by
        norm_num only [show 2 * R + R = 3 * R by omega]
        have hdle : ((2 * d + 1 : ℕ) : ℝ) ≤ (2 * d + 2 : ℕ) := by norm_num
        calc
          _ ≤ 12 * ((2 * d + 2 : ℕ) : ℝ) *
                (thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
                  (1 / 4 : ℝ) ^ d *
                  (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R))) +
              8 * ((2 * d + 2 : ℕ) : ℝ) *
                (thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
                  (1 / 4 : ℝ) ^ d *
                  (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R))) := by
            gcongr
          _ = _ := by ring
  calc
    _ ≤ 12 * thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
          (1 / 4 : ℝ) ^ d *
          (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) +
        20 * ((2 * d + 2 : ℕ) : ℝ) *
          thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
          (1 / 4 : ℝ) ^ d *
          (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := add_le_add hV' hD'
    _ ≤ _ := by
      have hdOne : (1 : ℝ) ≤ ((2 * d + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * d + 2 by omega)
      have hnon : 0 ≤ thetaCuspTailDerivativeNatExpConstant 2 (3 * R) *
          (1 / 4 : ℝ) ^ d *
          (2 * ((n + 1 : ℕ) : ℝ)) ^ (A * (6 * R)) := by positivity
      nlinarith

/-- The logarithmic-depth integrated phase edge beats every prescribed power, uniformly over
all finite-section degrees at least the mesh resolution. -/
theorem tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero
    (A M R : ℕ) (hR : 1 ≤ R) (d : ℕ → ℕ) (hd : ∀ n, n ≤ d n)
    (z : ℕ → ℂ) (hz : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ R) :
    Tendsto (fun n : ℕ =>
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm (d n) (z n)
          (xiCTaylorLogarithmicHaarDisplacement A n) *
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
    have hedge := thetaCuspTailPhaseTranslationEdgeIntegratedNorm_le_logarithmicMajorant
      A (d n) R n hR (z n) hzn
    have hq : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ M) := by positivity
    calc
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm (d n) (z n)
          (xiCTaylorLogarithmicHaarDisplacement A n) *
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

/-- A source-selected odd schedule has finite-section depth at least the anisotropic mesh
resolution. -/
theorem le_xiCTaylorScheduledThetaTailDepth
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) (n : ℕ) :
    n ≤ D (xiCTaylorAnisotropicScheduleStage sigma n) + 1 := by
  have hDstrict : StrictMono D := by
    intro a b hab
    have h := hD.1.1 hab
    unfold xiCTaylorOddDegreeSchedule at h
    omega
  have hstage := succ_le_xiCTaylorAnisotropicScheduleStage sigma n
  have hdiag : xiCTaylorAnisotropicScheduleStage sigma n ≤
      D (xiCTaylorAnisotropicScheduleStage sigma n) := hDstrict.id_le _
  omega

/-- Every anisotropic centered fibre is eventually contained in a fixed natural-radius ball. -/
theorem exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat
    (sigma : ℂ) :
    ∃ R : ℕ, 1 ≤ R ∧ ∀ᶠ n : ℕ in atTop,
      ‖xiCTaylorAnisotropicCenteredPoint sigma n‖ ≤ R := by
  let alpha : ℂ := xiCTaylorCenteredPoint sigma
  let R : ℕ := ⌈‖alpha‖⌉₊ + 1
  have hR : 1 ≤ R := by dsimp [R]; omega
  refine ⟨R, hR, ?_⟩
  have htend : Tendsto
      (fun n : ℕ => ‖xiCTaylorAnisotropicCenteredPoint sigma n‖)
      atTop (nhds ‖alpha‖) :=
    (tendsto_xiCTaylorAnisotropicCenteredPoint sigma).norm
  have hlt : ‖alpha‖ < (R : ℝ) := by
    dsimp [R]
    push_cast
    linarith [Nat.le_ceil ‖alpha‖]
  exact (htend.eventually (eventually_lt_nhds hlt)).mono fun _ hn => hn.le

/-- On every anisotropic fibre, the logarithmic-depth integrated phase edge beats twice the
local Xi-order.  No zero location or zero-free hypothesis is used. -/
theorem tendsto_scheduled_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_localOrder
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) :
    Tendsto (fun n : ℕ =>
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n) *
        (((n + 1 : ℕ) : ℝ) ^
          (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  exact tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero
    A (2 * (analyticOrderAt xi sigma).toNat) R hR
      (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
      (le_xiCTaylorScheduledThetaTailDepth hD sigma)
      (xiCTaylorAnisotropicCenteredPoint sigma) hz

/-- **Anisotropic relative phase-edge theorem.**  The exact density-integrated finite
cosine--sine translation edge, with its value and spectral derivative kept together, is
`o(n) |P|^(2 : ℕ)` on every source-selected anisotropic Taylor mesh. -/
theorem eventually_scheduled_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n) <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  apply eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
    hD sigma (fun n =>
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm
        (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (xiCTaylorAnisotropicCenteredPoint sigma n)
        (xiCTaylorLogarithmicHaarDisplacement A n))
  · exact tendsto_scheduled_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_localOrder
      hD A sigma
  · exact hepsilon

lemma exp_neg_dyadic_shift_le_half_pow (R k : ℕ) :
    Real.exp (-((R + 2 : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) ≤
      (1 / 2 : ℝ) ^ k := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    Real.exp (-((R + 2 : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) ≤
        Real.exp ((k : ℝ) * (-Real.log 2)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      have hR0 : (0 : ℝ) ≤ R := by positivity
      have hk0 : (0 : ℝ) ≤ k := by positivity
      have hfactor : (1 : ℝ) ≤ (R : ℝ) + 2 := by nlinarith
      have hklog : 0 ≤ (k : ℝ) * Real.log 2 := mul_nonneg hk0 hlog.le
      nlinarith [mul_le_mul_of_nonneg_right hfactor hklog]
    _ = (1 / 2 : ℝ) ^ k := by
      rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

lemma norm_sq_add_quarter_le_nat (R : ℕ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖z ^ (2 : ℕ) + 1 / 4‖ ≤ (R : ℝ) ^ (2 : ℕ) + 1 := by
  calc
    ‖z ^ (2 : ℕ) + 1 / 4‖ ≤ ‖z ^ (2 : ℕ)‖ + ‖(1 / 4 : ℂ)‖ := norm_add_le _ _
    _ = ‖z‖ ^ (2 : ℕ) + 1 / 4 := by norm_num
    _ ≤ (R : ℝ) ^ (2 : ℕ) + 1 / 4 := by gcongr
    _ ≤ (R : ℝ) ^ (2 : ℕ) + 1 := by norm_num

/-- A degree-uniform top-row bound in the simple geometric form needed for a logarithmic
diagonal depth. -/
theorem abs_integral_xiCTaylorThetaTailCoreDyadicHaarRemainderKernel_le_half_pow
    (d R k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |∫ p : ℝ × ℝ,
        xiCTaylorThetaTailCoreDyadicHaarRemainderKernel d z k p
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))| ≤
      ((4 * thetaCuspTailDerivativeNatExpConstant 2 (R + 2)) ^ (2 : ℕ) *
        ((R : ℝ) / 2 + 3 * ((R : ℝ) ^ (2 : ℕ) + 1) / 8) *
        (1 / 2 + ((R : ℝ) ^ (2 : ℕ) + 1) / 4)) * (1 / 2 : ℝ) ^ k := by
  have hraw :=
    abs_integral_xiCTaylorThetaTailCoreDyadicHaarRemainderKernel_le d R k z hz
  have hq := norm_sq_add_quarter_le_nat R z hz
  have hshift := exp_neg_dyadic_shift_le_half_pow R k
  have hC : 0 ≤ thetaCuspTailDerivativeNatExpConstant 2 (R + 2) := by
    unfold thetaCuspTailDerivativeNatExpConstant
    exact mul_nonneg
      (mul_nonneg (thetaCuspCoeffMass_nonneg _) (Real.exp_pos _).le)
      (tsum_nonneg fun _ => mul_nonneg (pow_nonneg (by positivity) _)
        (Real.exp_pos _).le)
  calc
    _ ≤ (2 : ℝ) ^ k *
        ((4 * thetaCuspTailDerivativeNatExpConstant 2 (R + 2)) *
          Real.exp (-((R + 2 : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) *
            (‖z‖ / 2 + 3 * ‖z ^ (2 : ℕ) + 1 / 4‖ / 8)) *
        ((4 * thetaCuspTailDerivativeNatExpConstant 2 (R + 2)) *
          Real.exp (-((R + 2 : ℕ) : ℝ) * ((k : ℝ) * Real.log 2)) *
            (1 / 2 + ‖z ^ (2 : ℕ) + 1 / 4‖ / 4)) := hraw
    _ ≤ (2 : ℝ) ^ k *
        ((4 * thetaCuspTailDerivativeNatExpConstant 2 (R + 2)) *
          (1 / 2 : ℝ) ^ k *
            ((R : ℝ) / 2 + 3 * ((R : ℝ) ^ (2 : ℕ) + 1) / 8)) *
        ((4 * thetaCuspTailDerivativeNatExpConstant 2 (R + 2)) *
          (1 / 2 : ℝ) ^ k *
            (1 / 2 + ((R : ℝ) ^ (2 : ℕ) + 1) / 4)) := by gcongr
    _ = ((4 * thetaCuspTailDerivativeNatExpConstant 2 (R + 2)) ^ (2 : ℕ) *
        ((R : ℝ) / 2 + 3 * ((R : ℝ) ^ (2 : ℕ) + 1) / 8) *
        (1 / 2 + ((R : ℝ) ^ (2 : ℕ) + 1) / 4)) * (1 / 2 : ℝ) ^ k := by
      have hcancel : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        _ = (4 * thetaCuspTailDerivativeNatExpConstant 2 (R + 2)) ^ (2 : ℕ) *
              ((R : ℝ) / 2 + 3 * ((R : ℝ) ^ (2 : ℕ) + 1) / 8) *
              (1 / 2 + ((R : ℝ) ^ (2 : ℕ) + 1) / 4) *
              (((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) * (1 / 2 : ℝ) ^ k) := by ring
        _ = _ := by rw [hcancel]; ring

lemma log_depth_decay_mul_pow_le_inv (M n : ℕ) :
    (1 / 2 : ℝ) ^ xiCTaylorLogarithmicHaarDepth (M + 1) n *
        (((n + 1 : ℕ) : ℝ) ^ M) ≤
      1 / (((n + 1 : ℕ) : ℝ)) := by
  let q : ℕ := n + 1
  let c : ℕ := Nat.clog 2 q
  have hq : 0 < q := by dsimp [q]; omega
  have hpowNat : q ^ (M + 1) ≤ 2 ^ ((M + 1) * c) := by
    calc
      q ^ (M + 1) ≤ (2 ^ c) ^ (M + 1) :=
        Nat.pow_le_pow_left (Nat.le_pow_clog (by omega : 1 < 2) q) _
      _ = 2 ^ ((M + 1) * c) := by rw [← pow_mul, Nat.mul_comm]
  have hpowReal : (q : ℝ) ^ (M + 1) ≤ (2 : ℝ) ^ ((M + 1) * c) := by
    exact_mod_cast hpowNat
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show xiCTaylorLogarithmicHaarDepth (M + 1) n =
      (M + 1) * c by rfl]
  rw [show (1 / 2 : ℝ) ^ ((M + 1) * c) =
      1 / (2 : ℝ) ^ ((M + 1) * c) by rw [one_div_pow]]
  change 1 / (2 : ℝ) ^ ((M + 1) * c) * (q : ℝ) ^ M ≤ 1 / (q : ℝ)
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos (by norm_num) _) hqR]
  rw [pow_succ] at hpowReal
  simpa [mul_comm] using hpowReal

lemma tendsto_log_depth_decay_mul_pow (M : ℕ) :
    Tendsto (fun n : ℕ =>
      (1 / 2 : ℝ) ^ xiCTaylorLogarithmicHaarDepth (M + 1) n *
        (((n + 1 : ℕ) : ℝ) ^ M)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (by positivity) (by positivity)
  · exact Eventually.of_forall fun n => log_depth_decay_mul_pow_le_inv M n
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Choosing logarithmic depth `2m+1`, where `m` is the local Xi order, makes the degree-uniform
Haar top row negligible on the same anisotropic schedule as the finite translation edge. -/
theorem tendsto_scheduled_dyadicHaarRemainderKernel_mul_localOrder_zero
    {D : ℕ → ℕ} (sigma : ℂ) :
    Tendsto (fun n : ℕ =>
      |∫ p : ℝ × ℝ,
          xiCTaylorThetaTailCoreDyadicHaarRemainderKernel
            (D (xiCTaylorAnisotropicScheduleStage sigma n))
            (xiCTaylorAnisotropicCenteredPoint sigma n)
            (xiCTaylorLogarithmicHaarDepth
              (2 * (analyticOrderAt xi sigma).toNat + 1) n) p
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))| *
        (((n + 1 : ℕ) : ℝ) ^
          (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  let M : ℕ := 2 * (analyticOrderAt xi sigma).toNat
  let C : ℝ := (4 * thetaCuspTailDerivativeNatExpConstant 2 (R + 2)) ^ (2 : ℕ) *
    ((R : ℝ) / 2 + 3 * ((R : ℝ) ^ (2 : ℕ) + 1) / 8) *
    (1 / 2 + ((R : ℝ) ^ (2 : ℕ) + 1) / 4)
  have hmajor : Tendsto (fun n : ℕ => C *
      ((1 / 2 : ℝ) ^ xiCTaylorLogarithmicHaarDepth (M + 1) n *
        (((n + 1 : ℕ) : ℝ) ^ M))) atTop (nhds 0) := by
    simpa using (tendsto_log_depth_decay_mul_pow M).const_mul C
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (abs_nonneg _)
      (pow_nonneg (by positivity) _)
  · filter_upwards [hz] with n hzn
    have hrow :=
      abs_integral_xiCTaylorThetaTailCoreDyadicHaarRemainderKernel_le_half_pow
        (D (xiCTaylorAnisotropicScheduleStage sigma n)) R
        (xiCTaylorLogarithmicHaarDepth (M + 1) n)
        (xiCTaylorAnisotropicCenteredPoint sigma n) hzn
    have hq : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ M) := by positivity
    simpa only [M, C] using mul_le_mul_of_nonneg_right hrow hq
  · convert hmajor using 1
    funext n
    dsimp [M, C]
    ring

end
end RHTower

namespace RHTower

noncomputable section

/-- Density-integrated value of the exact positive-phase translation edge. -/
def thetaCuspTailPhaseTranslationEdgeAverage
    (d : ℕ) (z : ℂ) (a : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      (finitePositivePhaseTranslationTopEdge d x a).eval z

/-- Density-integrated spectral derivative of the exact positive-phase translation edge. -/
def thetaCuspTailPhaseTranslationEdgeDerivativeAverage
    (d : ℕ) (z : ℂ) (a : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      (finitePositivePhaseTranslationTopEdge d x a).derivative.eval z

/-- The self-current of the complete density-integrated phase edge. -/
def thetaCuspTailPhaseTranslationEdgeIntegratedCurrent
    (d : ℕ) (z : ℂ) (a : ℝ) : ℝ :=
  (thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a *
    (starRingEnd ℂ) (thetaCuspTailPhaseTranslationEdgeAverage d z a)).im

lemma norm_thetaCuspTailPhaseTranslationEdgeAverage_le
    (d : ℕ) (z : ℂ) (a : ℝ) :
    ‖thetaCuspTailPhaseTranslationEdgeAverage d z a‖ ≤
      ∫ x : ℝ in Ioi 0,
        |thetaCuspTailSecondDensity x| *
          ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖ := by
  unfold thetaCuspTailPhaseTranslationEdgeAverage
  calc
    ‖∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          (finitePositivePhaseTranslationTopEdge d x a).eval z‖ ≤
      ∫ x : ℝ in Ioi 0,
        ‖(thetaCuspTailSecondDensity x : ℂ) *
          (finitePositivePhaseTranslationTopEdge d x a).eval z‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp

lemma norm_thetaCuspTailPhaseTranslationEdgeDerivativeAverage_le
    (d : ℕ) (z : ℂ) (a : ℝ) :
    ‖thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a‖ ≤
      ∫ x : ℝ in Ioi 0,
        |thetaCuspTailSecondDensity x| *
          ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ := by
  unfold thetaCuspTailPhaseTranslationEdgeDerivativeAverage
  calc
    ‖∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          (finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ ≤
      ∫ x : ℝ in Ioi 0,
        ‖(thetaCuspTailSecondDensity x : ℂ) *
          (finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp

/-- The exact integrated edge current is dominated by the square of the joint value--derivative
edge envelope.  Keeping the sum intact avoids separating the cosine and sine channels. -/
theorem abs_thetaCuspTailPhaseTranslationEdgeIntegratedCurrent_le_sq
    (d : ℕ) (z : ℂ) (a : ℝ) :
    |thetaCuspTailPhaseTranslationEdgeIntegratedCurrent d z a| ≤
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm d z a ^ (2 : ℕ) := by
  let V : ℝ := ∫ x : ℝ in Ioi 0,
    |thetaCuspTailSecondDensity x| *
      ‖(finitePositivePhaseTranslationTopEdge d x a).eval z‖
  let W : ℝ := ∫ x : ℝ in Ioi 0,
    |thetaCuspTailSecondDensity x| *
      ‖(finitePositivePhaseTranslationTopEdge d x a).derivative.eval z‖
  have hV : ‖thetaCuspTailPhaseTranslationEdgeAverage d z a‖ ≤ V :=
    norm_thetaCuspTailPhaseTranslationEdgeAverage_le d z a
  have hW : ‖thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a‖ ≤ W :=
    norm_thetaCuspTailPhaseTranslationEdgeDerivativeAverage_le d z a
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  unfold thetaCuspTailPhaseTranslationEdgeIntegratedCurrent
  calc
    |(thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a *
        (starRingEnd ℂ) (thetaCuspTailPhaseTranslationEdgeAverage d z a)).im| ≤
      ‖thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a *
        (starRingEnd ℂ) (thetaCuspTailPhaseTranslationEdgeAverage d z a)‖ :=
      Complex.abs_im_le_norm _
    _ = ‖thetaCuspTailPhaseTranslationEdgeDerivativeAverage d z a‖ *
        ‖thetaCuspTailPhaseTranslationEdgeAverage d z a‖ := by simp
    _ ≤ W * V := mul_le_mul hW hV (norm_nonneg _) hW0
    _ ≤ (V + W) ^ (2 : ℕ) := by nlinarith
    _ = thetaCuspTailPhaseTranslationEdgeIntegratedNorm d z a ^ (2 : ℕ) := by
      unfold thetaCuspTailPhaseTranslationEdgeIntegratedNorm
      dsimp [V, W]

/-- The exact scheduled integrated top-edge self-current beats twice the local Xi-order. -/
theorem tendsto_scheduled_thetaCuspTailPhaseTranslationEdgeIntegratedCurrent_localOrder
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) :
    Tendsto (fun n : ℕ =>
      |thetaCuspTailPhaseTranslationEdgeIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| *
        (((n + 1 : ℕ) : ℝ) ^
          (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
  let S : ℕ → ℝ := fun n =>
    thetaCuspTailPhaseTranslationEdgeIntegratedNorm
      (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
      (xiCTaylorAnisotropicCenteredPoint sigma n)
      (xiCTaylorLogarithmicHaarDisplacement A n)
  let M : ℕ := 2 * (analyticOrderAt xi sigma).toNat
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  have hd := le_xiCTaylorScheduledThetaTailDepth hD sigma
  have hS0 : Tendsto S atTop (nhds 0) := by
    simpa only [S, pow_zero, mul_one] using
      tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero
        A 0 R hR
          (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1) hd
          (xiCTaylorAnisotropicCenteredPoint sigma) hz
  have hSM : Tendsto (fun n => S n * (((n + 1 : ℕ) : ℝ) ^ M))
      atTop (nhds 0) := by
    simpa only [S, M] using
      tendsto_scheduled_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_localOrder
        hD A sigma
  have hmajor : Tendsto (fun n => S n *
      (S n * (((n + 1 : ℕ) : ℝ) ^ M))) atTop (nhds 0) := by
    simpa using hS0.mul hSM
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (abs_nonneg _)
      (pow_nonneg (by positivity) _)
  · filter_upwards [] with n
    have hcurrent := abs_thetaCuspTailPhaseTranslationEdgeIntegratedCurrent_le_sq
      (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
      (xiCTaylorAnisotropicCenteredPoint sigma n)
      (xiCTaylorLogarithmicHaarDisplacement A n)
    have hq : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ M) := by positivity
    calc
      |thetaCuspTailPhaseTranslationEdgeIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| *
          ((n + 1 : ℕ) : ℝ) ^ M ≤
        S n ^ (2 : ℕ) * ((n + 1 : ℕ) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right hcurrent hq
      _ = S n * (S n * ((n + 1 : ℕ) : ℝ) ^ M) := by ring
  · simpa only [M] using hmajor

/-- **Sublinear upper current of the finite translation edge.**  At logarithmic Haar depth the
absolute exact integrated edge current is `o(n) |P|^(2 : ℕ)` on every anisotropic rational mesh. -/
theorem eventually_abs_scheduled_thetaCuspTailPhaseTranslationEdgeIntegratedCurrent_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |thetaCuspTailPhaseTranslationEdgeIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  apply eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
    hD sigma (fun n =>
      |thetaCuspTailPhaseTranslationEdgeIntegratedCurrent
        (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (xiCTaylorAnisotropicCenteredPoint sigma n)
        (xiCTaylorLogarithmicHaarDisplacement A n)|)
  · exact tendsto_scheduled_thetaCuspTailPhaseTranslationEdgeIntegratedCurrent_localOrder
      hD A sigma
  · exact hepsilon

end

end RHTower

namespace RHTower

noncomputable section

/-- One local-order logarithmic Haar depth simultaneously removes the cofinal row and the exact
finite translation-edge current on the anisotropic mesh. -/
theorem eventually_logarithmicHaarTopRow_and_phaseEdgeCurrent_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |∫ p : ℝ × ℝ,
          xiCTaylorThetaTailCoreDyadicHaarRemainderKernel
            (D (xiCTaylorAnisotropicScheduleStage sigma n))
            (xiCTaylorAnisotropicCenteredPoint sigma n)
            (xiCTaylorLogarithmicHaarDepth
              (2 * (analyticOrderAt xi sigma).toNat + 1) n) p
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) ∧
      |thetaCuspTailPhaseTranslationEdgeIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement
            (2 * (analyticOrderAt xi sigma).toNat + 1) n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  have htop := eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
    hD sigma (fun n =>
      |∫ p : ℝ × ℝ,
          xiCTaylorThetaTailCoreDyadicHaarRemainderKernel
            (D (xiCTaylorAnisotropicScheduleStage sigma n))
            (xiCTaylorAnisotropicCenteredPoint sigma n)
            (xiCTaylorLogarithmicHaarDepth
              (2 * (analyticOrderAt xi sigma).toNat + 1) n) p
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))|)
    (tendsto_scheduled_dyadicHaarRemainderKernel_mul_localOrder_zero
      (D := D) sigma) hepsilon
  have hedge :=
    eventually_abs_scheduled_thetaCuspTailPhaseTranslationEdgeIntegratedCurrent_lt_scaled_normSq
      hD (2 * (analyticOrderAt xi sigma).toNat + 1) sigma hepsilon
  exact htop.and hedge

end

end RHTower

namespace RHTower

noncomputable section

/-- Density-integrated value of the reflected negative-phase translation edge. -/
def thetaCuspTailNegativePhaseTranslationEdgeAverage
    (d : ℕ) (z : ℂ) (a : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      (finiteNegativePhaseTranslationTopEdge d x a).eval z

/-- Density-integrated derivative of the reflected negative-phase translation edge. -/
def thetaCuspTailNegativePhaseTranslationEdgeDerivativeAverage
    (d : ℕ) (z : ℂ) (a : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity x : ℂ) *
      (finiteNegativePhaseTranslationTopEdge d x a).derivative.eval z

/-- The self-current of the complete density-integrated negative-phase edge. -/
def thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent
    (d : ℕ) (z : ℂ) (a : ℝ) : ℝ :=
  (thetaCuspTailNegativePhaseTranslationEdgeDerivativeAverage d z a *
    (starRingEnd ℂ) (thetaCuspTailNegativePhaseTranslationEdgeAverage d z a)).im

/-- Reflection transports the complete negative-phase value average to the positive channel. -/
theorem thetaCuspTailNegativePhaseTranslationEdgeAverage_eq_positive_neg
    (d : ℕ) (z : ℂ) (a : ℝ) :
    thetaCuspTailNegativePhaseTranslationEdgeAverage d z a =
      thetaCuspTailPhaseTranslationEdgeAverage d (-z) a := by
  unfold thetaCuspTailNegativePhaseTranslationEdgeAverage
    thetaCuspTailPhaseTranslationEdgeAverage
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [finiteNegativePhaseTranslationTopEdge_eval_eq_positive_eval_neg]

/-- The reflected derivative has the chain-rule sign and no further error. -/
theorem thetaCuspTailNegativePhaseTranslationEdgeDerivativeAverage_eq_neg_positive_neg
    (d : ℕ) (z : ℂ) (a : ℝ) :
    thetaCuspTailNegativePhaseTranslationEdgeDerivativeAverage d z a =
      -thetaCuspTailPhaseTranslationEdgeDerivativeAverage d (-z) a := by
  unfold thetaCuspTailNegativePhaseTranslationEdgeDerivativeAverage
    thetaCuspTailPhaseTranslationEdgeDerivativeAverage
  rw [← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [finiteNegativePhaseTranslationTopEdge_derivative_eval_eq_neg_positive_derivative_eval_neg]
  ring

/-- The two diagonal phase-edge currents are opposite at reflected spectral points. -/
theorem thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent_eq_neg_positive_neg
    (d : ℕ) (z : ℂ) (a : ℝ) :
    thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent d z a =
      -thetaCuspTailPhaseTranslationEdgeIntegratedCurrent d (-z) a := by
  rw [thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent,
    thetaCuspTailNegativePhaseTranslationEdgeAverage_eq_positive_neg,
    thetaCuspTailNegativePhaseTranslationEdgeDerivativeAverage_eq_neg_positive_neg]
  unfold thetaCuspTailPhaseTranslationEdgeIntegratedCurrent
  simp

/-- Absolute negative-channel current is controlled by the same joint edge envelope at `-z`. -/
theorem abs_thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent_le_sq
    (d : ℕ) (z : ℂ) (a : ℝ) :
    |thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent d z a| ≤
      thetaCuspTailPhaseTranslationEdgeIntegratedNorm d (-z) a ^ (2 : ℕ) := by
  rw [thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent_eq_neg_positive_neg, abs_neg]
  exact abs_thetaCuspTailPhaseTranslationEdgeIntegratedCurrent_le_sq d (-z) a

/-- The reflected phase-edge current beats twice the local Xi-order on the same one-sided
anisotropic mesh.  The proof uses only boundedness of the reflected spectral points, not a
reflection of the mesh or of the Taylor denominator. -/
theorem tendsto_scheduled_thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent_localOrder
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) :
    Tendsto (fun n : ℕ =>
      |thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| *
        (((n + 1 : ℕ) : ℝ) ^
          (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
  let S : ℕ → ℝ := fun n =>
    thetaCuspTailPhaseTranslationEdgeIntegratedNorm
      (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
      (-xiCTaylorAnisotropicCenteredPoint sigma n)
      (xiCTaylorLogarithmicHaarDisplacement A n)
  let M : ℕ := 2 * (analyticOrderAt xi sigma).toNat
  obtain ⟨R, hR, hz⟩ :=
    exists_eventually_xiCTaylorAnisotropicCenteredPoint_norm_le_nat sigma
  have hzneg : ∀ᶠ n : ℕ in atTop,
      ‖-xiCTaylorAnisotropicCenteredPoint sigma n‖ ≤ R := by
    simpa only [norm_neg] using hz
  have hd := le_xiCTaylorScheduledThetaTailDepth hD sigma
  have hS0 : Tendsto S atTop (nhds 0) := by
    simpa only [S, pow_zero, mul_one] using
      tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero
        A 0 R hR
          (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1) hd
          (fun n => -xiCTaylorAnisotropicCenteredPoint sigma n) hzneg
  have hSM : Tendsto (fun n => S n * (((n + 1 : ℕ) : ℝ) ^ M))
      atTop (nhds 0) := by
    simpa only [S] using
      tendsto_thetaCuspTailPhaseTranslationEdgeIntegratedNorm_mul_pow_zero
        A M R hR
          (fun n => D (xiCTaylorAnisotropicScheduleStage sigma n) + 1) hd
          (fun n => -xiCTaylorAnisotropicCenteredPoint sigma n) hzneg
  have hmajor : Tendsto (fun n => S n *
      (S n * (((n + 1 : ℕ) : ℝ) ^ M))) atTop (nhds 0) := by
    simpa using hS0.mul hSM
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => mul_nonneg (abs_nonneg _)
      (pow_nonneg (by positivity) _)
  · filter_upwards [] with n
    have hcurrent := abs_thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent_le_sq
      (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
      (xiCTaylorAnisotropicCenteredPoint sigma n)
      (xiCTaylorLogarithmicHaarDisplacement A n)
    have hq : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ M) := by positivity
    calc
      |thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| *
          ((n + 1 : ℕ) : ℝ) ^ M ≤
        S n ^ (2 : ℕ) * ((n + 1 : ℕ) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right hcurrent hq
      _ = S n * (S n * ((n + 1 : ℕ) : ℝ) ^ M) := by ring
  · simpa only [M] using hmajor

/-- **Sublinear reflected edge current.**  The negative diagonal finite translation edge is also
`o(n) |P|^(2 : ℕ)` on every source-selected anisotropic rational mesh. -/
theorem eventually_abs_scheduled_thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (A : ℕ) (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement A n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  apply eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
    hD sigma (fun n =>
      |thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent
        (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
        (xiCTaylorAnisotropicCenteredPoint sigma n)
        (xiCTaylorLogarithmicHaarDisplacement A n)|)
  · exact
      tendsto_scheduled_thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent_localOrder
        hD A sigma
  · exact hepsilon

/-- A single local-order logarithmic Haar depth simultaneously removes the cofinal row and both
exact diagonal phase-edge currents.  This is the complete two-component finite-translation gate. -/
theorem eventually_logarithmicHaarTopRow_and_twoPhaseEdgeCurrents_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      |∫ p : ℝ × ℝ,
          xiCTaylorThetaTailCoreDyadicHaarRemainderKernel
            (D (xiCTaylorAnisotropicScheduleStage sigma n))
            (xiCTaylorAnisotropicCenteredPoint sigma n)
            (xiCTaylorLogarithmicHaarDepth
              (2 * (analyticOrderAt xi sigma).toNat + 1) n) p
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) ∧
      |thetaCuspTailPhaseTranslationEdgeIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement
            (2 * (analyticOrderAt xi sigma).toNat + 1) n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) ∧
      |thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent
          (D (xiCTaylorAnisotropicScheduleStage sigma n) + 1)
          (xiCTaylorAnisotropicCenteredPoint sigma n)
          (xiCTaylorLogarithmicHaarDisplacement
            (2 * (analyticOrderAt xi sigma).toNat + 1) n)| <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  have hpositive :=
    eventually_logarithmicHaarTopRow_and_phaseEdgeCurrent_lt_scaled_normSq
      hD sigma hepsilon
  have hnegative :=
    eventually_abs_scheduled_thetaCuspTailNegativePhaseTranslationEdgeIntegratedCurrent_lt_scaled_normSq
      hD (2 * (analyticOrderAt xi sigma).toNat + 1) sigma hepsilon
  filter_upwards [hpositive, hnegative] with n hpos hneg
  exact ⟨hpos.1, hpos.2, hneg⟩

end

end RHTower
