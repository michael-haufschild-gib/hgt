import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailAllConductorBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailShift
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinFullTwoTail

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

private theorem cglLemma62_tail_ordinate_shifted_power_le
    (t v : ℝ) (n : ℕ) :
    (1 + |v - t|) ^ n ≤ (1 + |t|) ^ n * (1 + |v|) ^ n := by
  have hbase : 1 + |v - t| ≤ (1 + |t|) * (1 + |v|) := by
    rw [abs_sub_comm]
    have htri : |t - v| ≤ |t| + |v| := by
      calc
        |t - v| = |t + (-v)| := by ring
        _ ≤ |t| + |-v| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    nlinarith [abs_nonneg t, abs_nonneg v]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + |v - t|) hbase n
  rw [mul_pow] at hpow
  exact hpow

private theorem cglLemma62_tail_one_add_abs_power_le
    (v : ℝ) (n : ℕ) (hv : 1 ≤ |v|) :
    (1 + |v|) ^ n ≤ 2 ^ n * |v| ^ n := by
  have hbase : 1 + |v| ≤ 2 * |v| := by linarith
  calc
    (1 + |v|) ^ n ≤ (2 * |v|) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    _ = _ := mul_pow _ _ n

/-- Arbitrary polynomial decay of CGL's literal far-left complementary tail.
The Mellin order is increased by the functional-factor degree, so this is the
quantitative input for the source's finite-ordinate truncation. -/
theorem cglLemma62_farTail_rapid_point_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth)
    (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 1 ≤ |v| →
      ‖cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C / |v| ^ r := by
  rcases cglLemma62_primitiveFunctionalFactor_tail_all_factorized_bound B.primitive d with
    ⟨A, hA, hA_bound⟩
  let n : ℕ := 2 * d.value + 1 + r
  let K := cglLemma62TailMellinUniformBudget w d n
  let E := cglLemma62TailEulerConductorBudget B d
  let D : ℝ := (M.value : ℝ) ^ (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))
  let C : ℝ := K * A * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
    (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) * E * D *
    (1 + |t|) ^ (2 * d.value + 1) * 2 ^ (2 * d.value + 1)
  have hK : 0 ≤ K := by
    dsimp [K, cglLemma62TailMellinUniformBudget]
    apply integral_nonneg
    intro u
    unfold deningerMeyerBoundedMellinMajorant
    apply Finset.sum_nonneg
    intro j hj
    positivity
  have hE : 0 ≤ E := by
    let z : CGLLemma62TailEulerPoint d := ⟨(-2 * (d.value : ℝ) : ℂ), by simp⟩
    exact le_trans (norm_nonneg _)
      (cglLemma62EulerCorrectionAt_far_conductorBudget_norm_le B d z)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hden : 0 < 2 * (d.value : ℝ) := by
      have hd : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
      positivity
    positivity
  have hNpow : 0 ≤ (N.value : ℝ) ^ (-2 * (d.value : ℝ)) := by positivity
  have hqpow : 0 ≤ (B.primitive.modulus.value : ℝ) ^
      (1 / 2 + 2 * (d.value : ℝ)) := by positivity
  have htpow : 0 ≤ (1 + |t|) ^ (2 * d.value + 1) := by positivity
  have htwopow : 0 ≤ (2 : ℝ) ^ (2 * d.value + 1) := by positivity
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg hK hA) hNpow) hqpow) hE) hD) htpow) htwopow
  · intro v hv
    let p : CGLLemma62TailMellinPoint d := {
      x := -2 * (d.value : ℝ)
      y := v
      lower := by rfl
      upper := by
        have hd : (1 : ℝ) ≤ d.value := by exact_mod_cast d.positive
        linarith }
    let z : CGLLemma62TailFunctionalPoint d := {
      value := cglLemma62FarLeftPoint d v - (t : ℂ) * I
      real_eq := by
        unfold cglLemma62FarLeftPoint
        simp }
    let e : CGLLemma62TailEulerPoint d := {
      value := cglLemma62FarLeftPoint d v - (t : ℂ) * I
      real_eq := by
        unfold cglLemma62FarLeftPoint
        simp }
    have hvpos : 0 < |v| := lt_of_lt_of_le zero_lt_one hv
    have hH0 := cglLemma62_mellinTransform_tail_uniformAllOrderDecay w d n p
    have hH : ‖cglLemma62MellinTransform w (cglLemma62FarLeftPoint d v)‖ ≤
        K / |v| ^ n := by
      apply (le_div_iff₀ (pow_pos hvpos n)).mpr
      simpa [K, p, cglLemma62FarLeftPoint, mul_comm] using hH0
    have hN := cglLemma62_lengthPower_farLeft_norm_eq N d v
    have hG0 := hA_bound z
    have hGbase : (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) ≤
        (1 + |v - t|) ^ (2 * d.value + 1) := by
      calc
        _ ≤ (1 + |v - t|) ^ ((2 * d.value + 1 : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          · linarith [abs_nonneg (v - t)]
          · push_cast
            linarith
        _ = _ := Real.rpow_natCast _ _
    have hGheight : (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) ≤
        (1 + |t|) ^ (2 * d.value + 1) *
          (2 ^ (2 * d.value + 1) * |v| ^ (2 * d.value + 1)) := by
      calc
        _ ≤ (1 + |v - t|) ^ (2 * d.value + 1) := hGbase
        _ ≤ (1 + |t|) ^ (2 * d.value + 1) *
            (1 + |v|) ^ (2 * d.value + 1) :=
          cglLemma62_tail_ordinate_shifted_power_le t v _
        _ ≤ _ := by
          gcongr
          exact cglLemma62_tail_one_add_abs_power_le v _ hv
    have hG : ‖cglLemma62PrimitiveFunctionalFactor B.primitive
        (cglLemma62FarLeftPoint d v - (t : ℂ) * I)‖ ≤
        A * (B.primitive.modulus.value : ℝ) ^
          (1 / 2 + 2 * (d.value : ℝ)) *
          ((1 + |t|) ^ (2 * d.value + 1) *
            (2 ^ (2 * d.value + 1) * |v| ^ (2 * d.value + 1))) := by
      calc
        _ = ‖cglLemma62PrimitiveFunctionalFactor B.primitive z.value‖ := by rfl
        _ ≤ A * (B.primitive.modulus.value : ℝ) ^
            (1 / 2 + 2 * (d.value : ℝ)) *
            (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
              have hzIm : z.value.im = v - t := by
                dsimp [z]
                unfold cglLemma62FarLeftPoint
                simp
              simpa only [hzIm] using hG0
        _ ≤ _ := mul_le_mul_of_nonneg_left hGheight
          (mul_nonneg hA (Real.rpow_nonneg (by positivity) _))
    have hE0 := cglLemma62EulerCorrectionAt_far_conductorBudget_norm_le B d e
    have hEcorr : ‖cglLemma62EulerCorrectionAt B
        (cglLemma62FarLeftPoint d v - (t : ℂ) * I)‖ ≤ E := by
      simpa [E, e] using hE0
    have htail0 := cglLemma62_far_dirichletTail_norm_le B t d M v
    have htail : ‖cglLemma62DirichletTail B.character⁻¹ M.value
        (cglLemma62FarRightPointAC t d v)‖ ≤ D := by
      simpa [D] using htail0
    have hpower : |v| ^ (2 * d.value + 1) / |v| ^ n ≤ |v| ^ (-r : ℤ) := by
      dsimp [n]
      have hne : |v| ≠ 0 := ne_of_gt hvpos
      rw [show 2 * d.value + 1 + r = (2 * d.value + 1) + r by omega,
        pow_add, zpow_neg, zpow_natCast]
      field_simp [hne]
      rw [show 2 * d.value + 1 + r = (2 * d.value + 1) + r by omega,
        pow_add, pow_succ]
    unfold cglLemma62FarTailIntegrand
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hN]
    calc
      ‖cglLemma62MellinTransform w (cglLemma62FarLeftPoint d v)‖ *
          (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          ‖cglLemma62PrimitiveFunctionalFactor B.primitive
            (cglLemma62FarLeftPoint d v - ↑t * I)‖ *
          ‖cglLemma62EulerCorrectionAt B
            (cglLemma62FarLeftPoint d v - ↑t * I)‖ *
          ‖cglLemma62DirichletTail B.character⁻¹ M.value
            (cglLemma62FarRightPointAC t d v)‖ ≤
        (K / |v| ^ n) * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          (A * (B.primitive.modulus.value : ℝ) ^
            (1 / 2 + 2 * (d.value : ℝ)) *
            ((1 + |t|) ^ (2 * d.value + 1) *
              (2 ^ (2 * d.value + 1) * |v| ^ (2 * d.value + 1)))) * E * D := by
          gcongr
      _ = C * (|v| ^ (2 * d.value + 1) / |v| ^ n) := by
        dsimp [C]
        ring
      _ ≤ C * |v| ^ (-r : ℤ) :=
        mul_le_mul_of_nonneg_left hpower (by dsimp [C]; positivity)
      _ = C / |v| ^ r := by
        rw [zpow_neg, zpow_natCast]
        field_simp [ne_of_gt hvpos]

/-- Closed data for a symmetric rapid-decay truncation of CGL's far-left
tail.  Rate and radius side conditions are certified fields, never caller
premises. -/
structure CGLLemma62TailTruncationCertificate where
  radius : ℝ
  radius_one : 1 ≤ radius
  decayRate : ℕ
  decayRate_two : 2 ≤ decayRate

/-- The difference between CGL's full far-left tail integral and a certified
symmetric truncation is bounded by its exact two-sided power tail. -/
theorem cglLemma62_farTail_integral_sub_truncation_le_power
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth)
    (U : CGLLemma62TailTruncationCertificate) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖(∫ v : ℝ, cglLemma62FarTailIntegrand w N B t M.value d v) -
          ∫ v : ℝ in -U.radius..U.radius,
            cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        2 * C * (U.radius ^ (1 - (U.decayRate : ℝ)) /
          ((U.decayRate : ℝ) - 1)) := by
  obtain ⟨C, hC, hpoint⟩ := cglLemma62_farTail_rapid_point_bound w N B t M d U.decayRate
  have hintegrable : Integrable (fun v : ℝ =>
      cglLemma62FarTailIntegrand w N B t M.value d v) := by
    refine (cglLemma62_tailContour_left_integrable w N B t M d).congr ?_
    filter_upwards with v
    simpa [cglLemma62FarLeftPoint] using
      cglLemma62_tailContourIntegrand_eq_farTail w N B t M.value d v
  have hrate : (1 : ℝ) < U.decayRate := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) U.decayRate_two)
  have hradius : 0 < U.radius := lt_of_lt_of_le zero_lt_one U.radius_one
  have hbound : ∀ v : ℝ, U.radius ≤ |v| →
      ‖cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C * |v| ^ (-(U.decayRate : ℝ)) := by
    intro v hv
    calc
      _ ≤ C / |v| ^ U.decayRate := hpoint v (U.radius_one.trans hv)
      _ = _ := by
        rw [Real.rpow_neg (abs_nonneg v), Real.rpow_natCast]
        ring
  exact ⟨C, hC, RHTower.Sieve.norm_integral_sub_interval_le_powerTail
    hintegrable hC hrate hradius hbound⟩

end

end RHTower
