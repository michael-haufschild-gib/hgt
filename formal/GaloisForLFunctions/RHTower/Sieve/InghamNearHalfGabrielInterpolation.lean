import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielPoleClearedBound
import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielConstantBudget
import GaloisForLFunctions.HTGeometry.ClockParametricIntegralHolomorphy

/-!
# The moving Gabriel interpolation down to the critical line

The uniform Gabriel geometry of `InghamUniformGabrielBudget` (centre `σ − (1 − σ)/1000`, right edge
`1 + 9(1 − σ)/100`, interior power `4(β − 1/2)/(3β − c − 1)`) is stated there for `7/10 ≤ σ`. Every
step of the interpolation only uses that the centre lies in the strip `1/2 ≤ c ≤ β`, which holds for
`501/1001 ≤ σ`: at `σ = 501/1001` the centre is exactly `1/2` and the interior power exactly `4/3`.
This file restates the budget facts, the analytic scalar family and the interpolation inequality on
`501/1001 ≤ σ ≤ 1`, with unchanged proofs.
-/


namespace RHTower.Sieve.InghamNearHalf

noncomputable section

/-! ### From `InghamUniformGabrielDualBudget` -/

section
open Complex

theorem uniformGabrielSeedDenominator_pos
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) :
    0 < uniformGabrielSeedDenominator sigma := by
  rw [uniformGabrielSeedDenominator_eq]
  nlinarith

theorem four_thirds_le_inghamUniformGabrielInteriorPower
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    (4 / 3 : ℝ) ≤ inghamUniformGabrielInteriorPower sigma := by
  have hden : 0 < 1 + (1271 / 1000 : ℝ) * (1 - sigma) := by positivity
  rw [inghamUniformGabrielInteriorPower_eq sigma]
  rw [le_div_iff₀ hden]
  nlinarith

theorem inghamUniformGabrielSeedExponent_pos
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    0 < inghamUniformGabrielSeedExponent sigma := by
  unfold inghamUniformGabrielSeedExponent
  exact div_pos
    (uniformGabrielSeedDenominator_pos hsigma0)
    (uniformGabrielDenominator_pos hsigma1)

@[simp] theorem inghamUniformGabrielDualExponent_center
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) :
    inghamUniformGabrielDualExponent sigma
        (inghamUniformGabrielCenter sigma : ℂ) = 1 := by
  have hS := (uniformGabrielSeedDenominator_pos hsigma0).ne'
  have hnum :
      (inghamUniformGabrielCenter sigma : ℂ) +
          ((inghamUniformGabrielRightEdge sigma - 1 : ℝ) : ℂ) =
        (uniformGabrielSeedDenominator sigma : ℂ) := by
    unfold uniformGabrielSeedDenominator
    push_cast
    ring
  unfold inghamUniformGabrielDualExponent
  rw [hnum, div_self (Complex.ofReal_ne_zero.mpr hS)]

theorem inghamUniformGabriel_seed_left_identity
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    4 * inghamUniformGabrielSeedExponent sigma *
        ((inghamUniformGabrielRightEdge sigma - 1 / 2) /
          uniformGabrielSeedDenominator sigma) =
      inghamUniformGabrielInteriorPower sigma := by
  have hD := (uniformGabrielDenominator_pos hsigma1).ne'
  have hS := (uniformGabrielSeedDenominator_pos hsigma0).ne'
  unfold inghamUniformGabrielSeedExponent
    inghamUniformGabrielInteriorPower
  field_simp [hD, hS]

theorem inghamUniformGabriel_seed_right_identity
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    2 * inghamUniformGabrielSeedExponent sigma *
        (2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
          uniformGabrielSeedDenominator sigma) =
      inghamUniformGabrielInteriorPower sigma := by
  rw [show 2 * inghamUniformGabrielSeedExponent sigma *
      (2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielSeedDenominator sigma) =
      4 * inghamUniformGabrielSeedExponent sigma *
        ((inghamUniformGabrielRightEdge sigma - 1 / 2) /
          uniformGabrielSeedDenominator sigma) by ring]
  exact inghamUniformGabriel_seed_left_identity hsigma0 hsigma1

end

/-! ### From `InghamUniformGabrielDualPower` -/

section
open Complex Filter Set Topology

@[simp] theorem inghamUniformGabrielDualPower_center
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (w : ℂ) :
    inghamUniformGabrielDualPower sigma w
        (inghamUniformGabrielCenter sigma : ℂ) = w := by
  by_cases hw : w = 0
  · simp [inghamUniformGabrielDualPower, hw]
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [inghamUniformGabrielDualPower, if_neg hw,
      inghamUniformGabrielDualExponent_center hsigma0, one_mul]
    rw [← Complex.ofReal_exp, Real.exp_log hn]
    field_simp [Complex.ofReal_ne_zero.mpr hn.ne']

theorem norm_inghamUniformGabrielDualPower_left
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (w z : ℂ) (hz : z.re = 1 / 2) :
    ‖inghamUniformGabrielDualPower sigma w z‖ =
      ‖w‖ ^ ((inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielSeedDenominator sigma) := by
  have hexp : 0 < (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielSeedDenominator sigma := by
    apply div_pos
    · unfold inghamUniformGabrielRightEdge
      nlinarith
    · exact uniformGabrielSeedDenominator_pos hsigma0
  by_cases hw : w = 0
  · subst w
    rw [inghamUniformGabrielDualPower, if_pos rfl, norm_zero]
    exact (Real.zero_rpow hexp.ne').symm
  · rw [norm_inghamUniformGabrielDualPower hw,
      inghamUniformGabrielDualExponent_re_left hz]

theorem norm_inghamUniformGabrielDualPower_right
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (w z : ℂ)
    (hz : z.re = inghamUniformGabrielRightEdge sigma) :
    ‖inghamUniformGabrielDualPower sigma w z‖ =
      ‖w‖ ^ (2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielSeedDenominator sigma) := by
  have hexp : 0 < 2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielSeedDenominator sigma := by
    apply div_pos
    · unfold inghamUniformGabrielRightEdge
      nlinarith
    · exact uniformGabrielSeedDenominator_pos hsigma0
  by_cases hw : w = 0
  · subst w
    rw [inghamUniformGabrielDualPower, if_pos rfl, norm_zero]
    exact (Real.zero_rpow hexp.ne').symm
  · rw [norm_inghamUniformGabrielDualPower hw,
      inghamUniformGabrielDualExponent_re_right hz]

@[simp] theorem norm_inghamUniformGabrielDualSeed
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) (w : ℂ) :
    ‖inghamUniformGabrielDualSeed sigma w‖ =
      ‖w‖ ^ inghamUniformGabrielSeedExponent sigma := by
  have hexp := inghamUniformGabrielSeedExponent_pos hsigma0 hsigma1
  by_cases hw : w = 0
  · subst w
    simp [inghamUniformGabrielDualSeed, Real.zero_rpow hexp.ne']
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [inghamUniformGabrielDualSeed, if_neg hw, norm_mul, norm_div,
      Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w),
      Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _), div_self hn.ne', one_mul]

@[simp] theorem mul_inghamUniformGabrielDualSeed
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) (w : ℂ) :
    w * inghamUniformGabrielDualSeed sigma w =
      (↑(‖w‖ ^ inghamUniformGabrielInteriorPower sigma) : ℂ) := by
  by_cases hw : w = 0
  · subst w
    have hp : 0 < inghamUniformGabrielInteriorPower sigma := by
      rw [inghamUniformGabrielInteriorPower_eq_one_add_seedExponent hsigma1]
      have : 0 < inghamUniformGabrielSeedExponent sigma :=
        inghamUniformGabrielSeedExponent_pos hsigma0 hsigma1
      linarith
    simp [inghamUniformGabrielDualSeed, Real.zero_rpow hp.ne']
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [inghamUniformGabrielDualSeed, if_neg hw]
    have hphase : w * (starRingEnd ℂ w / (‖w‖ : ℂ)) = (‖w‖ : ℂ) := by
      rw [div_eq_mul_inv, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp [Complex.ofReal_ne_zero.mpr hn.ne']
      norm_num
    rw [← mul_assoc, hphase, ← Complex.ofReal_mul]
    norm_cast
    calc
      ‖w‖ * ‖w‖ ^ inghamUniformGabrielSeedExponent sigma =
          ‖w‖ ^ (1 : ℝ) * ‖w‖ ^ inghamUniformGabrielSeedExponent sigma := by
            rw [Real.rpow_one]
      _ = ‖w‖ ^ ((1 : ℝ) + inghamUniformGabrielSeedExponent sigma) :=
        (Real.rpow_add hn _ _).symm
      _ = ‖w‖ ^ inghamUniformGabrielInteriorPower sigma := by
        rw [inghamUniformGabrielInteriorPower_eq_one_add_seedExponent hsigma1]

theorem norm_inghamUniformGabrielDualPower_seed_left_pow_four
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (w z : ℂ) (hz : z.re = 1 / 2) :
    ‖inghamUniformGabrielDualPower sigma
        (inghamUniformGabrielDualSeed sigma w) z‖ ^ 4 =
      ‖w‖ ^ inghamUniformGabrielInteriorPower sigma := by
  rw [norm_inghamUniformGabrielDualPower_left hsigma0 hsigma1 _ _ hz,
    norm_inghamUniformGabrielDualSeed hsigma0 hsigma1]
  rw [← Real.rpow_mul (norm_nonneg w)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (norm_nonneg w)]
  congr 1
  convert inghamUniformGabriel_seed_left_identity hsigma0 hsigma1 using 1
  all_goals ring

theorem norm_inghamUniformGabrielDualPower_seed_right_pow_two
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (w z : ℂ) (hz : z.re = inghamUniformGabrielRightEdge sigma) :
    ‖inghamUniformGabrielDualPower sigma
        (inghamUniformGabrielDualSeed sigma w) z‖ ^ 2 =
      ‖w‖ ^ inghamUniformGabrielInteriorPower sigma := by
  rw [norm_inghamUniformGabrielDualPower_right hsigma0 hsigma1 _ _ hz,
    norm_inghamUniformGabrielDualSeed hsigma0 hsigma1]
  rw [← Real.rpow_mul (norm_nonneg w)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (norm_nonneg w)]
  congr 1
  convert inghamUniformGabriel_seed_right_identity hsigma0 hsigma1 using 1
  all_goals ring

theorem inghamUniformGabrielDualExponent_re_pos
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    0 < (inghamUniformGabrielDualExponent sigma z).re := by
  rw [inghamUniformGabrielDualExponent_re]
  apply div_pos
  · unfold inghamUniformGabrielRightEdge
    nlinarith
  · exact uniformGabrielSeedDenominator_pos hsigma0

/-- Moving center dual seed remains continuous across its phase singularity. -/
theorem continuous_inghamUniformGabrielDualSeed
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    Continuous (inghamUniformGabrielDualSeed sigma) := by
  have hexp := inghamUniformGabrielSeedExponent_pos hsigma0 hsigma1
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst w
    rw [ContinuousAt, show inghamUniformGabrielDualSeed sigma 0 = 0 by
      simp [inghamUniformGabrielDualSeed], tendsto_zero_iff_norm_tendsto_zero]
    rw [show (fun z : ℂ => ‖inghamUniformGabrielDualSeed sigma z‖) =
        fun z : ℂ => ‖z‖ ^ inghamUniformGabrielSeedExponent sigma by
      funext z
      exact norm_inghamUniformGabrielDualSeed hsigma0 hsigma1 z]
    have hnorm : Tendsto (fun z : ℂ => ‖z‖) (𝓝 0) (𝓝 0) :=
      by simpa using
        (((continuous_norm : Continuous fun z : ℂ => ‖z‖).continuousAt :
          ContinuousAt (fun z : ℂ => ‖z‖) (0 : ℂ)).tendsto)
    simpa [Function.comp_def, Real.zero_rpow hexp.ne'] using
      (Real.continuous_rpow_const hexp.le).continuousAt.tendsto.comp hnorm
  · have hev : ∀ᶠ z : ℂ in 𝓝 w, z ≠ 0 := eventually_ne_nhds hw
    have hcand : ContinuousAt (fun z : ℂ => starRingEnd ℂ z / (‖z‖ : ℂ) *
        (↑(‖z‖ ^ inghamUniformGabrielSeedExponent sigma) : ℂ)) w := by
      have hstar : ContinuousAt (fun z : ℂ => star z) w :=
        (continuous_star : Continuous fun z : ℂ => star z).continuousAt
      have hnormR : ContinuousAt (fun z : ℂ => ‖z‖) w :=
        (continuous_norm : Continuous fun z : ℂ => ‖z‖).continuousAt
      have hnormC : ContinuousAt (fun z : ℂ => (‖z‖ : ℂ)) w :=
        Complex.continuous_ofReal.continuousAt.comp hnormR
      have hdiv := hstar.div hnormC
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))
      have hrpowR : ContinuousAt
          (fun z : ℂ => ‖z‖ ^ inghamUniformGabrielSeedExponent sigma) w :=
        (Real.continuous_rpow_const hexp.le).continuousAt.comp hnormR
      have hrpowC : ContinuousAt
          (fun z : ℂ => (↑(‖z‖ ^ inghamUniformGabrielSeedExponent sigma) : ℂ)) w :=
        Complex.continuous_ofReal.continuousAt.comp hrpowR
      exact hdiv.mul hrpowC
    apply hcand.congr_of_eventuallyEq
    filter_upwards [hev] with z hz
    simp [inghamUniformGabrielDualSeed, hz]

end

/-! ### From `InghamUniformGabrielScalarFamily` -/

section
open Complex MeasureTheory Set

/-- Scalar family represents the moving center moment exactly. -/
theorem inghamUniformGabrielScalarFamily_center
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (f : ℂ → ℂ) (T : ℝ) :
    inghamUniformGabrielScalarFamily sigma f T
        (inghamUniformGabrielCenter sigma : ℂ) =
      (inghamUniformGabrielCenterMoment sigma f T : ℂ) := by
  rw [inghamUniformGabrielScalarFamily,
    inghamUniformGabrielCenterMoment]
  calc
    (∫ t in Icc (-T) T,
      f ((inghamUniformGabrielCenter sigma : ℂ) + t * I) *
        inghamUniformGabrielDualPower sigma
          (inghamUniformGabrielDualSeed sigma
            (f ((inghamUniformGabrielCenter sigma : ℂ) + t * I)))
          (inghamUniformGabrielCenter sigma : ℂ)) =
        ∫ t in Icc (-T) T,
          (↑(‖f ((inghamUniformGabrielCenter sigma : ℂ) + t * I)‖ ^
            inghamUniformGabrielInteriorPower sigma) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [inghamUniformGabrielDualPower_center hsigma0,
        mul_inghamUniformGabrielDualSeed hsigma0 hsigma1]
    _ = (↑(∫ t in Icc (-T) T,
        ‖f ((inghamUniformGabrielCenter sigma : ℂ) + t * I)‖ ^
          inghamUniformGabrielInteriorPower sigma) : ℂ) := integral_ofReal

theorem norm_inghamUniformGabrielScalarFamily_center
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (f : ℂ → ℂ) (T : ℝ) :
    ‖inghamUniformGabrielScalarFamily sigma f T
        (inghamUniformGabrielCenter sigma : ℂ)‖ =
      inghamUniformGabrielCenterMoment sigma f T := by
  rw [inghamUniformGabrielScalarFamily_center hsigma0 hsigma1,
    Complex.norm_real,
    Real.norm_of_nonneg (inghamUniformGabrielCenterMoment_nonneg sigma f T)]

private theorem memLp_restrict_Icc_of_continuous
    {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : Continuous g) (a b : ℝ) (p : ENNReal) :
    MemLp g p (volume.restrict (Icc a b)) :=
  _root_.RHTower.Sieve.memLp_restrict_Icc_of_continuous hg a b p

theorem norm_inghamUniformGabrielScalarFamily_left_le_of_vertical_continuous
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ} (T : ℝ) {z : ℂ}
    (hFcont : Continuous fun t : ℝ => f (z + (t : ℂ) * I))
    (hcenterCont : Continuous fun t : ℝ =>
      f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))
    (hz : z.re = 1 / 2) :
    ‖inghamUniformGabrielScalarFamily sigma f T z‖ ≤
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
          (3 / 4 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 4 : ℝ) := by
  let mu : Measure ℝ := volume.restrict (Icc (-T) T)
  let F : ℝ → ℂ := fun t => f (z + (t : ℂ) * I)
  let G : ℝ → ℂ := fun t =>
    inghamUniformGabrielDualPower sigma
      (inghamUniformGabrielDualSeed sigma
        (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z
  have hFcont' : Continuous F := by
    simpa only [F] using hFcont
  have hzexp : 0 < (inghamUniformGabrielDualExponent sigma z).re := by
    apply inghamUniformGabrielDualExponent_re_pos hsigma0 hsigma1
    rw [hz]
  have hGcont : Continuous G := by
    dsimp only [G]
    exact (continuous_inghamUniformGabrielDualPower_const sigma z hzexp).comp
      ((continuous_inghamUniformGabrielDualSeed hsigma0 hsigma1).comp hcenterCont)
  have hFLp : MemLp F (ENNReal.ofReal (4 / 3 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hFcont' (-T) T _
  have hGLp : MemLp G (ENNReal.ofReal (4 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hGcont (-T) T _
  have hpq : (4 / 3 : ℝ).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := mu) hpq hFLp hGLp
  have hGmoment : (∫ t, ‖G t‖ ^ (4 : ℝ) ∂mu) =
      inghamUniformGabrielCenterMoment sigma f T := by
    rw [inghamUniformGabrielCenterMoment]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact norm_inghamUniformGabrielDualPower_seed_left_pow_four
      hsigma0 hsigma1 _ _ hz
  rw [show (1 / (4 / 3 : ℝ)) = 3 / 4 by norm_num,
    show (1 / (4 : ℝ)) = 1 / 4 by norm_num, hGmoment] at hholder
  rw [inghamUniformGabrielScalarFamily]
  calc
    ‖∫ t in Icc (-T) T,
        f (z + (t : ℂ) * I) *
          inghamUniformGabrielDualPower sigma
            (inghamUniformGabrielDualSeed sigma
              (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z‖ ≤
      ∫ t in Icc (-T) T,
        ‖f (z + (t : ℂ) * I) *
          inghamUniformGabrielDualPower sigma
            (inghamUniformGabrielDualSeed sigma
              (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t, ‖F t‖ * ‖G t‖ ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [norm_mul]
    _ ≤ (∫ t, ‖F t‖ ^ (4 / 3 : ℝ) ∂mu) ^ (3 / 4 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 4 : ℝ) := hholder
    _ = (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
          (3 / 4 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 4 : ℝ) := rfl

theorem norm_inghamUniformGabrielScalarFamily_left_le
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ} (hf : Continuous f) (T : ℝ) {z : ℂ} (hz : z.re = 1 / 2) :
    ‖inghamUniformGabrielScalarFamily sigma f T z‖ ≤
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
          (3 / 4 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 4 : ℝ) := by
  apply norm_inghamUniformGabrielScalarFamily_left_le_of_vertical_continuous
    hsigma0 hsigma1 T
  · exact hf.comp (by fun_prop)
  · exact hf.comp (by fun_prop)
  · exact hz

theorem norm_inghamUniformGabrielScalarFamily_right_le_of_vertical_continuous
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ} (T : ℝ) {z : ℂ}
    (hFcont : Continuous fun t : ℝ => f (z + (t : ℂ) * I))
    (hcenterCont : Continuous fun t : ℝ =>
      f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))
    (hz : z.re = inghamUniformGabrielRightEdge sigma) :
    ‖inghamUniformGabrielScalarFamily sigma f T z‖ ≤
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 2 : ℝ) := by
  let mu : Measure ℝ := volume.restrict (Icc (-T) T)
  let F : ℝ → ℂ := fun t => f (z + (t : ℂ) * I)
  let G : ℝ → ℂ := fun t =>
    inghamUniformGabrielDualPower sigma
      (inghamUniformGabrielDualSeed sigma
        (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z
  have hFcont' : Continuous F := by
    simpa only [F] using hFcont
  have hzexp : 0 < (inghamUniformGabrielDualExponent sigma z).re := by
    apply inghamUniformGabrielDualExponent_re_pos hsigma0 hsigma1
    rw [hz]
    unfold inghamUniformGabrielRightEdge
    nlinarith
  have hGcont : Continuous G := by
    dsimp only [G]
    exact (continuous_inghamUniformGabrielDualPower_const sigma z hzexp).comp
      ((continuous_inghamUniformGabrielDualSeed hsigma0 hsigma1).comp hcenterCont)
  have hFLp : MemLp F (ENNReal.ofReal (2 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hFcont' (-T) T _
  have hGLp : MemLp G (ENNReal.ofReal (2 : ℝ)) mu :=
    memLp_restrict_Icc_of_continuous hGcont (-T) T _
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := mu) Real.HolderConjugate.two_two hFLp hGLp
  have hGmoment : (∫ t, ‖G t‖ ^ (2 : ℝ) ∂mu) =
      inghamUniformGabrielCenterMoment sigma f T := by
    rw [inghamUniformGabrielCenterMoment]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact norm_inghamUniformGabrielDualPower_seed_right_pow_two
      hsigma0 hsigma1 _ _ hz
  rw [show (1 / (2 : ℝ)) = 1 / 2 by norm_num, hGmoment] at hholder
  rw [inghamUniformGabrielScalarFamily]
  calc
    ‖∫ t in Icc (-T) T,
        f (z + (t : ℂ) * I) *
          inghamUniformGabrielDualPower sigma
            (inghamUniformGabrielDualSeed sigma
              (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z‖ ≤
      ∫ t in Icc (-T) T,
        ‖f (z + (t : ℂ) * I) *
          inghamUniformGabrielDualPower sigma
            (inghamUniformGabrielDualSeed sigma
              (f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t, ‖F t‖ * ‖G t‖ ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [norm_mul]
    _ ≤ (∫ t, ‖F t‖ ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 2 : ℝ) := hholder
    _ = (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 2 : ℝ) := rfl

theorem norm_inghamUniformGabrielScalarFamily_right_le
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ} (hf : Continuous f) (T : ℝ) {z : ℂ}
    (hz : z.re = inghamUniformGabrielRightEdge sigma) :
    ‖inghamUniformGabrielScalarFamily sigma f T z‖ ≤
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (inghamUniformGabrielCenterMoment sigma f T) ^ (1 / 2 : ℝ) := by
  apply norm_inghamUniformGabrielScalarFamily_right_le_of_vertical_continuous
    hsigma0 hsigma1 T
  · exact hf.comp (by fun_prop)
  · exact hf.comp (by fun_prop)
  · exact hz

end

/-! ### From `InghamUniformGabrielInterpolationBudget` -/

section

theorem inghamUniformGabrielCenter_ge_half
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) :
    1 / 2 ≤ inghamUniformGabrielCenter sigma := by
  unfold inghamUniformGabrielCenter
  nlinarith

theorem inghamUniformGabrielCenter_mem_closedStrip
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    (inghamUniformGabrielCenter sigma : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma) := by
  exact ⟨inghamUniformGabrielCenter_ge_half hsigma0,
    inghamUniformGabrielCenter_le_rightEdge hsigma1⟩

theorem inghamUniformGabrielRightWeight_nonneg
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    0 ≤ inghamUniformGabrielRightWeight sigma := by
  unfold inghamUniformGabrielRightWeight
  exact div_nonneg
    (sub_nonneg.mpr (inghamUniformGabrielCenter_ge_half hsigma0))
    (sub_nonneg.mpr (inghamUniformGabrielRightEdge_gt_half hsigma1).le)

theorem inghamUniformGabrielInteriorPower_pos
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    0 < inghamUniformGabrielInteriorPower sigma :=
  lt_of_lt_of_le (by norm_num) <|
    four_thirds_le_inghamUniformGabrielInteriorPower hsigma0 hsigma1

theorem inghamUniformGabrielReciprocalPower_pos
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    0 < inghamUniformGabrielReciprocalPower sigma := by
  rw [inghamUniformGabrielReciprocalPower_eq hsigma1]
  exact one_div_pos.mpr
    (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1)

end

/-! ### From `InghamUniformGabrielConstantBudget` -/

section

theorem inghamUniformGabrielRightShare_nonneg
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    0 ≤ inghamUniformGabrielRightShare sigma := by
  unfold inghamUniformGabrielRightShare
  exact div_nonneg
    (by
      have hc := inghamUniformGabrielCenter_ge_half hsigma0
      linarith)
    (uniformGabrielDenominator_pos hsigma1).le

theorem inghamUniformGabrielCriticalShare_le_one
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielCriticalShare sigma ≤ 1 := by
  rw [← inghamUniformGabriel_shares_sum hsigma1]
  exact le_add_of_nonneg_right
    (inghamUniformGabrielRightShare_nonneg hsigma0 hsigma1)

end

/-! ### From `InghamUniformGabrielScalarCore` -/

section
open Complex Set

/-- Variable-strip scalar-family core. Hadamard three-lines and exact cancellation leave the
reciprocal moving moment power on the center integral. -/
theorem inghamUniformGabriel_of_scalarFamily
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {H : ℂ → ℂ} {L R I : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hI : 0 < I)
    (hd : DiffContOnCl ℂ H
      (Complex.HadamardThreeLines.verticalStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hB : BddAbove ((norm ∘ H) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hleft : ∀ z ∈ Complex.re ⁻¹' {(1 / 2 : ℝ)},
      ‖H z‖ ≤ L ^ (3 / 4 : ℝ) * I ^ (1 / 4 : ℝ))
    (hright : ∀ z ∈ Complex.re ⁻¹' {inghamUniformGabrielRightEdge sigma},
      ‖H z‖ ≤ R ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ))
    (hcenter : ‖H (inghamUniformGabrielCenter sigma : ℂ)‖ = I) :
    I ^ inghamUniformGabrielReciprocalPower sigma ≤
      L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma) := by
  have hstrip := inghamUniformGabrielCenter_mem_closedStrip hsigma0 hsigma1
  have hthree :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := H) (z := (inghamUniformGabrielCenter sigma : ℂ))
      (a := L ^ (3 / 4 : ℝ) * I ^ (1 / 4 : ℝ))
      (b := R ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ))
      (l := (1 / 2 : ℝ)) (u := inghamUniformGabrielRightEdge sigma)
      (inghamUniformGabrielRightEdge_gt_half hsigma1) hstrip hd hB hleft hright
  have hweights :
      1 - (inghamUniformGabrielCenter sigma - (1 / 2 : ℝ)) /
          (inghamUniformGabrielRightEdge sigma - (1 / 2 : ℝ)) =
            inghamUniformGabrielLeftWeight sigma ∧
      (inghamUniformGabrielCenter sigma - (1 / 2 : ℝ)) /
          (inghamUniformGabrielRightEdge sigma - (1 / 2 : ℝ)) =
            inghamUniformGabrielRightWeight sigma := by
    constructor
    · have hsum := inghamUniformGabriel_weights_sum hsigma1
      unfold inghamUniformGabrielRightWeight at hsum
      linarith
    · rfl
  rw [hcenter] at hthree
  simp only [ofReal_re] at hthree
  rw [hweights.1, hweights.2] at hthree
  have hfactor :
      (L ^ (3 / 4 : ℝ) * I ^ (1 / 4 : ℝ)) ^
          inghamUniformGabrielLeftWeight sigma *
        (R ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ)) ^
          inghamUniformGabrielRightWeight sigma =
      (L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) *
      I ^ (1 - inghamUniformGabrielReciprocalPower sigma) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hI.le _),
      Real.mul_rpow (Real.rpow_nonneg hR.le _) (Real.rpow_nonneg hI.le _)]
    rw [← Real.rpow_mul hL.le, ← Real.rpow_mul hI.le,
      ← Real.rpow_mul hR.le, ← Real.rpow_mul hI.le]
    calc
      L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
          I ^ ((1 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        (R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma) *
          I ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) =
        (L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
          R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) *
        (I ^ ((1 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
          I ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) := by ring
      _ = (L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
          R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) *
        I ^ (((1 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) +
          ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) := by
        rw [← Real.rpow_add hI]
      _ = (L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
          R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) *
        I ^ (1 - inghamUniformGabrielReciprocalPower sigma) := by
        congr 2
        unfold inghamUniformGabrielReciprocalPower
        ring
  rw [hfactor] at hthree
  have hIq : 0 < I ^ (1 - inghamUniformGabrielReciprocalPower sigma) :=
    Real.rpow_pos_of_pos hI _
  apply le_of_mul_le_mul_right _ hIq
  calc
    I ^ inghamUniformGabrielReciprocalPower sigma *
        I ^ (1 - inghamUniformGabrielReciprocalPower sigma) = I := by
      rw [← Real.rpow_add hI]
      convert Real.rpow_one I using 2
      all_goals ring
    _ ≤ (L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma)) *
      I ^ (1 - inghamUniformGabrielReciprocalPower sigma) := hthree

end

/-! ### From `InghamUniformGabrielIntegralInterpolation` -/

section
open Complex MeasureTheory Set

/-- Moving Gabriel interpolation for the concrete dual scalar integral. -/
theorem inghamUniformGabrielCenterMoment_interpolate_of_vertical_continuous
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ}
    (hvertical : ∀ z : ℂ, 1 / 2 ≤ z.re →
      Continuous fun t : ℝ => f (z + (t : ℂ) * I))
    (T L R : ℝ)
    (hL : 0 < L) (hR : 0 < R)
    (hd : DiffContOnCl ℂ (inghamUniformGabrielScalarFamily sigma f T)
      (Complex.HadamardThreeLines.verticalStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hB : BddAbove ((norm ∘ inghamUniformGabrielScalarFamily sigma f T) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hleftMoment : ∀ z : ℂ, z.re = 1 / 2 →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤ L)
    (hrightMoment : ∀ z : ℂ, z.re = inghamUniformGabrielRightEdge sigma →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤ R) :
    (inghamUniformGabrielCenterMoment sigma f T) ^
        inghamUniformGabrielReciprocalPower sigma ≤
      L ^ ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        R ^ ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma) := by
  by_cases hIzero : inghamUniformGabrielCenterMoment sigma f T = 0
  · rw [hIzero, Real.zero_rpow
      (inghamUniformGabrielReciprocalPower_pos hsigma0 hsigma1).ne']
    positivity
  · have hI : 0 < inghamUniformGabrielCenterMoment sigma f T :=
      lt_of_le_of_ne
        (inghamUniformGabrielCenterMoment_nonneg sigma f T) (Ne.symm hIzero)
    apply inghamUniformGabriel_of_scalarFamily hsigma0 hsigma1 hL hR hI hd hB
    · intro z hz
      have hzre : z.re = 1 / 2 := by simpa using hz
      have hhold :=
        norm_inghamUniformGabrielScalarFamily_left_le_of_vertical_continuous
          hsigma0 hsigma1 T
          (hvertical z hzre.ge)
          (hvertical (inghamUniformGabrielCenter sigma : ℂ)
            (inghamUniformGabrielCenter_ge_half hsigma0)) hzre
      have hm0 : 0 ≤ ∫ t in Icc (-T) T,
          ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ) :=
        integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _
      have hpow :
          (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ^
              (3 / 4 : ℝ) ≤ L ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hm0 (hleftMoment z hzre) (by norm_num)
      exact hhold.trans (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg
          (inghamUniformGabrielCenterMoment_nonneg sigma f T) _))
    · intro z hz
      have hzre : z.re = inghamUniformGabrielRightEdge sigma := by simpa using hz
      have hhold :=
        norm_inghamUniformGabrielScalarFamily_right_le_of_vertical_continuous
          hsigma0 hsigma1 T
          (hvertical z (by
            rw [hzre]
            exact (inghamUniformGabrielRightEdge_gt_half hsigma1).le))
          (hvertical (inghamUniformGabrielCenter sigma : ℂ)
            (inghamUniformGabrielCenter_ge_half hsigma0)) hzre
      have hm0 : 0 ≤ ∫ t in Icc (-T) T,
          ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ) :=
        integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _
      have hpow :
          (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ^
              (1 / 2 : ℝ) ≤ R ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hm0 (hrightMoment z hzre) (by norm_num)
      exact hhold.trans (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg
          (inghamUniformGabrielCenterMoment_nonneg sigma f T) _))
    · exact norm_inghamUniformGabrielScalarFamily_center hsigma0 hsigma1 f T

/-- Raising the reciprocal-power estimate recovers the exact critical/right shares used by the
uniform exponent budget. -/
theorem inghamUniformGabrielCenterMoment_le_shares_of_vertical_continuous
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ}
    (hvertical : ∀ z : ℂ, 1 / 2 ≤ z.re →
      Continuous fun t : ℝ => f (z + (t : ℂ) * I))
    (T L R : ℝ)
    (hL : 0 < L) (hR : 0 < R)
    (hd : DiffContOnCl ℂ (inghamUniformGabrielScalarFamily sigma f T)
      (Complex.HadamardThreeLines.verticalStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hB : BddAbove ((norm ∘ inghamUniformGabrielScalarFamily sigma f T) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)))
    (hleftMoment : ∀ z : ℂ, z.re = 1 / 2 →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤ L)
    (hrightMoment : ∀ z : ℂ, z.re = inghamUniformGabrielRightEdge sigma →
      (∫ t in Icc (-T) T, ‖f (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤ R) :
    inghamUniformGabrielCenterMoment sigma f T ≤
      L ^ inghamUniformGabrielCriticalShare sigma *
        R ^ inghamUniformGabrielRightShare sigma := by
  have hbase :=
    inghamUniformGabrielCenterMoment_interpolate_of_vertical_continuous
      hsigma0 hsigma1 hvertical T L R hL hR hd hB hleftMoment hrightMoment
  have hp : 0 < inghamUniformGabrielInteriorPower sigma :=
    inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1
  have hI0 := inghamUniformGabrielCenterMoment_nonneg sigma f T
  have hpow := Real.rpow_le_rpow
    (Real.rpow_nonneg hI0 _) hbase hp.le
  rw [← Real.rpow_mul hI0] at hpow
  rw [Real.mul_rpow (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hR.le _)] at hpow
  rw [← Real.rpow_mul hL.le, ← Real.rpow_mul hR.le] at hpow
  have hrecip : inghamUniformGabrielReciprocalPower sigma *
      inghamUniformGabrielInteriorPower sigma = 1 := by
    rw [inghamUniformGabrielReciprocalPower_eq hsigma1]
    exact one_div_mul_cancel hp.ne'
  rw [hrecip, Real.rpow_one,
    show ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) *
        inghamUniformGabrielInteriorPower sigma =
      inghamUniformGabrielCriticalShare sigma by
        rw [mul_comm]
        exact inghamUniformGabriel_left_share_identity hsigma1,
    show ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma) *
        inghamUniformGabrielInteriorPower sigma =
      inghamUniformGabrielRightShare sigma by
        rw [mul_comm]
        exact inghamUniformGabriel_right_share_identity hsigma1] at hpow
  exact hpow

private theorem rpow_le_max_one_of_le
    {x C e : ℝ} (hx : 0 ≤ x) (hxC : x ≤ C) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    x ^ e ≤ max 1 C :=
  _root_.RHTower.Sieve.rpow_le_max_one_of_le hx hxC he0 he1

private theorem norm_uniformGabrielDual_seed_le_max
    {sigma C : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {w z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) (inghamUniformGabrielRightEdge sigma))
    (hw : ‖w‖ ≤ C) :
    ‖inghamUniformGabrielDualPower sigma
        (inghamUniformGabrielDualSeed sigma w) z‖ ≤ max 1 C := by
  have hA0 : 0 < (inghamUniformGabrielDualExponent sigma z).re :=
    inghamUniformGabrielDualExponent_re_pos hsigma0 hsigma1 hz.1
  have hA1 : (inghamUniformGabrielDualExponent sigma z).re ≤
      2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielSeedDenominator sigma := by
    rw [inghamUniformGabrielDualExponent_re]
    rw [div_le_div_iff_of_pos_right (uniformGabrielSeedDenominator_pos hsigma0)]
    linarith [hz.2]
  rw [norm_inghamUniformGabrielDualPower_of_pos_re sigma z _ hA0,
    norm_inghamUniformGabrielDualSeed hsigma0 hsigma1,
    ← Real.rpow_mul (norm_nonneg w)]
  apply rpow_le_max_one_of_le (norm_nonneg w) hw
  · exact mul_nonneg
      (inghamUniformGabrielSeedExponent_pos hsigma0 hsigma1).le hA0.le
  · have hseed := inghamUniformGabriel_seed_right_identity hsigma0 hsigma1
    have hbound := inghamUniformGabrielInteriorPower_le_two hsigma1
    have hseednonneg :=
      (inghamUniformGabrielSeedExponent_pos hsigma0 hsigma1).le
    have hmul : inghamUniformGabrielSeedExponent sigma *
        (inghamUniformGabrielDualExponent sigma z).re ≤
      inghamUniformGabrielSeedExponent sigma *
        (2 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
          uniformGabrielSeedDenominator sigma) :=
      mul_le_mul_of_nonneg_left hA1 hseednonneg
    nlinarith

/-- A bounded field on the moving closed strip produces a bounded scalar family. -/
theorem bddAbove_inghamUniformGabrielScalarFamily_of_bound
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    {f : ℂ → ℂ} (T C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) (inghamUniformGabrielRightEdge sigma), ‖f z‖ ≤ C) :
    BddAbove ((norm ∘ inghamUniformGabrielScalarFamily sigma f T) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)) := by
  let mu : Measure ℝ := volume.restrict (Icc (-T) T)
  refine ⟨∫ _ : ℝ, C * max 1 C ∂mu, ?_⟩
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  change ‖inghamUniformGabrielScalarFamily sigma f T z‖ ≤ _
  rw [inghamUniformGabrielScalarFamily]
  apply norm_integral_le_of_norm_le (integrable_const _)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [norm_mul]
  have hzshift : z + (t : ℂ) * I ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma) := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  have hcenter : (inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma) := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using
      inghamUniformGabrielCenter_mem_closedStrip hsigma0 hsigma1
  exact mul_le_mul (hf _ hzshift)
    (norm_uniformGabrielDual_seed_le_max hsigma0 hsigma1 (z := z)
      (w := f ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))
      hz (hf _ hcenter))
    (norm_nonneg _) hC

end

/-! ### From `InghamUniformGabrielScalarAnalytic` -/

section
open Set Complex Metric MeasureTheory intervalIntegral

private theorem differentiableOn_intervalIntegral_of_holomorphic_on_open
    {a b : ℝ} {U : Set ℂ} (hU : IsOpen U) {F : ℝ → ℂ → ℂ}
    (hFc : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (univ ×ˢ U))
    (hFd : ∀ t : ℝ, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun w => ∫ t in a..b, F t w) U :=
  _root_.RHTower.Sieve.differentiableOn_intervalIntegral_of_holomorphic_on_open hU hFc hFd

private def inghamUniformGabrielSafeHalfPlane : Set ℂ := {z | 1 / 4 < z.re}

private theorem isOpen_inghamUniformGabrielSafeHalfPlane : IsOpen inghamUniformGabrielSafeHalfPlane := by
  exact isOpen_lt continuous_const continuous_re

private def inghamUniformGabrielScalarIntegrand
    (sigma : ℝ) (X : ℕ) (kappa T : ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  inghamGabrielPoleClearedError X kappa T (z + (t : ℂ) * I) *
    inghamUniformGabrielDualPower sigma
      (inghamUniformGabrielDualSeed sigma
        (inghamGabrielPoleClearedError X kappa T
          ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))) z

private theorem continuous_inghamUniformGabrielCenterDualDatum
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (X : ℕ) (kappa T : ℝ) :
    Continuous fun t : ℝ => inghamUniformGabrielDualSeed sigma
      (inghamGabrielPoleClearedError X kappa T
        ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)) := by
  apply (continuous_inghamUniformGabrielDualSeed hsigma0 hsigma1).comp
  rw [continuous_iff_continuousAt]
  intro t
  have hpoint : (inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have hc := inghamUniformGabrielCenter_ge_half hsigma0
    simp at hre
    linarith
  exact ContinuousAt.comp
    (f := fun u : ℝ => (inghamUniformGabrielCenter sigma : ℂ) + (u : ℂ) * I)
    (analyticAt_inghamGabrielPoleClearedError X kappa T hpoint).continuousAt
    (by fun_prop)

private theorem continuousOn_inghamUniformGabrielScalarIntegrand
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (X : ℕ) (kappa T : ℝ) :
    ContinuousOn (fun q : ℝ × ℂ =>
      inghamUniformGabrielScalarIntegrand sigma X kappa T q.1 q.2)
      (univ ×ˢ inghamUniformGabrielSafeHalfPlane) := by
  intro q hq
  have hshiftPoint : q.2 + (q.1 : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have hsafe : 1 / 4 < q.2.re := hq.2
    simp at hre
    linarith
  have hfield : ContinuousAt (fun p : ℝ × ℂ =>
      inghamGabrielPoleClearedError X kappa T (p.2 + (p.1 : ℂ) * I)) q :=
    ContinuousAt.comp
      (f := fun p : ℝ × ℂ => p.2 + (p.1 : ℂ) * I)
      (analyticAt_inghamGabrielPoleClearedError X kappa T hshiftPoint).continuousAt
      (by fun_prop)
  let datum : ℝ → ℂ := fun t => inghamUniformGabrielDualSeed sigma
    (inghamGabrielPoleClearedError X kappa T
      ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I))
  have hdatum : Continuous datum :=
    continuous_inghamUniformGabrielCenterDualDatum
      hsigma0 hsigma1 X kappa T
  have hexp : 0 < (inghamUniformGabrielDualExponent sigma q.2).re := by
    have hsafe : 1 / 4 < q.2.re := hq.2
    rw [inghamUniformGabrielDualExponent_re]
    apply div_pos
    · unfold inghamUniformGabrielRightEdge
      nlinarith
    · exact uniformGabrielSeedDenominator_pos hsigma0
  have hpair := continuousAt_inghamUniformGabrielDualPower_pair
    (sigma := sigma) (w := datum q.1) (z := q.2) hexp
  have hdual : ContinuousAt (fun p : ℝ × ℂ =>
      inghamUniformGabrielDualPower sigma (datum p.1) p.2) q :=
    ContinuousAt.comp (f := fun p : ℝ × ℂ => (datum p.1, p.2)) hpair
      ((hdatum.comp continuous_fst).continuousAt.prodMk
        continuous_snd.continuousAt)
  exact (hfield.mul hdual).continuousWithinAt

private theorem differentiableOn_inghamUniformGabrielScalarIntegrand
    (sigma : ℝ) (X : ℕ) (kappa T : ℝ) (t : ℝ) :
    DifferentiableOn ℂ
      (inghamUniformGabrielScalarIntegrand sigma X kappa T t)
      inghamUniformGabrielSafeHalfPlane :=
  _root_.RHTower.Sieve.differentiableOn_inghamUniformGabrielScalarIntegrand sigma X kappa T t

private theorem differentiableOn_inghamUniformGabrielScalarFamily_poleCleared
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (X : ℕ) {kappa T : ℝ} (hT : 0 ≤ T) :
    DifferentiableOn ℂ
      (inghamUniformGabrielScalarFamily sigma
        (inghamGabrielPoleClearedError X kappa T) T)
      inghamUniformGabrielSafeHalfPlane := by
  have hdiff := differentiableOn_intervalIntegral_of_holomorphic_on_open
    isOpen_inghamUniformGabrielSafeHalfPlane
    (continuousOn_inghamUniformGabrielScalarIntegrand
      hsigma0 hsigma1 X kappa T)
    (differentiableOn_inghamUniformGabrielScalarIntegrand sigma X kappa T)
    (a := -T) (b := T)
  have heq : (fun z => inghamUniformGabrielScalarFamily sigma
      (inghamGabrielPoleClearedError X kappa T) T z) =
      fun z => ∫ t in (-T)..T,
        inghamUniformGabrielScalarIntegrand sigma X kappa T t z := by
    funext z
    rw [inghamUniformGabrielScalarFamily,
      intervalIntegral.integral_of_le (by linarith),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  change DifferentiableOn ℂ (fun z => inghamUniformGabrielScalarFamily sigma
    (inghamGabrielPoleClearedError X kappa T) T z) inghamUniformGabrielSafeHalfPlane
  rw [heq]
  exact hdiff

/-- The actual Gaussian pole-cleared coefficient-three scalar family has all strip regularity
required by Hadamard three-lines. -/
theorem diffContOnCl_inghamUniformGabrielScalarFamily_poleCleared
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (X : ℕ) {kappa T : ℝ} (hT : 0 ≤ T) :
    DiffContOnCl ℂ
      (inghamUniformGabrielScalarFamily sigma
        (inghamGabrielPoleClearedError X kappa T) T)
      (Complex.HadamardThreeLines.verticalStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)) := by
  have hdiff := differentiableOn_inghamUniformGabrielScalarFamily_poleCleared
    hsigma0 hsigma1 X (kappa := kappa) (T := T) hT
  have hclosure : closure (Complex.HadamardThreeLines.verticalStrip
      (1 / 2) (inghamUniformGabrielRightEdge sigma)) ⊆
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma) := by
    apply closure_minimal
    · intro z hz
      exact ⟨hz.1.le, hz.2.le⟩
    · exact isClosed_Icc.preimage continuous_re
  constructor
  · intro z hz
    exact (hdiff z (by
      change 1 / 4 < z.re
      linarith [hz.1])).mono (by
        intro w hw
        change 1 / 4 < w.re
        linarith [hw.1])
  · intro z hz
    have hzclosed := hclosure hz
    have hzsafe : z ∈ inghamUniformGabrielSafeHalfPlane := by
      change 1 / 4 < z.re
      linarith [hzclosed.1]
    exact (hdiff.differentiableAt
      (isOpen_inghamUniformGabrielSafeHalfPlane.mem_nhds hzsafe)).continuousAt.continuousWithinAt

end

/-! ### From `InghamUniformGabrielPoleClearedBound` -/

section
open Complex Nat ArithmeticFunction Finset Set

/-- Actual pole-cleared moving scalar family satisfies Hadamard's global boundedness premise. -/
theorem bddAbove_inghamUniformGabrielScalarFamily_poleCleared
    {sigma : ℝ} (hsigma0 : 501 / 1001 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (X : ℕ) {kappa T : ℝ} (hkappa : 0 < kappa) (hT : 0 < T) :
    BddAbove ((norm ∘ inghamUniformGabrielScalarFamily sigma
      (inghamGabrielPoleClearedError X kappa T) T) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_inghamGabrielPoleClearedError_le_halfTwoStrip X hkappa hT
  apply bddAbove_inghamUniformGabrielScalarFamily_of_bound hsigma0 hsigma1 T C hC
  intro z hz
  apply hbound z
  exact ⟨hz.1, hz.2.trans (by
    unfold inghamUniformGabrielRightEdge
    nlinarith)⟩

end


end

end RHTower.Sieve.InghamNearHalf
