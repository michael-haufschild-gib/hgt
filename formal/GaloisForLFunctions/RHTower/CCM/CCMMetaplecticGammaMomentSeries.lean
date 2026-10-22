import GaloisForLFunctions.RHTower.CCM.CCMMetaplecticGammaMomentDeterminacy
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace RHTower

theorem semilocalArchimedeanGammaDensity_neg (s : ℝ) :
    semilocalArchimedeanGammaDensity (-s) =
      semilocalArchimedeanGammaDensity s := by
  unfold semilocalArchimedeanGammaDensity
  congr 1
  have harg :
      ((1 : ℝ) : ℂ) / 4 + ((-s : ℝ) : ℂ) / 2 * I =
        (starRingEnd ℂ) (((1 : ℝ) : ℂ) / 4 + (s : ℂ) / 2 * I) := by
    simp only [map_add, map_div₀, map_ofNat, Complex.conj_ofReal,
      map_mul, Complex.conj_I]
    push_cast
    ring
  have hgamma :
      Complex.Gamma (((1 : ℝ) : ℂ) / 4 + ((-s : ℝ) : ℂ) / 2 * I) =
        (starRingEnd ℂ)
          (Complex.Gamma (((1 : ℝ) : ℂ) / 4 + (s : ℂ) / 2 * I)) := by
    rw [← Complex.Gamma_conj]
    congr
  rw [hgamma, Complex.normSq_conj]

theorem ccmMetaplecticGammaMoment_odd (n : ℕ) :
    ccmMetaplecticGammaMoment (2 * n + 1) = 0 := by
  let f : ℝ → ℝ := fun s =>
    s ^ (2 * n + 1) * semilocalArchimedeanGammaDensity s
  have hf : Integrable f :=
    integrable_pow_mul_semilocalArchimedeanGammaDensity (2 * n + 1)
  have hpoint : (fun s : ℝ => f (-s)) = fun s : ℝ => -f s := by
    funext s
    simp only [f, semilocalArchimedeanGammaDensity_neg]
    rw [show 2 * n + 1 = 2 * n + 1 by rfl, pow_succ, pow_mul]
    ring
  have hneg := integral_neg_eq_self f (volume : Measure ℝ)
  rw [hpoint, integral_neg] at hneg
  have hzero : ∫ s : ℝ, f s = 0 := by linarith
  rw [ccmMetaplecticGammaMoment, semilocalArchimedeanGammaMeasure,
    integral_withDensity_eq_integral_smul
      continuous_semilocalArchimedeanGammaDensityNNReal.measurable]
  rw [← hzero]
  apply integral_congr_ae
  filter_upwards with s
  simp only [semilocalArchimedeanGammaDensityNNReal, f]
  change semilocalArchimedeanGammaDensity s * s ^ (2 * n + 1) =
    s ^ (2 * n + 1) * semilocalArchimedeanGammaDensity s
  ring

theorem ccmMetaplecticGammaMoment_series
    {x : ℝ} (hx : |x| ≤ Real.pi / 4) :
    HasSum (fun n : ℕ =>
      (ccmMetaplecticGammaMoment n : ℂ) *
        (I * (x : ℂ)) ^ n / (n.factorial : ℂ))
      (semilocalArchimedeanCharacteristic x : ℂ) := by
  let F : ℕ → ℝ → ℂ := fun n s =>
    ((I * (x : ℂ)) * (s : ℂ)) ^ n / (n.factorial : ℂ)
  let bound : ℕ → ℝ → ℝ := fun n s =>
    (|x| * |s|) ^ n / (n.factorial : ℝ)
  have hboundInt : Integrable (fun s : ℝ => Real.exp (|x| * |s|))
      semilocalArchimedeanGammaMeasure := by
    apply Integrable.mono'
      integrable_exp_pi_div_four_abs_semilocalArchimedeanGammaMeasure
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_abs)).aestronglyMeasurable)
    filter_upwards with s
    change |Real.exp (|x| * |s|)| ≤ Real.exp ((Real.pi / 4) * |s|)
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hx (abs_nonneg s))
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) semilocalArchimedeanGammaMeasure := by
    intro n
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  have hnorm : ∀ n, ∀ s, ‖F n s‖ = bound n s := by
    intro n s
    simp only [F, bound, norm_div, norm_pow, norm_mul, norm_I,
      Complex.norm_real, Real.norm_eq_abs, one_mul]
    norm_cast
  have hboundSummable : ∀ᵐ s ∂semilocalArchimedeanGammaMeasure,
      Summable fun n => bound n s := by
    filter_upwards with s
    simpa [bound] using
      (NormedSpace.expSeries_div_hasSum_exp (|x| * |s|)).summable
  have hboundIntegral : Integrable (fun s : ℝ => ∑' n, bound n s)
      semilocalArchimedeanGammaMeasure := by
    have heq : (fun s : ℝ => ∑' n, bound n s) =
        fun s : ℝ => Real.exp (|x| * |s|) := by
      funext s
      exact (by simpa [bound, ← Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (|x| * |s|)).tsum_eq)
    rw [heq]
    exact hboundInt
  have hlim : ∀ᵐ s ∂semilocalArchimedeanGammaMeasure,
      HasSum (fun n => F n s)
        (Complex.exp ((I * (x : ℂ)) * (s : ℂ))) := by
    filter_upwards with s
    simpa [F, ← Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp
        ((I * (x : ℂ)) * (s : ℂ)))
  have hseries := hasSum_integral_of_dominated_convergence
    (μ := semilocalArchimedeanGammaMeasure) bound hFmeas
    (fun n => Filter.Eventually.of_forall fun s => (hnorm n s).le)
    hboundSummable hboundIntegral hlim
  have hterm : ∀ n : ℕ,
      (∫ s : ℝ, F n s ∂semilocalArchimedeanGammaMeasure) =
        (ccmMetaplecticGammaMoment n : ℂ) *
          (I * (x : ℂ)) ^ n / (n.factorial : ℂ) := by
    intro n
    have hfun : F n = fun s : ℝ =>
        ((I * (x : ℂ)) ^ n / (n.factorial : ℂ)) * ((s ^ n : ℝ) : ℂ) := by
      funext s
      simp only [F]
      push_cast
      ring
    rw [hfun, integral_const_mul, integral_complex_ofReal]
    simp only [ccmMetaplecticGammaMoment]
    ring
  have hseries' := HasSum.congr_fun hseries (fun n => (hterm n).symm)
  have htarget :
      (∫ s : ℝ, Complex.exp ((I * (x : ℂ)) * (s : ℂ))
        ∂semilocalArchimedeanGammaMeasure) =
        (semilocalArchimedeanCharacteristic x : ℂ) := by
    convert integral_cexp_semilocalArchimedeanGammaMeasure x using 1
    · congr 1
      funext s
      congr 1
      push_cast
      ring
  rw [htarget] at hseries'
  exact hseries'

/-! ## The source's unrestricted series claim is false

The 2023 source states the moment expansion for every real `x`.  The density has an exponential
tail of exact rate `π`, so this cannot be a global Taylor series.  The following argument is fully
analytic.  Legendre duplication and the exact critical-line Gamma modulus give a positive lower
tail `C exp (-π|s|)`.  Consequently its even moments force the even Taylor terms at `x = π` to stay
uniformly away from zero.  Thus the series is not summable there.  This is a closed correction of
the literature claim, not a convergence assumption or numerical observation.
-/

/-- Duplication gives an explicit lower bound for the quarter-line Gamma modulus. -/
theorem norm_Gamma_quarter_add_half_height_lower (s : ℝ) :
    Real.sqrt Real.pi * Real.exp (-(Real.pi * |s| / 2)) *
          (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi /
          Real.Gamma (3 / 4)
      ≤ ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I)‖ := by
  let A : ℝ := ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I)‖
  let B : ℝ := ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (s : ℂ) * I)‖
  let D : ℝ := ‖Complex.Gamma (((3 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I)‖
  have hdup := Complex.Gamma_mul_Gamma_add_half
    (((1 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I)
  have hdupNorm := congrArg norm hdup
  simp only [norm_mul] at hdupNorm
  have hpow :
      ‖(2 : ℂ) ^ (1 - 2 * (((1 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I))‖ =
        (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    norm_num
  rw [hpow] at hdupNorm
  have hzplus :
      (((1 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I) + 1 / 2 =
        ((3 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  have h2z :
      2 * (((1 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I) =
        ((1 / 2 : ℝ) : ℂ) + (s : ℂ) * I := by
    push_cast
    ring
  rw [hzplus, h2z] at hdupNorm
  have hdupAD : A * D = B * (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    simpa only [A, B, D, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hdupNorm
  have hD : D ≤ Real.Gamma (3 / 4) := by
    dsimp only [D]
    convert (GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re
      (s := (((3 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I)) (by norm_num)) using 1
    norm_num
  have hB : Real.sqrt Real.pi * Real.exp (-(Real.pi * |s| / 2)) ≤ B := by
    dsimp only [B]
    convert (GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_bounds s).1 using 1
    norm_num
  have hA : 0 ≤ A := norm_nonneg _
  have hC : 0 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi := by positivity
  have hG : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  rw [div_le_iff₀ hG]
  have hmul := mul_le_mul_of_nonneg_right hB hC
  calc
    Real.sqrt Real.pi * Real.exp (-(Real.pi * |s| / 2)) *
          (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi
        = (Real.sqrt Real.pi * Real.exp (-(Real.pi * |s| / 2))) *
            ((2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi) := by ring
    _ ≤ B * ((2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi) := hmul
    _ = A * D := by rw [hdupAD]; ring
    _ ≤ A * Real.Gamma (3 / 4) := mul_le_mul_of_nonneg_left hD hA

/-- Positive constant in the explicit lower tail of the CCM Gamma density. -/
def ccmMetaplecticGammaLowerTailConstant : ℝ :=
  (2 * Real.pi) ^ (-(3 : ℝ) / 2) *
    (Real.sqrt Real.pi * (2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi /
      Real.Gamma (3 / 4)) ^ 2

theorem ccmMetaplecticGammaLowerTailConstant_pos :
    0 < ccmMetaplecticGammaLowerTailConstant := by
  unfold ccmMetaplecticGammaLowerTailConstant
  have hG : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  positivity

/-- Explicit global lower exponential tail for the normalized quarter-Gamma density. -/
theorem ccmMetaplecticGammaDensity_lowerTail (s : ℝ) :
    ccmMetaplecticGammaLowerTailConstant * Real.exp (-Real.pi * |s|) ≤
      semilocalArchimedeanGammaDensity s := by
  let L : ℝ := Real.sqrt Real.pi * (2 : ℝ) ^ (1 / 2 : ℝ) *
    Real.sqrt Real.pi / Real.Gamma (3 / 4)
  let A : ℝ := ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I)‖
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hlow : L * Real.exp (-(Real.pi * |s| / 2)) ≤ A := by
    dsimp only [L, A]
    convert norm_Gamma_quarter_add_half_height_lower s using 1
    ring
  have hleft : 0 ≤ L * Real.exp (-(Real.pi * |s| / 2)) :=
    mul_nonneg hL (Real.exp_pos _).le
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact norm_nonneg _
  have hsq : (L * Real.exp (-(Real.pi * |s| / 2))) ^ 2 ≤ A ^ 2 := by
    nlinarith
  have hnorm : (0 : ℝ) ≤ (2 * Real.pi) ^ (-(3 : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  calc
    ccmMetaplecticGammaLowerTailConstant * Real.exp (-Real.pi * |s|) =
        (2 * Real.pi) ^ (-(3 : ℝ) / 2) *
          (L * Real.exp (-(Real.pi * |s| / 2))) ^ 2 := by
            unfold ccmMetaplecticGammaLowerTailConstant
            dsimp only [L]
            have hexpsq : Real.exp (-(Real.pi * |s| / 2)) ^ 2 =
                Real.exp (-Real.pi * |s|) := by
              rw [sq, ← Real.exp_add]
              congr 1
              ring
            rw [mul_pow, hexpsq]
            ring
    _ ≤ (2 * Real.pi) ^ (-(3 : ℝ) / 2) * A ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hnorm
    _ = semilocalArchimedeanGammaDensity s := by
      unfold semilocalArchimedeanGammaDensity
      rw [Complex.normSq_eq_norm_sq]
      congr 2
      dsimp only [A]
      congr 1
      push_cast
      ring

/-- The Gamma density's even moments inherit the factorial lower growth forced by its lower tail. -/
theorem ccmMetaplecticGammaMoment_even_lower (n : ℕ) :
    ccmMetaplecticGammaLowerTailConstant *
        (2 * (2 * n).factorial / Real.pi ^ (2 * n + 1)) ≤
      ccmMetaplecticGammaMoment (2 * n) := by
  have hmomentEq : ccmMetaplecticGammaMoment (2 * n) =
      ∫ s : ℝ, s ^ (2 * n) * semilocalArchimedeanGammaDensity s := by
    rw [ccmMetaplecticGammaMoment, semilocalArchimedeanGammaMeasure,
      integral_withDensity_eq_integral_smul
        continuous_semilocalArchimedeanGammaDensityNNReal.measurable]
    apply integral_congr_ae
    filter_upwards with s
    simp only [semilocalArchimedeanGammaDensityNNReal]
    change semilocalArchimedeanGammaDensity s * s ^ (2 * n) =
      s ^ (2 * n) * semilocalArchimedeanGammaDensity s
    ring
  rw [hmomentEq]
  have hminor : Integrable (fun s : ℝ =>
      ccmMetaplecticGammaLowerTailConstant *
        (|s| ^ (2 * n) * Real.exp (-Real.pi * |s|))) :=
    (HTGeometry.integrable_abs_pow_mul_exp_neg_abs (2 * n) Real.pi_pos).const_mul _
  have hmajor : Integrable (fun s : ℝ =>
      s ^ (2 * n) * semilocalArchimedeanGammaDensity s) :=
    integrable_pow_mul_semilocalArchimedeanGammaDensity (2 * n)
  have hle : (∫ s : ℝ,
      ccmMetaplecticGammaLowerTailConstant *
        (|s| ^ (2 * n) * Real.exp (-Real.pi * |s|))) ≤
      ∫ s : ℝ, s ^ (2 * n) * semilocalArchimedeanGammaDensity s := by
    apply integral_mono hminor hmajor
    intro s
    have hd := ccmMetaplecticGammaDensity_lowerTail s
    have hp : 0 ≤ s ^ (2 * n) := Even.pow_nonneg (even_two_mul n) s
    have habspow : |s| ^ (2 * n) = s ^ (2 * n) := by
      calc
        |s| ^ (2 * n) = |s ^ (2 * n)| := (abs_pow s (2 * n)).symm
        _ = s ^ (2 * n) := abs_of_nonneg hp
    change ccmMetaplecticGammaLowerTailConstant *
        (|s| ^ (2 * n) * Real.exp (-Real.pi * |s|)) ≤
      s ^ (2 * n) * semilocalArchimedeanGammaDensity s
    rw [habspow]
    nlinarith [mul_le_mul_of_nonneg_left hd hp]
  calc
    ccmMetaplecticGammaLowerTailConstant *
        (2 * (2 * n).factorial / Real.pi ^ (2 * n + 1)) =
        ∫ s : ℝ, ccmMetaplecticGammaLowerTailConstant *
          (|s| ^ (2 * n) * Real.exp (-Real.pi * |s|)) := by
            rw [integral_const_mul,
              HTGeometry.integral_abs_evenPow_mul_exp_neg_abs n Real.pi_pos]
    _ ≤ _ := hle

/-- Taylor term used in the 2023 CCM moment-series proposition. -/
def ccmMetaplecticGammaMomentSeriesTerm (x : ℝ) (n : ℕ) : ℂ :=
  (ccmMetaplecticGammaMoment n : ℂ) *
    (I * (x : ℂ)) ^ n / (n.factorial : ℂ)

/-- At `x = π`, every even Taylor term has a fixed positive norm lower bound. -/
theorem ccmMetaplecticGammaMomentSeriesTerm_even_norm_lower (n : ℕ) :
    2 * ccmMetaplecticGammaLowerTailConstant / Real.pi ≤
      ‖ccmMetaplecticGammaMomentSeriesTerm Real.pi (2 * n)‖ := by
  let F : ℝ := ((2 * n).factorial : ℝ)
  let P : ℝ := Real.pi ^ (2 * n)
  let M : ℝ := ccmMetaplecticGammaMoment (2 * n)
  have hF : 0 < F := by
    dsimp only [F]
    positivity
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have hC : 0 < ccmMetaplecticGammaLowerTailConstant :=
    ccmMetaplecticGammaLowerTailConstant_pos
  have hm : ccmMetaplecticGammaLowerTailConstant * (2 * F / (P * Real.pi)) ≤ M := by
    have h := ccmMetaplecticGammaMoment_even_lower n
    rw [show Real.pi ^ (2 * n + 1) = P * Real.pi by
      dsimp only [P]
      rw [pow_succ]] at h
    simpa only [F, M] using h
  have hmpos : 0 < M := by
    have hleft : 0 < ccmMetaplecticGammaLowerTailConstant *
        (2 * F / (P * Real.pi)) := by
      positivity
    linarith
  have hscale : 0 ≤ P / F := by positivity
  have hmul := mul_le_mul_of_nonneg_right hm hscale
  have hreal : 2 * ccmMetaplecticGammaLowerTailConstant / Real.pi ≤ M * P / F := by
    calc
      2 * ccmMetaplecticGammaLowerTailConstant / Real.pi =
          (ccmMetaplecticGammaLowerTailConstant * (2 * F / (P * Real.pi))) *
            (P / F) := by
              field_simp [Real.pi_ne_zero, ne_of_gt hF, ne_of_gt hP]
      _ ≤ M * (P / F) := hmul
      _ = M * P / F := by ring
  have hnorm : ‖ccmMetaplecticGammaMomentSeriesTerm Real.pi (2 * n)‖ = M * P / F := by
    unfold ccmMetaplecticGammaMomentSeriesTerm
    rw [norm_div, norm_mul, norm_pow, norm_mul, norm_I, one_mul,
      Complex.norm_real, Complex.norm_real, Complex.norm_natCast]
    simp only [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    change |M| * P / F = M * P / F
    rw [abs_of_pos hmpos]
  rw [hnorm]
  exact hreal

/-- The 2023 CCM moment series is not summable at the explicit point `x = π`. -/
theorem ccmMetaplecticGammaMomentSeries_not_summable_at_pi :
    ¬ Summable (ccmMetaplecticGammaMomentSeriesTerm Real.pi) := by
  intro hs
  have heven : Summable
      (ccmMetaplecticGammaMomentSeriesTerm Real.pi ∘ fun n : ℕ => 2 * n) :=
    hs.comp_injective (by
      intro a b hab
      change 2 * a = 2 * b at hab
      exact Nat.mul_left_cancel (by norm_num) hab)
  have htend := heven.tendsto_atTop_zero.norm
  rw [Metric.tendsto_atTop] at htend
  have heps : 0 < ccmMetaplecticGammaLowerTailConstant / Real.pi :=
    div_pos ccmMetaplecticGammaLowerTailConstant_pos Real.pi_pos
  obtain ⟨N, hN⟩ := htend
    (ccmMetaplecticGammaLowerTailConstant / Real.pi) heps
  have hsmall := hN N le_rfl
  simp only [Function.comp_apply, norm_zero, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)] at hsmall
  have hlower := ccmMetaplecticGammaMomentSeriesTerm_even_norm_lower N
  rw [show 2 * ccmMetaplecticGammaLowerTailConstant / Real.pi =
    2 * (ccmMetaplecticGammaLowerTailConstant / Real.pi) by ring] at hlower
  linarith

/-- Hence the source's claimed value is not the sum of the moment series at `x = π`. -/
theorem ccmMetaplecticGammaMomentSeries_not_hasSum_at_pi :
    ¬ HasSum (ccmMetaplecticGammaMomentSeriesTerm Real.pi)
      (semilocalArchimedeanCharacteristic Real.pi : ℂ) := by
  intro h
  exact ccmMetaplecticGammaMomentSeries_not_summable_at_pi h.summable

/-- Closed no-go for the unrestricted-real version of the 2023 moment-series proposition. -/
theorem ccmMetaplecticGammaMomentSeries_global_literature_claim_false :
    ¬ ∀ x : ℝ, HasSum (ccmMetaplecticGammaMomentSeriesTerm x)
      (semilocalArchimedeanCharacteristic x : ℂ) := by
  intro h
  exact ccmMetaplecticGammaMomentSeries_not_hasSum_at_pi (h Real.pi)

end RHTower
