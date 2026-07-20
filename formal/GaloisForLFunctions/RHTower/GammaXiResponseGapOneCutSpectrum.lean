import GaloisForLFunctions.RHTower.GammaJordanXiTangentResponseGap
import GaloisForLFunctions.RHTower.GammaVerticalRatioAsymptotic
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The one-cut Krein spectrum of the Gamma--Xi response gap

The joined Gamma--Jordan response has spectral density `2 s² f_{1/2}(s)`, while the
all-depth Xi tangent response has density `s² f_1(s)` in the common hyperbolic coordinate.
This file proves that their exact density difference has one and only one positive spectral
cut.  Thus its global translation-invariant extension cannot itself be a Hilbert variogram: its
canonical global structure is a difference of a high-frequency Hilbert channel and a
low-frequency Hilbert channel.  This does not decide negative type after restriction to the
inverse-prime chamber.

The new input is the synthesis.  Its parent ingredients are already unconditional in the corpus:
strict horizontal monotonicity of the imaginary digamma profile and the vertical Gamma-ratio
asymptotic.
-/

noncomputable section

open Complex Filter Real Set

namespace RHTower

/-! ## The two exact spectral densities -/

/-- The ratio `f₁/f_{1/2}` of the two generalized hyperbolic-secant spectral densities. -/
def gammaXiResponseSpectralRatio (s : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) *
    Complex.normSq
      (Complex.Gamma ((1 : ℝ) / 2 + (s / 2) * Complex.I)) /
    Complex.normSq
      (Complex.Gamma ((1 : ℝ) / 4 + (s / 2) * Complex.I))

/-- The Xi-tangent density `f₁`, expressed intrinsically relative to the already constructed
Gamma density `f_{1/2}`. -/
def xiTangentSpectralDensity (s : ℝ) : ℝ :=
  gammaXiResponseSpectralRatio s * semilocalArchimedeanGammaDensity s

/-- The signed density of the joined-Gamma response minus the Xi tangent response. -/
def gammaXiResponseGapSpectralDensity (s : ℝ) : ℝ :=
  s ^ 2 * semilocalArchimedeanGammaDensity s *
    (2 - gammaXiResponseSpectralRatio s)

/-- The normalized joined-Gamma response law `A(s)=2s²f_{1/2}(s)`. -/
def gammaJordanResponseSpectralDensity (s : ℝ) : ℝ :=
  2 * s ^ 2 * semilocalArchimedeanGammaDensity s

/-- The normalized Xi-tangent response law `B(s)=s²f₁(s)`. -/
def xiShiftTangentResponseSpectralDensity (s : ℝ) : ℝ :=
  s ^ 2 * xiTangentSpectralDensity s

theorem xiTangentSpectralDensity_eq_normalized_Gamma (s : ℝ) :
    xiTangentSpectralDensity s =
      (2 * Real.pi)⁻¹ *
        Complex.normSq
          (Complex.Gamma ((1 : ℝ) / 2 + (s / 2) * Complex.I)) := by
  have hbase : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hquarter : Complex.normSq
      (Complex.Gamma ((1 : ℝ) / 4 + (s / 2) * Complex.I)) ≠ 0 := by
    exact (Complex.normSq_pos.mpr <| Complex.Gamma_ne_zero fun n hn => by
      have hre := congrArg Complex.re hn
      norm_num at hre
      linarith [Nat.cast_nonneg (α := ℝ) n]).ne'
  unfold xiTangentSpectralDensity gammaXiResponseSpectralRatio
    semilocalArchimedeanGammaDensity
  rw [Real.sqrt_eq_rpow]
  calc
    (2 * Real.pi) ^ (1 / 2 : ℝ) *
          Complex.normSq (Complex.Gamma ((1 : ℝ) / 2 + (s / 2) * Complex.I)) /
          Complex.normSq (Complex.Gamma ((1 : ℝ) / 4 + (s / 2) * Complex.I)) *
        ((2 * Real.pi) ^ (-(3 : ℝ) / 2) *
          Complex.normSq (Complex.Gamma ((1 : ℝ) / 4 + (s / 2) * Complex.I))) =
        ((2 * Real.pi) ^ (1 / 2 : ℝ) *
          (2 * Real.pi) ^ (-(3 : ℝ) / 2)) *
          Complex.normSq (Complex.Gamma ((1 : ℝ) / 2 + (s / 2) * Complex.I)) := by
            simp only [Complex.normSq_eq_norm_sq] at hquarter ⊢
            field_simp [hquarter]
            apply mul_div_cancel_right₀
            exact norm_ne_zero_iff.mpr <| Complex.Gamma_ne_zero fun n hn => by
              have hre := congrArg Complex.re hn
              norm_num at hre
              linarith [Nat.cast_nonneg (α := ℝ) n]
    _ = (2 * Real.pi) ^ (-1 : ℝ) *
          Complex.normSq (Complex.Gamma ((1 : ℝ) / 2 + (s / 2) * Complex.I)) := by
            rw [← Real.rpow_add hbase]
            norm_num
    _ = (2 * Real.pi)⁻¹ *
          Complex.normSq (Complex.Gamma ((1 : ℝ) / 2 + (s / 2) * Complex.I)) := by
            rw [Real.rpow_neg_one]

theorem semilocalArchimedeanGammaDensity_pos (s : ℝ) :
    0 < semilocalArchimedeanGammaDensity s := by
  unfold semilocalArchimedeanGammaDensity
  apply mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) Real.pi_pos) _)
  exact Complex.normSq_pos.mpr <| Complex.Gamma_ne_zero fun n hn => by
    have hre := congrArg Complex.re hn
    norm_num at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]

theorem gammaXiResponseSpectralRatio_pos (s : ℝ) :
    0 < gammaXiResponseSpectralRatio s := by
  unfold gammaXiResponseSpectralRatio
  have hhalf : 0 < Complex.normSq
      (Complex.Gamma ((1 : ℝ) / 2 + (s / 2) * Complex.I)) :=
    Complex.normSq_pos.mpr <| Complex.Gamma_ne_zero fun n hn => by
      have hre := congrArg Complex.re hn
      norm_num at hre
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hquarter : 0 < Complex.normSq
      (Complex.Gamma ((1 : ℝ) / 4 + (s / 2) * Complex.I)) :=
    Complex.normSq_pos.mpr <| Complex.Gamma_ne_zero fun n hn => by
      have hre := congrArg Complex.re hn
      norm_num at hre
      linarith [Nat.cast_nonneg (α := ℝ) n]
  positivity

theorem gammaXiResponseGapSpectralDensity_eq_sub (s : ℝ) :
    gammaXiResponseGapSpectralDensity s =
      gammaJordanResponseSpectralDensity s -
        xiShiftTangentResponseSpectralDensity s := by
  unfold gammaXiResponseGapSpectralDensity gammaJordanResponseSpectralDensity
    xiShiftTangentResponseSpectralDensity xiTangentSpectralDensity
  ring

theorem xiShiftTangentResponseSpectralDensity_eq_ratio_mul_gamma
    (s : ℝ) :
    xiShiftTangentResponseSpectralDensity s =
      (gammaXiResponseSpectralRatio s / 2) *
        gammaJordanResponseSpectralDensity s := by
  unfold xiShiftTangentResponseSpectralDensity xiTangentSpectralDensity
    gammaJordanResponseSpectralDensity
  ring

/-! ## Strict spectral-ratio flow -/

/-- Logarithmic form of the density ratio. -/
def gammaXiResponseSpectralLogRatio (s : ℝ) : ℝ :=
  Real.log (Real.sqrt (2 * Real.pi)) +
    2 *
      (Real.log ‖Complex.Gamma ((1 : ℝ) / 2 + (s / 2) * Complex.I)‖ -
        Real.log ‖Complex.Gamma ((1 : ℝ) / 4 + (s / 2) * Complex.I)‖)

private theorem gammaVerticalArg_ne_neg_nat {a t : ℝ} (ha : 0 < a) (n : ℕ) :
    (a : ℂ) + (t : ℂ) * Complex.I ≠ -(n : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Vertical Cauchy--Riemann form of the logarithmic Gamma derivative. -/
theorem hasDerivAt_log_norm_Gamma_vertical {a t : ℝ} (ha : 0 < a) :
    HasDerivAt
      (fun u : ℝ =>
        Real.log ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖)
      (-(Complex.digamma ((a : ℂ) + (t : ℂ) * Complex.I)).im) t := by
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have hz : ∀ n : ℕ, z ≠ -(n : ℂ) := fun n => gammaVerticalArg_ne_neg_nat ha n
  have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hz
  have harg : HasDerivAt
      (fun u : ℝ => (a : ℂ) + (u : ℂ) * Complex.I) Complex.I t := by
    have hu : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := t)
    simpa using hu.mul_const Complex.I |>.const_add (a : ℂ)
  have hΓd : HasDerivAt Complex.Gamma (deriv Complex.Gamma z) z :=
    (Complex.differentiableAt_Gamma z hz).hasDerivAt
  have hu : HasDerivAt
      (fun u : ℝ => Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I))
      (deriv Complex.Gamma z * Complex.I) t := by
    simpa [z] using hΓd.comp t harg
  have hure : HasDerivAt
      (fun u : ℝ => (Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)).re)
      (deriv Complex.Gamma z * Complex.I).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hu
  have huim : HasDerivAt
      (fun u : ℝ => (Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)).im)
      (deriv Complex.Gamma z * Complex.I).im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hu
  let B : ℝ := 2 *
    ((Complex.Gamma z).re * (deriv Complex.Gamma z * Complex.I).re +
      (Complex.Gamma z).im * (deriv Complex.Gamma z * Complex.I).im)
  have hnsq : HasDerivAt
      (fun u : ℝ => Complex.normSq
        (Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I))) B t := by
    have h := hure.mul hure |>.add (huim.mul huim)
    rw [show (fun u : ℝ => Complex.normSq
        (Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I))) =
      fun u : ℝ =>
        (Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)).re ^ 2 +
          (Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)).im ^ 2 by
      funext u
      rw [Complex.normSq_apply]
      ring]
    convert h using 1
    · funext u
      simp only [Pi.add_apply, Pi.mul_apply, pow_two]
    · dsimp [B]
      ring
  have hn0 : Complex.normSq (Complex.Gamma z) ≠ 0 :=
    fun h => hΓ (Complex.normSq_eq_zero.mp h)
  have hlog := (Real.hasDerivAt_log hn0).comp t hnsq
  have hscaled := hlog.const_mul (1 / 2 : ℝ)
  change HasDerivAt
      (fun u : ℝ => (1 / 2 : ℝ) * Real.log
        (Complex.normSq
          (Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I))))
      _ t at hscaled
  have hfun :
      (fun u : ℝ =>
        (1 / 2 : ℝ) * Real.log
          (Complex.normSq
            (Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)))) =
      fun u : ℝ =>
        Real.log ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ := by
    funext u
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    ring
  rw [hfun] at hscaled
  convert hscaled using 1
  rw [Complex.digamma_def, logDeriv_apply, Complex.div_im]
  dsimp [B, z]
  field_simp
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_sub]
  ring

theorem hasDerivAt_gammaXiResponseSpectralLogRatio {s : ℝ} :
    HasDerivAt gammaXiResponseSpectralLogRatio
      (ReflectedDigammaAnomaly.verticalDigammaIm (1 / 4) (s / 2) -
        ReflectedDigammaAnomaly.verticalDigammaIm (1 / 2) (s / 2)) s := by
  have hhalf := (hasDerivAt_log_norm_Gamma_vertical
    (a := (1 : ℝ) / 2) (t := s / 2) (by norm_num)).comp s
      ((hasDerivAt_id s).div_const 2)
  have hquarter := (hasDerivAt_log_norm_Gamma_vertical
    (a := (1 : ℝ) / 4) (t := s / 2) (by norm_num)).comp s
      ((hasDerivAt_id s).div_const 2)
  unfold gammaXiResponseSpectralLogRatio
  convert (hhalf.sub hquarter).const_mul 2 |>.const_add
    (Real.log (Real.sqrt (2 * Real.pi))) using 1
  · funext u
    simp only [Function.comp_apply, Pi.sub_apply, id_eq]
    congr 3 <;> push_cast <;> ring
  · unfold ReflectedDigammaAnomaly.verticalDigammaIm
    ring

theorem gammaXiResponseSpectralLogRatio_deriv_pos {s : ℝ} (hs : 0 < s) :
    0 < deriv gammaXiResponseSpectralLogRatio s := by
  rw [(hasDerivAt_gammaXiResponseSpectralLogRatio (s := s)).deriv]
  exact sub_pos.mpr <| ReflectedDigammaAnomaly.verticalDigammaIm_strictAnti
    (sigma := (1 : ℝ) / 4) (tau := (1 : ℝ) / 2) (t := s / 2)
      (by norm_num) (by norm_num) (by positivity)

theorem gammaXiResponseSpectralLogRatio_strictMonoOn :
    StrictMonoOn gammaXiResponseSpectralLogRatio (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro s _hs
    exact (hasDerivAt_gammaXiResponseSpectralLogRatio (s := s)).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ici, mem_Ioi] at hs
    exact gammaXiResponseSpectralLogRatio_deriv_pos hs

theorem gammaXiResponseSpectralRatio_eq_exp_logRatio (s : ℝ) :
    gammaXiResponseSpectralRatio s =
      Real.exp (gammaXiResponseSpectralLogRatio s) := by
  have hc : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 <|
    mul_pos (by norm_num) Real.pi_pos
  have hhalf : 0 < ‖Complex.Gamma
      ((1 : ℝ) / 2 + (s / 2) * Complex.I)‖ := norm_pos_iff.mpr <|
    Complex.Gamma_ne_zero fun n hn => by
      have hre := congrArg Complex.re hn
      norm_num at hre
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hquarter : 0 < ‖Complex.Gamma
      ((1 : ℝ) / 4 + (s / 2) * Complex.I)‖ := norm_pos_iff.mpr <|
    Complex.Gamma_ne_zero fun n hn => by
      have hre := congrArg Complex.re hn
      norm_num at hre
      linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold gammaXiResponseSpectralRatio gammaXiResponseSpectralLogRatio
  rw [Real.exp_add, Real.exp_log hc]
  rw [show 2 * (Real.log ‖Complex.Gamma
        ((1 : ℝ) / 2 + (s / 2) * Complex.I)‖ -
      Real.log ‖Complex.Gamma
        ((1 : ℝ) / 4 + (s / 2) * Complex.I)‖) =
      (Real.log ‖Complex.Gamma
          ((1 : ℝ) / 2 + (s / 2) * Complex.I)‖ +
        Real.log ‖Complex.Gamma
          ((1 : ℝ) / 2 + (s / 2) * Complex.I)‖) -
      (Real.log ‖Complex.Gamma
          ((1 : ℝ) / 4 + (s / 2) * Complex.I)‖ +
        Real.log ‖Complex.Gamma
          ((1 : ℝ) / 4 + (s / 2) * Complex.I)‖) by ring,
    Real.exp_sub, Real.exp_add, Real.exp_add,
    Real.exp_log hhalf, Real.exp_log hquarter,
    Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_eq_norm_sq, div_eq_mul_inv]
  ring

theorem gammaXiResponseSpectralRatio_strictMonoOn :
    StrictMonoOn gammaXiResponseSpectralRatio (Ici 0) := by
  intro a ha b hb hab
  rw [gammaXiResponseSpectralRatio_eq_exp_logRatio,
    gammaXiResponseSpectralRatio_eq_exp_logRatio, Real.exp_lt_exp]
  exact gammaXiResponseSpectralLogRatio_strictMonoOn ha hb hab

/-- The Xi-shift tangent response is strictly larger than the Gamma--Jordan response in
monotone-likelihood-ratio order on the positive spectral half-line.  The cross-product form
avoids division at the common quadratic zero at the origin. -/
theorem xiShift_vs_gammaResponseSpectra_strictMonotoneLikelihoodRatio
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    xiShiftTangentResponseSpectralDensity t *
        gammaJordanResponseSpectralDensity s >
      xiShiftTangentResponseSpectralDensity s *
        gammaJordanResponseSpectralDensity t := by
  have ht : 0 < t := hs.trans hst
  have hratio : gammaXiResponseSpectralRatio s <
      gammaXiResponseSpectralRatio t :=
    gammaXiResponseSpectralRatio_strictMonoOn hs.le ht.le hst
  have hAs : 0 < gammaJordanResponseSpectralDensity s := by
    unfold gammaJordanResponseSpectralDensity
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hs))
      (semilocalArchimedeanGammaDensity_pos s)
  have hAt : 0 < gammaJordanResponseSpectralDensity t := by
    unfold gammaJordanResponseSpectralDensity
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos ht))
      (semilocalArchimedeanGammaDensity_pos t)
  rw [xiShiftTangentResponseSpectralDensity_eq_ratio_mul_gamma,
    xiShiftTangentResponseSpectralDensity_eq_ratio_mul_gamma]
  calc
    (gammaXiResponseSpectralRatio t / 2 *
          gammaJordanResponseSpectralDensity t) *
        gammaJordanResponseSpectralDensity s =
        (gammaXiResponseSpectralRatio t / 2) *
          (gammaJordanResponseSpectralDensity t *
            gammaJordanResponseSpectralDensity s) := by ring
    _ > (gammaXiResponseSpectralRatio s / 2) *
          (gammaJordanResponseSpectralDensity t *
            gammaJordanResponseSpectralDensity s) :=
      mul_lt_mul_of_pos_right (by linarith) (mul_pos hAt hAs)
    _ = (gammaXiResponseSpectralRatio s / 2 *
          gammaJordanResponseSpectralDensity s) *
        gammaJordanResponseSpectralDensity t := by ring

theorem gammaXiResponseSpectralRatio_even (s : ℝ) :
    gammaXiResponseSpectralRatio (-s) = gammaXiResponseSpectralRatio s := by
  unfold gammaXiResponseSpectralRatio
  have hhalf :
      (1 : ℂ) / 2 + (-(s : ℂ)) / 2 * Complex.I =
        starRingEnd ℂ ((1 : ℂ) / 2 + (s : ℂ) / 2 * Complex.I) := by
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> ring
  have hquarter :
      (1 : ℂ) / 4 + (-(s : ℂ)) / 2 * Complex.I =
        starRingEnd ℂ ((1 : ℂ) / 4 + (s : ℂ) / 2 * Complex.I) := by
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> ring
  push_cast
  rw [hhalf, hquarter, Complex.Gamma_conj, Complex.Gamma_conj]
  simp [Complex.normSq_apply]

theorem gammaXiResponseSpectralRatio_abs (s : ℝ) :
    gammaXiResponseSpectralRatio |s| = gammaXiResponseSpectralRatio s := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_nonpos hs, gammaXiResponseSpectralRatio_even]

/-! ## The endpoint and far-field sides of the cut -/

theorem gammaXiResponseSpectralRatio_zero_lt_two :
    gammaXiResponseSpectralRatio 0 < 2 := by
  have hquarterPos : 0 < Real.Gamma ((1 : ℝ) / 4) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hthreeQuarterPos : 0 < Real.Gamma ((3 : ℝ) / 4) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hanti : Real.Gamma ((3 : ℝ) / 4) < Real.Gamma ((1 : ℝ) / 4) :=
    Real.Gamma_strictAntiOn_Ioc
      (show (1 / 4 : ℝ) ∈ Ioc 0 1 by norm_num)
      (show (3 / 4 : ℝ) ∈ Ioc 0 1 by norm_num)
      (by norm_num)
  have hdup := Real.Gamma_mul_Gamma_add_half_of_pos
    (s := (1 : ℝ) / 4) (by norm_num)
  have hdup' :
      Real.Gamma ((1 : ℝ) / 4) * Real.Gamma ((3 : ℝ) / 4) =
        Real.sqrt 2 * Real.pi := by
    rw [show (1 / 4 : ℝ) + 1 / 2 = 3 / 4 by norm_num,
      show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num,
      Real.Gamma_one_half_eq] at hdup
    have hsqrtTwo : (2 : ℝ) ^ (1 - 1 / 2 : ℝ) = Real.sqrt 2 := by
      norm_num [← Real.sqrt_eq_rpow]
    rw [hsqrtTwo] at hdup
    calc
      Real.Gamma ((1 : ℝ) / 4) * Real.Gamma ((3 : ℝ) / 4) =
          Real.sqrt Real.pi * Real.sqrt 2 * Real.sqrt Real.pi := hdup
      _ = Real.sqrt 2 * (Real.sqrt Real.pi) ^ 2 := by ring
      _ = Real.sqrt 2 * Real.pi := by rw [Real.sq_sqrt Real.pi_nonneg]
  have hsquare : Real.sqrt 2 * Real.pi < Real.Gamma ((1 : ℝ) / 4) ^ 2 := by
    rw [← hdup', pow_two]
    exact mul_lt_mul_of_pos_left hanti hquarterPos
  have hsqrtMul : Real.sqrt (2 * Real.pi) =
      Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hnum :
      Real.sqrt (2 * Real.pi) * Real.pi <
        Real.sqrt Real.pi * Real.Gamma ((1 : ℝ) / 4) ^ 2 := by
    rw [hsqrtMul]
    calc
      Real.sqrt 2 * Real.sqrt Real.pi * Real.pi =
          Real.sqrt Real.pi * (Real.sqrt 2 * Real.pi) := by ring
      _ < Real.sqrt Real.pi * Real.Gamma ((1 : ℝ) / 4) ^ 2 :=
        mul_lt_mul_of_pos_left hsquare (Real.sqrt_pos.2 Real.pi_pos)
  have hratio :
      Real.sqrt (2 * Real.pi) * Real.pi /
          Real.Gamma ((1 : ℝ) / 4) ^ 2 < Real.sqrt Real.pi := by
    rw [div_lt_iff₀ (sq_pos_of_pos hquarterPos)]
    simpa [mul_comm] using hnum
  have hsqrtPi : Real.sqrt Real.pi < 2 := by
    nlinarith [Real.sq_sqrt Real.pi_nonneg, Real.pi_lt_four,
      Real.sqrt_nonneg Real.pi]
  have hhalfNorm : Complex.normSq (Complex.Gamma ((1 : ℂ) / 2)) =
      Real.pi := by
    rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.Gamma_ofReal, Complex.normSq_ofReal, Real.Gamma_one_half_eq,
      Real.mul_self_sqrt Real.pi_nonneg]
  have hquarterNorm : Complex.normSq (Complex.Gamma ((1 : ℂ) / 4)) =
      Real.Gamma ((1 : ℝ) / 4) ^ 2 := by
    rw [show (1 : ℂ) / 4 = ((1 / 4 : ℝ) : ℂ) by norm_num,
      Complex.Gamma_ofReal, Complex.normSq_ofReal, pow_two]
  calc
    gammaXiResponseSpectralRatio 0 =
        Real.sqrt (2 * Real.pi) * Real.pi /
          Real.Gamma ((1 : ℝ) / 4) ^ 2 := by
      unfold gammaXiResponseSpectralRatio
      norm_num only [zero_div, Complex.ofReal_zero, zero_mul, add_zero]
      change Real.sqrt (2 * Real.pi) *
          Complex.normSq (Complex.Gamma ((1 : ℂ) / 2)) /
          Complex.normSq (Complex.Gamma ((1 : ℂ) / 4)) = _
      rw [hhalfNorm, hquarterNorm]
    _ < Real.sqrt Real.pi := hratio
    _ < 2 := hsqrtPi

theorem gammaXiResponseSpectralLogRatio_tendsto_atTop :
    Tendsto gammaXiResponseSpectralLogRatio atTop atTop := by
  have hscale : Tendsto (fun s : ℝ => s / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  let E : ℝ → ℝ := fun τ =>
    (Real.log ‖Complex.Gamma (((1 : ℝ) / 4 : ℂ) + (τ : ℂ) * Complex.I)‖ -
      Real.log ‖Complex.Gamma (((1 / 4 + 1 / 4 : ℝ) : ℂ) +
        (τ : ℂ) * Complex.I)‖) +
      (1 / 4 : ℝ) * Real.log τ
  have herror : Tendsto (E ∘ fun s : ℝ => s / 2) atTop (nhds 0) := by
    simpa [E] using (gamma_vertical_ratio_log_tendsto
      (a := (1 : ℝ) / 4) (δ := (1 : ℝ) / 4) (by norm_num) (by norm_num)).comp hscale
  have hlog : Tendsto (fun s : ℝ => Real.log (s / 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp hscale
  rw [tendsto_atTop]
  intro M
  have herrorSmall := herror.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 by norm_num))
  have hlogLarge := (tendsto_atTop.1 hlog)
    (2 * (M + |Real.log (Real.sqrt (2 * Real.pi))| + 3))
  filter_upwards [herrorSmall, hlogLarge] with s hsError hsLog
  rw [dist_zero_right, Real.norm_eq_abs, abs_lt] at hsError
  simp only [Function.comp_apply] at hsError
  unfold gammaXiResponseSpectralLogRatio
  have hrewrite :
      Real.log ‖Complex.Gamma ((1 : ℝ) / 2 + (s / 2) * Complex.I)‖ -
          Real.log ‖Complex.Gamma ((1 : ℝ) / 4 + (s / 2) * Complex.I)‖ =
        (1 / 4 : ℝ) * Real.log (s / 2) - E (s / 2) := by
    dsimp only [E]
    norm_num
  rw [hrewrite]
  have hconst : -|Real.log (Real.sqrt (2 * Real.pi))| ≤
      Real.log (Real.sqrt (2 * Real.pi)) := neg_abs_le _
  nlinarith

theorem gammaXiResponseSpectralRatio_tendsto_atTop :
    Tendsto gammaXiResponseSpectralRatio atTop atTop := by
  have h := Real.tendsto_exp_atTop.comp gammaXiResponseSpectralLogRatio_tendsto_atTop
  exact h.congr' <| Filter.Eventually.of_forall fun s =>
    (gammaXiResponseSpectralRatio_eq_exp_logRatio s).symm

/-! ## The unique cut and the exact sign chambers -/

theorem exists_unique_gammaXiResponseSpectralCutoff :
    ∃! s : ℝ, 0 < s ∧ gammaXiResponseSpectralRatio s = 2 := by
  have hlarge := gammaXiResponseSpectralRatio_tendsto_atTop.eventually_gt_atTop 2
  have hpos : ∀ᶠ s : ℝ in atTop, 0 < s := eventually_gt_atTop 0
  obtain ⟨B, hB, hBpos⟩ := (hlarge.and hpos).exists
  have hcont : ContinuousOn gammaXiResponseSpectralRatio (Icc 0 B) := by
    rw [show gammaXiResponseSpectralRatio = fun s =>
        Real.exp (gammaXiResponseSpectralLogRatio s) by
      funext s
      exact gammaXiResponseSpectralRatio_eq_exp_logRatio s]
    intro s _hs
    exact (Real.continuous_exp.continuousAt.comp
      (hasDerivAt_gammaXiResponseSpectralLogRatio (s := s)).continuousAt).continuousWithinAt
  have hmem : (2 : ℝ) ∈ Icc
      (gammaXiResponseSpectralRatio 0) (gammaXiResponseSpectralRatio B) :=
    ⟨gammaXiResponseSpectralRatio_zero_lt_two.le, hB.le⟩
  obtain ⟨s, hsIcc, hsEq⟩ :=
    (intermediate_value_Icc (show (0 : ℝ) ≤ B by linarith) hcont) hmem
  have hspos : 0 < s := by
    rcases hsIcc.1.eq_or_lt with hzero | hpos'
    · subst s
      linarith [gammaXiResponseSpectralRatio_zero_lt_two]
    · exact hpos'
  refine ⟨s, ⟨hspos, hsEq⟩, ?_⟩
  intro u hu
  have hu0 : u ∈ Ici (0 : ℝ) := hu.1.le
  have hs0 : s ∈ Ici (0 : ℝ) := hspos.le
  exact (gammaXiResponseSpectralRatio_strictMonoOn.injOn hs0 hu0
    (hsEq.trans hu.2.symm)).symm

/-- The canonical positive spectral cut. -/
def gammaXiResponseSpectralCutoff : ℝ :=
  Classical.choose exists_unique_gammaXiResponseSpectralCutoff

theorem gammaXiResponseSpectralCutoff_pos :
    0 < gammaXiResponseSpectralCutoff :=
  (Classical.choose_spec exists_unique_gammaXiResponseSpectralCutoff).1.1

theorem gammaXiResponseSpectralRatio_cutoff :
    gammaXiResponseSpectralRatio gammaXiResponseSpectralCutoff = 2 :=
  (Classical.choose_spec exists_unique_gammaXiResponseSpectralCutoff).1.2

theorem gammaXiResponseSpectralRatio_lt_two_iff
    {s : ℝ} (hs : 0 ≤ s) :
    gammaXiResponseSpectralRatio s < 2 ↔
      s < gammaXiResponseSpectralCutoff := by
  constructor
  · intro hratio
    by_contra hnot
    have hcutle : gammaXiResponseSpectralCutoff ≤ s := le_of_not_gt hnot
    rcases hcutle.eq_or_lt with heq | hlt
    · rw [← heq, gammaXiResponseSpectralRatio_cutoff] at hratio
      exact lt_irrefl _ hratio
    · have hmono := gammaXiResponseSpectralRatio_strictMonoOn
        gammaXiResponseSpectralCutoff_pos.le hs hlt
      rw [gammaXiResponseSpectralRatio_cutoff] at hmono
      linarith
  · intro hslt
    have hmono := gammaXiResponseSpectralRatio_strictMonoOn hs
      gammaXiResponseSpectralCutoff_pos.le hslt
    rwa [gammaXiResponseSpectralRatio_cutoff] at hmono

theorem gammaXiResponseSpectralRatio_eq_two_iff
    {s : ℝ} (hs : 0 ≤ s) :
    gammaXiResponseSpectralRatio s = 2 ↔
      s = gammaXiResponseSpectralCutoff := by
  constructor
  · intro h
    exact (Classical.choose_spec exists_unique_gammaXiResponseSpectralCutoff).2 s ⟨
      lt_of_le_of_ne hs (by
        intro hzero
        subst s
        linarith [gammaXiResponseSpectralRatio_zero_lt_two]), h⟩
  · rintro rfl
    exact gammaXiResponseSpectralRatio_cutoff

theorem gammaXiResponseSpectralRatio_gt_two_iff
    {s : ℝ} (hs : 0 ≤ s) :
    2 < gammaXiResponseSpectralRatio s ↔
      gammaXiResponseSpectralCutoff < s := by
  constructor
  · intro hratio
    by_contra hnot
    have hsle : s ≤ gammaXiResponseSpectralCutoff := le_of_not_gt hnot
    rcases hsle.eq_or_lt with heq | hlt
    · rw [heq, gammaXiResponseSpectralRatio_cutoff] at hratio
      exact lt_irrefl _ hratio
    · have hmono := gammaXiResponseSpectralRatio_strictMonoOn hs
        gammaXiResponseSpectralCutoff_pos.le hlt
      rw [gammaXiResponseSpectralRatio_cutoff] at hmono
      linarith
  · intro hlt
    have hmono := gammaXiResponseSpectralRatio_strictMonoOn
      gammaXiResponseSpectralCutoff_pos.le hs hlt
    rwa [gammaXiResponseSpectralRatio_cutoff] at hmono

theorem gammaXiResponseGapSpectralDensity_pos_iff (s : ℝ) :
    0 < gammaXiResponseGapSpectralDensity s ↔
      0 < |s| ∧ |s| < gammaXiResponseSpectralCutoff := by
  rw [gammaXiResponseGapSpectralDensity]
  have hdensity := semilocalArchimedeanGammaDensity_pos s
  have hratioAbs := gammaXiResponseSpectralRatio_abs s
  constructor
  · intro h
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      norm_num at h
    have hfactor : 0 < 2 - gammaXiResponseSpectralRatio s := by
      by_contra hnot
      have hle : 2 - gammaXiResponseSpectralRatio s ≤ 0 := le_of_not_gt hnot
      have hleft : 0 ≤ s ^ 2 * semilocalArchimedeanGammaDensity s :=
        mul_nonneg (sq_nonneg s) hdensity.le
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hleft hle)) h
    have hlt : |s| < gammaXiResponseSpectralCutoff :=
      (gammaXiResponseSpectralRatio_lt_two_iff (abs_nonneg s)).mp <| by
        rw [hratioAbs]
        linarith
    exact ⟨abs_pos.mpr hs0, hlt⟩
  · rintro ⟨hs0, hlt⟩
    have hratio : gammaXiResponseSpectralRatio s < 2 := by
      rw [← hratioAbs]
      exact (gammaXiResponseSpectralRatio_lt_two_iff (abs_nonneg s)).mpr hlt
    exact mul_pos (mul_pos (sq_pos_of_ne_zero (abs_pos.mp hs0)) hdensity) (by linarith)

theorem gammaXiResponseGapSpectralDensity_eq_zero_iff (s : ℝ) :
    gammaXiResponseGapSpectralDensity s = 0 ↔
      s = 0 ∨ |s| = gammaXiResponseSpectralCutoff := by
  unfold gammaXiResponseGapSpectralDensity
  rw [mul_eq_zero, mul_eq_zero]
  have hdensity : semilocalArchimedeanGammaDensity s ≠ 0 :=
    (semilocalArchimedeanGammaDensity_pos s).ne'
  simp only [hdensity, or_false, sq_eq_zero_iff, sub_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr <| (gammaXiResponseSpectralRatio_eq_two_iff (abs_nonneg s)).mp <| by
        rw [gammaXiResponseSpectralRatio_abs]
        exact h.symm
  · intro h
    rcases h with rfl | hcut
    · exact Or.inl rfl
    · exact Or.inr <| by
        have := (gammaXiResponseSpectralRatio_eq_two_iff (abs_nonneg s)).mpr hcut
        rw [gammaXiResponseSpectralRatio_abs] at this
        exact this.symm

theorem gammaXiResponseGapSpectralDensity_neg_iff (s : ℝ) :
    gammaXiResponseGapSpectralDensity s < 0 ↔
      gammaXiResponseSpectralCutoff < |s| := by
  unfold gammaXiResponseGapSpectralDensity
  have hdensity := semilocalArchimedeanGammaDensity_pos s
  have hcut := gammaXiResponseSpectralCutoff_pos
  have hratioAbs := gammaXiResponseSpectralRatio_abs s
  constructor
  · intro h
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      norm_num at h
    have hfactor : 2 - gammaXiResponseSpectralRatio s < 0 := by
      by_contra hnot
      have hge : 0 ≤ 2 - gammaXiResponseSpectralRatio s := le_of_not_gt hnot
      exact (not_lt_of_ge (mul_nonneg
        (mul_nonneg (sq_nonneg s) hdensity.le) hge)) h
    exact (gammaXiResponseSpectralRatio_gt_two_iff (abs_nonneg s)).mp <| by
      rw [hratioAbs]
      linarith
  · intro hlt
    have hratio : 2 < gammaXiResponseSpectralRatio s := by
      rw [← hratioAbs]
      exact (gammaXiResponseSpectralRatio_gt_two_iff (abs_nonneg s)).mpr hlt
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      simp at hlt
      linarith
    exact mul_neg_of_pos_of_neg
      (mul_pos (sq_pos_of_ne_zero hs0) hdensity) (by linarith)

/-- The exact three-chamber one-cut law. -/
theorem gammaXiResponseGapSpectralDensity_oneCut (s : ℝ) :
    (0 < gammaXiResponseGapSpectralDensity s ↔
        0 < |s| ∧ |s| < gammaXiResponseSpectralCutoff) ∧
      (gammaXiResponseGapSpectralDensity s = 0 ↔
        s = 0 ∨ |s| = gammaXiResponseSpectralCutoff) ∧
      (gammaXiResponseGapSpectralDensity s < 0 ↔
        gammaXiResponseSpectralCutoff < |s|) := by
  exact ⟨gammaXiResponseGapSpectralDensity_pos_iff s,
    gammaXiResponseGapSpectralDensity_eq_zero_iff s,
    gammaXiResponseGapSpectralDensity_neg_iff s⟩

end RHTower
