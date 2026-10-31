import GaloisForLFunctions.ConjugateDiagonalGeometry.ThetaPrefixesReadHorizontalCollisionCharge
import GaloisForLFunctions.RHTower.XiThetaExplicitBounds
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# Explicit finite-theta collision rounding and height-uniform theta-current control

Unwinding the existential constants in the regularized finite-theta curvature chain yields:
1. Explicit quadratic growth `‖riemannXi z‖ ≤ exp (5 (‖z‖ + 1)²)` from the geometric Jacobi-theta
   tail bound `evenKernel 0 x - 1 ≤ 3 exp (-π x)`.
2. Explicit planar log-square (`3 · 10¹²`), finite-theta potential (`2 · 10⁹`), and scalar/pair
   current (`5 · 10¹²`) constants, together with an explicit Jensen bound on `xiStripWindowTotalOrder`.
3. A **universal height-independent stage threshold** `n ≥ 6` at which the theta-prefix
   product-current error is strictly below `1 / 8` simultaneously across all real heights `T : ℝ`.
4. An explicit closed-form fixed-window and gap-calibrated rounding stage
   `thetaCollisionRoundingStage T δ` at which `⌊finiteThetaCollisionReading T n + 1/2⌋₊` equals
   `xiHorizontalCollisionCharge T` (resolving milestones A8 and gap-calibrated B12).
5. Uniform-in-height vanishing `finiteThetaCollisionReading T n < 1 / 8` (and rounded value `0`)
   across all `T : ℝ` and `n ≥ 6` simultaneously under `RiemannHypothesis`, and equivalence with
   `RiemannHypothesis`.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace MeromorphicOn
open scoped BigOperators Laplacian Topology Classical

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ### 1. Explicit `riemannXi` growth and logarithm constants -/

/-- Explicit exponential bound on the complexified Jacobi-theta tail for `1 ≤ x`. -/
theorem norm_riemannThetaTail_le_three_exp {x : ℝ} (hx : 1 ≤ x) :
    ‖RiemannGaussian.riemannThetaTail x‖ ≤ 3 * Real.exp (-Real.pi * x) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hnonneg : 0 ≤ HurwitzZeta.evenKernel 0 x - 1 :=
    sub_nonneg.mpr (_root_.RHTower.one_le_evenKernel_zero hx0)
  have hcast : RiemannGaussian.riemannThetaTail x =
      ((HurwitzZeta.evenKernel 0 x - 1 : ℝ) : ℂ) := by
    unfold RiemannGaussian.riemannThetaTail
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact _root_.RHTower.evenKernel_zero_sub_one_le hx

/-- Explicit global quadratic growth `‖riemannXi z‖ ≤ exp (5 (‖z‖ + 1)²)` with no existential witness. -/
theorem norm_riemannXi_le_exp_five (z : ℂ) :
    ‖RiemannGaussian.riemannXi z‖ ≤ Real.exp (5 * (‖z‖ + 1) ^ 2) := by
  let R : ℝ := ‖z‖ + 1
  let T : ℝ := R ^ 2
  have hR1 : 1 ≤ R := by dsimp only [R]; linarith [norm_nonneg z]
  have hT1 : 1 ≤ T := by dsimp only [T]; nlinarith [sq_nonneg (R - 1)]
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have h2pi_le1 : 2 / Real.pi ≤ 1 := (div_le_one hpi0).mpr (by linarith)
  have h6pi_le2 : 2 * (3 : ℝ) / Real.pi ≤ 2 := (div_le_iff₀ hpi0).mpr (by linarith)
  have hcomp : ‖completedRiemannZeta₀ z‖ ≤ 2 * Real.exp T := by
    calc
      ‖completedRiemannZeta₀ z‖ ≤
          (2 * (3 : ℝ) / Real.pi) * Real.exp ((2 / Real.pi) * (‖z‖ + 1) ^ 2) :=
        RiemannGaussian.norm_completedRiemannZeta₀_le (by norm_num) hpi0
          (fun _ hx => norm_riemannThetaTail_le_three_exp hx) z
      _ ≤ 2 * Real.exp T := by
        apply mul_le_mul h6pi_le2 _ (Real.exp_nonneg _) (by norm_num)
        exact Real.exp_le_exp.mpr (by
          dsimp only [T, R]
          nlinarith [mul_le_mul_of_nonneg_right h2pi_le1 (sq_nonneg (‖z‖ + 1))])
  have hone_sub : ‖1 - z‖ ≤ R :=
    (norm_sub_le 1 z).trans (by simp [R, add_comm])
  have hpoly : ‖z‖ * ‖1 - z‖ ≤ T := by
    calc
      ‖z‖ * ‖1 - z‖ ≤ R * R :=
        mul_le_mul (by dsimp only [R]; linarith) hone_sub (norm_nonneg _) (zero_le_one.trans hR1)
      _ = T := by simp [T, pow_two]
  have hmain : ‖z * (1 - z) * completedRiemannZeta₀ z‖ ≤ 2 * T * Real.exp T := by
    rw [norm_mul, norm_mul]
    calc
      ‖z‖ * ‖1 - z‖ * ‖completedRiemannZeta₀ z‖ ≤ T * (2 * Real.exp T) :=
        mul_le_mul hpoly hcomp (norm_nonneg _) (zero_le_one.trans hT1)
      _ = 2 * T * Real.exp T := by ring
  have hE1 : 1 ≤ Real.exp T := Real.one_le_exp (zero_le_one.trans hT1)
  have hTE1 : 1 ≤ T * Real.exp T := one_le_mul_of_one_le_of_one_le hT1 hE1
  have hthree_le_exp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hsq : (2 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
    rw [← Real.exp_nat_mul] at hsq
    norm_num at hsq ⊢
    linarith
  have hT_exp : T ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  unfold RiemannGaussian.riemannXi
  calc
    ‖z * (1 - z) * completedRiemannZeta₀ z - 1‖ ≤
        ‖z * (1 - z) * completedRiemannZeta₀ z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 * T * Real.exp T + 1 := by simpa using add_le_add_right hmain 1
    _ ≤ 3 * T * Real.exp T := by linarith
    _ ≤ Real.exp 2 * Real.exp T * Real.exp T := by
      have h3T : 3 * T ≤ Real.exp 2 * Real.exp T :=
        mul_le_mul hthree_le_exp2 hT_exp (zero_le_one.trans hT1) (Real.exp_pos 2).le
      exact mul_le_mul_of_nonneg_right h3T (Real.exp_pos T).le
    _ = Real.exp (2 + T + T) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (5 * T) := Real.exp_le_exp.mpr (by linarith)

private lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have he1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hehalf : Real.exp (1 / 2) < 2 := by
    have hsq : Real.exp (1 / 2) ^ 2 < (2 : ℝ) ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
      exact he1
    nlinarith [Real.exp_pos (1 / 2)]
  have hlog := Real.log_lt_log (Real.exp_pos (1 / 2)) hehalf
  rwa [Real.log_exp] at hlog

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

/-! ### 2. Explicit planar log-square, theta-tail, and current-error constants -/

/-- Explicit polynomial constant for `∫_{closedBall 0 (n+2)} (log ‖xi z‖)² ≤ C (n + 1)⁶`. -/
def explicitXiLogSqConstant : ℝ := 3 * 10 ^ 12

/-- Explicit planar log-square integral bound on every source disc `closedBall 0 (n + 2)`. -/
theorem integral_xi_log_sq_le_explicit (n : ℕ) :
    IntegrableOn (fun z : ℂ => Real.log ‖_root_.RHTower.xi z‖ ^ 2)
      (closedBall 0 ((n : ℝ) + 2)) ∧
    (∫ z in closedBall 0 ((n : ℝ) + 2), Real.log ‖_root_.RHTower.xi z‖ ^ 2) ≤
      explicitXiLogSqConstant * ((n : ℝ) + 1) ^ 6 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ht0 : 0 ≤ (n : ℝ) + 1 := by positivity
  have ht1 : 1 ≤ (n : ℝ) + 1 := by linarith only [hn]
  have ht2 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one ht1 2
  have hR : RiemannGaussian.xiCanonicalRadius n ≤ 13 * ((n : ℝ) + 1) := by
    linarith only [(RiemannGaussian.xiCanonicalRadius_spec n).2.1, hn]
  have hR1 : RiemannGaussian.xiCanonicalRadius n + 1 ≤ 14 * ((n : ℝ) + 1) := by
    linarith only [hR, hn]
  have hR2 : 2 * RiemannGaussian.xiCanonicalRadius n + 1 ≤ 27 * ((n : ℝ) + 1) := by
    linarith only [hR, hn]
  have hr0 : 0 ≤ (n : ℝ) + 2 := by positivity
  have hr : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by linarith only [hn]
  have hrR : (n : ℝ) + 2 ≤ RiemannGaussian.xiCanonicalRadius n / 4 := by
    linarith only [(RiemannGaussian.xiCanonicalRadius_spec n).1]
  obtain ⟨hi, hraw⟩ := xi_log_sq_canonical_integrable_bound (by norm_num : (1 : ℝ) ≤ 5)
    norm_riemannXi_le_exp_five n hr0 hrR
  refine ⟨hi, ?_⟩
  have hRpos := RiemannGaussian.xiCanonicalRadius_pos n
  have hB0 : 0 ≤ 2 * (5 : ℝ) * (RiemannGaussian.xiCanonicalRadius n + 1) ^ 2 + Real.log 2 := by
    positivity
  have hB : 2 * (5 : ℝ) * (RiemannGaussian.xiCanonicalRadius n + 1) ^ 2 + Real.log 2 ≤
      1961 * ((n : ℝ) + 1) ^ 2 := by
    have h1 : 2 * (5 : ℝ) * (RiemannGaussian.xiCanonicalRadius n + 1) ^ 2 ≤
        1960 * ((n : ℝ) + 1) ^ 2 := by
      have hp := pow_le_pow_left₀ (by positivity) hR1 2
      nlinarith
    have h2 : Real.log 2 ≤ 1 * ((n : ℝ) + 1) ^ 2 :=
      log_two_le_one.trans (by linarith)
    linarith
  have hD0 : 0 ≤ (5 : ℝ) * (2 * RiemannGaussian.xiCanonicalRadius n + 1) ^ 2 / Real.log 2 := by
    positivity
  have hD : (5 : ℝ) * (2 * RiemannGaussian.xiCanonicalRadius n + 1) ^ 2 / Real.log 2 ≤
      7290 * ((n : ℝ) + 1) ^ 2 := by
    have hp := pow_le_pow_left₀ (by positivity) hR2 2
    rw [div_le_iff₀ hlog2_pos]
    have hhalf := half_lt_log_two
    nlinarith [mul_le_mul_of_nonneg_left hhalf.le (sq_nonneg ((n : ℝ) + 1))]
  have hpi4 : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hfirst :
      2 * (2 * (5 : ℝ) * (RiemannGaussian.xiCanonicalRadius n + 1) ^ 2 + Real.log 2) ^ 2 *
          (Real.pi * ((n : ℝ) + 2) ^ 2) ≤
        2 * (1961 * ((n : ℝ) + 1) ^ 2) ^ 2 * (4 * (2 * ((n : ℝ) + 1)) ^ 2) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hB 2) (by norm_num)
    · exact mul_le_mul hpi4 (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg _) (by norm_num)
    · positivity
    · positivity
  have hsecond :
      2 * ((5 : ℝ) * (2 * RiemannGaussian.xiCanonicalRadius n + 1) ^ 2 / Real.log 2) ^ 2 *
          (8 * Real.pi * (2 * RiemannGaussian.xiCanonicalRadius n) ^ 2) ≤
        2 * (7290 * ((n : ℝ) + 1) ^ 2) ^ 2 * (8 * 4 * (26 * ((n : ℝ) + 1)) ^ 2) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD0 hD 2) (by norm_num)
    · apply mul_le_mul (by linarith) _ (sq_nonneg _) (by norm_num)
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    · positivity
    · positivity
  calc
    (∫ z in closedBall 0 ((n : ℝ) + 2), Real.log ‖_root_.RHTower.xi z‖ ^ 2) ≤
        2 * (1961 * ((n : ℝ) + 1) ^ 2) ^ 2 * (4 * (2 * ((n : ℝ) + 1)) ^ 2) +
          2 * (7290 * ((n : ℝ) + 1) ^ 2) ^ 2 * (8 * 4 * (26 * ((n : ℝ) + 1)) ^ 2) :=
      hraw.trans (add_le_add hfirst hsecond)
    _ ≤ explicitXiLogSqConstant * ((n : ℝ) + 1) ^ 6 := by
      unfold explicitXiLogSqConstant
      have hp6 : 0 ≤ ((n : ℝ) + 1) ^ 6 := pow_nonneg ht0 6
      nlinarith

private lemma explicitSourceLocalError_le {n : ℕ} (hn : 1 ≤ n) :
    sourceCutoffControl n *
      xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2) ≤
    (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * explicitXiLogSqConstant * ((n : ℝ) + 1) ^ 6) *
      Real.exp (-((n : ℝ) + 1) ^ 4) := by
  have hCb := integral_xi_log_sq_le_explicit n
  have hr : 0 ≤ (n : ℝ) + 2 := by positivity
  have hK := explicitSourceLogScale_ge_four hn
  have hK0 : 0 < explicitSourceLogScale n := by linarith only [hK]
  have hη := explicitSourceRegulator_pos n
  have hlog : IntegrableOn (fun z : ℂ => Real.log ‖_root_.RHTower.xi z‖)
      (closedBall 0 ((n : ℝ) + 2)) := by
    simpa only [abs_of_nonneg hr] using integrableOn_xi_log_norm 0 ((n : ℝ) + 2)
  have herr : IntegrableOn
      (fun z : ℂ => |xiLogPotential (explicitSourceRegulator n) z -
        Real.log ‖_root_.RHTower.xi z‖|)
      (closedBall 0 ((n : ℝ) + 2)) := by
    have hi : IntegrableOn
        (fun z : ℂ => xiLogPotential (explicitSourceRegulator n) z -
          Real.log ‖_root_.RHTower.xi z‖)
        (closedBall 0 ((n : ℝ) + 2)) :=
      ((contDiff_xiLogPotential hη).continuous.continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 2))).sub hlog
    convert hi.norm using 1
    rfl
  have hconst : IntegrableOn
      (fun _ : ℂ => (1 / 2 : ℝ) * Real.exp (-explicitSourceLogScale n / 2))
      (closedBall 0 ((n : ℝ) + 2)) :=
    continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall 0 ((n : ℝ) + 2))
  have hsq := hCb.1.const_mul (8 / explicitSourceLogScale n)
  have hlocal : xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2) ≤
      (Real.pi * ((n : ℝ) + 2) ^ 2 / 2) * Real.exp (-explicitSourceLogScale n / 2) +
      (8 / explicitSourceLogScale n) * (explicitXiLogSqConstant * ((n : ℝ) + 1) ^ 6) := by
    unfold xiLocalPotentialError
    rw [abs_of_nonneg hr]
    calc
      (∫ z in closedBall 0 ((n : ℝ) + 2),
          |xiLogPotential (explicitSourceRegulator n) z -
            Real.log ‖_root_.RHTower.xi z‖|) ≤
          ∫ z in closedBall 0 ((n : ℝ) + 2),
            (1 / 2 : ℝ) * Real.exp (-explicitSourceLogScale n / 2) +
              (8 / explicitSourceLogScale n) * Real.log ‖_root_.RHTower.xi z‖ ^ 2 := by
        apply integral_mono_ae herr (hconst.add hsq)
        filter_upwards [ae_restrict_of_ae xi_ne_zero_ae] with z hz
        exact xiLogPotential_exp_error_le_log_square hK hz
      _ = (Real.pi * ((n : ℝ) + 2) ^ 2 / 2) * Real.exp (-explicitSourceLogScale n / 2) +
          (8 / explicitSourceLogScale n) *
            ∫ z in closedBall 0 ((n : ℝ) + 2), Real.log ‖_root_.RHTower.xi z‖ ^ 2 := by
        rw [integral_add hconst hsq, integral_const, integral_const_mul]
        simp only [measureReal_restrict_apply_univ, smul_eq_mul]
        rw [measureReal_def, Complex.volume_closedBall]
        simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
          ENNReal.coe_toReal, NNReal.coe_real_pi]
        ring
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hCb.2 (by positivity : 0 ≤ 8 / explicitSourceLogScale n))
  have hmexp : sourceCutoffControl n * Real.exp (-explicitSourceLogScale n / 2) ≤
      Real.exp (-((n : ℝ) + 1) ^ 4) :=
    HTGeometry.mul_exp_neg_exp_mul_half_le_exp_neg (source_radius_fourth_ge_sixteen hn)
      (one_le_sourceCutoffControl n)
  have hcancel : sourceCutoffControl n * (8 / explicitSourceLogScale n) =
      8 * Real.exp (-((n : ℝ) + 1) ^ 4) := by
    unfold explicitSourceLogScale
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos (((n : ℝ) + 1) ^ 4)).ne', (sourceCutoffControl_pos n).ne']
  calc
    sourceCutoffControl n *
        xiLocalPotentialError (explicitSourceRegulator n) 0 ((n : ℝ) + 2) ≤
        sourceCutoffControl n *
          ((Real.pi * ((n : ℝ) + 2) ^ 2 / 2) * Real.exp (-explicitSourceLogScale n / 2) +
            (8 / explicitSourceLogScale n) * (explicitXiLogSqConstant * ((n : ℝ) + 1) ^ 6)) :=
      mul_le_mul_of_nonneg_left hlocal (sourceCutoffControl_pos n).le
    _ = (Real.pi * ((n : ℝ) + 2) ^ 2 / 2) *
          (sourceCutoffControl n * Real.exp (-explicitSourceLogScale n / 2)) +
          (sourceCutoffControl n * (8 / explicitSourceLogScale n)) *
            (explicitXiLogSqConstant * ((n : ℝ) + 1) ^ 6) := by ring
    _ ≤ (Real.pi * ((n : ℝ) + 2) ^ 2 / 2) * Real.exp (-((n : ℝ) + 1) ^ 4) +
        (8 * Real.exp (-((n : ℝ) + 1) ^ 4)) * (explicitXiLogSqConstant * ((n : ℝ) + 1) ^ 6) := by
      rw [hcancel]
      exact add_le_add (mul_le_mul_of_nonneg_left hmexp
        (by positivity : 0 ≤ Real.pi * ((n : ℝ) + 2) ^ 2 / 2)) le_rfl
    _ = _ := by ring

/-- Exact bilateral profile mass `∫_ℝ exp(-|x|) dx = 2`. -/
theorem thetaAmplitudeProfileMass_eq_two : _root_.RHTower.thetaAmplitudeProfileMass = 2 := by
  have h := _root_.HTGeometry.integral_abs_evenPow_mul_exp_neg_abs 0 (by norm_num : (0 : ℝ) < 1)
  simpa only [_root_.RHTower.thetaAmplitudeProfileMass, mul_zero, pow_zero, one_mul, mul_one,
    neg_one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one, div_one] using h

/-- Explicit upper bound on the Hedenmalm theta-envelope constant. -/
theorem thetaEnvelopeUpper_le_sixty_five :
    _root_.RHTower.HedenmalmThetaSource.thetaEnvelopeUpper ≤ 65 := by
  unfold _root_.RHTower.HedenmalmThetaSource.thetaEnvelopeUpper
  have hw := _root_.RHTower.thetaCuspHigherAtomDominationWeight_le_geometric_rational
  have hpi4 : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos]
  nlinarith [ _root_.RHTower.thetaCuspHigherAtomDominationWeight_nonneg, Real.pi_pos]

/-- Explicit upper bound on `thetaCuspIntegerTailConstant`. -/
theorem thetaCuspIntegerTailConstant_le :
    _root_.RHTower.thetaCuspIntegerTailConstant ≤ 10 ^ 5 := by
  have hexp_pi : Real.exp Real.pi ≤ 81 := by
    have he1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    calc
      Real.exp Real.pi ≤ Real.exp 4 := Real.exp_le_exp.mpr Real.pi_lt_four.le
      _ = Real.exp ((4 : ℕ) * (1 : ℝ)) := by norm_num
      _ = Real.exp 1 ^ 4 := Real.exp_nat_mul (1 : ℝ) 4
      _ ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he1 4
      _ = 81 := by norm_num
  have hterm : ∀ m : ℕ, _root_.RHTower.thetaCuspIntegerTailWeight m ≤
      41472 * (1 / 2 : ℝ) ^ m := by
    intro m
    have hm4 : (m : ℝ) ^ 4 ≤ 256 * Real.exp (m : ℝ) := by
      have h1 : (m : ℝ) / 4 ≤ Real.exp ((m : ℝ) / 4) := by
        linarith [Real.add_one_le_exp ((m : ℝ) / 4)]
      have hp := pow_le_pow_left₀ (by positivity) h1 4
      have he4 : Real.exp ((m : ℝ) / 4) ^ 4 = Real.exp (m : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [div_pow, he4] at hp
      norm_num at hp
      linarith
    have hm_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rcases m with _ | m
      · simp
      · have h1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
        nlinarith
    have hexp_le : (m : ℝ) + -(Real.pi - 1) * (m : ℝ) ^ 2 ≤ -(m : ℝ) := by
      nlinarith [Real.pi_gt_three, sq_nonneg (m : ℝ), hm_sq]
    have he_inv : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).mpr
        (by linarith [Real.add_one_le_exp (1 : ℝ)])
    have hprod : Real.exp (m : ℝ) * Real.exp (-(Real.pi - 1) * (m : ℝ) ^ 2) ≤ (1 / 2 : ℝ) ^ m := by
      calc
        Real.exp (m : ℝ) * Real.exp (-(Real.pi - 1) * (m : ℝ) ^ 2) =
            Real.exp ((m : ℝ) + -(Real.pi - 1) * (m : ℝ) ^ 2) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-(m : ℝ)) := Real.exp_le_exp.mpr hexp_le
        _ = Real.exp (-1) ^ m := by
          rw [show -(m : ℝ) = (m : ℕ) * (-1 : ℝ) by ring, Real.exp_nat_mul]
        _ ≤ (1 / 2 : ℝ) ^ m := pow_le_pow_left₀ (Real.exp_pos _).le he_inv m
    unfold _root_.RHTower.thetaCuspIntegerTailWeight
    calc
      (2 * Real.exp Real.pi) * ((m : ℝ) ^ 4 * Real.exp (-(Real.pi - 1) * (m : ℝ) ^ 2)) ≤
          (2 * 81) * ((256 * Real.exp (m : ℝ)) * Real.exp (-(Real.pi - 1) * (m : ℝ) ^ 2)) := by
        apply mul_le_mul (by linarith) _ (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_right hm4 (Real.exp_pos _).le
      _ = 41472 * (Real.exp (m : ℝ) * Real.exp (-(Real.pi - 1) * (m : ℝ) ^ 2)) := by ring
      _ ≤ 41472 * (1 / 2 : ℝ) ^ m := mul_le_mul_of_nonneg_left hprod (by norm_num)
  have hgeo : Summable (fun m : ℕ => (41472 : ℝ) * (1 / 2 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 41472
  calc
    _root_.RHTower.thetaCuspIntegerTailConstant =
        ∑' m : ℕ, _root_.RHTower.thetaCuspIntegerTailWeight m := rfl
    _ ≤ ∑' m : ℕ, (41472 : ℝ) * (1 / 2 : ℝ) ^ m :=
      _root_.RHTower.summable_thetaCuspIntegerTailWeight.tsum_le_tsum hterm hgeo
    _ = 41472 * (1 - (1 / 2 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ ≤ 10 ^ 5 := by norm_num

/-- Explicit upper bound on `finiteThetaPotentialConstant`. -/
theorem finiteThetaPotentialConstant_le : finiteThetaPotentialConstant ≤ 2 * 10 ^ 9 := by
  unfold finiteThetaPotentialConstant
  rw [thetaAmplitudeProfileMass_eq_two]
  have htail := thetaCuspIntegerTailConstant_le
  have henv := thetaEnvelopeUpper_le_sixty_five
  have henv0 := _root_.RHTower.HedenmalmThetaSource.thetaEnvelopeUpper_pos.le
  have hsq : (_root_.RHTower.HedenmalmThetaSource.thetaEnvelopeUpper * 2) ^ 2 ≤ (65 * 2 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc
    _root_.RHTower.thetaCuspIntegerTailConstant *
        (_root_.RHTower.HedenmalmThetaSource.thetaEnvelopeUpper * 2) ^ 2 ≤
      (10 ^ 5 : ℝ) * (65 * 2 : ℝ) ^ 2 :=
      mul_le_mul htail hsq (sq_nonneg _) (by norm_num)
    _ ≤ 2 * 10 ^ 9 := by norm_num

/-- Explicit scalar and pair current-error constant `K_explicit = 5 · 10¹²`. -/
def explicitThetaPairConstant : ℝ := 5 * 10 ^ 12

private lemma compact_source_decay_bound_explicit {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 + 8 * C * ((n : ℝ) + 1) ^ 6) *
        Real.exp (-(((n : ℝ) + 1) ^ 4)) ≤
      (2 * Real.pi + 8 * C) * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
  have h := source_poly_exp_window_le hC 0 n 0 0
    (by simpa only [abs_zero] using Nat.cast_nonneg (α := ℝ) n)
    (by simp only [Nat.cast_zero, abs_zero, zero_mul]
        exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])))
  simp only [abs_zero, Nat.cast_zero, zero_mul, add_zero] at h
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  linarith only [sq_nonneg ((n : ℝ) + 3)]

/-- Explicit scalar current-error theorem with `explicitThetaPairConstant = 5 · 10¹²`. -/
theorem uniform_finiteTheta_compact_current_error_explicit
    (n : ℕ) (hn1 : 1 ≤ n) (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (B : ℝ) (hB : 0 ≤ B) (hn : (fun z => sourceCutoff n z * φ z) = φ)
    (hbound : ∀ z, |Δ φ z| ≤ B) :
    |finiteThetaSourceReading φ n - zetaSourceTrace φ| ≤
      explicitThetaPairConstant * B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
  obtain ⟨K_raw, hK_raw⟩ : ∃ K_raw : ℝ, K_raw = 2 * finiteThetaPotentialConstant +
      (2 * Real.pi)⁻¹ * (2 * Real.pi + 8 * explicitXiLogSqConstant) := ⟨_, rfl⟩
  have hK_le : K_raw ≤ explicitThetaPairConstant := by
    rw [hK_raw]
    unfold explicitXiLogSqConstant explicitThetaPairConstant
    have hpot := finiteThetaPotentialConstant_le
    have hpi3 : 3 < Real.pi := Real.pi_gt_three
    have hpi0 : 0 < Real.pi := Real.pi_pos
    have hdiv : (2 * Real.pi)⁻¹ * (2 * Real.pi + 8 * (3 * 10 ^ 12 : ℝ)) ≤ 1 + 4 * 10 ^ 12 := by
      rw [inv_mul_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hb : ∀ z ∈ closedBall (0 : ℂ) |(n : ℝ) + 2|,
      |Δ (fun w => sourceCutoff n w * φ w) z| ≤ sourceCutoffControl n * B := by
    intro z _
    rw [hn]
    exact (hbound z).trans (by nlinarith only [one_le_sourceCutoffControl n, hB])
  have hf := abs_finiteThetaSourceReading_sub_explicit_le φ hp hn1 hB hb
  have hs := abs_explicitSourceReading_sub_current_le φ hp n hb
  rw [hn, xiCurrentPairing_eq_trace φ hp hc] at hs
  have hf' : |finiteThetaSourceReading φ n - explicitSourceReading φ n| ≤
      (2 * B * finiteThetaPotentialConstant) *
        Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
    have hF := finiteThetaPotentialConstant_nonneg
    have h := mul_le_mul_of_nonneg_left (compact_source_decay_bound_explicit (C := 0) (by norm_num) n)
      (show 0 ≤ B * finiteThetaPotentialConstant / Real.pi by positivity)
    simp only [mul_zero, zero_mul, add_zero] at h
    have heq : (2 * Real.pi)⁻¹ * B * finiteThetaPotentialConstant *
        Real.exp (-(((n : ℝ) + 1) ^ 4)) * (Real.pi * ((n : ℝ) + 2) ^ 2) =
      B * finiteThetaPotentialConstant / Real.pi *
        (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 * Real.exp (-(((n : ℝ) + 1) ^ 4))) := by
      field_simp
    rw [heq] at hf
    exact hf.trans (h.trans_eq (by field_simp))
  have hs' : |explicitSourceReading φ n - zetaSourceTrace φ| ≤
      ((2 * Real.pi)⁻¹ * B * (2 * Real.pi + 8 * explicitXiLogSqConstant)) *
        Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
    have h := (explicitSourceLocalError_le hn1).trans
      (compact_source_decay_bound_explicit (by unfold explicitXiLogSqConstant; norm_num) n)
    have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (2 * Real.pi)⁻¹ * B by positivity)
    exact hs.trans (by nlinarith only [hm])
  have ht := dist_triangle (finiteThetaSourceReading φ n) (explicitSourceReading φ n)
    (zetaSourceTrace φ)
  simp only [Real.dist_eq] at ht
  calc
    |finiteThetaSourceReading φ n - zetaSourceTrace φ| ≤
        K_raw * B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) :=
      (ht.trans (add_le_add hf' hs')).trans_eq (by rw [hK_raw]; ring)
    _ ≤ explicitThetaPairConstant * B * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK_le hB) (Real.exp_pos _).le

private lemma cutoff_mul_eq_self_of_ball_support_explicit {φ : ℂ → ℝ} {r : ℝ} {k : ℕ}
    (hr : r ≤ (k : ℝ) + 1) (hs : ∀ z, z ∉ closedBall (0 : ℂ) r → φ z = 0) :
    (fun z => sourceCutoff k z * φ z) = φ := by
  funext z
  by_cases hz : z ∈ closedBall (0 : ℂ) r
  · have hk : sourceCutoff k z = 1 := by
      apply (sourceCutoff k).one_of_mem_closedBall
      rw [mem_closedBall] at hz ⊢
      exact hz.trans hr
    rw [hk, one_mul]
  · rw [hs z hz, mul_zero]

/-- Explicit product-current error theorem with `explicitThetaPairConstant = 5 · 10¹²`. -/
theorem finiteTheta_pair_current_error_explicit (R : ℕ) (F : ℂ → ℂ → ℝ)
    (hF : ContDiff ℝ 2 (Function.uncurry F)) (hbound : ∀ z w, |F z w| ≤ 1)
    (hzero : ∀ z w, z ∉ closedBall (0 : ℂ) ((R : ℝ) + 2) ∨
      w ∉ closedBall (0 : ℂ) ((R : ℝ) + 2) → F z w = 0)
    (k : ℕ) (hk : R + 3 ≤ k) :
    let B := pairTestDifferentialBound F R
    let ε := explicitThetaPairConstant * B * Real.exp (-((k : ℝ) ^ 4) + 56 * (k : ℝ) ^ 2 + 62)
    let S := (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
    |finiteThetaPairSourceReading F k -
      ∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) *
        (∑ w ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi w : ℝ) * F z w)| ≤
      ε * (2 * finiteThetaSourceReading (sourceCutoff (R + 1)) k + ε) := by
  dsimp only
  let B := pairTestDifferentialBound F R
  let ε := explicitThetaPairConstant * B * Real.exp (-((k : ℝ) ^ 4) + 56 * (k : ℝ) ^ 2 + 62)
  let S := (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
  let m : ℂ → ℝ := fun z => HTGeometry.zeroMult _root_.RHTower.xi z
  let χ : ℂ → ℝ := sourceCutoff (R + 1)
  have hB : 0 ≤ B := zero_le_one.trans (one_le_pairTestDifferentialBound F R)
  have hK : 0 ≤ explicitThetaPairConstant := by unfold explicitThetaPairConstant; norm_num
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hk1 : 1 ≤ k := by omega
  have hkR : (R : ℝ) + 3 ≤ (k : ℝ) + 1 := by exact_mod_cast (show R + 3 ≤ k + 1 by omega)
  have hread (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ)
      (hs : ∀ z, z ∉ closedBall (0 : ℂ) ((R : ℝ) + 3) → φ z = 0)
      (C : ℝ) (hC : 0 ≤ C) (hΔ : ∀ z, |Δ φ z| ≤ C) :
      |finiteThetaSourceReading φ k - ∑ z ∈ S, m z * φ z| ≤
        explicitThetaPairConstant * C * Real.exp (-((k : ℝ) ^ 4) + 56 * (k : ℝ) ^ 2 + 62) := by
    have hc := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 3)) hs
    have he := uniform_finiteTheta_compact_current_error_explicit k hk1 φ hp hc C hC
      (cutoff_mul_eq_self_of_ball_support_explicit hkR hs) hΔ
    rwa [zetaSourceTrace_eq_sum_on_ball _ φ hs] at he
  have hsmall {z : ℂ} (hz : z ∉ closedBall (0 : ℂ) ((R : ℝ) + 3)) :
      z ∉ closedBall (0 : ℂ) ((R : ℝ) + 2) := by
    intro h
    apply hz
    rw [mem_closedBall] at h ⊢
    linarith only [h]
  have hrow (z : ℂ) : ContDiff ℝ 2 (F z) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hcol (w : ℂ) : ContDiff ℝ 2 (fun z => F z w) := hF.comp (contDiff_id.prodMk contDiff_const)
  have hrowerr (z : ℂ) : |finiteThetaSourceReading (F z) k - ∑ w ∈ S, m w * F z w| ≤ ε * χ z :=
    (hread (F z) (hrow z) (fun w hw => hzero z w (Or.inr (hsmall hw)))
      (B * χ z) (mul_nonneg hB (sourceCutoff (R + 1)).nonneg)
      (fun w => pairTestDifferentialBound_row_global hF R hzero z w)).trans_eq
        (by dsimp only [ε]; ring)
  have hswap : ContDiff ℝ 2 (Function.uncurry (fun z w => F w z)) :=
    hF.comp (contDiff_snd.prodMk contDiff_fst)
  have hcolerr (w : ℂ) :
      |finiteThetaSourceReading (fun z => F z w) k - ∑ z ∈ S, m z * F z w| ≤ ε * χ w := by
    have hΔ (z : ℂ) : |Δ (fun u => F u w) z| ≤ B * χ w := by
      simpa only [pairTestDifferentialBound_swap] using
        pairTestDifferentialBound_row_global hswap R
          (fun u v h => hzero v u h.symm) w z
    exact (hread (fun z => F z w) (hcol w) (fun z hz => hzero z w (Or.inl (hsmall hz)))
      (B * χ w) (mul_nonneg hB (sourceCutoff (R + 1)).nonneg) hΔ).trans_eq
        (by dsimp only [ε]; ring)
  have hχsupp (z : ℂ) (hz : z ∉ closedBall (0 : ℂ) ((R : ℝ) + 3)) : χ z = 0 := by
    apply (sourceCutoff (R + 1)).zero_of_le_dist
    change (((R + 1 : ℕ) : ℝ) + 2) ≤ dist z 0
    rw [mem_closedBall] at hz
    push_cast
    linarith only [lt_of_not_ge hz]
  have hχΔ (z : ℂ) : |Δ χ z| ≤ B :=
    (abs_sourceCutoffLaplacian_le (R + 1) z).trans (by
      dsimp only [B, pairTestDifferentialBound]
      exact le_add_of_nonneg_left (by positivity))
  have hmass : |finiteThetaSourceReading χ k - ∑ z ∈ S, m z * χ z| ≤ ε :=
    hread χ (sourceCutoff (R + 1)).contDiff hχsupp B hB hχΔ
  have hmass' : (∑ z ∈ S, m z * χ z) ≤ finiteThetaSourceReading χ k + ε := by
    have h := (abs_le.mp hmass).1
    linarith only [h]
  have hprod := abs_finiteThetaProductSourceReading_sub_finitePair_le
    (fun z => (hrow z).continuous) (fun w => (hcol w).continuous) hbound S m
    (fun _ _ => Nat.cast_nonneg _) (sourceCutoff (R + 1)).continuous k hrowerr hcolerr
  have hsum : finiteThetaSourceReading χ k + (∑ z ∈ S, m z * χ z) ≤
      2 * finiteThetaSourceReading χ k + ε := by linarith only [hmass']
  exact hprod.trans (mul_le_mul_of_nonneg_left hsum hε)

/-- Explicit collision pair-current error theorem with no existential constant. -/
theorem thetaCollision_pair_error_explicit (T : ℝ) (n : ℕ) :
    let R := collisionWindowRadius T
    let S := (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
    |finiteThetaCollisionReading T n -
      ∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) *
        (∑ w ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi w : ℝ) *
          collisionWindowPairTest T R n z w)| ≤
      thetaCollisionCurrentError explicitThetaPairConstant T n *
        (2 * finiteThetaSourceReading (sourceCutoff (R + 1)) (thetaCollisionStage T n) +
          thetaCollisionCurrentError explicitThetaPairConstant T n) :=
  finiteTheta_pair_current_error_explicit (collisionWindowRadius T)
    (collisionWindowPairTest T (collisionWindowRadius T) n)
    (contDiff_collisionWindowPairTest T _ n) (abs_collisionWindowPairTest_le_one T _ n)
    (collisionWindowPairTest_eq_zero_outside T _ n) (thetaCollisionStage T n)
    (by unfold thetaCollisionStage thetaTestStage; omega)

/-! ### 3. Explicit Jensen divisor count and universal height-independent stage `n ≥ 6` -/

private lemma analyticOrderAt_riemannXi_eq_xi (z : ℂ) :
    analyticOrderAt RiemannGaussian.riemannXi z = analyticOrderAt _root_.RHTower.xi z := by
  have hfun : RiemannGaussian.riemannXi = (fun _ : ℂ => (-2 : ℂ)) * _root_.RHTower.xi :=
    funext gaussianXi_eq_neg_two_mul_xi
  have hc : AnalyticAt ℂ (fun _ : ℂ => (-2 : ℂ)) z := analyticAt_const
  have hx : AnalyticAt ℂ _root_.RHTower.xi z :=
    _root_.RHTower.xi_analyticOnNhd Set.univ z (Set.mem_univ z)
  rw [hfun, analyticOrderAt_mul hc hx, hc.analyticOrderAt_eq_zero.mpr (by norm_num), zero_add]

/-- Explicit Jensen bound on the total multiplicity of `xi` zeros in `closedBall 0 r` (`0 < r`). -/
theorem sum_xi_zeroMult_closedBall_le {r : ℝ} (hr : 0 < r) :
    (∑ z ∈ (_root_.RHTower.xi_zeros_closedBall_finite 0 r).toFinset,
      (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ)) ≤ 10 * (2 * r + 1) ^ 2 := by
  classical
  let D := divisor RiemannGaussian.riemannXi (closedBall (0 : ℂ) r)
  let S := (_root_.RHTower.xi_zeros_closedBall_finite 0 r).toFinset
  let T_supp := (D.finiteSupport (isCompact_closedBall (0 : ℂ) r)).toFinset
  have hxiAnalytic : AnalyticOnNhd ℂ RiemannGaussian.riemannXi (closedBall (0 : ℂ) r) :=
    RiemannGaussian.analyticOnNhd_riemannXi.mono (subset_univ _)
  have hDz : ∀ z ∈ S, D z = (HTGeometry.zeroMult _root_.RHTower.xi z : ℤ) := by
    intro z hz
    have hzdata := (_root_.RHTower.xi_zeros_closedBall_finite 0 r).mem_toFinset.mp hz
    rw [show D z = divisor RiemannGaussian.riemannXi (closedBall (0 : ℂ) r) z from rfl,
      hxiAnalytic.divisor_apply hzdata.1, analyticOrderAt_riemannXi_eq_xi z,
      ← ENat.coe_toNat (_root_.RHTower.xi_orderAt_ne_top z)]
    simp [HTGeometry.zeroMult]
  have hsub : S ⊆ T_supp := by
    intro z hz
    have hzdata := (_root_.RHTower.xi_zeros_closedBall_finite 0 r).mem_toFinset.mp hz
    rw [Set.Finite.mem_toFinset]
    change D z ≠ 0
    rw [hDz z hz]
    exact Int.ofNat_ne_zero.mpr (_root_.RHTower.xi_order_toNat_ne_zero hzdata.2)
  have hsum_le : (∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ)) ≤
      ((∑ᶠ u, D u : ℤ) : ℝ) := by
    calc
      (∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ)) =
          ∑ z ∈ S, (D z : ℝ) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [hDz z hz]
        norm_cast
      _ ≤ ∑ z ∈ T_supp, (D z : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro z _ _
        exact_mod_cast hxiAnalytic.divisor_nonneg z
      _ = ∑ᶠ z, (D z : ℝ) := by
        rw [finsum_eq_sum_of_support_subset]
        intro z hz
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        change D z ≠ 0
        intro h0
        exact hz (by simp [h0])
      _ = ((∑ᶠ z, D z : ℤ) : ℝ) :=
        (map_finsum (Int.castRingHom ℝ) (D.finiteSupport (isCompact_closedBall (0 : ℂ) r))).symm
  have hjensen := RiemannGaussian.jensen_riemannXi_divisor_le (by norm_num : (1 : ℝ) ≤ 5) hr
    norm_riemannXi_le_exp_five
  have hlog2 := half_lt_log_two
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ)) ≤
        (5 : ℝ) * (2 * r + 1) ^ 2 / Real.log 2 := hsum_le.trans hjensen
    _ ≤ 10 * (2 * r + 1) ^ 2 := by
      rw [div_le_iff₀ hlog2_pos]
      nlinarith [mul_le_mul_of_nonneg_left hlog2.le (sq_nonneg (2 * r + 1))]

/-- Explicit natural-number upper bound on `xiStripWindowTotalOrder T`. -/
def explicitWindowZeroBound (T : ℝ) : ℕ :=
  10 * (2 * (collisionWindowRadius T + 3) + 1) ^ 2

theorem one_le_explicitWindowZeroBound (T : ℝ) : 1 ≤ explicitWindowZeroBound T := by
  unfold explicitWindowZeroBound
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * (collisionWindowRadius T + 3) := ⟨_, rfl⟩
  rw [← hm]
  calc
    1 ≤ 10 * 1 := by omega
    _ ≤ 10 * (m + 1) ^ 2 :=
      Nat.mul_le_mul_left 10 (by simpa using Nat.pow_le_pow_left (Nat.le_add_left 1 m) 2)

/-- Explicit Jensen bound on the strip-window zero count `xiStripWindowTotalOrder T`. -/
theorem xiStripWindowTotalOrder_le_explicit (T : ℝ) :
    _root_.RHTower.xiStripWindowTotalOrder T ≤ explicitWindowZeroBound T := by
  classical
  let R := collisionWindowRadius T
  let W := (_root_.RHTower.stripZeros_finite T).toFinset
  let S := (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
  have hsub : W ⊆ S := by
    intro z hz
    have hwin := (_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hz
    have hχ := sourceCutoff_collisionWindowRadius_eq_one hwin.1
    have hs : z ∈ Function.support (sourceCutoff R : ℂ → ℝ) := by
      change sourceCutoff R z ≠ 0
      rw [hχ]
      exact one_ne_zero
    rw [(sourceCutoff R).support_eq] at hs
    change dist z 0 < (R : ℝ) + 2 at hs
    apply (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).mem_toFinset.mpr
    refine ⟨?_, hwin.2⟩
    rw [mem_closedBall]
    linarith only [hs]
  have hsum_nat : (_root_.RHTower.xiStripWindowTotalOrder T : ℝ) ≤
      ∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) := by
    unfold _root_.RHTower.xiStripWindowTotalOrder
    push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
  have hr : 0 < (R : ℝ) + 3 := by positivity
  have hreal : (_root_.RHTower.xiStripWindowTotalOrder T : ℝ) ≤
      (explicitWindowZeroBound T : ℝ) := by
    calc
      (_root_.RHTower.xiStripWindowTotalOrder T : ℝ) ≤
          10 * (2 * ((R : ℝ) + 3) + 1) ^ 2 :=
        hsum_nat.trans (sum_xi_zeroMult_closedBall_le hr)
      _ = (explicitWindowZeroBound T : ℝ) := by
        unfold explicitWindowZeroBound
        dsimp only [R]
        push_cast
        ring
  exact_mod_cast hreal

/-- **Height-uniform theta-current control (`N_univ = 6`).** For **every** real height `T : ℝ`
and **every** stage `n ≥ 6`, the finite-theta product-current error is strictly below `1 / 8`
with a universal stage threshold completely independent of `T`. -/
theorem thetaCollision_product_error_lt_eighth_uniform (T : ℝ) {n : ℕ} (hn : 6 ≤ n) :
    thetaCollisionCurrentError explicitThetaPairConstant T n *
      (2 * finiteThetaSourceReading (sourceCutoff (collisionWindowRadius T + 1))
        (thetaCollisionStage T n) +
        thetaCollisionCurrentError explicitThetaPairConstant T n) < 1 / 8 := by
  obtain ⟨R, hR⟩ : ∃ R, R = collisionWindowRadius T := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = thetaCollisionDifferentialCost T n := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = thetaCollisionStage T n := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε, ε = thetaCollisionCurrentError explicitThetaPairConstant T n := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ℂ → ℝ, χ = sourceCutoff (R + 1) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S,
      S = (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset := ⟨_, rfl⟩
  rw [← hR, ← hχ, ← hk, ← hε]
  have hk10 : 10 ≤ k := by rw [hk]; unfold thetaCollisionStage thetaTestStage; omega
  have hkR_nat : R + 3 ≤ k := by rw [hk, hR]; unfold thetaCollisionStage thetaTestStage; omega
  have hkR1 : (R : ℝ) + 3 ≤ (k : ℝ) + 1 := by exact_mod_cast (show R + 3 ≤ k + 1 by omega)
  have hkR : (R : ℝ) + 3 ≤ (k : ℝ) := by exact_mod_cast hkR_nat
  have hk_real : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk10
  have hquartic : -((k : ℝ) ^ 4) + 56 * (k : ℝ) ^ 2 + 62 ≤ -300 * (k : ℝ) := by
    have hk2 : 100 ≤ (k : ℝ) ^ 2 := by nlinarith
    have hk4 : 100 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
      nlinarith [mul_le_mul_of_nonneg_right hk2 (sq_nonneg (k : ℝ))]
    have hlin : 10 * (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hK_exp : explicitThetaPairConstant ≤ Real.exp 43 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h43 : (2 : ℝ) ^ 43 ≤ Real.exp 1 ^ 43 := pow_le_pow_left₀ (by norm_num) h2 43
    rw [← Real.exp_nat_mul] at h43
    unfold explicitThetaPairConstant
    norm_num at h43 ⊢
    linarith
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact zero_le_one.trans (one_le_pairTestDifferentialBound _ _)
  have hBk : B ≤ (k : ℝ) := by
    rw [hk, hB]
    exact differentialCost_le_thetaTestStage _ n _
  have hk_exp : (k : ℝ) ≤ Real.exp (k : ℝ) := by linarith [Real.add_one_le_exp (k : ℝ)]
  have hε_eq : ε = explicitThetaPairConstant * B *
      Real.exp (-((k : ℝ) ^ 4) + 56 * (k : ℝ) ^ 2 + 62) := by
    rw [hε, hk, hB]
    rfl
  have hε0 : 0 ≤ ε := by
    rw [hε_eq]
    unfold explicitThetaPairConstant
    positivity
  have hε_bound : ε ≤ Real.exp (-200 * (k : ℝ)) := by
    rw [hε_eq]
    calc
      explicitThetaPairConstant * B * Real.exp (-((k : ℝ) ^ 4) + 56 * (k : ℝ) ^ 2 + 62) ≤
          Real.exp 43 * Real.exp (k : ℝ) * Real.exp (-300 * (k : ℝ)) := by
        apply mul_le_mul
        · exact mul_le_mul hK_exp (hBk.trans hk_exp) hB0 (Real.exp_pos 43).le
        · exact Real.exp_le_exp.mpr hquartic
        · exact (Real.exp_pos _).le
        · positivity
      _ = Real.exp (43 + (k : ℝ) + -300 * (k : ℝ)) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (-200 * (k : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have hχsupp (z : ℂ) (hz : z ∉ closedBall (0 : ℂ) ((R : ℝ) + 3)) : χ z = 0 := by
    rw [hχ]
    apply (sourceCutoff (R + 1)).zero_of_le_dist
    change (((R + 1 : ℕ) : ℝ) + 2) ≤ dist z 0
    rw [mem_closedBall] at hz
    push_cast
    linarith only [lt_of_not_ge hz]
  have hχΔ (z : ℂ) : |Δ χ z| ≤ B := by
    rw [hχ, hB]
    unfold thetaCollisionDifferentialCost pairTestDifferentialBound
    rw [← hR]
    exact (abs_sourceCutoffLaplacian_le (R + 1) z).trans (le_add_of_nonneg_left (by positivity))
  have hmass_err : |finiteThetaSourceReading χ k -
      ∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) * χ z| ≤ ε := by
    have hc := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 3)) hχsupp
    have hcont : ContDiff ℝ 2 χ := by rw [hχ]; exact (sourceCutoff (R + 1)).contDiff
    have he := uniform_finiteTheta_compact_current_error_explicit k (by omega) χ
      hcont hc B hB0
      (cutoff_mul_eq_self_of_ball_support_explicit hkR1 hχsupp) hχΔ
    rw [hS, hε_eq]
    rwa [zetaSourceTrace_eq_sum_on_ball _ χ hχsupp] at he
  have hsum_χ : (∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) * χ z) ≤
      90 * (k : ℝ) ^ 2 := by
    have hχ_le1 : ∀ z, χ z ≤ 1 := fun z => by rw [hχ]; exact (sourceCutoff (R + 1)).le_one
    calc
      (∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) * χ z) ≤
          ∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) * 1 := by
        refine Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (hχ_le1 z) (Nat.cast_nonneg _)
      _ = ∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) := by simp
      _ ≤ 10 * (2 * ((R : ℝ) + 3) + 1) ^ 2 := by
        rw [hS]
        exact sum_xi_zeroMult_closedBall_le (by positivity)
      _ ≤ 10 * (2 * (k : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by norm_num)
      _ ≤ 90 * (k : ℝ) ^ 2 := by nlinarith
  have hε_le1 : ε ≤ 1 :=
    hε_bound.trans (Real.exp_le_one_iff.mpr (by linarith))
  have hQ_le : finiteThetaSourceReading χ k ≤ 90 * (k : ℝ) ^ 2 + 1 := by
    have h1 := (abs_le.mp hmass_err).2
    linarith
  have hk2_exp : (k : ℝ) ^ 2 ≤ 4 * Real.exp (k : ℝ) := by
    have hhalf : (k : ℝ) / 2 ≤ Real.exp ((k : ℝ) / 2) := by
      linarith [Real.add_one_le_exp ((k : ℝ) / 2)]
    have hsq := pow_le_pow_left₀ (by positivity) hhalf 2
    have he2 : Real.exp ((k : ℝ) / 2) ^ 2 = Real.exp (k : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [div_pow, he2] at hsq
    norm_num at hsq
    linarith
  have h2Q_exp : 2 * finiteThetaSourceReading χ k + ε ≤ Real.exp ((k : ℝ) + 10) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h10 : (1024 : ℝ) ≤ Real.exp 10 := by
      have hp := pow_le_pow_left₀ (by norm_num) h2 10
      rw [← Real.exp_nat_mul] at hp
      norm_num at hp ⊢
      exact hp
    have hlin : 2 * finiteThetaSourceReading χ k + ε ≤ 1024 * Real.exp (k : ℝ) := by
      have h1k : 1 ≤ Real.exp (k : ℝ) := Real.one_le_exp (by linarith)
      linarith
    calc
      2 * finiteThetaSourceReading χ k + ε ≤ Real.exp 10 * Real.exp (k : ℝ) :=
        hlin.trans (mul_le_mul_of_nonneg_right h10 (Real.exp_pos _).le)
      _ = Real.exp ((k : ℝ) + 10) := by rw [← Real.exp_add, add_comm]
  have hQ0 : 0 ≤ finiteThetaSourceReading χ k :=
    finiteThetaSourceReading_nonneg (fun z => by rw [hχ]; exact (sourceCutoff (R + 1)).nonneg) k
  have hexp_lt : Real.exp (-1980 : ℝ) < 1 / 8 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h16 : (16 : ℝ) ≤ Real.exp 4 := by
      have hp := pow_le_pow_left₀ (by norm_num) h2 4
      rw [← Real.exp_nat_mul] at hp
      norm_num at hp ⊢
      exact hp
    have h1980 : (16 : ℝ) < Real.exp 1980 :=
      lt_of_le_of_lt h16 (Real.exp_lt_exp.mpr (by norm_num))
    have hinv : Real.exp (-1980 : ℝ) < 1 / 16 := by
      rw [Real.exp_neg, one_div]
      exact (inv_lt_inv₀ (Real.exp_pos 1980) (by norm_num)).mpr h1980
    linarith
  calc
    ε * (2 * finiteThetaSourceReading χ k + ε) ≤
        Real.exp (-200 * (k : ℝ)) * Real.exp ((k : ℝ) + 10) :=
      mul_le_mul hε_bound h2Q_exp (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-200 * (k : ℝ) + ((k : ℝ) + 10)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-1980 : ℝ) := Real.exp_le_exp.mpr (by linarith)
    _ < 1 / 8 := hexp_lt

/-- **Height-uniform pair-test approximation (`N_univ = 6`).** Across all real heights `T : ℝ`
and all stages `n ≥ 6`, `finiteThetaCollisionReading T n` approximates its finite-divisor pair sum
within `< 1 / 8`. -/
theorem abs_finiteThetaCollisionReading_sub_pairSum_lt_eighth_uniform
    (T : ℝ) {n : ℕ} (hn : 6 ≤ n) :
    let R := collisionWindowRadius T
    let S := (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
    |finiteThetaCollisionReading T n -
      ∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) *
        (∑ w ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi w : ℝ) *
          collisionWindowPairTest T R n z w)| < 1 / 8 :=
  (thetaCollision_pair_error_explicit T n).trans_lt
    (thetaCollision_product_error_lt_eighth_uniform T hn)

/-! ### 4. Explicit fixed-window and gap-calibrated rounding rate (Milestones A8 & B12) -/

private lemma collisionWindowCutoff_eq_window_of_gap_explicit (T : ℝ) (n : ℕ) {z : ℂ}
    (hz : z ∈ (_root_.RHTower.xi_zeros_closedBall_finite 0
      ((collisionWindowRadius T : ℝ) + 3)).toFinset)
    (hn : 1 ≤ (n : ℝ) * collisionWindowGap T) :
    collisionWindowCutoff T (collisionWindowRadius T) n z =
      if z ∈ _root_.RHTower.stripZeros T then 1 else 0 := by
  have hzS : z ∈ collisionWindowSeparationSet T :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
  have hzero : (0 : ℂ) ∈ collisionWindowSeparationSet T := Finset.mem_insert_self _ _
  have htop : (⟨0, T⟩ : ℂ) ∈ collisionWindowSeparationSet T :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hgap0 (h : z.im ≠ 0) : collisionWindowGap T ≤ |z.im| := by
    have he := (min_le_right
      (finiteCollisionGap (_root_.RHTower.stripZeros_finite T).toFinset)
      (finiteCoordinateGap (collisionWindowSeparationSet T) Complex.im)).trans
        (finiteCoordinateGap_le _ Complex.im hzS hzero (by simpa only [zero_im] using h))
    simpa only [collisionWindowGap, zero_im, sub_zero] using he
  have hgapT (h : z.im ≠ T) : collisionWindowGap T ≤ |T - z.im| :=
    (min_le_right _ _).trans (finiteCoordinateGap_le _ Complex.im htop hzS h.symm)
  have hh : collisionHeightCutoff T n z.im = if 0 ≤ z.im ∧ z.im < T then 1 else 0 := by
    by_cases hy : 0 ≤ z.im
    · by_cases hT : z.im < T
      · have hg : collisionWindowGap T ≤ T - z.im := by
          simpa only [abs_of_pos (sub_pos.mpr hT)] using hgapT hT.ne
        have hprod : 1 ≤ (n : ℝ) * (T - z.im) :=
          hn.trans (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _))
        rw [if_pos ⟨hy, hT⟩, collisionHeightCutoff,
          Real.smoothTransition.one_of_one_le (by
            nlinarith only [mul_nonneg (Nat.cast_nonneg n) hy]),
          Real.smoothTransition.one_of_one_le hprod, mul_one]
      · rw [if_neg (fun h => hT h.2), collisionHeightCutoff,
          Real.smoothTransition.zero_of_nonpos
            (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n)
              (sub_nonpos.mpr (le_of_not_gt hT))), mul_zero]
    · have hy0 : z.im < 0 := lt_of_not_ge hy
      have hg : collisionWindowGap T ≤ -z.im := by
        simpa only [abs_of_neg hy0] using hgap0 hy0.ne
      have hprod := hn.trans (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg n))
      rw [if_neg (fun h => hy h.1), collisionHeightCutoff,
        Real.smoothTransition.zero_of_nonpos (by nlinarith only [hprod]), zero_mul]
  rw [collisionWindowCutoff, hh]
  by_cases hw : z ∈ _root_.RHTower.stripZeros T
  · rw [if_pos hw, if_pos ⟨hw.1.2.2.1, hw.1.2.2.2⟩,
      sourceCutoff_collisionWindowRadius_eq_one hw.1, mul_one]
  · have hh' : ¬ (0 ≤ z.im ∧ z.im < T) := by
      intro hi
      have hs := _root_.RHTower.xi_zero_re_mem_open_unit
        ((_root_.RHTower.xi_zeros_closedBall_finite 0
          ((collisionWindowRadius T : ℝ) + 3)).mem_toFinset.mp hz).2
      exact hw ⟨⟨hs.1, hs.2, hi.1, hi.2⟩,
        ((_root_.RHTower.xi_zeros_closedBall_finite 0
          ((collisionWindowRadius T : ℝ) + 3)).mem_toFinset.mp hz).2⟩
    rw [if_neg hw, if_neg hh', mul_zero]

private lemma collisionPairSum_eq_window_of_gap_explicit (T : ℝ) (n : ℕ)
    (hgap : 1 ≤ (n : ℝ) * collisionWindowGap T) :
    let R := collisionWindowRadius T
    let S := (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
    (∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) *
        (∑ w ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi w : ℝ) *
          collisionWindowPairTest T R n z w)) = xiWindowGaussianPairSum T ((n : ℝ) ^ 2) := by
  classical
  let R := collisionWindowRadius T
  let S := (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
  let W := (_root_.RHTower.stripZeros_finite T).toFinset
  let m : ℂ → ℝ := fun z => HTGeometry.zeroMult _root_.RHTower.xi z
  have hsub : W ⊆ S := by
    intro z hz
    have hwin := (_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hz
    have hχ := sourceCutoff_collisionWindowRadius_eq_one hwin.1
    have hs : z ∈ Function.support (sourceCutoff R : ℂ → ℝ) := by
      change sourceCutoff R z ≠ 0
      rw [hχ]
      exact one_ne_zero
    rw [(sourceCutoff R).support_eq] at hs
    change dist z 0 < (R : ℝ) + 2 at hs
    apply (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).mem_toFinset.mpr
    refine ⟨?_, hwin.2⟩
    rw [mem_closedBall]
    linarith only [hs]
  have hn (z : ℂ) (hz : z ∈ S) :
      collisionWindowCutoff T R n z = if z ∈ _root_.RHTower.stripZeros T then 1 else 0 :=
    collisionWindowCutoff_eq_window_of_gap_explicit T n hz hgap
  have hcutone (z : ℂ) (hz : z ∈ W) : collisionWindowCutoff T R n z = 1 := by
    simpa only [if_pos ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hz)] using hn z (hsub hz)
  have hcutzero (z : ℂ) (hz : z ∈ S) (hw : z ∉ W) : collisionWindowCutoff T R n z = 0 := by
    have hnot : z ∉ _root_.RHTower.stripZeros T := fun h =>
      hw ((_root_.RHTower.stripZeros_finite T).mem_toFinset.mpr h)
    simpa only [if_neg hnot] using hn z hz
  change (∑ z ∈ S, m z * (∑ w ∈ S, m w * collisionWindowPairTest T R n z w)) = _
  calc
    _ = ∑ z ∈ W, m z * (∑ w ∈ S, m w * collisionWindowPairTest T R n z w) := by
      symm
      apply Finset.sum_subset hsub
      intro z hz hw
      simp only [collisionWindowPairTest, hcutzero z hz hw, zero_mul,
        mul_zero, Finset.sum_const_zero]
    _ = xiWindowGaussianPairSum T ((n : ℝ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hi : (∑ w ∈ S, m w * collisionWindowPairTest T R n z w) =
          ∑ w ∈ W, m w * collisionWindowPairTest T R n z w := by
        symm
        apply Finset.sum_subset hsub
        intro w hw hnot
        simp only [collisionWindowPairTest, hcutzero w hw hnot, mul_zero, zero_mul]
      rw [hi, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [collisionWindowPairTest, hcutone z hz, hcutone w hw, one_mul, one_mul]
      ring

private lemma xiWindowGaussianPairSum_error_at_gap_explicit (T q : ℝ) (hq : 0 ≤ q) :
    |xiWindowGaussianPairSum T q - (_root_.RHTower.xiHorizontalCollisionCharge T : ℝ)| ≤
      (_root_.RHTower.xiStripWindowTotalOrder T : ℝ) ^ 2 * Real.exp (-q * (collisionWindowGap T) ^ 2) := by
  let S := (_root_.RHTower.stripZeros_finite T).toFinset
  let m := HTGeometry.zeroMult _root_.RHTower.xi
  have hd : collisionWindowGap T ≤ finiteCollisionGap S := min_le_left _ _
  have hcharge : (_root_.RHTower.xiHorizontalCollisionCharge T : ℝ) =
      ∑ z ∈ S, ∑ w ∈ S, (m z : ℝ) * (m w : ℝ) *
        (if z.im = w.im ∧ z ≠ w then 1 else 0) := by
    rw [_root_.RHTower.xiHorizontalCollisionCharge_eq_sum_pairs,
      _root_.RHTower.xiHorizontalCollisionPairs, Finset.sum_filter, Finset.sum_product]
    push_cast
    simp only [S, m, HTGeometry.zeroMult, mul_ite, mul_one, mul_zero]
  have h := abs_horizontalCollisionGaussian_pair_error S m (collisionWindowGap_pos T).le
    (fun _ hz _ hw h => hd.trans ((min_le_left _ _).trans (finiteCoordinateGap_le S _ hz hw h)))
    (fun _ hz _ hw h => hd.trans ((min_le_right _ _).trans (finiteCoordinateGap_le S _ hz hw h))) q hq
  rw [← hcharge] at h
  simpa only [xiWindowGaussianPairSum, _root_.RHTower.xiStripWindowTotalOrder,
    Nat.cast_sum, m, HTGeometry.zeroMult] using h

/-- Explicit closed-form rounding stage as a function of window height `T` and any lower bound
`0 < δ ≤ collisionWindowGap T` (zero existential constants). -/
def thetaCollisionRoundingStage (T δ : ℝ) : ℕ :=
  max 6 (Nat.ceil (Real.sqrt (max 1 (Real.log (8 * (explicitWindowZeroBound T : ℝ) ^ 2))) / δ))

/-- Explicit closed-form rounding threshold for a fixed window `T`. -/
def explicitWindowRoundingThreshold (T : ℝ) : ℕ :=
  thetaCollisionRoundingStage T (collisionWindowGap T)

/-- **Explicit gap-calibrated rounding rate (Milestones A8 & B12).** For any `T : ℝ`, any gap
lower bound `0 < δ ≤ collisionWindowGap T`, and every `n ≥ thetaCollisionRoundingStage T δ`,
`|finiteThetaCollisionReading T n - xiHorizontalCollisionCharge T| < 1 / 4` and rounding
recovers `xiHorizontalCollisionCharge T` on the nose. -/
theorem abs_finiteThetaCollisionReading_sub_charge_lt_quarter_of_stage
    (T : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ collisionWindowGap T)
    {n : ℕ} (hn : thetaCollisionRoundingStage T δ ≤ n) :
    |finiteThetaCollisionReading T n - (_root_.RHTower.xiHorizontalCollisionCharge T : ℝ)| <
      1 / 4 := by
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ,
      L = max 1 (Real.log (8 * (explicitWindowZeroBound T : ℝ) ^ 2)) := ⟨_, rfl⟩
  have hn6 : 6 ≤ n := (le_max_left 6 _).trans hn
  have hnceil : Nat.ceil (Real.sqrt L / δ) ≤ n := by
    rw [hL_def]
    exact (le_max_right 6 _).trans hn
  have hL1 : 1 ≤ L := by rw [hL_def]; exact le_max_left _ _
  have hLlog : Real.log (8 * (explicitWindowZeroBound T : ℝ) ^ 2) ≤ L := by
    rw [hL_def]; exact le_max_right _ _
  have hsqrt1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
  have hnδ : Real.sqrt L ≤ (n : ℝ) * δ :=
    (div_le_iff₀ hδ0).mp ((Nat.le_ceil (Real.sqrt L / δ)).trans (Nat.cast_le.mpr hnceil))
  have hgap : 1 ≤ (n : ℝ) * collisionWindowGap T := by
    calc
      (1 : ℝ) ≤ Real.sqrt L := hsqrt1
      _ ≤ (n : ℝ) * δ := hnδ
      _ ≤ (n : ℝ) * collisionWindowGap T :=
        mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg n)
  have hpair := abs_finiteThetaCollisionReading_sub_pairSum_lt_eighth_uniform T hn6
  dsimp only at hpair
  rw [collisionPairSum_eq_window_of_gap_explicit T n hgap] at hpair
  have hn_sq : L ≤ ((n : ℝ) * collisionWindowGap T) ^ 2 := by
    have h1 : Real.sqrt L ≤ (n : ℝ) * collisionWindowGap T :=
      hnδ.trans (mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg n))
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg L) h1 2
    rwa [Real.sq_sqrt (zero_le_one.trans hL1)] at hsq
  have hM_le : (_root_.RHTower.xiStripWindowTotalOrder T : ℝ) ≤ (explicitWindowZeroBound T : ℝ) :=
    by exact_mod_cast xiStripWindowTotalOrder_le_explicit T
  have hM_pos : 0 < (explicitWindowZeroBound T : ℝ) :=
    by exact_mod_cast (Nat.succ_le_iff.mp (one_le_explicitWindowZeroBound T))
  have h8M_pos : 0 < 8 * (explicitWindowZeroBound T : ℝ) ^ 2 := by positivity
  have hgauss :
      (_root_.RHTower.xiStripWindowTotalOrder T : ℝ) ^ 2 *
          Real.exp (-((n : ℝ) ^ 2) * (collisionWindowGap T) ^ 2) ≤ 1 / 8 := by
    have hexp_le :
        Real.exp (-((n : ℝ) ^ 2) * (collisionWindowGap T) ^ 2) ≤
          (8 * (explicitWindowZeroBound T : ℝ) ^ 2)⁻¹ := by
      rw [← Real.exp_log h8M_pos, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have hrew : -((n : ℝ) ^ 2) * (collisionWindowGap T) ^ 2 =
          -(((n : ℝ) * collisionWindowGap T) ^ 2) := by ring
      rw [hrew]
      linarith
    calc
      (_root_.RHTower.xiStripWindowTotalOrder T : ℝ) ^ 2 *
          Real.exp (-((n : ℝ) ^ 2) * (collisionWindowGap T) ^ 2) ≤
        (explicitWindowZeroBound T : ℝ) ^ 2 * (8 * (explicitWindowZeroBound T : ℝ) ^ 2)⁻¹ :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hM_le 2) hexp_le
          (Real.exp_pos _).le (sq_nonneg _)
      _ = 1 / 8 := by field_simp [hM_pos.ne']
  have hwin := (xiWindowGaussianPairSum_error_at_gap_explicit T ((n : ℝ) ^ 2)
    (sq_nonneg (n : ℝ))).trans hgauss
  have htri := dist_triangle (finiteThetaCollisionReading T n)
    (xiWindowGaussianPairSum T ((n : ℝ) ^ 2))
    (_root_.RHTower.xiHorizontalCollisionCharge T : ℝ)
  simp only [Real.dist_eq] at htri
  linarith

/-- **Explicit rounding theorem (Milestones A8 & gap-calibrated B12).** -/
theorem floor_finiteThetaCollisionReading_eq_of_stage
    (T : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ collisionWindowGap T)
    {n : ℕ} (hn : thetaCollisionRoundingStage T δ ≤ n) :
    Nat.floor (finiteThetaCollisionReading T n + 1 / 2) =
      _root_.RHTower.xiHorizontalCollisionCharge T := by
  have h := abs_finiteThetaCollisionReading_sub_charge_lt_quarter_of_stage T hδ0 hδ hn
  apply (Nat.floor_eq_iff (add_nonneg (finiteThetaCollisionReading_nonneg T n)
    (by norm_num))).mpr
  constructor <;> linarith only [(abs_lt.mp h).1, (abs_lt.mp h).2]

/-- **Explicit fixed-window rounding theorem (Milestone A8).** For every `T : ℝ` and every
`n ≥ explicitWindowRoundingThreshold T`, `⌊finiteThetaCollisionReading T n + 1/2⌋₊ = O(T)`. -/
theorem floor_finiteThetaCollisionReading_eq_of_threshold
    (T : ℝ) {n : ℕ} (hn : explicitWindowRoundingThreshold T ≤ n) :
    Nat.floor (finiteThetaCollisionReading T n + 1 / 2) =
      _root_.RHTower.xiHorizontalCollisionCharge T :=
  floor_finiteThetaCollisionReading_eq_of_stage T (collisionWindowGap_pos T) le_rfl hn

/-! ### 5. Height-uniform critical-line vanishing and RH equivalence (Milestone B12) -/

/-- **Uniform-in-height critical-line vanishing.** Under `RiemannHypothesis`, for **all** real
heights `T : ℝ` and **all** stages `n ≥ 6` simultaneously (with zero dependence on zero spacing
or window-boundary proximity), `0 ≤ finiteThetaCollisionReading T n < 1 / 8`. -/
theorem finiteThetaCollisionReading_lt_eighth_uniform_of_riemannHypothesis
    (hRH : RiemannHypothesis) (T : ℝ) {n : ℕ} (hn : 6 ≤ n) :
    finiteThetaCollisionReading T n < 1 / 8 := by
  let R := collisionWindowRadius T
  let S := (_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
  have hpair := abs_finiteThetaCollisionReading_sub_pairSum_lt_eighth_uniform T hn
  dsimp only at hpair
  have hzero_sum :
      (∑ z ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi z : ℝ) *
        (∑ w ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi w : ℝ) *
          collisionWindowPairTest T R n z w)) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    have hz0 : _root_.RHTower.xi z = 0 :=
      ((_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).mem_toFinset.mp hz).2
    have hzre : z.re = 1 / 2 := _root_.RHTower.xi_zero_re_eq_half_of_RH hRH hz0
    have hinner :
        (∑ w ∈ S, (HTGeometry.zeroMult _root_.RHTower.xi w : ℝ) *
          collisionWindowPairTest T R n z w) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      have hw0 : _root_.RHTower.xi w = 0 :=
        ((_root_.RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).mem_toFinset.mp hw).2
      have hwre : w.re = 1 / 2 := _root_.RHTower.xi_zero_re_eq_half_of_RH hRH hw0
      have hg : horizontalCollisionGaussian ((n : ℝ) ^ 2) z w = 0 := by
        simp [horizontalCollisionGaussian, hzre, hwre]
      simp [collisionWindowPairTest, hg]
    rw [hinner, mul_zero]
  rw [hzero_sum, sub_zero, abs_of_nonneg (finiteThetaCollisionReading_nonneg T n)] at hpair
  exact hpair

/-- Under `RiemannHypothesis`, the rounded theta-prefix reading vanishes at every stage `n ≥ 6`
uniformly across all real heights `T : ℝ`. -/
theorem floor_finiteThetaCollisionReading_eq_zero_uniform_of_riemannHypothesis
    (hRH : RiemannHypothesis) (T : ℝ) {n : ℕ} (hn : 6 ≤ n) :
    Nat.floor (finiteThetaCollisionReading T n + 1 / 2) = 0 := by
  have h := finiteThetaCollisionReading_lt_eighth_uniform_of_riemannHypothesis hRH T hn
  have h0 := finiteThetaCollisionReading_nonneg T n
  exact Nat.floor_eq_zero.mpr (by linarith)

/-- **Uniform-in-height RH equivalence (Milestone B12).** `RiemannHypothesis` is equivalent to
the rounded finite-theta collision reading vanishing for all `n ≥ 6` uniformly across all `T : ℝ`
(and even to being `< 2` at the explicit rounding threshold on natural windows `m : ℕ`). -/
theorem riemannHypothesis_iff_uniform_floor_finiteThetaCollisionReading_eq_zero :
    RiemannHypothesis ↔
      ∀ T : ℝ, ∀ n : ℕ, 6 ≤ n → Nat.floor (finiteThetaCollisionReading T n + 1 / 2) = 0 := by
  constructor
  · intro hRH T n hn
    exact floor_finiteThetaCollisionReading_eq_zero_uniform_of_riemannHypothesis hRH T hn
  · intro hunif
    apply _root_.RHTower.riemannHypothesis_of_forall_nat_horizontalCollisionCharge_lt_two
    intro m
    let n := explicitWindowRoundingThreshold (m : ℝ)
    have hn6 : 6 ≤ n := le_max_left 6 _
    have hfloor := floor_finiteThetaCollisionReading_eq_of_threshold (m : ℝ) (le_refl n)
    rw [← hfloor, hunif (m : ℝ) n hn6]
    omega

/-- Natural-window explicit-threshold RH equivalence. -/
theorem riemannHypothesis_iff_forall_nat_floor_threshold_lt_two :
    RiemannHypothesis ↔
      ∀ m : ℕ, Nat.floor (finiteThetaCollisionReading (m : ℝ)
        (explicitWindowRoundingThreshold (m : ℝ)) + 1 / 2) < 2 := by
  constructor
  · intro hRH m
    have hn6 : 6 ≤ explicitWindowRoundingThreshold (m : ℝ) := le_max_left 6 _
    rw [floor_finiteThetaCollisionReading_eq_zero_uniform_of_riemannHypothesis hRH (m : ℝ) hn6]
    omega
  · intro hbound
    apply _root_.RHTower.riemannHypothesis_of_forall_nat_horizontalCollisionCharge_lt_two
    intro m
    have hfloor := floor_finiteThetaCollisionReading_eq_of_threshold (m : ℝ) (le_refl _)
    rw [← hfloor]
    exact hbound m

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.thetaCollision_product_error_lt_eighth_uniform
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.floor_finiteThetaCollisionReading_eq_of_stage
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.riemannHypothesis_iff_uniform_floor_finiteThetaCollisionReading_eq_zero
