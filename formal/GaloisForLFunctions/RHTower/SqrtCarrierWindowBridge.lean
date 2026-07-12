import GaloisForLFunctions.RHTower.SqrtCarrierCertificate
import GaloisForLFunctions.RHTower.DpolyBallFloor
import GaloisForLFunctions.RHTower.DetectionSecondMoment
import GaloisForLFunctions.RHTower.LargeValuesDpoly

/-!
# The certified carrier floor in the window machinery's native shapes

The certified floor for the square-dilated Möbius carrier holds at every point of the
half-plane `re z ≥ 1/2 + ε` under a purely numeric gap condition.  This file re-emits it
in each interface shape the tree's floor/window machinery consumes:

* `RHTower.sqrtCarrier_certified_floor_line` — the floor at every point of the vertical
  line `re = σ` for any `σ ≥ 1/2 + ε`;
* `RHTower.sqrtCarrier_good_height_cofinal` — the cofinal good-heights format of
  `FloorFailureCofinal`: above every bound there is a height with the floor (indeed all
  heights carry it);
* `RHTower.sqrtCarrier_weighted_dpoly_floor` — the detection-native form: in the
  σ-weighted one-dimensional coefficient convention of `SecondMoment`/
  `DetectionSecondMoment` (`dpoly` with coefficients `sqrtMoebiusCoeff n · n^(-σ)`), the
  carrier is bounded away from zero at every height — the mollified-carrier
  nondegeneracy datum the window machinery places against detection windows;
* `RHTower.sqrtCarrier_strip_floor` — the sub-abscissa extension: through
  `dpoly2_chart_floor`, a finite variation budget pushes the certified floor to real
  part `σ₁`, including `σ₁` below `1/2 + ε`, at every height;
* `RHTower.sqrtCarrier_ball_floor` — the chart form: through `dpoly2_ball_floor`, the
  certified center floor spreads to any closed ball around a center on the half-plane,
  with the log-Lipschitz budget — floors on annulus charts crossing below the abscissa.
-/

noncomputable section

namespace RHTower

open Complex Metric

private theorem re_add_mul_I (σ τ : ℝ) : ((σ : ℂ) + (τ : ℂ) * I).re = σ := by simp

/-- The certified floor on the whole vertical line `re = σ`, `σ ≥ 1/2 + ε`. -/
theorem sqrtCarrier_certified_floor_line {ε t₀ : ℝ} (hε : 0 < ε) {σ : ℝ}
    (hσ : 1 / 2 + ε ≤ σ) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε)) (τ : ℝ) :
    t₀ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) ((σ : ℂ) + (τ : ℂ) * I)‖ :=
  sqrtCarrier_certified_floor hε (by rw [re_add_mul_I]; exact hσ) hN hgap

/-- **Good heights, `FloorFailureCofinal` format.**  At every real part `σ ≥ 1/2 + ε` the
certified floor holds at cofinally many heights — the `hline` datum of the cofinal floor
machinery, here without any density hypothesis. -/
theorem sqrtCarrier_good_height_cofinal {ε t₀ : ℝ} (hε : 0 < ε) {σ : ℝ}
    (hσ : 1 / 2 + ε ≤ σ) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε)) :
    ∀ M : ℝ, ∃ τ, M < τ ∧
      t₀ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) ((σ : ℂ) + (τ : ℂ) * I)‖ :=
  fun M => ⟨M + 1, by linarith,
    sqrtCarrier_certified_floor_line hε hσ hN hgap (M + 1)⟩

/-- **Detection-native nondegeneracy.**  In the σ-weighted one-dimensional coefficient
convention of the second-moment/detection stack, the weighted square-dilated carrier is
bounded away from zero at every height `τ` — the carrier floor datum for window
placement against the mollified detection polynomial. -/
theorem sqrtCarrier_weighted_dpoly_floor {ε t₀ : ℝ} (hε : 0 < ε) {σ : ℝ}
    (hσ : 1 / 2 + ε ≤ σ) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε)) (τ : ℝ) :
    t₀ < ‖dpoly (fun n => sqrtMoebiusCoeff n * (n : ℝ) ^ (-σ)) (Finset.Icc 1 N) τ‖ := by
  have h := sqrtCarrier_certified_floor_line hε hσ hN hgap τ
  rwa [dpoly2_line_eq _ _ (fun _ hn => (Finset.mem_Icc.mp hn).1) σ τ] at h

/-- **Sub-abscissa strip floor.**  A finite variation budget extends the certified floor
from the line `re = 1/2 + ε` to real part `σ₁` — including `σ₁ < 1/2 + ε`, below the
carrier's abscissa of convergence — at every height. -/
theorem sqrtCarrier_strip_floor {ε t₀ ε₁ : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε)) (σ₁ : ℝ)
    (hbudget : ∑ n ∈ Finset.Icc 1 N, |sqrtMoebiusCoeff n| *
        |(n : ℝ) ^ (-σ₁) - (n : ℝ) ^ (-(1 / 2 + ε))| ≤ t₀ - ε₁) (τ : ℝ) :
    ε₁ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) ((σ₁ : ℂ) + (τ : ℂ) * I)‖ :=
  dpoly2_chart_floor sqrtMoebiusCoeff (Finset.Icc 1 N)
    (fun _ hn => (Finset.mem_Icc.mp hn).1) σ₁ (1 / 2 + ε) τ t₀ ε₁
    (sqrtCarrier_certified_floor_line hε le_rfl hN hgap τ) hbudget

/-- **Chart/ball floor.**  The certified center floor spreads to any closed ball around a
center on the half-plane, with the log-Lipschitz budget of `DpolyBallFloor` — carrier
floors on annulus charts, including charts crossing below the abscissa. -/
theorem sqrtCarrier_ball_floor {ε t₀ ε₁ R : ℝ} (hε : 0 < ε) {z₀ : ℂ}
    (hz₀ : 1 / 2 + ε ≤ z₀.re) {N : ℕ} (hN : 1 ≤ Nat.sqrt N) (hR : 0 ≤ R)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε))
    (hbudget : (∑ n ∈ Finset.Icc 1 N, |sqrtMoebiusCoeff n| *
        (Real.log n * (n : ℝ) ^ (-(z₀.re - R)))) * R ≤ t₀ - ε₁) :
    ∀ z ∈ closedBall z₀ R, ε₁ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z‖ :=
  dpoly2_ball_floor sqrtMoebiusCoeff (Finset.Icc 1 N)
    (fun _ hn => (Finset.mem_Icc.mp hn).1) hR
    (sqrtCarrier_certified_floor hε hz₀ hN hgap) hbudget

/-! ## The first certified floor below the abscissa of convergence -/

/-- **Below the abscissa.**  At real part `9/20 < 1/2` — where the square-dilated Möbius
series diverges — the cutoff-`4` carrier keeps the certified floor `3/10` at every
height: strip transfer from the certified line `re = 5` (where the rpow radius
`2^(-9) = 1/512` is exact), with the single nontrivial budget term bracketed by the
pure-power certificate `(11/20)²⁰·4⁹ ≥ 20²⁰`. -/
theorem sqrtCarrier_floor_witness_below_abscissa (τ : ℝ) :
    (3 / 10 : ℝ) < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 4) ((9 / 20 : ℝ) + (τ : ℂ) * I)‖ := by
  have hsqrt : Nat.sqrt 4 = 2 := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.sqrt_eq']
  have h2 : ¬ IsSquare (2 : ℕ) := by
    rintro ⟨r, hr⟩
    rcases Nat.lt_or_ge r 2 with h | h
    · interval_cases r <;> omega
    · nlinarith
  have h3 : ¬ IsSquare (3 : ℕ) := by
    rintro ⟨r, hr⟩
    rcases Nat.lt_or_ge r 2 with h | h
    · interval_cases r <;> omega
    · nlinarith
  have hc1 : sqrtMoebiusCoeff 1 = 1 := by
    rw [sqrtMoebiusCoeff, show (1 : ℕ) = 1 * 1 from rfl, sqrtPart_apply_mul_self]
    norm_num [ArithmeticFunction.moebius_apply_one]
  have hc2 : sqrtMoebiusCoeff 2 = 0 := by
    rw [sqrtMoebiusCoeff, sqrtPart_apply_of_not_isSquare _ h2]
    norm_num
  have hc3 : sqrtMoebiusCoeff 3 = 0 := by
    rw [sqrtMoebiusCoeff, sqrtPart_apply_of_not_isSquare _ h3]
    norm_num
  have hc4 : sqrtMoebiusCoeff 4 = -1 := by
    rw [sqrtMoebiusCoeff, show (4 : ℕ) = 2 * 2 by norm_num, sqrtPart_apply_mul_self,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  refine sqrtCarrier_strip_floor (ε := 9 / 2) (t₀ := 17 / 20) (by norm_num) (N := 4)
    (by rw [hsqrt]; norm_num) ?_ (9 / 20) ?_ τ
  · rw [hsqrt, show -(2 * (9 / 2 : ℝ)) = ((-9 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  · rw [show (1 / 2 + 9 / 2 : ℝ) = 5 by norm_num,
      show (Finset.Icc (1 : ℕ) 4) = {1, 2, 3, 4} by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton, hc1, hc2, hc3, hc4]
    simp only [Nat.cast_one, Real.one_rpow, sub_self, abs_zero, mul_zero, zero_mul,
      abs_neg, abs_one, one_mul, zero_add]
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ ((4 : ℕ) : ℝ)) (by norm_num : (-5 : ℝ) ≤ -(9 / 20)))),
      show (17 / 20 - 3 / 10 : ℝ) = 11 / 20 by norm_num]
    refine le_trans (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) ?_
    rw [show (-(9 / 20 : ℝ)) = -(((9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) by norm_num]
    exact rpow_neg_div_le_of_one_le_pow (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

/-! ## The window inequality: carrier mass below, detection mass above -/

/-- **Carrier window mass.**  On any window `[T, T+U]`, the σ-weighted square-dilated
carrier's second moment is at least `t₀²·U` — the lower companion, on the same window and
in the same coefficient dialect, of the detection stack's second-moment upper bounds. -/
theorem sqrtCarrier_window_mass {ε t₀ : ℝ} (hε : 0 < ε) (ht₀ : 0 ≤ t₀) {σ : ℝ}
    (hσ : 1 / 2 + ε ≤ σ) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε))
    (T U : ℝ) (hU : 0 ≤ U) :
    t₀ ^ 2 * U ≤ ∫ t in T..(T + U),
      ‖dpoly (fun n => sqrtMoebiusCoeff n * (n : ℝ) ^ (-σ)) (Finset.Icc 1 N) t‖ ^ 2 := by
  have hcont : Continuous (fun t =>
      ‖dpoly (fun n => sqrtMoebiusCoeff n * (n : ℝ) ^ (-σ)) (Finset.Icc 1 N) t‖ ^ 2) :=
    ((dpoly_continuous _ _).norm).pow 2
  calc t₀ ^ 2 * U = ∫ _ in T..(T + U), t₀ ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ _ := by
        refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
          (hcont.intervalIntegrable T (T + U)) fun x _ => ?_
        exact pow_le_pow_left₀ ht₀
          (le_of_lt (sqrtCarrier_weighted_dpoly_floor hε hσ hN hgap x)) 2

/-- **Window separation: carrier over detection.**  On a common window `[T, T+U]` and at
a common weight `σ`, whenever the divisor-tail-plus-harmonic detection bound is below the
carrier mass floor `t₀²·U`, the σ-weighted detection second moment is strictly smaller
than the σ-weighted carrier second moment — the quantitative separation the zero-density
argument runs on: carrier mass bounded below while detection mass stays small. -/
theorem sqrtCarrier_exceeds_detection_window {ε t₀ : ℝ} (hε : 0 < ε) (ht₀ : 0 ≤ t₀)
    {σ : ℝ} (hσ : 1 / 2 + ε ≤ σ) {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    (hgap : t₀ + (Nat.sqrt N : ℝ) ^ (-(2 * ε)) / (2 * ε) < 2 * ε / (1 + 2 * ε))
    {Nd y : ℕ} (hmin : 1 ≤ min Nd y) (T U : ℝ) (hU : 0 ≤ U)
    (hsep : U * (∑' k : ℕ, Set.indicator {j | min Nd y < j}
          (fun k => (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ)) k)
        + 4 * ((Nd * y : ℕ) : ℝ) * (∑ j ∈ Finset.Icc 1 (Nd * y), 1 / (j : ℝ))
            * ∑ k ∈ prodSupport (Finset.Icc 1 Nd) (Finset.Icc 1 y), (detCoeffW Nd y σ k) ^ 2
      < t₀ ^ 2 * U) :
    (∫ t in T..(T + U), ‖dpoly (detCoeffW Nd y σ)
        (prodSupport (Finset.Icc 1 Nd) (Finset.Icc 1 y)) t‖ ^ 2)
      < ∫ t in T..(T + U),
        ‖dpoly (fun n => sqrtMoebiusCoeff n * (n : ℝ) ^ (-σ)) (Finset.Icc 1 N) t‖ ^ 2 :=
  lt_of_le_of_lt
    (detectionW_secondMoment_bound σ (by linarith) hmin T U hU)
    (lt_of_lt_of_le hsep (sqrtCarrier_window_mass hε ht₀ hσ hN hgap T U hU))

/-! ## Effective divisor tail and the numeric separation witness -/

/-- Pointwise effective divisor bound: `d(k)²·k^(-2σ) ≤ k^(2-2σ)` for `k ≥ 1`, by the
trivial bound `d(k) ≤ k`. -/
theorem divisor_sq_rpow_le {k : ℕ} (hk : 1 ≤ k) (σ : ℝ) :
    ((k.divisors.card : ℝ)) ^ 2 * (k : ℝ) ^ (-2 * σ) ≤ (k : ℝ) ^ (2 - 2 * σ) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hd : ((k.divisors.card : ℝ)) ^ 2 ≤ ((k : ℝ)) ^ (2 : ℕ) := by
    have hcast : (k.divisors.card : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.card_divisors_le_self k
    exact pow_le_pow_left₀ (by positivity) hcast 2
  calc ((k.divisors.card : ℝ)) ^ 2 * (k : ℝ) ^ (-2 * σ)
      ≤ ((k : ℝ)) ^ (2 : ℕ) * (k : ℝ) ^ (-2 * σ) :=
        mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hk0.le _)
    _ = (k : ℝ) ^ (2 - 2 * σ) := by
        rw [← Real.rpow_natCast ((k : ℝ)) 2, ← Real.rpow_add hk0]
        congr 1
        push_cast
        ring

/-- **Effective divisor-tail bound.**  For `σ > 3/2` the divisor-square tail of the
detection diagonal is bounded by the explicit p-series constant:
`∑'_{k>m} d(k)²·k^(-2σ) ≤ m^(3-2σ)/(2σ-3)`. -/
theorem divisor_tail_tsum_le {m : ℕ} (hm : 1 ≤ m) {σ : ℝ} (hσ : 3 / 2 < σ) :
    ∑' k : ℕ, Set.indicator {j | m < j}
        (fun k => ((k.divisors.card : ℝ)) ^ 2 * (k : ℝ) ^ (-2 * σ)) k
      ≤ (m : ℝ) ^ (3 - 2 * σ) / (2 * σ - 3) := by
  set f : ℕ → ℝ := fun k => ((k.divisors.card : ℝ)) ^ 2 * (k : ℝ) ^ (-2 * σ) with hf
  have hc : 1 < 2 * σ - 2 := by linarith
  have hnonneg : ∀ k, 0 ≤ Set.indicator {j | m < j} f k := fun k =>
    Set.indicator_nonneg (fun j _ => by positivity) k
  have hmaj : Summable (fun k : ℕ => (k : ℝ) ^ (-(2 * σ - 2))) := by
    refine (Real.summable_nat_rpow_inv.mpr hc).congr fun k => ?_
    rw [← Real.rpow_neg (Nat.cast_nonneg k)]
  have hind_le : ∀ k, Set.indicator {j | m < j} f k ≤ (k : ℝ) ^ (-(2 * σ - 2)) := by
    intro k
    rcases Nat.lt_or_ge m k with hkm | hkm
    · rw [Set.indicator_of_mem (by simpa using hkm)]
      refine le_trans (divisor_sq_rpow_le (le_trans hm hkm.le) σ) (le_of_eq ?_)
      congr 1
      ring
    · rw [Set.indicator_of_notMem (by simpa using Nat.not_lt.mpr hkm)]
      positivity
  have hsummable : Summable (Set.indicator {j | m < j} f) :=
    Summable.of_nonneg_of_le hnonneg hind_le hmaj
  have hsplit := Summable.sum_add_tsum_nat_add (m + 1) hsummable
  have hzero : ∑ k ∈ Finset.range (m + 1), Set.indicator {j | m < j} f k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkm : ¬ m < k := by
      have := Finset.mem_range.mp hk
      omega
    rw [Set.indicator_of_notMem (by simpa using hkm)]
  have htail_eq : ∑' k, Set.indicator {j | m < j} f k
      = ∑' i, Set.indicator {j | m < j} f (i + (m + 1)) := by
    rw [← hsplit, hzero, zero_add]
  rw [htail_eq]
  have hfinal : (m : ℝ) ^ (1 - (2 * σ - 2)) / ((2 * σ - 2) - 1)
      = (m : ℝ) ^ (3 - 2 * σ) / (2 * σ - 3) := by
    rw [show (1 : ℝ) - (2 * σ - 2) = 3 - 2 * σ by ring,
      show (2 * σ - 2) - 1 = 2 * σ - 3 by ring]
  rw [← hfinal]
  refine Real.tsum_le_of_sum_range_le (fun i => hnonneg _) fun n => ?_
  calc ∑ i ∈ Finset.range n, Set.indicator {j | m < j} f (i + (m + 1))
      ≤ ∑ i ∈ Finset.range n, ((i + (m + 1) : ℕ) : ℝ) ^ (-(2 * σ - 2)) :=
        Finset.sum_le_sum fun i _ => hind_le _
    _ ≤ (m : ℝ) ^ (1 - (2 * σ - 2)) / ((2 * σ - 2) - 1) := sum_range_add_rpow_neg_le hc hm n

/-- **The first numeric window separation.**  At parameters
`(N, (Nd, y), σ, t₀, U) = (9, (2, 2), 2, 73/100, 40)` and on every window `[T, T+40]`,
the σ-weighted detection second moment is strictly smaller than the σ-weighted
square-dilated carrier second moment: the gap hypothesis is discharged by `norm_num`
through the divisor-tail bound (`≤ 1/2`), the exact harmonic sum `H(4) = 25/12`, and the
banked coefficient bounds (`∑ e_k² ≤ 9/256`); the carrier floor is the certificate at
`ε = 3/2` with exact radius `3⁻³/3 = 1/81`. -/
theorem sqrtCarrier_exceeds_detection_witness (T : ℝ) :
    (∫ t in T..(T + 40), ‖dpoly (detCoeffW 2 2 2)
        (prodSupport (Finset.Icc 1 2) (Finset.Icc 1 2)) t‖ ^ 2)
      < ∫ t in T..(T + 40),
        ‖dpoly (fun n => sqrtMoebiusCoeff n * (n : ℝ) ^ (-(2 : ℝ)))
          (Finset.Icc 1 9) t‖ ^ 2 := by
  have hsqrt9 : Nat.sqrt 9 = 3 := by rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.sqrt_eq']
  refine sqrtCarrier_exceeds_detection_window (ε := 3 / 2) (t₀ := 73 / 100)
    (by norm_num) (by norm_num) (σ := 2) (by norm_num) (N := 9)
    (by rw [hsqrt9]; norm_num) ?_ (Nd := 2) (y := 2) (by norm_num) T 40 (by norm_num) ?_
  · rw [hsqrt9, show -(2 * (3 / 2 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  · have htail : ∑' k : ℕ, Set.indicator {j | min 2 2 < j}
        (fun k : ℕ => ((k.divisors.card : ℝ)) ^ 2 * (k : ℝ) ^ (-2 * (2 : ℝ))) k ≤ 1 / 2 := by
      rw [Nat.min_self]
      refine le_trans (divisor_tail_tsum_le (by norm_num) (by norm_num)) (le_of_eq ?_)
      rw [show (3 - 2 * (2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      norm_num
    have hd4 : (4 : ℕ).divisors.card = 3 := by decide
    have h4 := sq_detCoeffW_le (N := 2) (y := 2) (2 : ℝ)
      (by norm_num : 1 ≤ 4) (by norm_num : (4 : ℕ) ≠ 1)
    rw [hd4, show (-2 * (2 : ℝ)) = ((-4 : ℤ) : ℝ) by norm_num, Real.rpow_intCast] at h4
    have h4' : (detCoeffW 2 2 2 4) ^ 2 ≤ 9 / 256 := by
      refine le_trans h4 (le_of_eq ?_)
      norm_num
    have hdetsum : ∑ k ∈ prodSupport (Finset.Icc 1 2) (Finset.Icc 1 2),
        (detCoeffW 2 2 2 k) ^ 2 ≤ 9 / 256 := by
      rw [show prodSupport (Finset.Icc 1 2) (Finset.Icc 1 2) = {1, 2, 4} by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton,
        detCoeffW_eq_zero_of_le 2 le_rfl (by norm_num) (by norm_num),
        detCoeffW_eq_zero_of_le 2 (by norm_num) le_rfl le_rfl]
      calc (0 : ℝ) ^ 2 + ((0 : ℝ) ^ 2 + (detCoeffW 2 2 2 4) ^ 2)
          = (detCoeffW 2 2 2 4) ^ 2 := by ring
        _ ≤ 9 / 256 := h4'
    have hH : ∑ j ∈ Finset.Icc (1 : ℕ) (2 * 2), 1 / (j : ℝ) = 25 / 12 := by
      rw [show Finset.Icc (1 : ℕ) (2 * 2) = {1, 2, 3, 4} by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      norm_num
    calc (40 : ℝ) * (∑' k : ℕ, Set.indicator {j | min 2 2 < j}
            (fun k : ℕ => ((k.divisors.card : ℝ)) ^ 2 * (k : ℝ) ^ (-2 * (2 : ℝ))) k)
          + 4 * ((2 * 2 : ℕ) : ℝ) * (∑ j ∈ Finset.Icc (1 : ℕ) (2 * 2), 1 / (j : ℝ))
            * ∑ k ∈ prodSupport (Finset.Icc 1 2) (Finset.Icc 1 2), (detCoeffW 2 2 2 k) ^ 2
        ≤ 40 * (1 / 2) + 4 * ((2 * 2 : ℕ) : ℝ) * (25 / 12) * (9 / 256) := by
          rw [hH]
          refine add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num)) ?_
          exact mul_le_mul_of_nonneg_left hdetsum (by positivity)
      _ < (73 / 100) ^ 2 * 40 := by norm_num

end RHTower
