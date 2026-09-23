import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeSourceField
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualSeriesFreezing

noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace RHTower

/-- Coarse all-height derivative bound used only for local uniform differentiation
of the complete dual source series. -/
theorem exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_global_invScale :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (tau : ℝ) {Y : ℝ}, 0 < Y →
      ‖deriv (fun u : ℝ => smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        K * (1 + |tau|) ^ 3 / Y := by
  obtain ⟨E, hE, hglobal⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatioSqHeightDerivative_le_global
  let q : ℝ → ℝ := fun v =>
    (1 + |v|) ^ 4 * Real.exp (-(v ^ 2))
  let M : ℝ := ∫ v : ℝ, q v
  let a : ℝ := 1 / (2 * Real.pi)
  let K : ℝ := a * (3 * E) * M
  have hq : Integrable q := integrable_one_add_abs_pow_four_mul_exp_neg_sq
  have hq0 : ∀ v, 0 ≤ q v := fun v => by
    dsimp only [q]
    positivity
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact integral_nonneg hq0
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro tau Y hY
  let C : ℝ := 3 * E * (1 + |tau|) ^ 3 / Y
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hboundInt : Integrable (fun v : ℝ => C * q v) := hq.const_mul C
  have hint :
      ‖∫ v : ℝ,
          smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand tau Y v‖ ≤
        ∫ v : ℝ, C * q v := by
    apply norm_integral_le_of_norm_le hboundInt
    exact Filter.Eventually.of_forall fun v => by
      have hsquare := hglobal tau v
      have hm := norm_smoothAFEMellinIntegrand_vertical_le hY
        (show (0 : ℝ) < 1 by norm_num) v
      have hm' :
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
            (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
        simpa [Real.rpow_neg_one] using hm
      have hexp1 : Real.exp (1 : ℝ) ≤ 3 :=
        Real.exp_one_lt_d9.le.trans (by norm_num)
      have hpow : (1 + |v|) ^ 3 ≤ (1 + |v|) ^ 4 := by
        have hb : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
        nlinarith [pow_nonneg (by linarith : 0 ≤ 1 + |v|) 3]
      unfold smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand
      rw [norm_mul]
      calc
        ‖smoothAFEZetaChiShiftRatioSqHeightDerivative tau v‖ *
              ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
            ≤ (E * (1 + |tau|) ^ 3 * (1 + |v|) ^ 3) *
                ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by gcongr
        _ ≤ (E * (1 + |tau|) ^ 3 * (1 + |v|) ^ 3) *
                ((Y⁻¹ * 3) * Real.exp (-(v ^ 2))) := by gcongr
        _ = (3 * E * (1 + |tau|) ^ 3 / Y) *
              ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) := by
                rw [inv_eq_one_div]
                ring
        _ ≤ C * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
              dsimp only [C]
              gcongr
        _ = C * q v := rfl
  rw [(hasDerivAt_smoothAFEZetaSquareDualWeight hY tau).deriv]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    a * ‖∫ v : ℝ,
          smoothAFEZetaSquareDualWeightHeightDerivativeIntegrand tau Y v‖
        ≤ a * ∫ v : ℝ, C * q v := by gcongr
    _ = a * (C * M) := by rw [integral_const_mul]
    _ = K * (1 + |tau|) ^ 3 / Y := by
      dsimp only [K, C]
      ring

/-- Inner square-dual AFE series, before multiplication by the neutral `chi^(2 : ℕ)` factor. -/
def smoothAFEZetaSquareDualSourceField (T r t : ℝ) : ℂ :=
  ∑' n : ℕ, ((n + 1).divisors.card : ℂ) *
    (n + 1 : ℂ) ^ (linePt t - 1) *
      smoothAFEZetaSquareDualWeight r ((n + 1 : ℝ) * T)

private def smoothAFEZetaSquareDualSourceCoefficient
    (T r t : ℝ) (n : ℕ) : ℂ :=
  ((n + 1).divisors.card : ℂ) *
    (n + 1 : ℂ) ^ (linePt t - 1) *
      smoothAFEZetaSquareDualWeight r ((n + 1 : ℝ) * T)

private theorem norm_smoothAFEZetaSquareDualSourceCoefficient
    (T r t : ℝ) (n : ℕ) :
    ‖smoothAFEZetaSquareDualSourceCoefficient T r t n‖ =
      ((n + 1).divisors.card : ℝ) *
        (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          ‖smoothAFEZetaSquareDualWeight r ((n + 1 : ℝ) * T)‖ := by
  rw [smoothAFEZetaSquareDualSourceCoefficient, norm_mul, norm_mul,
    Complex.norm_natCast, norm_natSucc_cpow_linePt_sub_one_dualMass]

theorem summable_smoothAFEZetaSquareDualSourceCoefficient
    {T : ℝ} (hT : 0 < T) (r t : ℝ) :
    Summable (smoothAFEZetaSquareDualSourceCoefficient T r t) := by
  obtain ⟨K, hK, hweight⟩ :=
    exists_norm_smoothAFEZetaSquareDualWeight_le_invScale
  let q : ℕ → ℝ := fun n =>
    (K * (1 + |r|) ^ 2 / T) *
      (((n + 1).divisors.card : ℝ) /
        (n + 1 : ℝ) ^ (3 / 2 : ℝ))
  have hq : Summable q :=
    (summable_card_divisors_div_natSucc_rpow_three_halves).mul_left
      (K * (1 + |r|) ^ 2 / T)
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hq
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hY : 0 < (n + 1 : ℝ) * T := mul_pos hn hT
  rw [norm_smoothAFEZetaSquareDualSourceCoefficient]
  calc
    ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            ‖smoothAFEZetaSquareDualWeight r ((n + 1 : ℝ) * T)‖
        ≤ ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (K * (1 + |r|) ^ 2 / ((n + 1 : ℝ) * T)) := by
              gcongr
              exact hweight r hY
    _ = q n := by
      dsimp only [q]
      have hp : (n + 1 : ℝ) ^ (3 / 2 : ℝ) =
          (n + 1 : ℝ) ^ (1 / 2 : ℝ) * (n + 1 : ℝ) := by
        rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
          Real.rpow_add hn, Real.rpow_one]
      rw [Real.rpow_neg hn.le, hp]
      field_simp [hn.ne', hT.ne']

theorem exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_global_threeHalves :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {T r t : ℝ} {n : ℕ}, 0 < T →
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ≤
          (K * (1 + |r|) ^ 3 / T) *
            (((n + 1).divisors.card : ℝ) /
              (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
  obtain ⟨K, hK, hderiv⟩ :=
    exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_global_invScale
  refine ⟨K, hK, ?_⟩
  intro T r t n hT
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hY : 0 < (n + 1 : ℝ) * T := mul_pos hn hT
  rw [norm_smoothAFEZetaSquareDualDerivativeCoefficient]
  calc
    ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            ‖deriv (fun u : ℝ =>
              smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r‖
        ≤ ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (K * (1 + |r|) ^ 3 / ((n + 1 : ℝ) * T)) := by
              gcongr
              exact hderiv r hY
    _ = (K * (1 + |r|) ^ 3 / T) *
          (((n + 1).divisors.card : ℝ) /
            (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
      have hp : (n + 1 : ℝ) ^ (3 / 2 : ℝ) =
          (n + 1 : ℝ) ^ (1 / 2 : ℝ) * (n + 1 : ℝ) := by
        rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
          Real.rpow_add hn, Real.rpow_one]
      rw [Real.rpow_neg hn.le, hp]
      field_simp [hn.ne', hT.ne']

private theorem hasDerivAt_smoothAFEZetaSquareDualSourceCoefficient
    {T : ℝ} (hT : 0 < T) (r t : ℝ) (n : ℕ) :
    HasDerivAt (fun u : ℝ =>
      smoothAFEZetaSquareDualSourceCoefficient T u t n)
      (smoothAFEZetaSquareDualDerivativeCoefficient T r t n) r := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hY : 0 < (n + 1 : ℝ) * T := mul_pos hn hT
  have hw := hasDerivAt_smoothAFEZetaSquareDualWeight hY r
  have h := hw.const_mul
    (((n + 1).divisors.card : ℂ) *
      (n + 1 : ℂ) ^ (linePt t - 1))
  rw [← hw.deriv] at h
  simpa [smoothAFEZetaSquareDualSourceCoefficient,
    smoothAFEZetaSquareDualDerivativeCoefficient, mul_assoc] using h

/-- The complete inner dual AFE series differentiates in carrier height to the
literal phase-faithful source field. -/
theorem hasDerivAt_smoothAFEZetaSquareDualSourceField
    {T : ℝ} (hT : 0 < T) (r t : ℝ) :
    HasDerivAt (fun u : ℝ => smoothAFEZetaSquareDualSourceField T u t)
      (smoothAFEZetaSquareDualDerivativeSourceField T r t) r := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_global_threeHalves
  let q : ℕ → ℝ := fun n =>
    (K * (2 + |r|) ^ 3 / T) *
      (((n + 1).divisors.card : ℝ) /
        (n + 1 : ℝ) ^ (3 / 2 : ℝ))
  have hq : Summable q :=
    (summable_card_divisors_div_natSucc_rpow_three_halves).mul_left
      (K * (2 + |r|) ^ 3 / T)
  have hbound : ∀ n : ℕ, ∀ u ∈ Metric.ball r 1,
      ‖smoothAFEZetaSquareDualDerivativeCoefficient T u t n‖ ≤ q n := by
    intro n u hu
    have hudist : |u - r| < 1 := by
      simpa [Real.dist_eq] using hu
    have huabs : |u| ≤ |r| + 1 := by
      calc
        |u| = |(u - r) + r| := by ring_nf
        _ ≤ |u - r| + |r| := abs_add_le _ _
        _ ≤ |r| + 1 := by linarith
    have hheight : (1 + |u|) ^ 3 ≤ (2 + |r|) ^ 3 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hraw := hcoefficient (T := T) (r := u) (t := t) (n := n) hT
    calc
      ‖smoothAFEZetaSquareDualDerivativeCoefficient T u t n‖
          ≤ (K * (1 + |u|) ^ 3 / T) *
              (((n + 1).divisors.card : ℝ) /
                (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := hraw
      _ ≤ (K * (2 + |r|) ^ 3 / T) *
              (((n + 1).divisors.card : ℝ) /
                (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
            gcongr
      _ = q n := rfl
  change HasDerivAt
    (fun u : ℝ => ∑' n : ℕ,
      smoothAFEZetaSquareDualSourceCoefficient T u t n)
    (∑' n : ℕ, smoothAFEZetaSquareDualDerivativeCoefficient T r t n) r
  exact hasDerivAt_tsum_of_isPreconnected hq Metric.isOpen_ball
    (convex_ball r (1 : ℝ)).isPreconnected
    (fun n u _ => hasDerivAt_smoothAFEZetaSquareDualSourceCoefficient hT u t n)
    hbound (Metric.mem_ball_self (by norm_num))
    (summable_smoothAFEZetaSquareDualSourceCoefficient hT r t)
    (Metric.mem_ball_self (by norm_num))

theorem summable_norm_smoothAFEZetaSquareDualDerivativeCoefficient_global
    {T : ℝ} (hT : 0 < T) (r t : ℝ) :
    Summable (fun n : ℕ =>
      ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖) := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_global_threeHalves
  let q : ℕ → ℝ := fun n =>
    (K * (1 + |r|) ^ 3 / T) *
      (((n + 1).divisors.card : ℝ) /
        (n + 1 : ℝ) ^ (3 / 2 : ℝ))
  have hq : Summable q :=
    (summable_card_divisors_div_natSucc_rpow_three_halves).mul_left
      (K * (1 + |r|) ^ 3 / T)
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => hcoefficient hT) hq

theorem measurable_smoothAFEZetaSquareDualDerivativeSourceField
    (T t : ℝ) :
    Measurable (fun r : ℝ =>
      smoothAFEZetaSquareDualDerivativeSourceField T r t) := by
  unfold smoothAFEZetaSquareDualDerivativeSourceField
  apply Measurable.tsum
  intro n
  have hm : Measurable (fun r : ℝ =>
      deriv (fun u : ℝ =>
        smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r) :=
    measurable_deriv _
  have hd : Measurable (fun _ : ℝ => ((n + 1).divisors.card : ℂ)) :=
    measurable_const
  have hp : Measurable (fun _ : ℝ =>
      (n + 1 : ℂ) ^ (linePt t - 1)) := measurable_const
  change Measurable (fun r : ℝ =>
    (((n + 1).divisors.card : ℂ) *
      (n + 1 : ℂ) ^ (linePt t - 1)) *
        deriv (fun u : ℝ =>
          smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r)
  exact (hd.mul hp).mul hm

private theorem intervalIntegrable_smoothAFEZetaSquareDualDerivativeSourceField
    {T : ℝ} (hT : 0 < T) (a b t : ℝ) :
    IntervalIntegrable
      (fun r : ℝ => smoothAFEZetaSquareDualDerivativeSourceField T r t)
      volume a b := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_global_threeHalves
  have hordered : ∀ {c d : ℝ}, c ≤ d →
      IntervalIntegrable
        (fun r : ℝ => smoothAFEZetaSquareDualDerivativeSourceField T r t)
        volume c d := by
    intro c d hcd
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcd]
    let C : ℝ := (K * (1 + max |c| |d|) ^ 3 / T) *
      smoothAFEZetaSquareDivisorMajorant
    apply MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_smoothAFEZetaSquareDualDerivativeSourceField T t).aestronglyMeasurable.restrict)
      C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hrabs : |r| ≤ max |c| |d| :=
      abs_le_max_abs_abs hr.1 hr.2
    have hheight : (1 + |r|) ^ 3 ≤ (1 + max |c| |d|) ^ 3 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    let q : ℕ → ℝ := fun n =>
      (K * (1 + max |c| |d|) ^ 3 / T) *
        (((n + 1).divisors.card : ℝ) /
          (n + 1 : ℝ) ^ (3 / 2 : ℝ))
    have hq : Summable q :=
      (summable_card_divisors_div_natSucc_rpow_three_halves).mul_left
        (K * (1 + max |c| |d|) ^ 3 / T)
    have hsum :=
      summable_norm_smoothAFEZetaSquareDualDerivativeCoefficient_global hT r t
    have hpoint : ∀ n : ℕ,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ≤ q n := by
      intro n
      calc
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖
            ≤ (K * (1 + |r|) ^ 3 / T) *
                (((n + 1).divisors.card : ℝ) /
                  (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := hcoefficient hT
        _ ≤ (K * (1 + max |c| |d|) ^ 3 / T) *
                (((n + 1).divisors.card : ℝ) /
                  (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
              gcongr
        _ = q n := rfl
    change ‖∑' n : ℕ,
      smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ≤ C
    calc
      ‖∑' n : ℕ, smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖
          ≤ ∑' n : ℕ,
              ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ :=
            norm_tsum_le_tsum_norm hsum
      _ ≤ ∑' n : ℕ, q n := hsum.tsum_le_tsum hpoint hq
      _ = C := by
        rw [tsum_mul_left]
        rfl
  rcases le_total a b with hab | hba
  · exact hordered hab
  · exact (hordered hba).symm

/-- Exact fundamental theorem of calculus for carrier-height freezing of the
complete square-dual source series. -/
theorem integral_smoothAFEZetaSquareDualDerivativeSourceField_eq_sub
    {T : ℝ} (hT : 0 < T) (a b t : ℝ) :
    (∫ r in a..b, smoothAFEZetaSquareDualDerivativeSourceField T r t) =
      smoothAFEZetaSquareDualSourceField T b t -
        smoothAFEZetaSquareDualSourceField T a t := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_smoothAFEZetaSquareDualSourceField hT r t)
    (intervalIntegrable_smoothAFEZetaSquareDualDerivativeSourceField hT a b t)

end RHTower
