import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicHypergeometricAnalyticDerivatives

/-!
# Analytic Gauss ODE for the BM complementary second harmonic

The exact hypergeometric coefficient recurrence is lifted through convergent scalar series. Two
zero-prepending coefficient shifts implement multiplication by `z` and `z²`; coefficientwise
annihilation then proves the standard Gauss differential equation throughout the open unit disk.
The final statements specialize to the BM transformed parameters and identify the series values
with actual complex derivatives, including every Xi fibre.
-/

open Complex Real Set Filter Topology Nat FormalMultilinearSeries Polynomial

namespace RHTower

noncomputable section

def ordinaryHypergeometricFirstDerivativeSeriesValue
    (a b c z : ℂ) : ℂ :=
  ((ordinaryHypergeometricSeries ℂ a b c).derivSeries.sum z) 1

def ordinaryHypergeometricSecondDerivativeSeriesValue
    (a b c z : ℂ) : ℂ :=
  (((ordinaryHypergeometricSeries ℂ a b c).derivSeries.derivSeries.sum z) 1) 1

/-- Prepend one zero coefficient to a scalar sequence. -/
def shiftOneCoefficient (u : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | j + 1 => u j

@[simp]
theorem shiftOneCoefficient_zero (u : ℕ → ℂ) :
    shiftOneCoefficient u 0 = 0 := rfl

@[simp]
theorem shiftOneCoefficient_succ (u : ℕ → ℂ) (j : ℕ) :
    shiftOneCoefficient u (j + 1) = u j := rfl

/-- Multiplication of a convergent scalar power series by `z` shifts its coefficients once. -/
theorem HasSum.shiftOneCoefficient_mul_pow
    {u : ℕ → ℂ} {z S : ℂ}
    (h : HasSum (fun j => u j * z ^ j) S) :
    HasSum (fun j => shiftOneCoefficient u j * z ^ j) (z * S) := by
  have hs :
      HasSum
        (fun j => shiftOneCoefficient u (j + 1) * z ^ (j + 1))
        (z * S) := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h.mul_left z
  have hfull :=
    (hasSum_nat_add_iff
      (f := fun j => shiftOneCoefficient u j * z ^ j) 1).mp hs
  simpa using hfull

/-- Multiplication by `z²` shifts a convergent scalar power series twice. -/
theorem HasSum.shiftTwoCoefficient_mul_pow
    {u : ℕ → ℂ} {z S : ℂ}
    (h : HasSum (fun j => u j * z ^ j) S) :
    HasSum
      (fun j => shiftOneCoefficient (shiftOneCoefficient u) j * z ^ j)
      (z ^ (2 : ℕ) * S) := by
  have h1 := HasSum.shiftOneCoefficient_mul_pow h
  have h2 := HasSum.shiftOneCoefficient_mul_pow h1
  simpa [pow_two, mul_assoc] using h2

theorem ordinaryHypergeometricSeries_term
    (a b c z : ℂ) (j : ℕ) :
    (ordinaryHypergeometricSeries ℂ a b c j (fun _ => z)) =
      ordinaryHypergeometricFormalCoefficient a b c j * z ^ j := by
  rw [ordinaryHypergeometricSeries_apply_eq]
  simp [ordinaryHypergeometricFormalCoefficient]

theorem ordinaryHypergeometric_derivSeries_term_apply_one
    (a b c z : ℂ) (j : ℕ) :
    (((ordinaryHypergeometricSeries ℂ a b c).derivSeries j
      (fun _ => z)) 1) =
      ((j + 1 : ℕ) : ℂ) *
        ordinaryHypergeometricFormalCoefficient a b c (j + 1) * z ^ j := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    _root_.smul_apply,
    FormalMultilinearSeries.derivSeries_coeff_one]
  simp only [ordinaryHypergeometricSeries,
    FormalMultilinearSeries.coeff_ofScalars,
    ordinaryHypergeometricFormalCoefficient,
    nsmul_eq_mul]
  push_cast
  ring

theorem ordinaryHypergeometric_secondDerivSeries_term_apply_one_one
    (a b c z : ℂ) (j : ℕ) :
    ((((ordinaryHypergeometricSeries ℂ a b c).derivSeries.derivSeries j
      (fun _ => z)) 1) 1) =
      ((j + 2 : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) *
        ordinaryHypergeometricFormalCoefficient a b c (j + 2) * z ^ j := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    _root_.smul_apply]
  simp only [_root_.smul_apply,
    FormalMultilinearSeries.derivSeries_coeff_one]
  simp only [ordinaryHypergeometricSeries,
    FormalMultilinearSeries.coeff_ofScalars,
    ordinaryHypergeometricFormalCoefficient,
    nsmul_eq_mul]
  push_cast
  ring

/-- The hypergeometric value and its first two derivative-series values are represented by the
expected scalar coefficient sums throughout the convergence disk. -/
theorem ordinaryHypergeometric_hasSum_value_first_second
    (a b c z : ℂ)
    (hz : ‖z‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius) :
    HasSum
        (fun j => ordinaryHypergeometricFormalCoefficient a b c j * z ^ j)
        ((ordinaryHypergeometricSeries ℂ a b c).sum z) ∧
      HasSum
        (fun j => ((j + 1 : ℕ) : ℂ) *
          ordinaryHypergeometricFormalCoefficient a b c (j + 1) * z ^ j)
        (ordinaryHypergeometricFirstDerivativeSeriesValue a b c z) ∧
      HasSum
        (fun j => ((j + 2 : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) *
          ordinaryHypergeometricFormalCoefficient a b c (j + 2) * z ^ j)
        (ordinaryHypergeometricSecondDerivativeSeriesValue a b c z) := by
  let p := ordinaryHypergeometricSeries ℂ a b c
  let q := p.derivSeries
  let r := q.derivSeries
  have hzq : ‖z‖ₑ < q.radius :=
    lt_of_lt_of_le hz p.radius_le_radius_derivSeries
  have hzr : ‖z‖ₑ < r.radius :=
    lt_of_lt_of_le hzq q.radius_le_radius_derivSeries
  have hzmem : z ∈ Metric.eball (0 : ℂ) p.radius := by
    simpa only [Metric.mem_eball, edist_zero_right] using hz
  have hzqmem : z ∈ Metric.eball (0 : ℂ) q.radius := by
    simpa only [Metric.mem_eball, edist_zero_right] using hzq
  have hzrmem : z ∈ Metric.eball (0 : ℂ) r.radius := by
    simpa only [Metric.mem_eball, edist_zero_right] using hzr
  have hp0 := p.hasSum hzmem
  have hq0 := q.hasSum hzqmem
  have hr0 := r.hasSum hzrmem
  have hq1 := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).hasSum hq0
  have hr1 :=
    (ContinuousLinearMap.apply ℂ (ℂ →L[ℂ] ℂ) (1 : ℂ)).hasSum hr0
  have hr2 := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).hasSum hr1
  change HasSum
    (fun j => ((p.derivSeries j (fun _ => z)) 1))
    ((p.derivSeries.sum z) 1) at hq1
  change HasSum
    (fun j => (((p.derivSeries.derivSeries j (fun _ => z)) 1) 1))
    (((p.derivSeries.derivSeries.sum z) 1) 1) at hr2
  constructor
  · simpa only [p, ordinaryHypergeometricSeries_term] using hp0
  constructor
  · simpa only [p, ordinaryHypergeometricFirstDerivativeSeriesValue,
      ordinaryHypergeometric_derivSeries_term_apply_one] using hq1
  · simpa only [p, ordinaryHypergeometricSecondDerivativeSeriesValue,
      ordinaryHypergeometric_secondDerivSeries_term_apply_one_one] using hr2

/-- Coefficients of the analytic first-derivative series. -/
def ordinaryHypergeometricFirstCoefficient
    (a b c : ℂ) (j : ℕ) : ℂ :=
  ((j + 1 : ℕ) : ℂ) * ordinaryHypergeometricFormalCoefficient a b c (j + 1)

/-- Coefficients of the analytic second-derivative series. -/
def ordinaryHypergeometricSecondCoefficient
    (a b c : ℂ) (j : ℕ) : ℂ :=
  ((j + 2 : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) *
    ordinaryHypergeometricFormalCoefficient a b c (j + 2)

/-- Denominator avoidance gives the exact hypergeometric coefficient recurrence. -/
theorem ordinaryHypergeometricFormalCoefficient_succ_recurrence
    (a b c : ℂ) (hc : ∀ j : ℕ, (j : ℂ) ≠ -c) (j : ℕ) :
    ((j + 1 : ℕ) : ℂ) * (c + (j : ℂ)) *
        ordinaryHypergeometricFormalCoefficient a b c (j + 1) =
      (a + (j : ℂ)) * (b + (j : ℂ)) *
        ordinaryHypergeometricFormalCoefficient a b c j := by
  have hpc : (ascPochhammer ℂ j).eval c ≠ 0 := by
    rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
    push Not
    intro k hk hkc
    exact hc k hkc
  have hcj : c + (j : ℂ) ≠ 0 := by
    intro h
    apply hc j
    linear_combination h
  exact ordinaryHypergeometricCoefficient_succ_recurrence a b c j hpc hcj

/-- Coefficientwise standard-form Gauss ODE.  Shifts encode multiplication by `z` and `z²`. -/
theorem ordinaryHypergeometricStandardGaussCoefficient_eq_zero
    (a b c : ℂ) (hc : ∀ j : ℕ, (j : ℂ) ≠ -c) (j : ℕ) :
    shiftOneCoefficient (ordinaryHypergeometricSecondCoefficient a b c) j -
        shiftOneCoefficient
          (shiftOneCoefficient (ordinaryHypergeometricSecondCoefficient a b c)) j +
      c * ordinaryHypergeometricFirstCoefficient a b c j -
      (a + b + 1) *
        shiftOneCoefficient (ordinaryHypergeometricFirstCoefficient a b c) j -
      a * b * ordinaryHypergeometricFormalCoefficient a b c j = 0 := by
  cases j with
  | zero =>
      have hrec := ordinaryHypergeometricFormalCoefficient_succ_recurrence
        a b c hc 0
      simp [ordinaryHypergeometricFirstCoefficient] at hrec ⊢
      linear_combination hrec
  | succ j =>
      cases j with
      | zero =>
          have hrec := ordinaryHypergeometricFormalCoefficient_succ_recurrence
            a b c hc 1
          simp [ordinaryHypergeometricFirstCoefficient,
            ordinaryHypergeometricSecondCoefficient] at hrec ⊢
          linear_combination hrec
      | succ j =>
          have hrec := ordinaryHypergeometricFormalCoefficient_succ_recurrence
            a b c hc (j + 2)
          simp [ordinaryHypergeometricFirstCoefficient,
            ordinaryHypergeometricSecondCoefficient] at hrec ⊢
          linear_combination hrec

/-- Inside its convergence disk, the ordinary hypergeometric sum satisfies the analytic Gauss
differential equation, expressed through its exact first and second derivative-series values. -/
theorem ordinaryHypergeometric_standardGaussODE
    (a b c z : ℂ) (hc : ∀ j : ℕ, (j : ℂ) ≠ -c)
    (hz : ‖z‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius) :
    z * (1 - z) * ordinaryHypergeometricSecondDerivativeSeriesValue a b c z +
        (c - (a + b + 1) * z) *
          ordinaryHypergeometricFirstDerivativeSeriesValue a b c z -
      a * b * (ordinaryHypergeometricSeries ℂ a b c).sum z = 0 := by
  rcases ordinaryHypergeometric_hasSum_value_first_second a b c z hz with
    ⟨hF, hD1, hD2⟩
  change HasSum
    (fun j => ordinaryHypergeometricFormalCoefficient a b c j * z ^ j)
    ((ordinaryHypergeometricSeries ℂ a b c).sum z) at hF
  change HasSum
    (fun j => ordinaryHypergeometricFirstCoefficient a b c j * z ^ j)
    (ordinaryHypergeometricFirstDerivativeSeriesValue a b c z) at hD1
  change HasSum
    (fun j => ordinaryHypergeometricSecondCoefficient a b c j * z ^ j)
    (ordinaryHypergeometricSecondDerivativeSeriesValue a b c z) at hD2
  have hzD2 := HasSum.shiftOneCoefficient_mul_pow hD2
  have hz2D2 := HasSum.shiftTwoCoefficient_mul_pow hD2
  have hzD1 := HasSum.shiftOneCoefficient_mul_pow hD1
  have hres0 :=
    (((hzD2.sub hz2D2).add (hD1.mul_left c)).sub
      (hzD1.mul_left (a + b + 1))).sub (hF.mul_left (a * b))
  have hterm :
      (fun j =>
        shiftOneCoefficient (ordinaryHypergeometricSecondCoefficient a b c) j * z ^ j -
              shiftOneCoefficient
                (shiftOneCoefficient
                  (ordinaryHypergeometricSecondCoefficient a b c)) j * z ^ j +
            c * (ordinaryHypergeometricFirstCoefficient a b c j * z ^ j) -
          (a + b + 1) *
            (shiftOneCoefficient
              (ordinaryHypergeometricFirstCoefficient a b c) j * z ^ j) -
        a * b * (ordinaryHypergeometricFormalCoefficient a b c j * z ^ j)) =
        fun _ : ℕ => (0 : ℂ) := by
    funext j
    calc
      _ =
          (shiftOneCoefficient (ordinaryHypergeometricSecondCoefficient a b c) j -
              shiftOneCoefficient
                (shiftOneCoefficient
                  (ordinaryHypergeometricSecondCoefficient a b c)) j +
            c * ordinaryHypergeometricFirstCoefficient a b c j -
            (a + b + 1) *
              shiftOneCoefficient
                (ordinaryHypergeometricFirstCoefficient a b c) j -
            a * b * ordinaryHypergeometricFormalCoefficient a b c j) * z ^ j := by ring
      _ = 0 := by
        rw [ordinaryHypergeometricStandardGaussCoefficient_eq_zero a b c hc j]
        simp
  rw [hterm] at hres0
  have heq := hres0.unique (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  linear_combination heq

/-- The BM complementary hypergeometric factor satisfies its transformed Gauss equation
throughout the open unit disk. -/
theorem d4BMPlusPlusComplementaryHypergeometric_standardGaussODE
    (n : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) * d4BMPlusPlusComplementaryHypergeometricSecondDerivative n chi z +
        (d4BMPlusPlusComplementaryHypergeometricC n chi -
          (d4BMPlusPlusComplementaryHypergeometricA n chi +
            d4BMPlusPlusComplementaryHypergeometricB n chi + 1) * z) *
          d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi z -
      d4BMPlusPlusComplementaryHypergeometricA n chi *
        d4BMPlusPlusComplementaryHypergeometricB n chi *
          d4BMPlusPlusComplementaryHypergeometricFactor n chi z = 0 := by
  let a := d4BMPlusPlusComplementaryHypergeometricA n chi
  let b := d4BMPlusPlusComplementaryHypergeometricB n chi
  let c := d4BMPlusPlusComplementaryHypergeometricC n chi
  have hc : ∀ j : ℕ, (j : ℂ) ≠ -c := by
    intro j
    exact (d4BMPlusPlusComplementaryHypergeometricParameters_ne_negNat
      n chi hchi j).2.2
  have hzr : ‖z‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius := by
    change ‖z‖ₑ < (d4BMPlusPlusComplementaryHypergeometricSeries n chi).radius
    rw [d4BMPlusPlusComplementaryHypergeometricSeries_radius_eq_one n chi hchi]
    exact hz
  have hode := ordinaryHypergeometric_standardGaussODE a b c z hc hzr
  simpa only [a, b, c,
    ordinaryHypergeometricFirstDerivativeSeriesValue,
    ordinaryHypergeometricSecondDerivativeSeriesValue,
    d4BMPlusPlusComplementaryHypergeometricFirstDerivative,
    d4BMPlusPlusComplementaryHypergeometricSecondDerivative,
    d4BMPlusPlusComplementaryHypergeometricSeries,
    d4BMPlusPlusComplementaryHypergeometricFactor,
    ordinaryHypergeometric] using hode

/-- Actual-derivative form of the BM complementary Gauss ODE. -/
theorem d4BMPlusPlusComplementaryHypergeometric_deriv_standardGaussODE
    (n : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) *
          deriv (d4BMPlusPlusComplementaryHypergeometricFirstDerivative n chi) z +
        (d4BMPlusPlusComplementaryHypergeometricC n chi -
          (d4BMPlusPlusComplementaryHypergeometricA n chi +
            d4BMPlusPlusComplementaryHypergeometricB n chi + 1) * z) *
          deriv (d4BMPlusPlusComplementaryHypergeometricFactor n chi) z -
      d4BMPlusPlusComplementaryHypergeometricA n chi *
        d4BMPlusPlusComplementaryHypergeometricB n chi *
          d4BMPlusPlusComplementaryHypergeometricFactor n chi z = 0 := by
  rw [(hasDerivAt_d4BMPlusPlusComplementaryHypergeometricFactor
      n chi z hchi hz).deriv,
    (hasDerivAt_d4BMPlusPlusComplementaryHypergeometricFirstDerivative
      n chi z hchi hz).deriv]
  exact d4BMPlusPlusComplementaryHypergeometric_standardGaussODE n chi z hchi hz

/-- Every Xi fibre satisfies the actual-derivative complementary Gauss ODE on the open unit disk. -/
theorem d4BMXiPlusPlusComplementaryHypergeometric_deriv_standardGaussODE
    (n : ℕ) (q : XiZeroCopy) (z : ℂ) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) *
          deriv
            (d4BMPlusPlusComplementaryHypergeometricFirstDerivative n
              (d4BMXiMixedHorizonAngularMomentum q)) z +
        (d4BMPlusPlusComplementaryHypergeometricC n
            (d4BMXiMixedHorizonAngularMomentum q) -
          (d4BMPlusPlusComplementaryHypergeometricA n
              (d4BMXiMixedHorizonAngularMomentum q) +
            d4BMPlusPlusComplementaryHypergeometricB n
              (d4BMXiMixedHorizonAngularMomentum q) + 1) * z) *
          deriv
            (d4BMPlusPlusComplementaryHypergeometricFactor n
              (d4BMXiMixedHorizonAngularMomentum q)) z -
      d4BMPlusPlusComplementaryHypergeometricA n
          (d4BMXiMixedHorizonAngularMomentum q) *
        d4BMPlusPlusComplementaryHypergeometricB n
          (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMPlusPlusComplementaryHypergeometricFactor n
            (d4BMXiMixedHorizonAngularMomentum q) z = 0 := by
  exact d4BMPlusPlusComplementaryHypergeometric_deriv_standardGaussODE
    n _ z (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz

end

end RHTower
