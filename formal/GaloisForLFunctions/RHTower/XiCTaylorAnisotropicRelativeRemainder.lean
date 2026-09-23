import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteCoefficientGate

/-!
# Relative negligibility on the anisotropic Taylor mesh

The anisotropic mesh approaches every target transversely by at least `1/(n+1)`.  Analytic
peeling therefore gives a polynomial lower bound for Xi even when the target is a zero of
arbitrary multiplicity.  Superaccurate Taylor approximation transfers that lower bound to the
scheduled Taylor polynomial.  Consequently every scalar remainder which beats twice the local
order is negligible relative to `n` times the squared Taylor value, without a zero-free
hypothesis.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Any scalar remainder which, after multiplication by twice the local Xi-order power, tends to
zero is negligible relative to the anisotropic scaled squared scheduled Taylor value. -/
theorem eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) (E : ℕ → ℝ)
    (hE : Tendsto (fun n : ℕ =>
      E n * (((n + 1 : ℕ) : ℝ) ^
        (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      E n < (epsilon * ((n + 1 : ℕ) : ℝ)) *
        Complex.normSq
          ((xiCTaylorPolynomial
            (xiCTaylorOddDegreeSchedule D
              (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  obtain ⟨c, hc, hvalueLower⟩ := eventually_xiC_anisotropic_value_lower sigma
  have htolM := tendsto_xiCTaylorScheduleTolerance_stage_mul_pow sigma m
  have hsmallValue : ∀ᶠ n : ℕ in atTop,
      xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) *
          (((n + 1 : ℕ) : ℝ) ^ m) < c / 2 :=
    htolM.eventually (eventually_lt_nhds (half_pos hc))
  have hsmallE : ∀ᶠ n : ℕ in atTop,
      E n * (((n + 1 : ℕ) : ℝ) ^ (2 * m)) < epsilon * c ^ (2 : ℕ) / 4 := by
    have htarget : 0 < epsilon * c ^ (2 : ℕ) / 4 := by positivity
    simpa only [m] using hE.eventually (eventually_lt_nhds htarget)
  filter_upwards [hvalueLower, hsmallValue, hsmallE]
      with n hnLower hnSmall hnE
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let k : ℕ := xiCTaylorAnisotropicScheduleStage sigma n
  let P : Polynomial ℂ := xiCTaylorPolynomial (xiCTaylorOddDegreeSchedule D k)
  let tol : ℝ := xiCTaylorScheduleTolerance k
  let q : ℝ := ((n + 1 : ℕ) : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqOne : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hqpow : 0 < q ^ m := pow_pos hq _
  have happ := xiCTaylorSuperaccurateSchedule_at_anisotropicCenteredPoint hD.1 sigma n
  have hvalueErr : ‖P.eval z - XiC z‖ < tol := by
    simpa only [P, z, k, xiCTaylorPolynomial_eval, dist_eq_norm, norm_sub_rev] using happ.1
  have hXiTriangle : ‖XiC z‖ ≤ ‖P.eval z‖ + ‖P.eval z - XiC z‖ := by
    calc
      ‖XiC z‖ = ‖P.eval z - (P.eval z - XiC z)‖ := by congr 1; ring
      _ ≤ ‖P.eval z‖ + ‖P.eval z - XiC z‖ := norm_sub_le _ _
  have hnLower' : c / q ^ m ≤ ‖XiC z‖ := by
    simpa only [z, q, m, one_div_pow, mul_one_div] using hnLower
  have hnSmall' : tol * q ^ m < c / 2 := by
    simpa only [tol, q, k, m] using hnSmall
  have hPValueLowerMul : c / 2 < ‖P.eval z‖ * q ^ m := by
    have htriMul : ‖XiC z‖ * q ^ m ≤
        (‖P.eval z‖ + ‖P.eval z - XiC z‖) * q ^ m :=
      mul_le_mul_of_nonneg_right hXiTriangle (pow_nonneg hq.le m)
    have hlowerMul : c ≤ ‖XiC z‖ * q ^ m :=
      (div_le_iff₀ hqpow).mp hnLower'
    have herrMul : ‖P.eval z - XiC z‖ * q ^ m < c / 2 :=
      (mul_lt_mul_of_pos_right hvalueErr hqpow).trans hnSmall'
    nlinarith
  have hPValueLower : c / (2 * q ^ m) < ‖P.eval z‖ := by
    rw [div_lt_iff₀ (mul_pos (by norm_num) hqpow)]
    nlinarith
  have hnE' : E n * q ^ (2 * m) < epsilon * c ^ (2 : ℕ) / 4 := by
    simpa only [q, m] using hnE
  have hEbase : E n < (epsilon * q) * (c / (2 * q ^ m)) ^ (2 : ℕ) := by
    have hpowEq : q ^ (2 * m) = (q ^ m) ^ (2 : ℕ) := by
      rw [show 2 * m = m * 2 by omega, pow_mul]
    rw [show (epsilon * q) * (c / (2 * q ^ m)) ^ (2 : ℕ) =
        (epsilon * q * c ^ (2 : ℕ) / 4) / (q ^ m) ^ (2 : ℕ) by
          field_simp
          ring]
    rw [lt_div_iff₀ (sq_pos_of_pos hqpow)]
    rw [hpowEq] at hnE'
    have htargetMono : epsilon * c ^ (2 : ℕ) / 4 ≤ epsilon * q * c ^ (2 : ℕ) / 4 := by
      have hnonneg : 0 ≤ epsilon * c ^ (2 : ℕ) / 4 := by positivity
      calc
        epsilon * c ^ (2 : ℕ) / 4 = 1 * (epsilon * c ^ (2 : ℕ) / 4) := by ring
        _ ≤ q * (epsilon * c ^ (2 : ℕ) / 4) :=
          mul_le_mul_of_nonneg_right hqOne hnonneg
        _ = epsilon * q * c ^ (2 : ℕ) / 4 := by ring
    exact hnE'.trans_le htargetMono
  have hbaseSq : (c / (2 * q ^ m)) ^ (2 : ℕ) ≤ ‖P.eval z‖ ^ (2 : ℕ) := by
    have ha : 0 ≤ c / (2 * q ^ m) := by positivity
    have hb : 0 ≤ ‖P.eval z‖ := norm_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hPValueLower.le) (add_nonneg hb ha)]
  calc
    E n < (epsilon * q) * (c / (2 * q ^ m)) ^ (2 : ℕ) := hEbase
    _ ≤ (epsilon * q) * Complex.normSq (P.eval z) := by
      rw [Complex.normSq_eq_norm_sq]
      exact mul_le_mul_of_nonneg_left hbaseSq (mul_nonneg hepsilon.le hq.le)

end

end RHTower
