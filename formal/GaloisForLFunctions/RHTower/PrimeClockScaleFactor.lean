import GaloisForLFunctions.RHTower.PrimeClockShaleDiagonal

/-!
# The prime-clock scale-factor wall

The clock tangent of the formal prime coherent displacement `p ^ (-sigma - I*t)` has squared
one-particle norm

`sum_p (log p)^2 * p^(-2*sigma)`.

This file proves that the series is summable exactly for `sigma > 1/2`.  Consequently both
functional-equation-reflected clock perspectives have singular metric exactly at `sigma = 1/2`,
and RH is equivalent to that perspective-neutral external-clock condition at every `xi` zero.
-/

noncomputable section

namespace RHTower

/-- The per-prime contribution to the coherent-state clock metric (equivalently, the finite-cutoff
clock-generator variance). -/
def primeClockScaleMetric (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-2 * sigma)

private theorem scaled_primeHarmonic_le_scaleMetric
    {sigma : ℝ} (hsigma : sigma ≤ 1 / 2) (p : Nat.Primes) :
    (Real.log 2) ^ 2 * (1 / (p : ℝ)) ≤ primeClockScaleMetric sigma p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := one_le_two.trans hp2
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hlogsq : (Real.log 2) ^ 2 ≤ (Real.log (p : ℝ)) ^ 2 := by
    exact (sq_le_sq₀ hlog2 hlogp).2
      (Real.strictMonoOn_log.monotoneOn (by norm_num)
        (by change 0 < (p : ℝ); exact_mod_cast p.prop.pos) hp2)
  have hrpow : (1 / (p : ℝ)) ≤ (p : ℝ) ^ (-2 * sigma) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  unfold primeClockScaleMetric
  exact mul_le_mul hlogsq hrpow (by positivity) (sq_nonneg _)

/-- At or left of the critical line, the coherent prime-clock scale factor is infinite. -/
theorem not_summable_primeClockScaleMetric_of_le_half
    {sigma : ℝ} (hsigma : sigma ≤ 1 / 2) :
    ¬ Summable (primeClockScaleMetric sigma) := by
  intro hsum
  have hscaled : Summable (fun p : Nat.Primes => (Real.log 2) ^ 2 * (1 / (p : ℝ))) := by
    apply Summable.of_nonneg_of_le
    · intro p
      positivity
    · intro p
      exact scaled_primeHarmonic_le_scaleMetric hsigma p
    · exact hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff (pow_ne_zero 2 (Real.log_pos one_lt_two).ne')).mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

private theorem scaleMetric_le_rpow_majorant
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (p : Nat.Primes) :
    primeClockScaleMetric sigma p ≤
      (((2 * sigma - 1) / 4)⁻¹) ^ 2 * (p : ℝ) ^ (-(sigma + 1 / 2)) := by
  let eps : ℝ := (2 * sigma - 1) / 4
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hlog := Real.log_le_rpow_div hp0 heps
  have hlogsq : (Real.log (p : ℝ)) ^ 2 ≤ ((p : ℝ) ^ eps / eps) ^ 2 := by
    have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
      exact_mod_cast p.prop.one_lt.le)
    have hright : 0 ≤ (p : ℝ) ^ eps / eps := div_nonneg (by positivity) heps.le
    exact (sq_le_sq₀ hlog0 hright).2 hlog
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  unfold primeClockScaleMetric
  calc
    (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-2 * sigma)
        ≤ ((p : ℝ) ^ eps / eps) ^ 2 * (p : ℝ) ^ (-2 * sigma) := by
          gcongr
    _ = (((2 * sigma - 1) / 4)⁻¹) ^ 2 *
        (p : ℝ) ^ (-(sigma + 1 / 2)) := by
      calc
        ((p : ℝ) ^ eps / eps) ^ 2 * (p : ℝ) ^ (-2 * sigma)
            = eps⁻¹ ^ 2 * (((p : ℝ) ^ eps) ^ 2 *
                (p : ℝ) ^ (-2 * sigma)) := by field_simp
        _ = eps⁻¹ ^ 2 * ((p : ℝ) ^ (eps * 2) *
                (p : ℝ) ^ (-2 * sigma)) := by
              rw [← Real.rpow_mul_natCast hp0]
              norm_num
        _ = eps⁻¹ ^ 2 * (p : ℝ) ^ (eps * 2 + (-2 * sigma)) := by
              rw [← Real.rpow_add hp_pos]
        _ = (((2 * sigma - 1) / 4)⁻¹) ^ 2 *
                (p : ℝ) ^ (-(sigma + 1 / 2)) := by
              dsimp [eps]
              congr 1
              ring

/-- Right of the critical line, the coherent prime-clock scale factor is finite. -/
theorem summable_primeClockScaleMetric_of_half_lt
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Summable (primeClockScaleMetric sigma) := by
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(sigma + 1 / 2))) :=
    (Nat.Primes.summable_rpow).2 (by linarith)
  have hmajor : Summable (fun p : Nat.Primes =>
      (((2 * sigma - 1) / 4)⁻¹) ^ 2 * (p : ℝ) ^ (-(sigma + 1 / 2))) :=
    hpow.mul_left _
  apply Summable.of_nonneg_of_le
  · intro p
    unfold primeClockScaleMetric
    positivity
  · intro p
    exact scaleMetric_le_rpow_majorant hsigma p
  · exact hmajor

/-- The prime coherent-state clock metric is finite exactly to the right of the critical line. -/
theorem summable_primeClockScaleMetric_iff (sigma : ℝ) :
    Summable (primeClockScaleMetric sigma) ↔ 1 / 2 < sigma := by
  constructor
  · intro h
    exact lt_of_not_ge (fun hs => not_summable_primeClockScaleMetric_of_le_half hs h)
  · exact summable_primeClockScaleMetric_of_half_lt

/-- Both functional-equation-reflected prime-clock perspectives have singular clock metric. -/
def PerspectiveNeutralExternalClock (sigma : ℝ) : Prop :=
  ¬ Summable (primeClockScaleMetric sigma) ∧
    ¬ Summable (primeClockScaleMetric (1 - sigma))

/-- The critical line is the unique locus where both reflected clock metrics are singular. -/
theorem perspectiveNeutralExternalClock_iff (sigma : ℝ) :
    PerspectiveNeutralExternalClock sigma ↔ sigma = 1 / 2 := by
  constructor
  · rintro ⟨hs, hreflect⟩
    have hsle : sigma ≤ 1 / 2 := by
      by_contra hnot
      exact hs ((summable_primeClockScaleMetric_iff sigma).2 (lt_of_not_ge hnot))
    have hreflectle : 1 - sigma ≤ 1 / 2 := by
      by_contra hnot
      exact hreflect ((summable_primeClockScaleMetric_iff (1 - sigma)).2
        (lt_of_not_ge hnot))
    linarith
  · rintro rfl
    constructor
    · exact not_summable_primeClockScaleMetric_of_le_half le_rfl
    · norm_num
      exact not_summable_primeClockScaleMetric_of_le_half (sigma := 1 / 2) le_rfl

/-- RH says exactly that every `xi` zero forces an external clock in both reflected perspectives. -/
theorem riemannHypothesis_iff_xiZero_perspectiveNeutralExternalClock :
    RiemannHypothesis ↔
      ∀ rho : ℂ, xi rho = 0 → PerspectiveNeutralExternalClock rho.re := by
  constructor
  · intro hRH rho hzero
    apply (perspectiveNeutralExternalClock_iff rho.re).2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hreflected : (1 : ℂ) - rho ∈ rightHalf := by
        rw [mem_rightHalf]
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      exact (rh_iff_xi_ne_zero_right.mp hRH _ hreflected)
        (by rw [xi_one_sub]; exact hzero)
    · exact (rh_iff_xi_ne_zero_right.mp hRH rho (mem_rightHalf.mpr hgt)) hzero
  · intro hclock
    apply rh_iff_xi_ne_zero_right.mpr
    intro rho hrho hzero
    have hline := (perspectiveNeutralExternalClock_iff rho.re).1 (hclock rho hzero)
    exact (ne_of_gt (mem_rightHalf.mp hrho)) hline

end RHTower
