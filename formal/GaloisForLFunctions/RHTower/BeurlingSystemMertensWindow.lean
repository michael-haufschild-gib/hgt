import GaloisForLFunctions.RHTower.BeurlingSystemPrimeSumAsymptotic

/-!
# The generalized Mertens window law

If a discrete Beurling system satisfies the prime number theorem, then for every `u > 1`

```text
∑_{X^(1/u) < |p| ≤ X} |p|⁻¹ → log u.
```

Abel summation turns the sum into `π_P(X)/X - π_P(Y)/Y + ∫_Y^X π_P(t)/t² dt`.  The two boundary
terms vanish because `π_P(t)/t → 0`, and substituting `π_P(t) = (t/log t)(1 + E(t))` leaves the
exact iterated logarithm `log log X - log log Y = log u` plus an `E`-weighted remainder which is
bounded by the same iterated logarithm times a vanishing factor.
-/

open Filter Topology Set MeasureTheory intervalIntegral

namespace RHTower

namespace BeurlingSystem

variable {B : BeurlingSystem}

/-! ## The iterated logarithm kernel -/

theorem hasDerivAt_logLog {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => Real.log (Real.log s)) (t⁻¹ / Real.log t) t := by
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; linarith
  exact (Real.hasDerivAt_log ht0).log (ne_of_gt (Real.log_pos ht))

theorem continuousAt_invDivLog {t : ℝ} (ht : 1 < t) :
    ContinuousAt (fun s : ℝ => s⁻¹ / Real.log s) t := by
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; linarith
  exact (continuousAt_inv₀ ht0).div (Real.continuousAt_log ht0) (ne_of_gt (Real.log_pos ht))

theorem intervalIntegrable_invDivLog {Y X : ℝ} (hY : 1 < Y) (hYX : Y ≤ X) :
    IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) volume Y X := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hYX]
  exact fun t ht => (continuousAt_invDivLog (lt_of_lt_of_le hY ht.1)).continuousWithinAt

theorem integral_invDivLog {Y X : ℝ} (hY : 1 < Y) (hYX : Y ≤ X) :
    (∫ t in Y..X, t⁻¹ / Real.log t) = Real.log (Real.log X) - Real.log (Real.log Y) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_logLog (by
      rw [uIcc_of_le hYX] at ht
      exact lt_of_lt_of_le hY ht.1))
    (intervalIntegrable_invDivLog hY hYX)

theorem invDivLog_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ t⁻¹ / Real.log t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos ht
  positivity

/-! ## The window identity -/

theorem tendsto_primeCount_div (hpnt : B.HasPrimePNT) :
    Tendsto (fun t : ℝ => (B.primeCount t : ℝ) / t) atTop (nhds 0) := by
  have h := hpnt.div_atTop Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : t ≠ 0 := by intro h'; rw [h'] at ht; linarith
  have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  field_simp

theorem intervalIntegrable_pntError_invDivLog (hdisc : B.IsDiscrete) {Y X : ℝ} (hY : 2 ≤ Y)
    (hYX : Y ≤ X) :
    IntervalIntegrable (fun t : ℝ => B.pntError t * (t⁻¹ / Real.log t)) volume Y X := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hYX]
  refine (((integrableOn_pntError hdisc X).mono_set
    (Icc_subset_Icc hY le_rfl)).mul_continuousOn ?_ isCompact_Icc).mono_set Ioc_subset_Icc_self
  intro t ht
  exact (continuousAt_invDivLog (by have := ht.1; linarith)).continuousWithinAt

/-- Abel summation for the reciprocal weight on a window. -/
theorem primeInvWindowSum_eq (hdisc : B.IsDiscrete) {Y X : ℝ} (hY : 2 ≤ Y) (hYX : Y ≤ X) :
    ∑ p ∈ (finite_primeWindow hdisc Y X).toFinset, (B.labelNorm p)⁻¹
      = (B.primeCount X : ℝ) / X - (B.primeCount Y : ℝ) / Y
        + (Real.log (Real.log X) - Real.log (Real.log Y))
        + ∫ t in Y..X, B.pntError t * (t⁻¹ / Real.log t) := by
  have hY1 : (1 : ℝ) < Y := by linarith
  have hderiv : ∀ t ∈ Icc Y X, HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := by
    intro t ht
    have ht0 : t ≠ 0 := by
      have h2 : Y ≤ t := ht.1
      intro h
      rw [h] at h2
      linarith
    exact hasDerivAt_inv ht0
  have hint : IntervalIntegrable (fun t : ℝ => -(t ^ 2)⁻¹) volume Y X := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hYX]
    intro t ht
    have ht0 : t ≠ 0 := by
      have h2 : Y ≤ t := ht.1
      intro h
      rw [h] at h2
      linarith
    exact (((continuous_pow 2).continuousAt.inv₀ (pow_ne_zero 2 ht0)).neg).continuousWithinAt
  have habel := sum_primeWindow_eq_sub_sub_integral hdisc hYX hderiv hint
  have hpt : ∀ t ∈ uIcc Y X, (-(t ^ 2)⁻¹) * (B.primeCount t : ℝ)
      = -(t⁻¹ / Real.log t) - B.pntError t * (t⁻¹ / Real.log t) := by
    intro t ht
    rw [uIcc_of_le hYX] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY1 ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    rw [primeCount_eq_mul B ht1]
    field_simp
    ring
  have hI1 : IntervalIntegrable (fun t : ℝ => -(t⁻¹ / Real.log t)) volume Y X :=
    (intervalIntegrable_invDivLog hY1 hYX).neg
  have hI2 : IntervalIntegrable (fun t : ℝ => B.pntError t * (t⁻¹ / Real.log t)) volume Y X :=
    intervalIntegrable_pntError_invDivLog hdisc hY hYX
  have hsplit : (∫ t in Y..X, (-(t ^ 2)⁻¹) * (B.primeCount t : ℝ))
      = -(Real.log (Real.log X) - Real.log (Real.log Y))
        - ∫ t in Y..X, B.pntError t * (t⁻¹ / Real.log t) := by
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub hI1 hI2,
      intervalIntegral.integral_neg, integral_invDivLog hY1 hYX]
  rw [habel, hsplit]
  simp only [inv_eq_one_div]
  ring

/-! ## The limit -/

theorem log_log_rpow_sub {u X : ℝ} (hu : 1 < u) (hX : 1 < X) :
    Real.log (Real.log X) - Real.log (Real.log (X ^ (1 / u))) = Real.log u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hinv : (0 : ℝ) < 1 / u := div_pos one_pos hu0
  rw [Real.log_rpow (by linarith : (0 : ℝ) < X), Real.log_mul (ne_of_gt hinv) (ne_of_gt hlogX),
    Real.log_div one_ne_zero (ne_of_gt hu0), Real.log_one]
  ring

/-- **The generalized Mertens window law.**  Under the prime number theorem the reciprocal sum over
`(X^(1/u), X]` converges to `log u`. -/
theorem tendsto_primeInvWindowSum (hdisc : B.IsDiscrete) (hpnt : B.HasPrimePNT) {u : ℝ}
    (hu : 1 < u) :
    Tendsto (fun X : ℝ => ∑ p ∈ (finite_primeWindow hdisc (X ^ (1 / u)) X).toFinset,
      (B.labelNorm p)⁻¹) atTop (nhds (Real.log u)) := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos hu
  have hinv : (0 : ℝ) < 1 / u := div_pos one_pos hu0
  have hrpow : Tendsto (fun X : ℝ => X ^ (1 / u)) atTop atTop := tendsto_rpow_atTop hinv
  have hYleX : ∀ X : ℝ, 1 ≤ X → X ^ (1 / u) ≤ X := by
    intro X hX
    nth_rewrite 2 [← Real.rpow_one X]
    exact Real.rpow_le_rpow_of_exponent_le hX (by rw [div_le_one hu0]; linarith)
  have hA : Tendsto (fun X : ℝ => (B.primeCount X : ℝ) / X) atTop (nhds 0) :=
    tendsto_primeCount_div hpnt
  have hB : Tendsto
      (fun X : ℝ => (B.primeCount (X ^ (1 / u)) : ℝ) / X ^ (1 / u)) atTop (nhds 0) :=
    (tendsto_primeCount_div hpnt).comp hrpow
  -- the error-weighted remainder
  have hD : Tendsto (fun X : ℝ =>
      ∫ t in (X ^ (1 / u))..X, B.pntError t * (t⁻¹ / Real.log t)) atTop (nhds 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hden : (0 : ℝ) < Real.log u + 1 := by linarith
    set δ : ℝ := ε / (Real.log u + 1) with hδ
    have hδ0 : 0 < δ := div_pos hε hden
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
      (NormedAddGroup.tendsto_nhds_zero.mp (tendsto_pntError hpnt) δ hδ0)
    filter_upwards [eventually_gt_atTop (1 : ℝ), hrpow.eventually_ge_atTop (max T₀ 2)]
      with X hX1 hXY
    have hY2 : (2 : ℝ) ≤ X ^ (1 / u) := le_trans (le_max_right _ _) hXY
    have hYT : T₀ ≤ X ^ (1 / u) := le_trans (le_max_left _ _) hXY
    have hYX : X ^ (1 / u) ≤ X := hYleX X hX1.le
    have hY1 : (1 : ℝ) < X ^ (1 / u) := by linarith
    have hEbd : ∀ t ∈ Icc (X ^ (1 / u)) X,
        |B.pntError t * (t⁻¹ / Real.log t)| ≤ δ * (t⁻¹ / Real.log t) := by
      intro t ht
      have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hY1 ht.1
      have hker : 0 ≤ t⁻¹ / Real.log t := invDivLog_nonneg ht1
      have hE : |B.pntError t| ≤ δ := by
        have h := hT₀ t (le_trans hYT ht.1)
        rw [Real.norm_eq_abs] at h
        exact h.le
      rw [abs_mul, abs_of_nonneg hker]
      exact mul_le_mul_of_nonneg_right hE hker
    have hint1 : IntervalIntegrable (fun t : ℝ => B.pntError t * (t⁻¹ / Real.log t)) volume
        (X ^ (1 / u)) X := intervalIntegrable_pntError_invDivLog hdisc hY2 hYX
    have hint2 : IntervalIntegrable (fun t : ℝ => δ * (t⁻¹ / Real.log t)) volume
        (X ^ (1 / u)) X := (intervalIntegrable_invDivLog hY1 hYX).const_mul _
    have hup : (∫ t in (X ^ (1 / u))..X, B.pntError t * (t⁻¹ / Real.log t))
        ≤ ∫ t in (X ^ (1 / u))..X, δ * (t⁻¹ / Real.log t) :=
      intervalIntegral.integral_mono_on hYX hint1 hint2 fun t ht =>
        le_trans (le_abs_self _) (hEbd t ht)
    have hlow : (∫ t in (X ^ (1 / u))..X, -(δ * (t⁻¹ / Real.log t)))
        ≤ ∫ t in (X ^ (1 / u))..X, B.pntError t * (t⁻¹ / Real.log t) :=
      intervalIntegral.integral_mono_on hYX hint2.neg hint1 fun t ht =>
        neg_le_of_abs_le (hEbd t ht)
    rw [intervalIntegral.integral_neg] at hlow
    have hval : (∫ t in (X ^ (1 / u))..X, δ * (t⁻¹ / Real.log t)) = δ * Real.log u := by
      rw [intervalIntegral.integral_const_mul, integral_invDivLog hY1 hYX,
        log_log_rpow_sub hu hX1]
    rw [hval] at hup hlow
    have habs : |∫ t in (X ^ (1 / u))..X, B.pntError t * (t⁻¹ / Real.log t)|
        ≤ δ * Real.log u := abs_le.mpr ⟨hlow, hup⟩
    have hfin : δ * Real.log u < ε := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [hlogu, hε]
    rw [Real.norm_eq_abs]
    exact lt_of_le_of_lt habs hfin
  have hlim : Tendsto (fun X : ℝ =>
      (B.primeCount X : ℝ) / X - (B.primeCount (X ^ (1 / u)) : ℝ) / X ^ (1 / u)
        + Real.log u + ∫ t in (X ^ (1 / u))..X, B.pntError t * (t⁻¹ / Real.log t)) atTop
      (nhds (0 - 0 + Real.log u + 0)) :=
    ((hA.sub hB).add tendsto_const_nhds).add hD
  rw [show (0 : ℝ) - 0 + Real.log u + 0 = Real.log u by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hrpow.eventually_ge_atTop (2 : ℝ)]
    with X hX1 hY2
  have hYX : X ^ (1 / u) ≤ X := hYleX X hX1.le
  rw [primeInvWindowSum_eq hdisc hY2 hYX, log_log_rpow_sub hu hX1]

end BeurlingSystem

end RHTower
