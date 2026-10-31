import GaloisForLFunctions.RHTower.Heat.TheLocalHeatThreshold
import GaloisForLFunctions.RHTower.SpeiserShadowExponentialDensity

/-!
# The local heat threshold has Selberg's exponential tail

Let `λ_t` be the local heat threshold (`localHeatThreshold`) and `L = log U`.

**Theorem** (`exists_volume_localHeatThreshold_gt_le_exp`).  There are `A, K ≥ 0` such that for all
large `U` there are heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` with, for every
`2 ≤ κ ≤ L/2 − 2`,

  `|{t ∈ [T₁ + ½, T₂ − ½] : λ_t > κ²/(3L²)}| ≤ A (T₂ − T₁) e^{−κ/2400} + K L²`.

So `λ_t log² t` has an exponential tail in `√·` on average: `λ_t ≍ 1/log² t` at typical heights, and
the heights with `λ_t > κ/log U` have measure `≪ U exp(−√(3κ log U)/2400) + log² U`
(`eventually_volume_localHeatThreshold_gt_le_exp`), a rate for the density statement
`eventually_volume_localHeatThreshold_gt_le`.

**Proof.**  If `λ_t > κ²/(3L²)`, the cone-defect bound (`localHeatThreshold_le_of_cone`) gives a zero
`ρ` with `(Re ρ − ½)² > (Im ρ − t)² + κ²/L²`: depth `> κ/L` and `|t − Im ρ| < |Re ρ − ½|`.  So `t` lies in
the `κ`-shadow of the zeros of depth `≥ κ/L`, whose measure is the Selberg tail bound
`exists_speiserShadow_exponential_density`.
-/

open Complex Set MeasureTheory Filter

namespace RHTower.DeBruijn

/-- Above heat `κ²/(3L²)` the height lies in the `κ`-shadow: some zero has depth `≥ κ/L` and lies
within its depth of `t`. -/
theorem exists_shadow_of_lt_localHeatThreshold {t κ L : ℝ} (hκ : 0 ≤ κ) (hL : 0 < L)
    (h : κ ^ 2 / (3 * L ^ 2) < localHeatThreshold t) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ κ / L ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2| := by
  by_contra hne
  have hcone : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ^ 2
      ≤ ((xiSpectralPoint q).re - t) ^ 2 + 3 * (κ ^ 2 / (3 * L ^ 2)) := by
    intro q
    by_contra hq
    push Not at hq
    have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
    have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
    rw [hre, him, neg_sq, show 3 * (κ ^ 2 / (3 * L ^ 2)) = (κ / L) ^ 2 by field_simp] at hq
    refine hne ⟨q.1, xi_eq_zero_of_mem_divisor_support q.1, ?_, ?_⟩
    · have h1 : (κ / L) ^ 2 < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by nlinarith [sq_nonneg ((q.1 : ℂ).im - t)]
      have := sq_lt_sq.mp h1
      rw [abs_of_nonneg (div_nonneg hκ hL.le)] at this
      exact this.le
    · have h1 : (t - (q.1 : ℂ).im) ^ 2 < ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
        nlinarith [sq_nonneg (κ / L)]
      exact (sq_lt_sq.mp h1).le
  have := localHeatThreshold_le_of_cone (by positivity) hcone
  linarith

/-- **The exponential tail of the local heat threshold.**  For all large `U`, at admissible heights
`T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)`, every `2 ≤ κ ≤ L/2 − 2` gives
`|{t ∈ [T₁ + ½, T₂ − ½] : λ_t > κ²/(3L²)}| ≤ A (T₂ − T₁) e^{−κ/2400} + K L²`. -/
theorem exists_volume_localHeatThreshold_gt_le_exp :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ κ : ℝ, 2 ≤ κ → κ ≤ Real.log U / 2 - 2 →
          volume {t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) |
              κ ^ 2 / (3 * Real.log U ^ 2) < localHeatThreshold t} ≤
            ENNReal.ofReal (A * (T₂ - T₁) * Real.exp (-(κ / 2400)) + K * Real.log U ^ 2) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_speiserShadow_exponential_density
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hev, Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)] with U hU hL4
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun κ hκ hκL => (measure_mono ?_).trans (hbound κ hκ hκL)⟩
  rintro t ⟨ht, hlt⟩
  exact ⟨ht, exists_shadow_of_lt_localHeatThreshold (by linarith) (by linarith) hlt⟩

/-- **A rate for the vanishing heat rate.**  For every `κ > 0`, for all large `U`,
`|{t ∈ [U/4 + 2, U/2 − 2] : λ_t > κ/log U}| ≤ A U exp(−√(3κ log U)/2400) + K log² U`. -/
theorem eventually_volume_localHeatThreshold_gt_le_exp :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ ∀ κ : ℝ, 0 < κ → ∀ᶠ U in atTop,
      volume {t ∈ Icc (U / 4 + 2) (U / 2 - 2) | κ / Real.log U < localHeatThreshold t} ≤
        ENNReal.ofReal (A * U * Real.exp (-(Real.sqrt (3 * κ * Real.log U) / 2400))
          + K * Real.log U ^ 2) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_volume_localHeatThreshold_gt_le_exp
  refine ⟨A / 4, K, by positivity, hK, fun κ hκ => ?_⟩
  -- `√(3κL)` lies in `[2, L/2 − 2]` once `L` is large
  have hlow : ∀ᶠ U : ℝ in atTop, 4 / (3 * κ) ≤ Real.log U :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have hhigh : ∀ᶠ U : ℝ in atTop, 2 ≤ Real.log U / 2 - 2 - Real.sqrt (3 * κ * Real.log U) := by
    have h : Tendsto (fun L : ℝ => L / 2 - 2 - Real.sqrt (3 * κ * L)) atTop atTop := by
      have hsq : ∀ L : ℝ, 0 ≤ L → Real.sqrt (3 * κ * L) ≤ L / 4 + 12 * κ := by
        intro L hL
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [sq_nonneg (L / 4 - 6 * κ)]
      refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-(2 + 12 * κ))
        (tendsto_id.atTop_mul_const' (show (0 : ℝ) < 1 / 4 by norm_num)))
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
      have := hsq L hL
      simp only [id]
      linarith
    exact Real.tendsto_log_atTop.eventually (h.eventually_ge_atTop 2)
  filter_upwards [hev, hlow, hhigh, Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ),
    eventually_ge_atTop (0 : ℝ)] with U hU hUlow hUhigh hL4 hU0
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  set L := Real.log U with hLdef
  have hL : 0 < L := by linarith
  set s := Real.sqrt (3 * κ * L) with hs
  have hs2 : 2 ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) (by positivity)]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * κ)).mp hUlow
    nlinarith
  have hsq : s ^ 2 / (3 * L ^ 2) = κ / L := by
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp
  have h := hbound s hs2 (by linarith)
  rw [hsq] at h
  refine (measure_mono ?_).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
  · rintro t ⟨ht, hlt⟩
    exact ⟨⟨by linarith [hT₁.2, ht.1], by linarith [hT₂.1, ht.2]⟩, hlt⟩
  · have hT : T₂ - T₁ ≤ U / 4 := by linarith [hT₁.1, hT₂.2]
    have he := Real.exp_pos (-(s / 2400))
    have : A * (T₂ - T₁) * Real.exp (-(s / 2400)) ≤ A / 4 * U * Real.exp (-(s / 2400)) := by
      have := mul_le_mul_of_nonneg_left hT hA
      nlinarith
    linarith

end RHTower.DeBruijn

#print axioms RHTower.DeBruijn.exists_volume_localHeatThreshold_gt_le_exp
#print axioms RHTower.DeBruijn.eventually_volume_localHeatThreshold_gt_le_exp
