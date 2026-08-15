import GaloisForLFunctions.RHTower.RouteESaddlePntTransport

/-!
# The physical Euler saddle below the half density

For `0 < σ < 1/2` the second-order Euler deficits are no longer bounded by Mertens' first theorem,
because `p^{-2σ}` is not summable against `1/p`.  They are instead prime power sums at the
exponent `1 - 2σ`, hence of size `Y^{1-2σ}`, which is still negligible against the main term
`Y^{1-σ}` by the factor `Y^{-σ}`.  Consequently the centre and variance asymptotics

```text
Λ_{σ,Y} = (2/a) Y^a (1 + o(1)),      Var_{σ,Y} = (2/a) Y^a log Y (1 + o(1)),      a = 1 - σ,
```

hold for every fixed tilt `σ ∈ (0,1)`.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Deficit bounds at a low tilt -/

theorem eulerTiltDeficit_le_rpowLogSum (σ Y : ℝ) :
    eulerTiltDeficit σ Y ≤ primeRpowLogSumLE (1 - 2 * σ) Y := by
  rw [eulerTiltDeficit, primeRpowLogSumLE]
  refine Finset.sum_le_sum fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_lt.le
  have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
  have hu : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
  have hone : (1 : ℝ) ≤ 1 + (p : ℝ) ^ (-σ) := by linarith
  have hexp : (p : ℝ) ^ (1 - 2 * σ - 1) = (p : ℝ) ^ (-2 * σ) := by
    congr 1
    ring
  rw [hexp]
  have hnum : (0 : ℝ) ≤ (p : ℝ) ^ (-2 * σ) * Real.log p :=
    mul_nonneg (Real.rpow_nonneg hp0.le _) hlog
  calc (p : ℝ) ^ (-2 * σ) * Real.log p / (1 + (p : ℝ) ^ (-σ))
      ≤ (p : ℝ) ^ (-2 * σ) * Real.log p / 1 :=
        div_le_div_of_nonneg_left hnum (by norm_num) hone
    _ = (p : ℝ) ^ (-2 * σ) * Real.log p := by ring

theorem varianceTiltDeficit_le_rpowLogSqSum (σ Y : ℝ) :
    varianceTiltDeficit σ Y ≤ 3 * primeRpowLogSqSumLE (1 - 2 * σ) Y := by
  rw [varianceTiltDeficit, primeRpowLogSqSumLE, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hu : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hp0 _
  have hsq : (p : ℝ) ^ (-2 * σ) = (p : ℝ) ^ (-σ) * (p : ℝ) ^ (-σ) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  have hexp : (p : ℝ) ^ (1 - 2 * σ - 1) = (p : ℝ) ^ (-2 * σ) := by
    congr 1
    ring
  have hdenpos : (0 : ℝ) < (1 + (p : ℝ) ^ (-σ)) ^ 2 := by positivity
  have hlocal : (p : ℝ) ^ (-σ) * (2 * (p : ℝ) ^ (-σ) + (p : ℝ) ^ (-2 * σ))
      / (1 + (p : ℝ) ^ (-σ)) ^ 2 ≤ 3 * (p : ℝ) ^ (-2 * σ) := by
    rw [div_le_iff₀ hdenpos, hsq]
    nlinarith [hu, sq_nonneg ((p : ℝ) ^ (-σ))]
  have hval : (p : ℝ) ^ (-σ) * (2 * (p : ℝ) ^ (-σ) + (p : ℝ) ^ (-2 * σ)) * (Real.log p) ^ 2
      / (1 + (p : ℝ) ^ (-σ)) ^ 2
      = ((p : ℝ) ^ (-σ) * (2 * (p : ℝ) ^ (-σ) + (p : ℝ) ^ (-2 * σ))
          / (1 + (p : ℝ) ^ (-σ)) ^ 2) * (Real.log p) ^ 2 := by
    field_simp
  rw [hval, hexp]
  have hstep := mul_le_mul_of_nonneg_right hlocal (sq_nonneg (Real.log p))
  refine le_trans hstep (le_of_eq ?_)
  ring

/-! ## The low-tilt limits -/

theorem tendsto_rpow_neg_atTop {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun Y : ℝ => Y ^ (-σ)) atTop (nhds 0) := by
  have h : Tendsto (fun Y : ℝ => (Y ^ σ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hσ)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  rw [Real.rpow_neg hY.le]

theorem tendsto_eulerTiltDeficit_of_lt_half {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < 1 / 2) :
    Tendsto (fun Y : ℝ => eulerTiltDeficit σ Y / Y ^ (1 - σ)) atTop (nhds 0) := by
  have hb0 : (0 : ℝ) < 1 - 2 * σ := by linarith
  have hmain := tendsto_primeRpowLogSumLE hb0
  have hdecay := tendsto_rpow_neg_atTop hσ0
  have hmaj : Tendsto (fun Y : ℝ => primeRpowLogSumLE (1 - 2 * σ) Y / Y ^ (1 - σ)) atTop
      (nhds 0) := by
    have h := hmain.mul hdecay
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    have hpow : Y ^ (1 - 2 * σ) * Y ^ σ = Y ^ (1 - σ) := by
      rw [← Real.rpow_add hY]
      congr 1
      ring
    have hpos1 : (0 : ℝ) < Y ^ (1 - 2 * σ) := Real.rpow_pos_of_pos hY _
    have hpos2 : (0 : ℝ) < Y ^ σ := Real.rpow_pos_of_pos hY _
    rw [Real.rpow_neg hY.le, ← hpow]
    field_simp
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact div_nonneg (eulerTiltDeficit_nonneg σ Y) (Real.rpow_pos_of_pos hY _).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact div_le_div_of_nonneg_right (eulerTiltDeficit_le_rpowLogSum σ Y)
      (Real.rpow_pos_of_pos hY _).le

theorem tendsto_varianceTiltDeficit_of_lt_half {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < 1 / 2) :
    Tendsto (fun Y : ℝ => varianceTiltDeficit σ Y / (Y ^ (1 - σ) * Real.log Y)) atTop
      (nhds 0) := by
  have hb0 : (0 : ℝ) < 1 - 2 * σ := by linarith
  have hmain := tendsto_primeRpowLogSqSumLE hb0
  have hdecay := tendsto_rpow_neg_atTop hσ0
  have hmaj : Tendsto
      (fun Y : ℝ => 3 * primeRpowLogSqSumLE (1 - 2 * σ) Y / (Y ^ (1 - σ) * Real.log Y)) atTop
      (nhds 0) := by
    have h := (hmain.mul hdecay).const_mul (3 : ℝ)
    rw [mul_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hlog : (0 : ℝ) < Real.log Y := Real.log_pos hY
    have hpow : Y ^ (1 - 2 * σ) * Y ^ σ = Y ^ (1 - σ) := by
      rw [← Real.rpow_add hY0]
      congr 1
      ring
    have hpos1 : (0 : ℝ) < Y ^ (1 - 2 * σ) := Real.rpow_pos_of_pos hY0 _
    have hpos2 : (0 : ℝ) < Y ^ σ := Real.rpow_pos_of_pos hY0 _
    rw [Real.rpow_neg hY0.le, ← hpow]
    field_simp
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hlog : (0 : ℝ) < Real.log Y := Real.log_pos hY
    have hpos : (0 : ℝ) < Y ^ (1 - σ) := Real.rpow_pos_of_pos hY0 _
    exact div_nonneg (varianceTiltDeficit_nonneg σ Y) (by positivity)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hlog : (0 : ℝ) < Real.log Y := Real.log_pos hY
    have hpos : (0 : ℝ) < Y ^ (1 - σ) := Real.rpow_pos_of_pos hY0 _
    exact div_le_div_of_nonneg_right (varianceTiltDeficit_le_rpowLogSqSum σ Y) (by positivity)

/-- **The physical saddle centre at every positive tilt below one.** -/
theorem tendsto_saddleLogCenter_of_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun Y : ℝ => saddleLogCenter σ Y / Y ^ (1 - σ)) atTop (nhds (2 / (1 - σ))) := by
  rcases le_or_gt (1 / 2 : ℝ) σ with hσ | hσ
  · exact tendsto_saddleLogCenter hσ hσ1
  · have ha0 : (0 : ℝ) < 1 - σ := by linarith
    have h1 := tendsto_primeRpowLogSumLE ha0
    have h2 := tendsto_eulerTiltDeficit_of_lt_half hσ0 hσ
    have h := (h1.sub h2).const_mul (2 : ℝ)
    rw [sub_zero] at h
    have hval : (2 : ℝ) * (1 / (1 - σ)) = 2 / (1 - σ) := by ring
    rw [hval] at h
    refine h.congr fun Y => ?_
    rw [saddleLogCenter_eq]
    ring

/-- **The physical saddle variance at every positive tilt below one.** -/
theorem tendsto_saddleLogVariance_of_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun Y : ℝ => saddleLogVariance σ Y / (Y ^ (1 - σ) * Real.log Y)) atTop
      (nhds (2 / (1 - σ))) := by
  rcases le_or_gt (1 / 2 : ℝ) σ with hσ | hσ
  · exact tendsto_saddleLogVariance hσ hσ1
  · have ha0 : (0 : ℝ) < 1 - σ := by linarith
    have hmain := tendsto_primeRpowLogSqSumLE ha0
    have hdef := tendsto_varianceTiltDeficit_of_lt_half hσ0 hσ
    have hsum := (hmain.sub hdef).const_mul (2 : ℝ)
    rw [sub_zero] at hsum
    have hval : (2 : ℝ) * (1 / (1 - σ)) = 2 / (1 - σ) := by ring
    rw [hval] at hsum
    refine hsum.congr fun Y => ?_
    rw [saddleLogVariance_eq]
    ring

end

end RHTower
