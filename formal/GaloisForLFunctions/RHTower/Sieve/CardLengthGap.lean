import GaloisForLFunctions.RHTower.Sieve.MultiBlockFrame

/-!
# Comparing two window exponents

For `1/2 < β < β' < 1` the window `cardLength β' y = exp((log y)^{β'})` dominates
`cardLength β y` times any fixed multiple of `√(log y)`, because
`(log y)^{β'} − (log y)^{β} ≥ (1/2)(log y)^{β'}` eventually and `exp t ≥ t`.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-- A power below `β'` is eventually at most half of the `β'` power. -/
theorem eventually_rpow_le_half {β β' : ℝ} (hββ' : β < β') :
    ∀ᶠ L : ℝ in atTop, L ^ β ≤ (1 / 2) * L ^ β' := by
  have hgrow : Tendsto (fun L : ℝ => L ^ (β' - β)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  filter_upwards [hgrow.eventually_ge_atTop 2, eventually_ge_atTop (1 : ℝ)] with L hL hL1
  have hL0 : (0 : ℝ) < L := by linarith
  have hsplit : L ^ β * L ^ (β' - β) = L ^ β' := by
    rw [← Real.rpow_add hL0]; ring_nf
  have hpow0 : (0 : ℝ) < L ^ β := Real.rpow_pos_of_pos hL0 _
  nlinarith [hL, hsplit, hpow0]

/-- An affine function of `√L` is eventually below half of the `β'` power, for `β' > 1/2`. -/
theorem eventually_affine_sqrt_le {β' a b : ℝ} (hβ' : 1 / 2 < β') (hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop, a * L ^ ((1 : ℝ) / 2) + b ≤ (1 / 2) * L ^ β' := by
  have hgrow : Tendsto (fun L : ℝ => L ^ (β' - (1 : ℝ) / 2)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  filter_upwards [hgrow.eventually_ge_atTop (2 * (a + b) + 2), eventually_ge_atTop (1 : ℝ)]
    with L hL hL1
  have hL0 : (0 : ℝ) < L := by linarith
  have hhalf : (1 : ℝ) ≤ L ^ ((1 : ℝ) / 2) := Real.one_le_rpow hL1 (by norm_num)
  have hsplit : L ^ ((1 : ℝ) / 2) * L ^ (β' - (1 : ℝ) / 2) = L ^ β' := by
    rw [← Real.rpow_add hL0]; ring_nf
  have hstep : a * L ^ ((1 : ℝ) / 2) + b ≤ (a + b) * L ^ ((1 : ℝ) / 2) := by nlinarith [hhalf, hb]
  have hnn : (0 : ℝ) ≤ L ^ ((1 : ℝ) / 2) := by positivity
  have hkey : L ^ ((1 : ℝ) / 2) * (2 * (a + b) + 2) ≤ L ^ β' := by
    calc L ^ ((1 : ℝ) / 2) * (2 * (a + b) + 2)
        ≤ L ^ ((1 : ℝ) / 2) * L ^ (β' - (1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hL hnn
      _ = L ^ β' := hsplit
  nlinarith [hstep, hkey, hhalf, hb]

/-- **The window gap.**  For `1/2 < β < β' `, `cardLength β'` dominates any fixed multiple of
`cardLength β · √(log y)` plus a constant. -/
theorem eventually_cardLength_gap {β β' a b : ℝ} (hβ0 : 1 / 2 < β) (hββ' : β < β')
    (hb : 0 ≤ b) :
    ∀ᶠ y : ℝ in atTop,
      a * cardLength β y * Real.sqrt (Real.log y) + b ≤ cardLength β' y := by
  have hβ'half : 1 / 2 < β' := by linarith
  have hβpos : (0 : ℝ) < β := by linarith
  have hev : ∀ᶠ L : ℝ in atTop,
      a * Real.exp (L ^ β) * L ^ ((1 : ℝ) / 2) + b ≤ Real.exp (L ^ β') := by
    filter_upwards [eventually_rpow_le_half hββ',
      eventually_affine_sqrt_le (β' := β') (a := a) (b := b) hβ'half hb,
      eventually_ge_atTop (1 : ℝ)] with L hhalf haff hL1
    have hL0 : (0 : ℝ) < L := by linarith
    have hexpβ : (1 : ℝ) ≤ Real.exp (L ^ β) := Real.one_le_exp (Real.rpow_nonneg hL0.le _)
    have hexp0 : (0 : ℝ) < Real.exp (L ^ β) := Real.exp_pos _
    -- the affine part is below `exp((1/2)L^{β'})`
    have hle : a * L ^ ((1 : ℝ) / 2) + b ≤ Real.exp ((1 / 2) * L ^ β') := by
      refine haff.trans ?_
      linarith [Real.add_one_le_exp ((1 / 2) * L ^ β')]
    have hstep : a * Real.exp (L ^ β) * L ^ ((1 : ℝ) / 2) + b
        ≤ Real.exp (L ^ β) * (a * L ^ ((1 : ℝ) / 2) + b) := by
      have hb' : b ≤ Real.exp (L ^ β) * b := by nlinarith [hexpβ, hb]
      nlinarith [hb', hexpβ]
    refine hstep.trans ?_
    calc Real.exp (L ^ β) * (a * L ^ ((1 : ℝ) / 2) + b)
        ≤ Real.exp (L ^ β) * Real.exp ((1 / 2) * L ^ β') :=
          mul_le_mul_of_nonneg_left hle hexp0.le
      _ = Real.exp (L ^ β + (1 / 2) * L ^ β') := (Real.exp_add _ _).symm
      _ ≤ Real.exp (L ^ β') := Real.exp_le_exp.2 (by linarith [hhalf])
  filter_upwards [Real.tendsto_log_atTop.eventually hev, eventually_ge_atTop (1 : ℝ)]
    with y hy hy1
  have hlog0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
  have hsqrt : Real.sqrt (Real.log y) = (Real.log y) ^ ((1 : ℝ) / 2) :=
    Real.sqrt_eq_rpow (Real.log y)
  rw [cardLength, cardLength, hsqrt]
  exact hy

end

end RHTower.Sieve
