import GaloisForLFunctions.RHTower.Sieve.CardLengthGap

/-!
# Exponential window gaps at every positive exponent

`exp((log y)^β')` dominates `exp((log y)^β) * sqrt(log y)` whenever
`0 < β < β'`.  The older bridge unnecessarily required `β > 1/2`; this module removes that
restriction by using exponential-over-real-power asymptotics at the logarithmic scale.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

theorem eventually_affine_sqrt_le_exp_rpow
    {β a b : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop,
      a * L ^ ((1 : ℝ) / 2) + b ≤ Real.exp ((1 / 2) * L ^ β) := by
  let s : ℝ := ((1 : ℝ) / 2) / β
  have hsβ : β * s = (1 : ℝ) / 2 := by
    dsimp only [s]
    field_simp
  have hloBase := isLittleO_rpow_exp_pos_mul_atTop s (show (0 : ℝ) < 1 / 2 by norm_num)
  have hpow : Tendsto (fun L : ℝ => L ^ β) atTop atTop := tendsto_rpow_atTop hβ
  have hlo := hloBase.comp_tendsto hpow
  let c : ℝ := 1 / (4 * (|a| + b + 1))
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hexp : Tendsto (fun L : ℝ => Real.exp ((1 / 2) * L ^ β)) atTop atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    exact hpow.const_mul_atTop (by norm_num)
  filter_upwards [hlo.def hc, hexp.eventually_ge_atTop (4 * b),
      eventually_ge_atTop (1 : ℝ)] with L hsmall hlarge hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpow0 : 0 ≤ L ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
  have hexp0 : 0 < Real.exp ((1 / 2) * L ^ β) := Real.exp_pos _
  have hrewrite : (L ^ β) ^ s = L ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_mul hL0.le, hsβ]
  simp only [Function.comp_apply] at hsmall
  rw [hrewrite, Real.norm_of_nonneg hpow0] at hsmall
  simp only [Real.norm_eq_abs, abs_of_pos hexp0] at hsmall
  have hac : |a| * c ≤ 1 / 4 := by
    have hden : 0 < |a| + b + 1 := by positivity
    calc
      |a| * c = |a| / (4 * (|a| + b + 1)) := by
        dsimp only [c]
        ring
      _ ≤ 1 / 4 := by
        rw [div_le_iff₀ (by positivity : 0 < 4 * (|a| + b + 1))]
        nlinarith [abs_nonneg a, hb]
  have ha : a * L ^ ((1 : ℝ) / 2) ≤
      (1 / 4) * Real.exp ((1 / 2) * L ^ β) := by
    calc
      a * L ^ ((1 : ℝ) / 2) ≤ |a| * L ^ ((1 : ℝ) / 2) := by
        gcongr
        exact le_abs_self a
      _ ≤ |a| * (c * Real.exp ((1 / 2) * L ^ β)) := by
        gcongr
      _ = (|a| * c) * Real.exp ((1 / 2) * L ^ β) := by ring
      _ ≤ (1 / 4) * Real.exp ((1 / 2) * L ^ β) := by gcongr
  have hbexp : b ≤ (1 / 4) * Real.exp ((1 / 2) * L ^ β) := by linarith
  linarith

theorem eventually_cardLength_gap_all {β β' a b : ℝ}
    (hβ0 : 0 < β) (hββ' : β < β') (hb : 0 ≤ b) :
    ∀ᶠ y : ℝ in atTop,
      a * cardLength β y * Real.sqrt (Real.log y) + b ≤ cardLength β' y := by
  have hβ' : 0 < β' := hβ0.trans hββ'
  have hev : ∀ᶠ L : ℝ in atTop,
      a * Real.exp (L ^ β) * L ^ ((1 : ℝ) / 2) + b ≤ Real.exp (L ^ β') := by
    filter_upwards [eventually_rpow_le_half hββ',
      eventually_affine_sqrt_le_exp_rpow (β := β') (a := a) (b := b) hβ' hb,
      eventually_ge_atTop (1 : ℝ)] with L hhalf haff hL1
    have hL0 : (0 : ℝ) < L := zero_lt_one.trans_le hL1
    have hexpβ : (1 : ℝ) ≤ Real.exp (L ^ β) :=
      Real.one_le_exp (Real.rpow_nonneg hL0.le _)
    have hexp0 : (0 : ℝ) < Real.exp (L ^ β) := Real.exp_pos _
    have hstep : a * Real.exp (L ^ β) * L ^ ((1 : ℝ) / 2) + b
        ≤ Real.exp (L ^ β) * (a * L ^ ((1 : ℝ) / 2) + b) := by
      have hb' : b ≤ Real.exp (L ^ β) * b := by nlinarith [hexpβ, hb]
      nlinarith [hb', hexpβ]
    refine hstep.trans ?_
    calc
      Real.exp (L ^ β) * (a * L ^ ((1 : ℝ) / 2) + b)
          ≤ Real.exp (L ^ β) * Real.exp ((1 / 2) * L ^ β') :=
        mul_le_mul_of_nonneg_left haff hexp0.le
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
