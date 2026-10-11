import GaloisForLFunctions.RHTower.ZetaGateUpperRange

/-!
# The off-line moment from an upper-range gate and any proportion of simple critical zeros

`eventually_offLineMoment_le_of_zetaGateFrom_twoThirds` combines a mean-square gate on `[U^α, U]`
with the two-thirds proportion of simple critical zeros.  The proportion enters only through the
count credit `N₀(T₂) − N₀(T₁) ≥ (p − ε)N(T₂) − N(T₁)`, so any lower density `p ≤ 7/8` of simple
critical zeros gives

  `4π Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (log c − (1 + p) R + η) V`   eventually

(`eventually_offLineMoment_le_of_zetaGateFrom_proportion`).  The restriction `p ≤ 7/8` only keeps
the Riemann–von Mangoldt slack below `η/16`.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- The Riemann–von Mangoldt slack for a proportion `p ≤ 7/8`. -/
theorem proportion_eps'_bound {R η ε₀ p : ℝ} (hR : 0 < R) (hη : 0 < η) (hε₀0 : 0 < ε₀)
    (hp : p ≤ 7 / 8) :
    2 * Real.pi * (η / (60 * Real.pi * R)) * R * (1 + (p - ε₀) + 0) ≤ η / 16 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hid : 2 * Real.pi * (η / (60 * Real.pi * R)) * R = η / 30 := by
    field_simp
    try ring
  rw [hid]
  have hcoef : 1 + (p - ε₀) + 0 ≤ 15 / 8 := by linarith
  calc η / 30 * (1 + (p - ε₀) + 0) ≤ η / 30 * (15 / 8) :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = η / 16 := by ring

/-- **The off-line first moment from an upper-range gate and a simple-critical proportion `p`.**

If `(p − ε) N(T) ≤ N₀^{simple}(T)` eventually for every `ε > 0`, with `0 < p ≤ 7/8`, then
`4π · Σ_{Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (log c₁ − (1 + p) R + η) · V` eventually, for every `η > 0`. -/
theorem eventually_offLineMoment_le_of_zetaGateFrom_proportion {α R c₁ η p : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hR : 0 < R) (hc₁ : 1 ≤ c₁) (hη : 0 < η) (hp0 : 0 < p) (hp1 : p ≤ 7 / 8)
    (hprop : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (p - ε) * (xiPosZeroCount T : ℝ) ≤ (xiSimpleCriticalZeroCount T : ℝ))
    (hg₁ : ZetaMollifiedMeanSquareGateFrom α R c₁) :
    ∀ᶠ V in atTop,
      4 * Real.pi * offLineMoment V ≤ (Real.log c₁ - (1 + p) * R + η) * V := by
  classical
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨C, K, hC, hK, hceil⟩ :=
    exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare
  -- the slack in the proportion
  obtain ⟨ε₀, hε₀0, hε₀p, hε₀R⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ p ∧ ε₀ * R ≤ η / 16 := by
    refine ⟨min p (η / (16 * R)), lt_min hp0 (by positivity), min_le_left _ _, ?_⟩
    have h1 : min p (η / (16 * R)) ≤ η / (16 * R) := min_le_right _ _
    have h2 : η / (16 * R) * R = η / 16 := by field_simp
    calc min p (η / (16 * R)) * R ≤ η / (16 * R) * R :=
          mul_le_mul_of_nonneg_right h1 hR.le
      _ = η / 16 := h2
  have hκ₀ : (0 : ℝ) ≤ p - ε₀ := by linarith
  have hε0 : 0 < c₁ * (η / 8) := by positivity
  have hlogε := log_gate_slack_le hc₁ hη
  have hε'0 : 0 < η / (60 * Real.pi * R) := by positivity
  have hε'bound := proportion_eps'_bound (ε₀ := ε₀) hR hη hε₀0 hp1
  obtain ⟨T₀, _, hrvm⟩ := exists_xiZeroCount_close (η / (60 * Real.pi * R)) hε'0
  obtain ⟨U₁, hU₁⟩ := hprop ε₀ hε₀0
  have hev : ∀ᶠ U : ℝ in atTop,
      4 * Real.pi * offLineMoment (U - 1) ≤ (Real.log c₁ - (1 + p) * R + η) * (U - 1) := by
    filter_upwards [hg₁ (c₁ * (η / 8)) hε0, eventually_ge_atTop (max (T₀ + 1) (max (U₁ + 1) 23)),
      eventually_mul_log_le_quarter hK hη,
      eventually_const_le_quarter_sub_one (|Real.log c₁ - (1 + p) * R + η / 4| + 2 * C)
        (show 0 < η / 2 by positivity),
      eventually_count_upper_le hα0 hα1 (2 * Real.pi + 4 * Real.pi * R / Real.log 20)
        (show 0 < η / 8 by positivity)]
      with U hU hUbig hlogU hDU₀ hcountU
    obtain ⟨T₁, T₂, σ₀, Mb, b, N, hT₁, hT₂, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb,
      hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩ := hU
    have hU23 : 23 ≤ U := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hUbig
    have hUT₀ : T₀ + 1 ≤ U := le_trans (le_max_left _ _) hUbig
    have hUU₁ : U₁ + 1 ≤ U := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hUbig
    have hT₂big : U - 1 < T₂ := hT₂.1
    have hT₂U : T₂ ≤ U := hT₂.2
    have hT₁20 : 20 ≤ T₁ := hT₁.1
    have hT₁21 : T₁ ≤ U ^ α + 1 := hT₁.2
    have hUα := hcountU.2
    have hT12 : T₁ < T₂ := by linarith [hUα.2.1]
    have hT₂T₀ : T₀ ≤ T₂ := by linarith
    have hT₂U₁ : U₁ ≤ T₂ := by linarith
    have hlogT₂ : 0 < Real.log T₂ := Real.log_pos (by linarith)
    obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
    have hc := hceil b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂
      ((c₁ + c₁ * (η / 8)) * (T₂ - T₁)) hσ₀a hσ₀b hT₁20 hT12 hG1 hG2 hP1 hP2 hMsq Z hZ
    have hlogMsq : Real.log ((c₁ + c₁ * (η / 8)) * (T₂ - T₁) / (T₂ - T₁))
        = Real.log (c₁ + c₁ * (η / 8)) := by
      rw [mul_div_assoc, div_self (by linarith : T₂ - T₁ ≠ 0), mul_one]
    rw [hlogMsq] at hc
    -- the count credit, from the simple-critical proportion
    have hbridge1 := rightHalfOrderSum_sub_le_zetaZeroSum hT12.le Z hZ
    have hbridge2 := offLineMoment_le_add_zetaZeroMoment hT12.le Z hZ
    have hrefl₂ : (2 * rightHalfOrderSum T₂ : ℝ)
        = (xiPosZeroCount T₂ : ℝ) + (xiPosCriticalZeroCount T₂ : ℝ) := by
      exact_mod_cast two_mul_rightHalfOrderSum T₂
    have hR₁nat : rightHalfOrderSum T₁ ≤ xiPosZeroCount T₁ := by
      unfold rightHalfOrderSum xiPosZeroCount
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hR₁ : (rightHalfOrderSum T₁ : ℝ) ≤ (xiPosZeroCount T₁ : ℝ) := by exact_mod_cast hR₁nat
    have hprop₂ : (p - ε₀) * (xiPosZeroCount T₂ : ℝ) ≤ (xiSimpleCriticalZeroCount T₂ : ℝ) :=
      hU₁ T₂ hT₂U₁
    have hsimple : (xiSimpleCriticalZeroCount T₂ : ℝ) ≤ (xiPosCriticalZeroCount T₂ : ℝ) := by
      exact_mod_cast xiSimpleCriticalZeroCount_le_xiPosCriticalZeroCount T₂
    have hS : (1 + (p - ε₀) + 0) * (xiPosZeroCount T₂ : ℝ) / 2 - (xiPosZeroCount T₁ : ℝ)
        ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
      linarith only [hbridge1, hrefl₂, hR₁, hprop₂, hsimple]
    -- Riemann–von Mangoldt
    have hN₂ : (1 / (2 * Real.pi) - η / (60 * Real.pi * R)) * (T₂ * Real.log T₂)
        ≤ (xiPosZeroCount T₂ : ℝ) := by
      have h := hrvm T₂ hT₂T₀
      have hcast : ((xiZeroCount T₂ : ℤ) : ℝ) = (xiPosZeroCount T₂ : ℝ) := by
        rw [← xiPosZeroCount_eq_xiZeroCount (by linarith)]
        simp
      rw [hcast] at h
      have h1 := (abs_le.mp h).1
      have hid : (1 / (2 * Real.pi) - η / (60 * Real.pi * R)) * (T₂ * Real.log T₂)
          = 1 / (2 * Real.pi) * (T₂ * Real.log T₂)
            - η / (60 * Real.pi * R) * (T₂ * Real.log T₂) := by
        ring
      linarith only [h1, hid]
    have harith := offLineMoment_window_arith hR hlogT₂ hσ₀R (by linarith) hT12.le hK.le hlogMb
      (Real.log_nonneg (by linarith)) hκ₀ (le_refl (0 : ℝ)) hε'0.le (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hc hS hbridge2 hN₂
    have hmono := offLineMoment_mono (le_of_lt hT₂big)
    have hbr : Real.log (c₁ + c₁ * (η / 8))
        - R * (1 + (p - ε₀) + 0) * (1 - 2 * Real.pi * (η / (60 * Real.pi * R)))
        ≤ Real.log c₁ - (1 + p) * R + η / 4 := by
      have hid : R * (1 + (p - ε₀) + 0) * (1 - 2 * Real.pi * (η / (60 * Real.pi * R)))
          = (1 + p) * R - ε₀ * R
            - 2 * Real.pi * (η / (60 * Real.pi * R)) * R * (1 + (p - ε₀) + 0) := by ring
      linarith only [hlogε, hε'bound, hid, hε₀R]
    have hN₁nat : xiPosZeroCount T₁ ≤ xiPosZeroCount (U ^ α + 1) :=
      Finset.sum_le_sum_of_subset (stripFinsetPos_mono hT₁21)
    have hN₁ : (xiPosZeroCount T₁ : ℝ) ≤ (xiPosZeroCount (U ^ α + 1) : ℝ) := by
      exact_mod_cast hN₁nat
    have hM₁ : 4 * Real.pi * offLineMoment T₁
        ≤ 4 * Real.pi * (1 / 2 * (xiPosZeroCount (U ^ α + 1) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (offLineMoment_le_half_xiPosZeroCount T₁).trans (by linarith only [hN₁])
    have hlog20 : Real.log 20 ≤ Real.log T₂ := Real.log_le_log (by norm_num) (by linarith)
    have hlog20pos : 0 < Real.log 20 := Real.log_pos (by norm_num)
    have hlast : 4 * Real.pi * R * (xiPosZeroCount T₁ : ℝ) / Real.log T₂
        ≤ 4 * Real.pi * R * (xiPosZeroCount (U ^ α + 1) : ℝ) / Real.log 20 := by
      apply div_le_div₀ (by positivity) _ hlog20pos hlog20
      exact mul_le_mul_of_nonneg_left hN₁ (by positivity)
    have hlogT₂U : Real.log T₂ ≤ Real.log U := Real.log_le_log (by linarith) hT₂U
    have hKlog : 12 * K * Real.log T₂ ≤ η / 4 * U :=
      le_trans (mul_le_mul_of_nonneg_left hlogT₂U (by positivity)) hlogU
    have hmono' : 4 * Real.pi * offLineMoment (U - 1) ≤ 4 * Real.pi * offLineMoment T₂ :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    have hfinal := twoThirds_tail_arith (by linarith) hT₂big hT₂U harith hbr hM₁ hlast hKlog
      hmono'
    have hηU : η / 4 * U = η / 4 * (U - 1) + η / 4 := by ring
    have hη1 : η / 4 ≤ η / 4 * (U - 1) := by
      have h0 : 0 ≤ η / 4 * (U - 2) := mul_nonneg (by positivity) (by linarith only [hU23])
      have hid : η / 4 * (U - 1) = η / 4 + η / 4 * (U - 2) := by ring
      linarith only [h0, hid]
    have hBη : (Real.log c₁ - (1 + p) * R + η) * (U - 1)
        = (U - 1) * (Real.log c₁ - (1 + p) * R + η / 4) + 3 * (η / 4 * (U - 1)) := by
      ring
    have hDU : |Real.log c₁ - (1 + p) * R + η / 4| + 2 * C
        + 4 * Real.pi * (1 / 2 * (xiPosZeroCount (U ^ α + 1) : ℝ))
        + 4 * Real.pi * R * (xiPosZeroCount (U ^ α + 1) : ℝ) / Real.log 20 ≤ η / 4 * (U - 1) := by
      have h1 := hcountU.1
      have hid : 4 * Real.pi * (1 / 2 * (xiPosZeroCount (U ^ α + 1) : ℝ))
          + 4 * Real.pi * R * (xiPosZeroCount (U ^ α + 1) : ℝ) / Real.log 20
          = (2 * Real.pi + 4 * Real.pi * R / Real.log 20) * (xiPosZeroCount (U ^ α + 1) : ℝ) := by
        ring
      have hηsplit : η / 2 / 4 * (U - 1) + η / 8 * (U - 1) = η / 4 * (U - 1) := by ring
      linarith only [hDU₀, h1, hid, hηsplit]
    rw [hBη]
    linarith only [hfinal, hDU, hηU, hη1]
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  have := hshift.eventually hev
  simpa using this

end

end RHTower
