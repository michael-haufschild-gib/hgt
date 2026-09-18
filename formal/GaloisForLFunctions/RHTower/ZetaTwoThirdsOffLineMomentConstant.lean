/-
# The `(L)` ceiling with the unconditional two-thirds on-line proportion

`SingleInputOffLineMomentConstant.eventually_offLineMoment_le_of_gates` bounds the first
horizontal moment of the off-line zeta zeros by `(log c₁ − (1 + κ₀)R + η)V/(4π)`, where the on-line
proportion `κ₀` had to be derived from a second mean-square gate (Levinson's detector), which caps it
at `κ₀ < 1 − log c₂/R`.  Alpöge–Furman's unconditional two-thirds theorem (Zeta23, a pinned Lake
dependency; transported to the Xi census in `Zeta23SimpleCriticalDensity`) supplies
`κ₀ = 2/3` with no gate at all.  Substituting it into the same window arithmetic gives

  `4π · Σ_{Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (log c₁ − (5/3) R + η) · V`   eventually, for every `η > 0`,

from the single gate `ZetaMollifiedMeanSquareGate R c₁` (the mollified mean square of `ζΨ` on the
Levinson abscissa `½ − R/log T`).  With Young's constant `c₁(R, θ)` at Conrey's `θ = 4/7` and
`R ≈ 1.1` the ceiling is `≈ 0.0535·V` against `≈ 0.0714·V` for the two-gate theorem
(paper values; the Lean statement is the conditional inequality with the gate as its only input).

The proof is the two-gate proof with the odd-fibre density input replaced by
`two_thirds_simpleCritical_epsilon` and `xiSimpleCriticalZeroCount_le_xiPosCriticalZeroCount`.
-/
import GaloisForLFunctions.RHTower.SingleInputOffLineMomentConstant
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.RHTower.Zeta23HorizontalSingletonDensity

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **The `(L)` ceiling from one mean-square gate and the unconditional two-thirds proportion.**

`4π · Σ_{Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (log c₁ − (5/3) R + η) · V`  eventually, for every `η > 0`. -/
theorem eventually_offLineMoment_le_of_zetaGate_twoThirds {R c₁ η : ℝ} (hR : 0 < R)
    (hc₁ : 1 ≤ c₁) (hη : 0 < η) (hg₁ : ZetaMollifiedMeanSquareGate R c₁) :
    ∀ᶠ V in atTop,
      4 * Real.pi * offLineMoment V ≤ (Real.log c₁ - (5 / 3) * R + η) * V := by
  classical
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨C, K, hC, hK, hceil⟩ :=
    exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare
  -- the slack in the two-thirds proportion
  obtain ⟨ε₀, hε₀0, hε₀third, hε₀R⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 3 ∧ ε₀ * R ≤ η / 16 := by
    refine ⟨min (1 / 3) (η / (16 * R)), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
    have h1 : min (1 / 3) (η / (16 * R)) ≤ η / (16 * R) := min_le_right _ _
    have h2 : η / (16 * R) * R = η / 16 := by field_simp
    calc min (1 / 3) (η / (16 * R)) * R ≤ η / (16 * R) * R :=
          mul_le_mul_of_nonneg_right h1 hR.le
      _ = η / 16 := h2
  have hκ₀ : (0 : ℝ) ≤ 2 / 3 - ε₀ := by linarith
  set ε : ℝ := c₁ * (η / 8) with hεdef
  have hε0 : 0 < ε := by positivity
  have hlogε : Real.log (c₁ + ε) ≤ Real.log c₁ + η / 8 := by
    have h1 : Real.log (c₁ + ε) = Real.log c₁ + Real.log (1 + η / 8) := by
      rw [← Real.log_mul (by linarith) (by linarith)]
      congr 1
      rw [hεdef]
      ring
    have h2 : Real.log (1 + η / 8) ≤ η / 8 := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + η / 8)
      linarith
    linarith
  set ε' : ℝ := η / (60 * Real.pi * R) with hε'def
  have hε'0 : 0 < ε' := by positivity
  have hε'bound : 2 * Real.pi * ε' * R * (1 + (2 / 3 - ε₀) + 0) ≤ η / 16 := by
    have hid : 2 * Real.pi * ε' * R = η / 30 := by
      rw [hε'def]
      field_simp
      try ring
    rw [hid]
    have hcoef : 1 + (2 / 3 - ε₀) + 0 ≤ 5 / 3 := by linarith
    calc η / 30 * (1 + (2 / 3 - ε₀) + 0) ≤ η / 30 * (5 / 3) :=
          mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ ≤ η / 16 := by nlinarith
  obtain ⟨T₀, _, hrvm⟩ := exists_xiZeroCount_close ε' hε'0
  obtain ⟨U₁, hU₁⟩ := two_thirds_simpleCritical_epsilon ε₀ hε₀0
  set B : ℝ := Real.log c₁ - (5 / 3) * R + η / 4 with hBdef
  set D : ℝ := |B| + 2 * C + 4 * Real.pi * offLineMoment 21
    + 4 * Real.pi * R * (xiPosZeroCount 21 : ℝ) / Real.log 20 with hDdef
  have hlogsmall : ∀ᶠ U : ℝ in atTop, 12 * K * Real.log U ≤ η / 4 * U := by
    have hc : (0 : ℝ) < η / (4 * (12 * K + 1)) := by positivity
    have h := Real.isLittleO_log_id_atTop.def hc
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with U hU hU1
    have hU0 : (0 : ℝ) < U := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.log_pos hU1), id,
      abs_of_pos hU0] at hU
    have h12 : 12 * K * (η / (4 * (12 * K + 1)) * U) ≤ η / 4 * U := by
      have hid : 12 * K * (η / (4 * (12 * K + 1)) * U) = (12 * K / (12 * K + 1)) * (η / 4 * U) := by
        field_simp
        try ring
      rw [hid]
      have h1 : 12 * K / (12 * K + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have h2 : 0 ≤ η / 4 * U := by positivity
      nlinarith
    calc 12 * K * Real.log U ≤ 12 * K * (η / (4 * (12 * K + 1)) * U) :=
          mul_le_mul_of_nonneg_left hU (by positivity)
      _ ≤ η / 4 * U := h12
  have hDsmall : ∀ᶠ U : ℝ in atTop, D ≤ η / 4 * (U - 1) := by
    filter_upwards [eventually_ge_atTop (4 * D / η + 1)] with U hU
    have hid : η / 4 * (4 * D / η) = D := by
      field_simp
      try ring
    have : η / 4 * (4 * D / η) ≤ η / 4 * (U - 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hU]) (by positivity)
    linarith only [hid, this]
  have hev : ∀ᶠ U : ℝ in atTop,
      4 * Real.pi * offLineMoment (U - 1) ≤ (Real.log c₁ - (5 / 3) * R + η) * (U - 1) := by
    filter_upwards [hg₁ ε hε0, eventually_ge_atTop (max (T₀ + 1) (max (U₁ + 1) 23)),
      hlogsmall, hDsmall] with U hU hUbig hlogU hDU
    obtain ⟨T₁, T₂, σ₀, Mb, b, N, hT₁, hT₂, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb,
      hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩ := hU
    have hU23 : 23 ≤ U := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hUbig
    have hUT₀ : T₀ + 1 ≤ U := le_trans (le_max_left _ _) hUbig
    have hUU₁ : U₁ + 1 ≤ U := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hUbig
    have hT₂big : U - 1 < T₂ := hT₂.1
    have hT₂U : T₂ ≤ U := hT₂.2
    have hT₁20 : 20 ≤ T₁ := hT₁.1
    have hT₁21 : T₁ ≤ 21 := hT₁.2
    have hT12 : T₁ < T₂ := by linarith
    have hT₂T₀ : T₀ ≤ T₂ := by linarith
    have hT₂U₁ : U₁ ≤ T₂ := by linarith
    have hlogT₂ : 0 < Real.log T₂ := Real.log_pos (by linarith)
    obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
    have hc := hceil b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ ((c₁ + ε) * (T₂ - T₁))
      hσ₀a hσ₀b hT₁20 hT12 hG1 hG2 hP1 hP2 hMsq Z hZ
    have hlogMsq : Real.log ((c₁ + ε) * (T₂ - T₁) / (T₂ - T₁)) = Real.log (c₁ + ε) := by
      rw [mul_div_assoc, div_self (by linarith : T₂ - T₁ ≠ 0), mul_one]
    rw [hlogMsq] at hc
    -- the count credit, now from the unconditional two-thirds theorem
    have hbridge1 := rightHalfOrderSum_sub_le_zetaZeroSum hT12.le Z hZ
    have hbridge2 := offLineMoment_le_add_zetaZeroMoment hT12.le Z hZ
    have hrefl₂ : (2 * rightHalfOrderSum T₂ : ℝ)
        = (xiPosZeroCount T₂ : ℝ) + (xiPosCriticalZeroCount T₂ : ℝ) := by
      exact_mod_cast two_mul_rightHalfOrderSum T₂
    have hR₁nat : rightHalfOrderSum T₁ ≤ xiPosZeroCount T₁ := by
      unfold rightHalfOrderSum xiPosZeroCount
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hR₁ : (rightHalfOrderSum T₁ : ℝ) ≤ (xiPosZeroCount T₁ : ℝ) := by exact_mod_cast hR₁nat
    have hprop : (2 / 3 - ε₀) * (xiPosZeroCount T₂ : ℝ) ≤ (xiSimpleCriticalZeroCount T₂ : ℝ) :=
      hU₁ T₂ hT₂U₁
    have hsimple : (xiSimpleCriticalZeroCount T₂ : ℝ) ≤ (xiPosCriticalZeroCount T₂ : ℝ) := by
      exact_mod_cast xiSimpleCriticalZeroCount_le_xiPosCriticalZeroCount T₂
    have hS : (1 + (2 / 3 - ε₀) + 0) * (xiPosZeroCount T₂ : ℝ) / 2 - (xiPosZeroCount T₁ : ℝ)
        ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
      linarith only [hbridge1, hrefl₂, hR₁, hprop, hsimple]
    -- Riemann–von Mangoldt
    have hN₂ : (1 / (2 * Real.pi) - ε') * (T₂ * Real.log T₂) ≤ (xiPosZeroCount T₂ : ℝ) := by
      have h := hrvm T₂ hT₂T₀
      have hcast : ((xiZeroCount T₂ : ℤ) : ℝ) = (xiPosZeroCount T₂ : ℝ) := by
        rw [← xiPosZeroCount_eq_xiZeroCount (by linarith)]
        simp
      rw [hcast] at h
      have h1 := (abs_le.mp h).1
      have hid : (1 / (2 * Real.pi) - ε') * (T₂ * Real.log T₂)
          = 1 / (2 * Real.pi) * (T₂ * Real.log T₂) - ε' * (T₂ * Real.log T₂) := by ring
      linarith only [h1, hid]
    have harith := offLineMoment_window_arith hR hlogT₂ hσ₀R (by linarith) hT12.le hK.le hlogMb
      (Real.log_nonneg (by linarith)) hκ₀ (le_refl (0 : ℝ)) hε'0.le (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hc hS hbridge2 hN₂
    have hmono := offLineMoment_mono (le_of_lt hT₂big)
    have hbr : Real.log (c₁ + ε) - R * (1 + (2 / 3 - ε₀) + 0) * (1 - 2 * Real.pi * ε') ≤ B := by
      have hid : R * (1 + (2 / 3 - ε₀) + 0) * (1 - 2 * Real.pi * ε')
          = (5 / 3) * R - ε₀ * R - 2 * Real.pi * ε' * R * (1 + (2 / 3 - ε₀) + 0) := by ring
      rw [hBdef]
      linarith only [hlogε, hε'bound, hid, hε₀R]
    have hT₂B : T₂ * (Real.log (c₁ + ε) - R * (1 + (2 / 3 - ε₀) + 0) * (1 - 2 * Real.pi * ε'))
        ≤ T₂ * B := mul_le_mul_of_nonneg_left hbr (by linarith)
    have hTB : T₂ * B ≤ (U - 1) * B + |B| := by
      rcases le_or_gt 0 B with hB0 | hB0
      · have : T₂ * B ≤ U * B := mul_le_mul_of_nonneg_right hT₂U hB0
        rw [abs_of_nonneg hB0]
        linarith only [this]
      · have h0 : 0 ≤ (T₂ - (U - 1)) * (-B) :=
          mul_nonneg (by linarith only [hT₂big]) (by linarith only [hB0])
        have hid : (T₂ - (U - 1)) * (-B) = (U - 1) * B - T₂ * B := by ring
        rw [abs_of_neg hB0]
        linarith only [h0, hid, hB0]
    have hM₁ : 4 * Real.pi * offLineMoment T₁ ≤ 4 * Real.pi * offLineMoment 21 :=
      mul_le_mul_of_nonneg_left (offLineMoment_mono hT₁21) (by positivity)
    have hN₁nat : xiPosZeroCount T₁ ≤ xiPosZeroCount 21 :=
      Finset.sum_le_sum_of_subset (stripFinsetPos_mono hT₁21)
    have hN₁ : (xiPosZeroCount T₁ : ℝ) ≤ (xiPosZeroCount 21 : ℝ) := by exact_mod_cast hN₁nat
    have hlog20 : Real.log 20 ≤ Real.log T₂ := Real.log_le_log (by norm_num) (by linarith)
    have hlog20pos : 0 < Real.log 20 := Real.log_pos (by norm_num)
    have hlast : 4 * Real.pi * R * (xiPosZeroCount T₁ : ℝ) / Real.log T₂
        ≤ 4 * Real.pi * R * (xiPosZeroCount 21 : ℝ) / Real.log 20 := by
      apply div_le_div₀ (by positivity) _ hlog20pos hlog20
      exact mul_le_mul_of_nonneg_left hN₁ (by positivity)
    have hlogT₂U : Real.log T₂ ≤ Real.log U := Real.log_le_log (by linarith) hT₂U
    have hKlog : 12 * K * Real.log T₂ ≤ η / 4 * U :=
      le_trans (mul_le_mul_of_nonneg_left hlogT₂U (by positivity)) hlogU
    have hmono' : 4 * Real.pi * offLineMoment (U - 1) ≤ 4 * Real.pi * offLineMoment T₂ :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    have hDeq : D = |B| + 2 * C + 4 * Real.pi * offLineMoment 21
        + 4 * Real.pi * R * (xiPosZeroCount 21 : ℝ) / Real.log 20 := hDdef
    have hfinal : 4 * Real.pi * offLineMoment (U - 1) ≤ (U - 1) * B + D + η / 4 * U := by
      generalize offLineMoment (U - 1) = mU at *
      generalize offLineMoment T₂ = mT₂ at *
      generalize offLineMoment T₁ = mT₁ at *
      generalize offLineMoment 21 = m21 at *
      generalize (xiPosZeroCount T₁ : ℝ) = n₁ at *
      generalize (xiPosZeroCount 21 : ℝ) = n21 at *
      generalize Real.log T₂ = L₂ at *
      generalize Real.log (c₁ + ε) = lc at *
      linarith only [harith, hT₂B, hTB, hM₁, hlast, hKlog, hmono', hDeq]
    have hηU : η / 4 * U = η / 4 * (U - 1) + η / 4 := by ring
    have hη1 : η / 4 ≤ η / 4 * (U - 1) := by
      have h0 : 0 ≤ η / 4 * (U - 2) := mul_nonneg (by positivity) (by linarith only [hU23])
      have hid : η / 4 * (U - 1) = η / 4 + η / 4 * (U - 2) := by ring
      linarith only [h0, hid]
    have hBη : (Real.log c₁ - (5 / 3) * R + η) * (U - 1)
        = (U - 1) * B + 3 * (η / 4 * (U - 1)) := by
      rw [hBdef]
      ring
    rw [hBη]
    linarith only [hfinal, hDU, hηU, hη1]
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  have := hshift.eventually hev
  simpa using this

end

end RHTower
