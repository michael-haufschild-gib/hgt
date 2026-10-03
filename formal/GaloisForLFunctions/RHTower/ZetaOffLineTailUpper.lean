import GaloisForLFunctions.RHTower.ZetaGateUpperRange
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper
import GaloisForLFunctions.RHTower.ZetaOffLineMomentNinthConsequences

/-!
# The off-line tail law from the upper-range gate

The tail law `4π Σ m_ρ (Re ρ − ½ − R/log V)⁺ ≤ (log c − 2R + η)V` of `ZetaCriticalScaleTailFromGate`
holds with the window starting at `U^α` (`eventually_offLineTail_le_of_zetaGateFrom`): the zeros
below `U^α` contribute at most `N(U^α)/2 = o(U)`.  With Selberg's twisted mollifier of length
`U^{21/50}` (`ZetaOffLineMomentSelbergUpper`) the rate is `g(R) = −log(1 − e^{−21R/25})`
(`eventually_offLineTail_le_selberg_upper`): at most `(g(R) + η) V log V/(4πR)` zeros with
`Re ρ ≥ ½ + 2R/log V`, contracting seams on all but a fraction `≈ (3/2π)g(R)` of the right discs
of radius `2R/log V`, and a `κ`-shadow of measure `≤ (g(κ/2) + η)(V + 1)/π`.
-/

open Complex Filter Topology Set MeasureTheory Metric
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- `Σ m_ρ (Re ρ − ½)⁺ ≤ N(T)/2` for the tail at displacement `0`. -/
theorem offLineTail_zero_le_half (T : ℝ) :
    offLineTail 0 T ≤ 1 / 2 * (xiPosZeroCount T : ℝ) := by
  classical
  unfold offLineTail xiPosZeroCount
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  obtain ⟨-, h2, -, -, -⟩ := mem_stripFinsetPos.mp hz
  have h0 : (0 : ℝ) ≤ ((analyticOrderAt xi z).toNat : ℝ) := Nat.cast_nonneg _
  have hm : max (z.re - 1 / 2 - 0) 0 ≤ 1 / 2 := max_le (by linarith) (by norm_num)
  nlinarith

/-- **The off-line moment beyond the critical scale, from the upper-range gate.**
For every `η > 0`, eventually
`4π Σ_{0 < Im ρ ≤ V} m_ρ (Re ρ − ½ − R/log V)⁺ ≤ (log c − 2R + η) V`. -/
theorem eventually_offLineTail_le_of_zetaGateFrom {α R c₁ η : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hR : 0 < R) (hc₁ : 1 ≤ c₁) (hη : 0 < η) (hg : ZetaMollifiedMeanSquareGateFrom α R c₁) :
    ∀ᶠ V in atTop,
      4 * Real.pi * offLineTail (R / Real.log V) V ≤ (Real.log c₁ - 2 * R + η) * V := by
  classical
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨C, K, hC, hK, hwide⟩ := exists_zetaWideMoment_le_of_mollified_meanSquare
  set ε' : ℝ := η / (32 * Real.pi * R) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'R : 4 * Real.pi * R * ε' = η / 8 := by
    rw [hε']
    field_simp
    ring
  obtain ⟨T₀, _, hrvm⟩ := exists_xiZeroCount_close ε' hε'0
  set B : ℝ := Real.log c₁ - 2 * R + η / 4 with hB
  have hε0 : 0 < c₁ * (η / 8) := by positivity
  have hlogε := log_gate_slack_le hc₁ hη
  have hlog20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
  have hev : ∀ᶠ U : ℝ in atTop,
      4 * Real.pi * offLineTail (R / Real.log (U - 1)) (U - 1)
        ≤ (Real.log c₁ - 2 * R + η) * (U - 1) := by
    filter_upwards [hg (c₁ * (η / 8)) hε0, eventually_ge_atTop (max (T₀ + 1) 23),
      eventually_mul_log_le_quarter hK hη,
      eventually_const_le_quarter_sub_one (|B| + 2 * C) (show 0 < η / 2 by positivity),
      eventually_count_upper_le hα0 hα1 (4 * Real.pi * (R / Real.log 20) + 2 * Real.pi)
        (show 0 < η / 8 by positivity)]
      with U hU hUbig hlogU hDU₀ hcountU
    obtain ⟨T₁, T₂, σ₀, Mb, b, N, hT₁, hT₂, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb,
      hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩ := hU
    have hU23 : 23 ≤ U := le_trans (le_max_right _ _) hUbig
    have hUT₀ : T₀ + 1 ≤ U := le_trans (le_max_left _ _) hUbig
    obtain ⟨hT₂big, hT₂U⟩ := hT₂
    obtain ⟨hT₁20, hT₁21⟩ := hT₁
    have hUα := hcountU.2
    have hT12 : T₁ < T₂ := by linarith [hUα.2.1]
    have hlogT₂ : 0 < Real.log T₂ := Real.log_pos (by linarith)
    set d : ℝ := 1 / 2 - σ₀ with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    have hdR : d * Real.log T₂ = R := hσ₀R
    have hσ₀eq : σ₀ = 1 / 2 - d := by rw [hd]; ring
    obtain ⟨Z, hZ⟩ := exists_zetaWideRectangleZeros_finset (σ₀ := σ₀) hT₁20 hT12
    have hc := hwide b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂
      ((c₁ + c₁ * (η / 8)) * (T₂ - T₁)) hσ₀a hσ₀b hT₁20 hT12 hG1 hG2 hP1 hP2 hMsq Z hZ
    have hlogMsq : Real.log ((c₁ + c₁ * (η / 8)) * (T₂ - T₁) / (T₂ - T₁))
        = Real.log (c₁ + c₁ * (η / 8)) := by
      rw [mul_div_assoc, div_self (by linarith : T₂ - T₁ ≠ 0), mul_one]
    rw [hlogMsq] at hc
    have hZ' : ∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc (1 / 2 - d) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
      rw [← hσ₀eq]; exact hZ
    have hbridge := window_count_add_tail_le_zetaWideSum hd0.le hT12.le Z hZ'
    rw [← hσ₀eq] at hbridge
    -- Riemann–von Mangoldt at `T₂`
    have hN₂ : (1 / (2 * Real.pi) - ε') * (T₂ * Real.log T₂) ≤ (xiPosZeroCount T₂ : ℝ) := by
      have h := hrvm T₂ (by linarith)
      have hcast : ((xiZeroCount T₂ : ℤ) : ℝ) = (xiPosZeroCount T₂ : ℝ) := by
        rw [← xiPosZeroCount_eq_xiZeroCount (by linarith)]
        simp
      rw [hcast] at h
      have h1 := (abs_le.mp h).1
      linarith
    have hdN₂ : R * T₂ * (1 / (2 * Real.pi) - ε') ≤ d * (xiPosZeroCount T₂ : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hN₂ hd0.le
      have e : d * ((1 / (2 * Real.pi) - ε') * (T₂ * Real.log T₂))
          = (d * Real.log T₂) * T₂ * (1 / (2 * Real.pi) - ε') := by ring
      rw [e, hdR] at h
      exact h
    -- the window start
    have hdle : d ≤ R / Real.log 20 := by
      rw [le_div_iff₀ hlog20]
      have : Real.log 20 ≤ Real.log T₂ := Real.log_le_log (by norm_num) (by linarith)
      have := mul_le_mul_of_nonneg_left this hd0.le
      linarith only [this, hdR]
    have hN₁ : (xiPosZeroCount T₁ : ℝ) ≤ (xiPosZeroCount (U ^ α + 1) : ℝ) := by
      exact_mod_cast Finset.sum_le_sum_of_subset (stripFinsetPos_mono hT₁21)
    have hdN₁ : d * (xiPosZeroCount T₁ : ℝ)
        ≤ R / Real.log 20 * (xiPosZeroCount (U ^ α + 1) : ℝ) :=
      mul_le_mul hdle hN₁ (Nat.cast_nonneg _) (by positivity)
    have htail₁ : offLineTail d T₁ ≤ 1 / 2 * (xiPosZeroCount (U ^ α + 1) : ℝ) :=
      ((offLineTail_anti hd0.le).trans (offLineTail_zero_le_half T₁)).trans
        (by linarith only [hN₁])
    -- the gate constant
    have hlc0 : 0 ≤ Real.log (c₁ + c₁ * (η / 8)) :=
      Real.log_nonneg (by linarith only [hc₁, hε0])
    have hlc : (T₂ - T₁) / 2 * Real.log (c₁ + c₁ * (η / 8))
        ≤ T₂ / 2 * (Real.log c₁ + η / 8) := by
      have h1 : (T₂ - T₁) / 2 * Real.log (c₁ + c₁ * (η / 8))
          ≤ T₂ / 2 * Real.log (c₁ + c₁ * (η / 8)) :=
        mul_le_mul_of_nonneg_right (by linarith) hlc0
      exact h1.trans (mul_le_mul_of_nonneg_left hlogε (by linarith))
    have hlogU' : Real.log T₂ ≤ Real.log U := Real.log_le_log (by linarith) hT₂U
    have hKlog : K * (Real.log T₂ + Real.log Mb) ≤ 6 * K * Real.log U := by
      have : Real.log T₂ + Real.log Mb ≤ 6 * Real.log U := by linarith only [hlogMb, hlogU']
      have := mul_le_mul_of_nonneg_left this hK.le
      linarith only [this]
    have hmain : 4 * Real.pi * offLineTail d T₂
        ≤ T₂ * B + 2 * C + 12 * K * Real.log U
          + 4 * Real.pi * (R / Real.log 20) * (xiPosZeroCount (U ^ α + 1) : ℝ)
          + 4 * Real.pi * (1 / 2 * (xiPosZeroCount (U ^ α + 1) : ℝ)) := by
      have e1 : 2 * Real.pi * (R * T₂ * (1 / (2 * Real.pi) - ε')) = R * T₂ - T₂ * (η / 16) := by
        have : 2 * Real.pi * (R * T₂ * (1 / (2 * Real.pi) - ε'))
            = R * T₂ - T₂ * ((4 * Real.pi * R * ε') / 2) := by
          field_simp
          ring
        rw [this, hε'R]
        ring
      have h2π0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      have h2π := mul_le_mul_of_nonneg_left hdN₂ h2π0
      rw [e1] at h2π
      have hA := mul_le_mul_of_nonneg_left hbridge h2π0
      have hdN₁' := mul_le_mul_of_nonneg_left hdN₁ h2π0
      have htail₁' := mul_le_mul_of_nonneg_left htail₁ h2π0
      have hBdef : T₂ * B = T₂ * Real.log c₁ - 2 * R * T₂ + T₂ * (η / 4) := by rw [hB]; ring
      linarith only [hc, hA, hlc, hKlog, hdN₁', htail₁', h2π, hBdef]
    have hTB : T₂ * B ≤ (U - 1) * B + |B| := by
      rcases le_or_gt 0 B with hB0 | hB0
      · have : T₂ * B ≤ U * B := mul_le_mul_of_nonneg_right hT₂U hB0
        rw [abs_of_nonneg hB0]
        linarith
      · have h0 : 0 ≤ (T₂ - (U - 1)) * (-B) := mul_nonneg (by linarith) (by linarith)
        rw [abs_of_neg hB0]
        linarith only [h0, hB0]
    have hlogU1 : 0 < Real.log (U - 1) := Real.log_pos (by linarith)
    have hmono : offLineTail (R / Real.log (U - 1)) (U - 1) ≤ offLineTail d T₂ := by
      have hd' : d ≤ R / Real.log (U - 1) := by
        rw [le_div_iff₀ hlogU1]
        have : Real.log (U - 1) ≤ Real.log T₂ := Real.log_le_log (by linarith) hT₂big.le
        have := mul_le_mul_of_nonneg_left this hd0.le
        linarith only [this, hdR]
      exact (offLineTail_anti hd').trans (offLineTail_mono hT₂big.le)
    have hη1 : η / 4 ≤ η / 4 * (U - 1) := by
      have h0 : 0 ≤ η / 4 * (U - 2) := mul_nonneg (by positivity) (by linarith)
      linarith only [h0]
    have hfin : (Real.log c₁ - 2 * R + η) * (U - 1) = (U - 1) * B + 3 * (η / 4 * (U - 1)) := by
      rw [hB]; ring
    have hπmono := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    rw [hfin]
    have hcount := hcountU.1
    have hid : 4 * Real.pi * (R / Real.log 20) * (xiPosZeroCount (U ^ α + 1) : ℝ)
        + 4 * Real.pi * (1 / 2 * (xiPosZeroCount (U ^ α + 1) : ℝ))
        = (4 * Real.pi * (R / Real.log 20) + 2 * Real.pi) * (xiPosZeroCount (U ^ α + 1) : ℝ) := by
      ring
    have hηsplit : η / 2 / 4 * (U - 1) + η / 8 * (U - 1) = η / 4 * (U - 1) := by ring
    linarith only [hπmono, hmain, hTB, hlogU, hη1, hfin, hDU₀, hcount, hid, hηsplit]
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  have := hshift.eventually hev
  simpa using this


/-! ## The tail law with rate `21R/25` -/

/-- `g(R) = −log(1 − e^{−21R/25})`. -/
def selbergTailRateUpper (R : ℝ) : ℝ := -Real.log (1 - Real.exp (-(21 * R / 25)))

theorem selbergTailRateUpper_add_nonneg {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    0 ≤ selbergTailRateUpper R + η := by
  unfold selbergTailRateUpper
  have h := ZetaGateProductAFE.exp_neg_lt_one (show 0 < 21 * R / 25 by positivity)
  have hpos : 0 < 1 - Real.exp (-(21 * R / 25)) := by linarith
  have : Real.log (1 - Real.exp (-(21 * R / 25))) ≤ 0 :=
    Real.log_nonpos hpos.le (by linarith [Real.exp_pos (-(21 * R / 25))])
  linarith

theorem log_selbergBlockConstUpper_sub {R : ℝ} (hR : 0 < R) :
    Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) - 2 * R = selbergTailRateUpper R := by
  have h2 := ZetaGateProductAFE.exp_neg_lt_one (show 0 < 21 * R / 25 by positivity)
  unfold ZetaGateProductAFE.selbergBlockConstUpper selbergTailRateUpper
  rw [Real.log_div (Real.exp_pos _).ne' (by linarith), Real.log_exp]
  ring

/-- **The tail law with Selberg's twisted mollifier of length `U^{21/50}`.** -/
theorem eventually_offLineTail_le_selberg_upper {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ V in atTop,
      4 * Real.pi * offLineTail (R / Real.log V) V ≤ (selbergTailRateUpper R + η) * V := by
  have h := eventually_offLineTail_le_of_zetaGateFrom (α := (49 : ℝ) / 50) (by norm_num)
    (by norm_num) hR (ZetaGateProductAFE.one_le_selbergBlockConstUpper hR) hη
    (ZetaGateProductAFE.zetaMollifiedMeanSquareGateFrom_selberg_upper hR)
  rwa [log_selbergBlockConstUpper_sub hR] at h

theorem eventually_offLineCountBeyond_le_selberg_upper {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ V in atTop,
      offLineCountBeyond (2 * (R / Real.log V)) V
        ≤ (selbergTailRateUpper R + η) / (4 * Real.pi * R) * (V * Real.log V) :=
  eventually_offLineCountBeyond_le_of_tail hR (eventually_offLineTail_le_selberg_upper hR hη)

theorem eventually_goodCriticalScaleDiscs_selberg_upper {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ V in atTop, ∀ K : ℕ,
      3 * (2 * R / Real.log V) * K + 2 * R / Real.log V ≤ V →
      V ≤ 3 * (2 * R / Real.log V) * K + 4 * (2 * R / Real.log V) →
      (K : ℝ) - (3 * K + 4) * (selbergTailRateUpper R + η) / (2 * Real.pi)
          ≤ ((Finset.Icc 1 K \ badCriticalScaleDiscs (2 * R / Real.log V) K).card : ℝ) ∧
      ∀ hr : 0 < 2 * R / Real.log V,
        ∀ k ∈ Finset.Icc 1 K \ badCriticalScaleDiscs (2 * R / Real.log V) K,
          ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter (2 * R / Real.log V) k)
              (2 * R / Real.log V), xi ζ ≠ 0,
            ‖(xiDiscDatum (criticalScaleCenter (2 * R / Real.log V) k) (2 * R / Real.log V) hr
              hne).circlePhase.datum.adjointHankelSeam‖ < 1 :=
  eventually_goodCriticalScaleDiscs_of_tail hR (selbergTailRateUpper_add_nonneg hR hη)
    (eventually_offLineTail_le_selberg_upper hR hη)

theorem eventually_volume_kappaShadow_le_selberg_upper {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∀ᶠ V in atTop,
      volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
          κ / Real.log V ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} ≤
        ENNReal.ofReal ((selbergTailRateUpper (κ / 2) + η) * (V + 1) / Real.pi) :=
  eventually_volume_kappaShadow_le_of_tail hκ
    (eventually_offLineTail_le_selberg_upper (by positivity : 0 < κ / 2) hη)

end

end RHTower
