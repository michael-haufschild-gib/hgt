/-
# The single-input explicit `(L)` constant

Every explicit constant in the mollified-Littlewood lane rested on two external inputs: the
mollified mean square on a Levinson abscissa and the on-line proportion `κ`. The corpus's Levinson
consumer chain derives the proportion from the mean square of `(ζ+λζ')Ψ`
(`eventually_oddFiber_ge_of_gate_general`, any target `κ₀ < 1 − log c₂/R`), and the credited
ceiling `exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare` derives the
off-line first moment from the mean square of `ζΨ`. With the census bridges
(`OffLineMomentCensusBridge`: `2·Right = N + N₀`, odd fibres `≤ N₀`, window comparisons) and the
Riemann–von Mangoldt asymptotic, the two are assembled into

  `4π · Σ_{Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (log c₁ − (1 + κ₀) R + η) · V`   eventually,

for every `η > 0` (`eventually_offLineMoment_le_of_gates`): both inputs are now instances of one
theorem type, the twisted mollified mean square on the Levinson line.
-/
import GaloisForLFunctions.RHTower.ZetaOffLineFirstMomentLineCount
import GaloisForLFunctions.RHTower.ZetaLineLogMeanLittlewoodBudget
import GaloisForLFunctions.RHTower.OffLineMomentCensusBridge
import GaloisForLFunctions.RHTower.LevinsonOddFiberDensityGeneral
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- **The window arithmetic of the single-input `(L)` constant.** With `w = ½ − σ₀`, `wL = R`,
the credited ceiling `2π(M_Z + w S_Z) ≤ ½(T₂−T₁) lc + C + K(L + LMb)`, the count credit
`S_Z ≥ (1+κ₀+δ)N(T₂)/2 − N(T₁)`, the moment comparison `M(T₂) ≤ M(T₁) + M_Z`, and the
Riemann–von Mangoldt lower bound `N(T₂) ≥ (1/2π − ε') T₂ L`:

`4π M(T₂) ≤ T₂ (lc − R(1+κ₀+δ)(1 − 2πε')) + 12 K L + 2C + 4π M(T₁) + 4π R N(T₁)/L`. -/
theorem offLineMoment_window_arith {R L w T₁ T₂ C K LMb lc κ₀ δ ε' NT₁ NT₂ S MZ M₁ M₂ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hwL : w * L = R) (hT₁ : 0 ≤ T₁) (hT : T₁ ≤ T₂)
    (hK : 0 ≤ K) (hLMb : LMb ≤ 5 * L) (hlc : 0 ≤ lc) (hκ₀ : 0 ≤ κ₀) (hδ : 0 ≤ δ)
    (hε' : 0 ≤ ε') (hNT₁ : 0 ≤ NT₁) (hNT₂ : 0 ≤ NT₂)
    (hceil : 2 * Real.pi * (MZ + w * S) ≤ (T₂ - T₁) / 2 * lc + C + K * (L + LMb))
    (hS : (1 + κ₀ + δ) * NT₂ / 2 - NT₁ ≤ S)
    (hM : M₂ ≤ M₁ + MZ)
    (hrvm : (1 / (2 * Real.pi) - ε') * (T₂ * L) ≤ NT₂) :
    4 * Real.pi * M₂
      ≤ T₂ * (lc - R * (1 + κ₀ + δ) * (1 - 2 * Real.pi * ε')) + 12 * K * L + 2 * C
        + 4 * Real.pi * M₁ + 4 * Real.pi * R * NT₁ / L := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hw : w = R / L := by
    field_simp
    linarith [hwL]
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hcoef : 0 ≤ 1 + κ₀ + δ := by linarith
  set P : ℝ := w * ((1 + κ₀ + δ) * NT₂) with hP
  set A : ℝ := R * (1 + κ₀ + δ) * (1 - 2 * Real.pi * ε') * T₂ with hA
  have h1 : w * ((1 + κ₀ + δ) * NT₂ / 2 - NT₁) ≤ w * S := mul_le_mul_of_nonneg_left hS hw0
  have h1' : P / 2 - w * NT₁ ≤ w * S := by
    have hid : w * ((1 + κ₀ + δ) * NT₂ / 2 - NT₁) = P / 2 - w * NT₁ := by rw [hP]; ring
    linarith [h1, hid]
  have hrvm' : (1 + κ₀ + δ) * ((1 / (2 * Real.pi) - ε') * (T₂ * L))
      ≤ (1 + κ₀ + δ) * NT₂ := mul_le_mul_of_nonneg_left hrvm hcoef
  have h2 : w * ((1 + κ₀ + δ) * ((1 / (2 * Real.pi) - ε') * (T₂ * L))) ≤ P :=
    mul_le_mul_of_nonneg_left hrvm' hw0
  have hkey : w * ((1 + κ₀ + δ) * ((1 / (2 * Real.pi) - ε') * (T₂ * L)))
      = A / (2 * Real.pi) := by
    rw [hA, ← hwL]
    field_simp
    try ring
  have hPA : A / (2 * Real.pi) ≤ P := by rw [← hkey]; exact h2
  have hhalf : A / (4 * Real.pi) = (A / (2 * Real.pi)) / 2 := by ring
  have hwS : A / (4 * Real.pi) - w * NT₁ ≤ w * S := by linarith [h1', hPA, hhalf]
  have hwS2 : 2 * Real.pi * (A / (4 * Real.pi) - w * NT₁) ≤ 2 * Real.pi * (w * S) :=
    mul_le_mul_of_nonneg_left hwS (by positivity)
  have hsimp : 2 * Real.pi * (A / (4 * Real.pi) - w * NT₁)
      = A / 2 - 2 * Real.pi * R * NT₁ / L := by
    rw [hw]
    field_simp
    ring
  rw [hsimp] at hwS2
  have hKb : K * LMb ≤ K * (5 * L) := mul_le_mul_of_nonneg_left hLMb hK
  have hT1lc : 0 ≤ T₁ * lc := mul_nonneg hT₁ hlc
  have hMπ : 2 * Real.pi * M₂ ≤ 2 * Real.pi * (M₁ + MZ) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have hexp : T₂ * (lc - R * (1 + κ₀ + δ) * (1 - 2 * Real.pi * ε')) = T₂ * lc - A := by
    rw [hA]
    ring
  rw [hexp]
  have hgoal : 4 * Real.pi * R * NT₁ / L = 2 * (2 * Real.pi * R * NT₁ / L) := by ring
  linarith [hceil, hwS2, hKb, hT1lc, hMπ, hgoal]


/-- **The mollified mean-square gate for `ζΨ`.** For every `ε > 0` and all large `U` there is an
admissible window `[T₁,T₂] ⊆ [20,U]`, `T₂ > U − 1`, and a real unit-head bounded mollifier, with
the mean square of `ζΨ` on `σ₀ = ½ − R/log T₂` at most `(c+ε)(T₂−T₁)`. -/
def ZetaMollifiedMeanSquareGate (R c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop, ∃ (T₁ T₂ σ₀ Mb : ℝ) (b : ℕ → ℂ) (N : ℕ),
    T₁ ∈ Set.Icc (20 : ℝ) 21 ∧ T₂ ∈ Set.Ioc (U - 1) U ∧
    1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
    (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧
    1 ≤ Mb ∧ (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb ∧
    Real.log Mb ≤ 5 * Real.log T₂ ∧
    1 / 4 ≤ σ₀ ∧ σ₀ < 1 / 2 ∧ (1 / 2 - σ₀) * Real.log T₂ = R ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
    (∫ t in T₁..T₂, ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (c + ε) * (T₂ - T₁)

set_option maxHeartbeats 1000000 in
/-- **The single-input explicit `(L)` constant.** From the two mollified mean-square gates on the
same Levinson abscissa, `ζΨ` with constant `c₁` and `(ζ+λζ')Ψ` with constant `c₂`, and any target
`κ₀ + 2δ < 1 − log c₂/R`:

`4π · Σ_{Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (log c₁ − (1 + κ₀) R + η) · V`  eventually, for every `η > 0`. -/
theorem eventually_offLineMoment_le_of_gates {κ₀ R c₁ c₂ δ η : ℝ} (hκ₀ : 0 ≤ κ₀) (hR : 0 < R)
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hδ : 0 < δ) (hmargin : κ₀ + 2 * δ < 1 - Real.log c₂ / R)
    (hη : 0 < η) (hg₁ : ZetaMollifiedMeanSquareGate R c₁) (hg₂ : LevinsonMeanSquareGate R c₂) :
    ∀ᶠ V in atTop,
      4 * Real.pi * offLineMoment V ≤ (Real.log c₁ - (1 + κ₀) * R + η) * V := by
  classical
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨C, K, hC, hK, hceil⟩ :=
    exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare
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
  set ε' : ℝ := η / (16 * Real.pi * R * (2 + κ₀ + δ)) with hε'def
  have hε'0 : 0 < ε' := by positivity
  have hε'bound : 2 * Real.pi * ε' * R * (1 + κ₀ + δ) ≤ η / 8 := by
    have hid : 2 * Real.pi * ε' * R * (1 + κ₀ + δ)
        = η * ((1 + κ₀ + δ) / (8 * (2 + κ₀ + δ))) := by
      rw [hε'def]
      field_simp
      ring
    rw [hid]
    have hfrac : (1 + κ₀ + δ) / (8 * (2 + κ₀ + δ)) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    calc η * ((1 + κ₀ + δ) / (8 * (2 + κ₀ + δ))) ≤ η * (1 / 8) :=
          mul_le_mul_of_nonneg_left hfrac hη.le
      _ = η / 8 := by ring
  obtain ⟨T₀, _, hrvm⟩ := exists_xiZeroCount_close ε' hε'0
  obtain ⟨U₁, hU₁⟩ := Filter.eventually_atTop.mp
    (eventually_oddFiber_ge_of_gate_general hκ₀ hR hc₂ hδ hmargin hg₂)
  set B : ℝ := Real.log c₁ - (1 + κ₀) * R + η / 4 with hBdef
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
      4 * Real.pi * offLineMoment (U - 1) ≤ (Real.log c₁ - (1 + κ₀) * R + η) * (U - 1) := by
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
    -- the count credit
    have hbridge1 := rightHalfOrderSum_sub_le_zetaZeroSum hT12.le Z hZ
    have hbridge2 := offLineMoment_le_add_zetaZeroMoment hT12.le Z hZ
    have hrefl₂ : (2 * rightHalfOrderSum T₂ : ℝ)
        = (xiPosZeroCount T₂ : ℝ) + (xiPosCriticalZeroCount T₂ : ℝ) := by
      exact_mod_cast two_mul_rightHalfOrderSum T₂
    have hR₁nat : rightHalfOrderSum T₁ ≤ xiPosZeroCount T₁ := by
      unfold rightHalfOrderSum xiPosZeroCount
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hR₁ : (rightHalfOrderSum T₁ : ℝ) ≤ (xiPosZeroCount T₁ : ℝ) := by exact_mod_cast hR₁nat
    have hprop := hU₁ T₂ hT₂U₁
    have hodd : (xiOddFiberCount T₂ : ℝ) ≤ (xiPosCriticalZeroCount T₂ : ℝ) := by
      exact_mod_cast xiOddFiberCount_le_xiPosCriticalZeroCount T₂
    have hS : (1 + κ₀ + δ) * (xiPosZeroCount T₂ : ℝ) / 2 - (xiPosZeroCount T₁ : ℝ)
        ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
      linarith only [hbridge1, hrefl₂, hR₁, hprop, hodd]
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
      (Real.log_nonneg (by linarith)) hκ₀ hδ.le hε'0.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hc hS hbridge2 hN₂
    have hmono := offLineMoment_mono (le_of_lt hT₂big)
    have hbr : Real.log (c₁ + ε) - R * (1 + κ₀ + δ) * (1 - 2 * Real.pi * ε') ≤ B := by
      have hid : R * (1 + κ₀ + δ) * (1 - 2 * Real.pi * ε')
          = R * (1 + κ₀) + R * δ - 2 * Real.pi * ε' * R * (1 + κ₀ + δ) := by ring
      have hRδ : 0 ≤ R * δ := mul_nonneg hR.le hδ.le
      rw [hBdef]
      linarith only [hlogε, hε'bound, hid, hRδ]
    have hT₂B : T₂ * (Real.log (c₁ + ε) - R * (1 + κ₀ + δ) * (1 - 2 * Real.pi * ε'))
        ≤ T₂ * B := mul_le_mul_of_nonneg_left hbr (by linarith)
    have hTB : T₂ * B ≤ (U - 1) * B + |B| := by
      rcases le_or_gt 0 B with hB0 | hB0
      · have : T₂ * B ≤ U * B := mul_le_mul_of_nonneg_right hT₂U hB0
        rw [abs_of_nonneg hB0]
        linarith only [this]
      · have h0 : 0 ≤ (T₂ - (U - 1)) * (-B) := mul_nonneg (by linarith only [hT₂big]) (by linarith only [hB0])
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
    have hBη : (Real.log c₁ - (1 + κ₀) * R + η) * (U - 1) = (U - 1) * B + 3 * (η / 4 * (U - 1)) := by
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
