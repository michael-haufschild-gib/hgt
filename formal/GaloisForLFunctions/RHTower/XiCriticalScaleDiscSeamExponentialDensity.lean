import GaloisForLFunctions.RHTower.XiCriticalScaleDiscSeamSelbergDensity
import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensity
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBoxDensity

/-!
# Exponentially few critical-scale right discs fail to contract

Take the discs of radius `r = 2a/log U` centred at `1/2 + 2r + 3rk·i` with heights in the window
`[T₁, T₂]` (`criticalScaleWindow`); a disc is exceptional when it contains a zero of `ξ`, and off
the exceptional discs the adjoint seam of the `ξ` phase is a strict contraction.

With the admissible heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` of the exponential
near-line density (`exists_selberg_exponential_nearLine_zeroDensity`), one pair of heights serves
every radius at once, and

`#exceptional discs ≤ B e^{−a/1200} · #discs`   for all `1 ≤ a ≤ (log U − 2)/2`, `16a ≤ log U`,

with `B = 6A/π + 1` (`exists_criticalScale_badDisc_exponential_le`). Every exceptional disc holds a
zero with `Re ρ ≥ 1/2 + r` and different discs hold different zeros; the window holds at least
`(T₂ − T₁) log U/(6a) − 2` discs.
-/

noncomputable section

open Complex Metric Set Filter

namespace RHTower

/-- The arithmetic of the exponential proportion. -/
theorem badDisc_exponential_arith {X L a A K B E U : ℝ} (hX : U / 5 ≤ X) (hL : 0 < L)
    (ha1 : 1 ≤ a) (haL : a ≤ L) (hB : 6 * A / Real.pi ≤ B) (hB0 : 0 ≤ B)
    (hE : 0 < E) (hE1 : E ≤ 1) (hUE : Real.exp (2399 / 2400 * L) ≤ U * E)
    (hbig : K / (2 * Real.pi) * L + 2 * B ≤ B / 60 * Real.exp (2399 / 2400 * L)) :
    L / (2 * Real.pi * a) * (X * (A * E) + K * L) ≤ B * E * (X * L / (6 * a) - 2) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have ha0 : 0 < a := by linarith
  have hA : A / (2 * Real.pi) ≤ B / 12 := by
    rw [div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ hπ).mp hB
    nlinarith
  have hX0 : 0 ≤ X := by
    have hU : 0 ≤ U * E := le_trans (Real.exp_pos _).le hUE
    have : 0 ≤ U := by
      by_contra h; push Not at h
      have := mul_neg_of_neg_of_pos h hE; linarith
    linarith
  -- main part
  have h1 : L / (2 * Real.pi * a) * (X * (A * E)) ≤ B / 12 * E * X * L / a := by
    have e : L / (2 * Real.pi * a) * (X * (A * E)) = A / (2 * Real.pi) * E * X * L / a := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ ha0.le
    have := mul_le_mul_of_nonneg_right hA (show 0 ≤ E * X * L by positivity)
    nlinarith
  -- remainder
  have h2 : L / (2 * Real.pi * a) * (K * L) + 2 * B * E ≤ B / 12 * E * X * L / a := by
    have hEX : B / 60 * Real.exp (2399 / 2400 * L) ≤ B / 12 * E * X := by
      have h1' : B / 60 * Real.exp (2399 / 2400 * L) ≤ B / 60 * (U * E) :=
        mul_le_mul_of_nonneg_left hUE (by positivity)
      have h2' : B / 60 * (U * E) ≤ B / 12 * E * X := by
        have := mul_le_mul_of_nonneg_left hX (show 0 ≤ B / 12 * E by positivity)
        nlinarith
      linarith
    have hk : K / (2 * Real.pi) * L + 2 * B ≤ B / 12 * E * X := hbig.trans hEX
    have e : B / 12 * E * X * L / a = (B / 12 * E * X) * (L / a) := by ring
    rw [e]
    have hLa : 1 ≤ L / a := by rw [le_div_iff₀ ha0]; linarith
    have hKterm : L / (2 * Real.pi * a) * (K * L) = K / (2 * Real.pi) * L * (L / a) := by
      field_simp
    rw [hKterm]
    have h2B : 2 * B * E ≤ 2 * B * (L / a) := by
      have : E ≤ L / a := le_trans hE1 hLa
      nlinarith
    have := mul_le_mul_of_nonneg_right hk (show 0 ≤ L / a by positivity)
    nlinarith
  have e : B * E * (X * L / (6 * a) - 2) = 2 * (B / 12 * E * X * L / a) - 2 * B * E := by
    field_simp; ring
  rw [e, mul_add]
  linarith

/-- **Exponentially few critical-scale right discs are exceptional.** -/
theorem exists_criticalScale_badDisc_exponential_le :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ a : ℝ, 1 ≤ a → 2 * a + 2 ≤ Real.log U → 16 * a ≤ Real.log U →
          ((badCriticalScaleWindowDiscs (2 * a / Real.log U) T₁ T₂).card : ℝ) ≤
            B * Real.exp (-(a / 1200)) *
              (criticalScaleWindow (2 * a / Real.log U) T₁ T₂).card := by
  obtain ⟨A, K, hA, hK, hdens⟩ := exists_selberg_exponential_nearLine_zeroDensity
  set B : ℝ := 6 * A / Real.pi + 1 with hBdef
  have hB0 : 0 < B := by positivity
  refine ⟨B, hB0, ?_⟩
  have hbig := eventually_mul_log_add_pow_le_exp 1 (60 * (K / (2 * Real.pi) + 2 * B) / B)
    (show (0 : ℝ) < 2399 / 2400 by norm_num)
  filter_upwards [hdens, hbig, eventually_ge_atTop 100] with U hU hUbig hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hcount⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha1 ha2 ha16 => ?_⟩
  have hU0 : 0 < U := by linarith
  set L : ℝ := Real.log U with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  set r : ℝ := 2 * a / L with hr
  have hr0 : 0 < r := by positivity
  have hr8 : r ≤ 1 / 8 := by rw [hr, div_le_iff₀ hL0]; linarith only [ha16]
  have hT₁0 : 0 < T₁ := by linarith only [hT₁.1, hU100]
  have hT₁20 : 20 ≤ T₁ := by linarith only [hT₁.1, hU100]
  have hT12 : T₁ < T₂ := by linarith only [hT₁.2, hT₂.1, hU100]
  have ha0 : 0 < a := by linarith only [ha1]
  set E := Real.exp (-(a / 1200)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ha0])
  have hUE : Real.exp (2399 / 2400 * L) ≤ U * E := by
    have e : U = Real.exp L := (Real.exp_log hU0).symm
    rw [e, hE, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [ha2, hL0]
  have hbig' : K / (2 * Real.pi) * L + 2 * B ≤ B / 60 * Real.exp (2399 / 2400 * L) := by
    rw [pow_one] at hUbig
    have h1 : K / (2 * Real.pi) * L + 2 * B ≤ (K / (2 * Real.pi) + 2 * B) * (L + 3) := by
      have hk0 : 0 ≤ K / (2 * Real.pi) := by positivity
      have hd : (K / (2 * Real.pi) + 2 * B) * (L + 3) - (K / (2 * Real.pi) * L + 2 * B) =
          3 * (K / (2 * Real.pi)) + 2 * B * (L + 2) := by ring
      have hd0 : 0 ≤ 3 * (K / (2 * Real.pi)) + 2 * B * (L + 2) := by positivity
      linarith only [hd, hd0]
    have h2 : (K / (2 * Real.pi) + 2 * B) * (L + 3) =
        B / 60 * (60 * (K / (2 * Real.pi) + 2 * B) / B * (L + 3)) := by
      field_simp
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_left hUbig (show 0 ≤ B / 60 by positivity)
    linarith only [h1, this]
  have harith := badDisc_exponential_arith (X := T₂ - T₁) (U := U)
    (by linarith only [hT₁.2, hT₂.1, hU100]) hL0 ha1 (by linarith only [ha2, ha1])
    (by rw [hBdef]; exact le_add_of_nonneg_right zero_le_one) hB0.le hE0 hE1 hUE hbig'
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  have hbad := card_badCriticalScaleWindowDiscs_le hr0 hr8 hT₁0
    (by linarith only [hr8, hT₂.1, hU100]) hT12.le hZ
  have hc := hcount a ha1 ha2 Z hZ
  have hfilter : Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re) =
      Z.filter (fun w => 1 / 2 + r ≤ w.re) := Finset.filter_congr fun w _ => by rw [hr]
  rw [hfilter] at hc
  set S := ∑ w ∈ Z.filter (fun w => 1 / 2 + r ≤ w.re), ((analyticOrderAt riemannZeta w).toNat : ℝ)
    with hS
  have hSle : S ≤ L / (2 * Real.pi * a) * ((T₂ - T₁) * (A * Real.exp (-(a / 1200))) + K * L) := by
    have hpos : 0 < 2 * Real.pi * (a / L) := by positivity
    have e : L / (2 * Real.pi * a) = 1 / (2 * Real.pi * (a / L)) := by field_simp
    rw [e, one_div_mul_eq_div, le_div_iff₀ hpos]
    have e2 : S * (2 * Real.pi * (a / L)) = 2 * Real.pi * ((a / L) * S) := by ring
    rw [e2]
    exact hc
  have hwin := card_criticalScaleWindow_ge (T₂ := T₂) hr0 hT₁0.le
  have hwin' : (T₂ - T₁) * L / (6 * a) - 2 ≤ ((criticalScaleWindow r T₁ T₂).card : ℝ) := by
    have e : (T₂ - T₁) / (3 * r) = (T₂ - T₁) * L / (6 * a) := by rw [hr]; field_simp; ring
    rw [← e]; exact hwin
  have hwinE : B * E * ((T₂ - T₁) * L / (6 * a) - 2) ≤
      B * E * ((criticalScaleWindow r T₁ T₂).card : ℝ) :=
    mul_le_mul_of_nonneg_left hwin' (by positivity)
  calc ((badCriticalScaleWindowDiscs r T₁ T₂).card : ℝ) ≤ S := hbad
    _ ≤ _ := hSle
    _ ≤ _ := harith
    _ ≤ _ := hwinE

end RHTower
