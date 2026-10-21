import GaloisForLFunctions.ArithmeticIncidencePositivity.HarmonicWideMicroFold

/-!
# The overlapping strips of `2` and `3` at the window `23/40`

At `r = 23/40` the strip `S₂ = [log 2 − r, r]` of the atom of `2` has half-width
`η = r − ½ log 2 ≈ 0.2284` and contains the strip `S₃ = [log 3 − r, r]` of the atom of `3`, of width
`2r − log 3 ≈ 0.0514`; `e^{2r} < 4`, so these two atoms are the whole prime side. The wide fold with
`S₃ × S₃` fully withheld (`OverlappingPrimeStripsJointHarnack`) no longer reaches the atom of `2` here:
the withheld band is eight times wider than at `221/400`.

The harmonic micro-fold (`HarmonicWideMicroFold`) shares the band instead.
* The atom of `3` takes `θ = 69/100` of the surplus of `S₃ × S₃`, enough at
  `λ₃ ≥ 1.849` (`twentyThreeFortieths_threeStrip_lam`).
* The same-distance groups of the band keep the rate `ρ R₋`, `ρ = 62/131`.
* Off the band each group recovers `0.73(u + v)`, respectively `0.73|u − v|`, of its excess: slope
  `2.19`, `κ = 1`. The conditions `2.19(u + v) ≤ R₋` (`twentyThreeFortieths_sameCondition`),
  `2.19|u − v| ≤ R₊` (`twentyThreeFortieths_crossCondition`) and the band condition
  (`twentyThreeFortieths_bandCondition`) are checked by monotonicity of the drops of `ω` on three pieces.

The potential (`twentyThreeFortieths_potential`): in the gauge `1/100 + t` the folded weight integrates to
at least `1` at every folded point. Its lower bound is
`2u + 0.02ℓ − … + (β + u)(Q₂ + Q₃) + 1.46 RecG − band`.
* The window ratio `ℓ = log((u + η)/u)` is bounded below by the tangent of `log` at `2`.
* The two certificates are quartic polynomials in `u`, positive on `[0, b]` (`twentyThreeFortieths_regimeOne`)
  and on `[b, η]` (`twentyThreeFortieths_regimeTwo`), with minimum `≈ 0.006` at `u = η`.

The joint Harnack inequality follows
(`two_mul_primeTwoThreeShifts_le_stripSurplus_twentyThreeFortieths`).
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The window `r = 23/40` -/

/-- The window data at `r = 23/40`: `η = r − ½ log 2`, `b = log 3 − r − ½ log 2`, `2p = log 2 − 2η`. -/
theorem twentyThreeFortieths_window :
    0.2284264096 ≤ 23 / 40 - Real.log 2 / 2 ∧ 23 / 40 - Real.log 2 / 2 ≤ 0.2284264099 ∧
      0.1770386096 ≤ Real.log 3 - 23 / 40 - Real.log 2 / 2 ∧
      Real.log 3 - 23 / 40 - Real.log 2 / 2 ≤ 0.1770387099 ∧
      0.2362943606 ≤ Real.log 2 - 2 * (23 / 40 - Real.log 2 / 2) ∧
      0.46472077045 ≤ Real.log 2 - (23 / 40 - Real.log 2 / 2) ∧
      Real.log 2 - (23 / 40 - Real.log 2 / 2) ≤ 0.4647207712 ∧
      Real.log 2 - 2 * (Real.log 3 - 23 / 40 - Real.log 2 / 2) ≤ 0.3390699616 ∧
      0.3540772192 ≤ 2 * (Real.log 3 - 23 / 40 - Real.log 2 / 2) ∧
      (23 / 40 - Real.log 2 / 2) - (Real.log 3 - 23 / 40 - Real.log 2 / 2) ≤ 0.0513878 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  obtain ⟨h3, h4⟩ := log_three_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- `ω` at the points of the window, from `ω₂ ≤ ω ≤ ω₂ + t³/250` (`archLevyDensity_secondOrder_bounds`). -/
theorem twentyThreeFortieths_omega_rational :
    2.4324 ≤ archLevyDensity 0.2284264099 ∧ archLevyDensity 0.46472077045 ≤ 1.30989 ∧
      3.5795 ≤ archLevyDensity 0.15 ∧ archLevyDensity 0.3862943606 ≤ 1.53188 ∧
      10.2488 ≤ archLevyDensity 0.05 ∧ archLevyDensity 0.2862943606 ≤ 1.98803 ∧
      1.3284 ≤ archLevyDensity 0.4568528197 ∧
      1.8701 ≤ archLevyDensity 0.3068528197 ∧ archLevyDensity 0.5431471803 ≤ 1.15067 ∧
      9.97 ≤ archLevyDensity 0.0513878 ∧ archLevyDensity 0.2362943606 ≤ 2.36 ∧
      1.71 ≤ archLevyDensity 0.3390699616 ∧ archLevyDensity 0.3540772192 ≤ 1.6511 := by
  have b1 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.2284264099 by norm_num) (by norm_num)).1
  have b2 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.46472077045 by norm_num) (by norm_num)).2
  have b3 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.15 by norm_num) (by norm_num)).1
  have b4 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.3862943606 by norm_num) (by norm_num)).2
  have b5 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.05 by norm_num) (by norm_num)).1
  have b6 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.2862943606 by norm_num) (by norm_num)).2
  have b7 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.4568528197 by norm_num) (by norm_num)).1
  have b8 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.3068528197 by norm_num) (by norm_num)).1
  have b9 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.5431471803 by norm_num) (by norm_num)).2
  have b10 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.0513878 by norm_num) (by norm_num)).1
  have b11 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.2362943606 by norm_num) (by norm_num)).2
  have b12 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.3390699616 by norm_num) (by norm_num)).1
  have b13 := (archLevyDensity_secondOrder_bounds (show (0 : ℝ) < 0.3540772192 by norm_num) (by norm_num)).2
  norm_num at b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

/-- `ω(log 2) ≤ 0.94323`. -/
theorem archLevyDensity_logTwo_le : archLevyDensity (Real.log 2) ≤ 0.94323 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have hb := (archLevyDensity_secondOrder_bounds (show 0 < Real.log 2 by linarith) (by linarith)).2
  have hi : 1 / (2 * Real.log 2) ≤ 1 / (2 * 0.6931471803) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have k2 : (0.6931471803 : ℝ) ^ 2 ≤ Real.log 2 ^ 2 := pow_le_pow_left₀ (by norm_num) h1.le 2
  have k3 : Real.log 2 ^ 3 ≤ (0.6931471808 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) h2.le 3
  linarith

/-- `log(log 2) − log(log 2 − η) ≤ 0.39983` at `η = 23/40 − ½ log 2`: tangent of `log` at `3/2`. -/
theorem twentyThreeFortieths_logRatio_le :
    Real.log (Real.log 2) - Real.log (Real.log 2 - (23 / 40 - Real.log 2 / 2)) ≤ 0.39983 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  obtain ⟨h3, h4⟩ := log_three_bounds
  have hpos : 0 < Real.log 2 - (23 / 40 - Real.log 2 / 2) := by linarith
  have hL : 0 < Real.log 2 := by linarith
  rw [← Real.log_div hL.ne' hpos.ne']
  have hq : Real.log 2 / (Real.log 2 - (23 / 40 - Real.log 2 / 2)) ≤ 1.4915348 := by
    rw [div_le_iff₀ hpos]; linarith
  have ht := log_le_tangent (div_pos hL hpos) (show (0 : ℝ) < 3 / 2 by norm_num)
  rw [Real.log_div (x := 3) (y := 2) (by norm_num) (by norm_num)] at ht
  have : Real.log 2 / (Real.log 2 - (23 / 40 - Real.log 2 / 2)) / (3 / 2) ≤ 1.4915348 / (3 / 2) :=
    div_le_div_of_nonneg_right hq (by norm_num)
  norm_num at this ht ⊢
  linarith

/-! ### The harmonic conditions on the strip of `2` -/

/-- **The same-distance condition** `2.19 (u + v) ≤ R₋(u, v)` on the folded strip, `u ≠ v`. -/
theorem twentyThreeFortieths_sameCondition {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ (23 / 40 - (Real.log 2 - 23 / 40)) / 2)
    (hv0 : 0 ≤ v) (hv1 : v ≤ (23 / 40 - (Real.log 2 - 23 / 40)) / 2) (huv : u ≠ v) :
    219 / 100 * (u + v) ≤ 1 * wideSameRate (Real.log 2) u v := by
  obtain ⟨hη0, hη1, -, -, h2p, hd0, -, -, -, -⟩ := twentyThreeFortieths_window
  obtain ⟨o1, o2, o3, o4, o5, o6, -, -, -, -, -, -, -⟩ := twentyThreeFortieths_omega_rational
  have hη : (23 / 40 - (Real.log 2 - 23 / 40)) / 2 = 23 / 40 - Real.log 2 / 2 := by ring
  rw [hη] at hu1 hv1
  set η := 23 / 40 - Real.log 2 / 2 with hηdef
  set L := Real.log 2 with hL
  have ht : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
  have hts : |u - v| ≤ u + v := abs_le.mpr ⟨by linarith, by linarith⟩
  have ht2 : |u - v| + (u + v) ≤ 2 * η := by
    rcases le_total u v with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  unfold wideSameRate
  rw [one_mul]
  -- the drop of `ω` over `[η, L − η]`
  have hRη : 1.1225 ≤ archLevyDensity η - archLevyDensity (L - η) := by
    have k1 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : (0 : ℝ) < η))
      (mem_Ioi.mpr (show (0 : ℝ) < 0.2284264099 by norm_num)) hη1
    have k2 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (show (0 : ℝ) < 0.46472077045 by norm_num))
      (mem_Ioi.mpr (by linarith : (0 : ℝ) < L - η)) hd0
    linarith
  by_cases hs : u + v ≤ η
  · have k1 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr ht) (mem_Ioi.mpr (by linarith : 0 < u + v))
      hts
    have k2 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : 0 < u + v))
      (mem_Ioi.mpr (by linarith : 0 < η)) hs
    have k3 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : 0 < L - η))
      (mem_Ioi.mpr (by linarith : 0 < L - (u + v))) (by linarith)
    linarith
  -- past `η`: `|u − v| ≤ τ = 2η − (u + v)` and `L − (u + v) = τ + 2p`
  set τ := 2 * η - (u + v) with hτ
  have hτ0 : 0 < τ := by linarith
  have k1 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr ht) (mem_Ioi.mpr hτ0) (by linarith)
  have hL' : L - (u + v) = τ + (L - 2 * η) := by rw [hτ]; ring
  rw [hL']
  have hΔ : 0 ≤ L - 2 * η := by linarith
  by_cases h15 : 0.15 ≤ τ
  · have hd := archLevyDensity_sub_shift_le hτ0 (show τ ≤ η by linarith) hΔ
    rw [show η + (L - 2 * η) = L - η by ring] at hd
    linarith
  by_cases h05 : 0.05 ≤ τ
  · have hd := archLevyDensity_sub_shift_le hτ0 (show τ ≤ 0.15 by linarith) hΔ
    have k4 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (show (0 : ℝ) < 0.3862943606 by norm_num))
      (mem_Ioi.mpr (by linarith : (0 : ℝ) < 0.15 + (L - 2 * η))) (by linarith)
    linarith
  · have hd := archLevyDensity_sub_shift_le hτ0 (show τ ≤ 0.05 by linarith) hΔ
    have k4 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (show (0 : ℝ) < 0.2862943606 by norm_num))
      (mem_Ioi.mpr (by linarith : (0 : ℝ) < 0.05 + (L - 2 * η))) (by linarith)
    linarith

/-- **The crossing condition** `2.19|u − v| ≤ R₊(u, v)` on the folded strip, `u + v > 0`. -/
theorem twentyThreeFortieths_crossCondition {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ (23 / 40 - (Real.log 2 - 23 / 40)) / 2)
    (hv0 : 0 ≤ v) (hv1 : v ≤ (23 / 40 - (Real.log 2 - 23 / 40)) / 2) (hs : 0 < u + v) :
    219 / 100 * |u - v| ≤ 1 * wideCrossRate (Real.log 2) u v := by
  obtain ⟨hη0, hη1, -, -, h2p, -, -, -, -, -⟩ := twentyThreeFortieths_window
  obtain ⟨-, -, -, -, -, -, o7, o8, o9, -, -, -, -⟩ := twentyThreeFortieths_omega_rational
  have oL := archLevyDensity_logTwo_le
  have hη : (23 / 40 - (Real.log 2 - 23 / 40)) / 2 = 23 / 40 - Real.log 2 / 2 := by ring
  rw [hη] at hu1 hv1
  set η := 23 / 40 - Real.log 2 / 2 with hηdef
  set L := Real.log 2 with hL
  set t := |u - v| with htdef
  have ht0 : 0 ≤ t := abs_nonneg _
  have hts : t ≤ u + v := abs_le.mpr ⟨by linarith, by linarith⟩
  have ht2 : t + (u + v) ≤ 2 * η := by
    rcases le_total u v with h | h
    · rw [htdef, abs_of_nonpos (by linarith)]; linarith
    · rw [htdef, abs_of_nonneg (by linarith)]; linarith
  have htη : t ≤ η := by linarith
  unfold wideCrossRate
  rw [one_mul, ← htdef]
  -- `ω(u + v) ≥ ω(2η − t)` and `L − t = (2η − t) + 2p`
  have k1 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr hs) (mem_Ioi.mpr (by linarith : 0 < 2 * η - t))
    (by linarith)
  have hL' : L - t = (2 * η - t) + (L - 2 * η) := by ring
  rw [hL']
  have hΔ : 0 ≤ L - 2 * η := by linarith
  by_cases h15 : t ≤ 0.15
  · have hd := archLevyDensity_sub_shift_le (by linarith : 0 < 2 * η - t) (show 2 * η - t ≤ 2 * η by linarith) hΔ
    rw [show 2 * η + (L - 2 * η) = L by ring] at hd
    have k2 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : (0 : ℝ) < 2 * η))
      (mem_Ioi.mpr (show (0 : ℝ) < 0.4568528197 by norm_num)) (by linarith)
    linarith
  · have hd := archLevyDensity_sub_shift_le (by linarith : 0 < 2 * η - t)
      (show 2 * η - t ≤ 2 * η - 0.15 by linarith) hΔ
    rw [show 2 * η - 0.15 + (L - 2 * η) = L - 0.15 by ring] at hd
    have k2 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith : (0 : ℝ) < 2 * η - 0.15))
      (mem_Ioi.mpr (show (0 : ℝ) < 0.3068528197 by norm_num)) (by linarith)
    have k3 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (show (0 : ℝ) < 0.5431471803 by norm_num))
      (mem_Ioi.mpr (by linarith : (0 : ℝ) < L - 0.15)) (by linarith)
    linarith

/-- **The band condition.** On the band `u, v ≥ b` the shared same-distance rate still dominates the
crossing rate: `R₊ + 0.73|u − v| ≤ (62/131) R₋`. -/
theorem twentyThreeFortieths_bandCondition {u v : ℝ} (hu0 : Real.log 3 - 23 / 40 - Real.log 2 / 2 ≤ u)
    (hu1 : u ≤ (23 / 40 - (Real.log 2 - 23 / 40)) / 2) (hv0 : Real.log 3 - 23 / 40 - Real.log 2 / 2 ≤ v)
    (hv1 : v ≤ (23 / 40 - (Real.log 2 - 23 / 40)) / 2) (huv : u ≠ v) :
    wideCrossRate (Real.log 2) u v + 219 / 100 / (2 + 1) * |u - v| ≤
      2 * (1 - 69 / 100) / (2 - 69 / 100) * wideSameRate (Real.log 2) u v := by
  obtain ⟨hη0, hη1, hb0, hb1, h2p, -, -, -, h2b, hηb⟩ := twentyThreeFortieths_window
  obtain ⟨-, -, -, -, -, -, -, -, -, o10, o11, -, o13⟩ := twentyThreeFortieths_omega_rational
  have hη : (23 / 40 - (Real.log 2 - 23 / 40)) / 2 = 23 / 40 - Real.log 2 / 2 := by ring
  rw [hη] at hu1 hv1
  set η := 23 / 40 - Real.log 2 / 2 with hηdef
  set b := Real.log 3 - 23 / 40 - Real.log 2 / 2 with hbdef
  set L := Real.log 2 with hL
  have ht : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
  have htb : |u - v| ≤ η - b := abs_le.mpr ⟨by linarith, by linarith⟩
  unfold wideSameRate wideCrossRate
  have k1 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr ht)
    (mem_Ioi.mpr (show (0 : ℝ) < 0.0513878 by norm_num)) (by linarith)
  have k2 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (show (0 : ℝ) < 0.2362943606 by norm_num))
    (mem_Ioi.mpr (by linarith : (0 : ℝ) < L - (u + v))) (by linarith)
  have k3 := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (show (0 : ℝ) < 0.3540772192 by norm_num))
    (mem_Ioi.mpr (by linarith : (0 : ℝ) < u + v)) (by linarith)
  have k4 := archLevyDensity_pos (show (0 : ℝ) < L - |u - v| by linarith)
  norm_num
  nlinarith

/-! ### The potential of the harmonic fold of `2` -/

/-- The surplus and the defect of the wide fold in the gauge `β + t`:
`(β + u)(2U − 2∫D(1 − q)) ≥ 2u(1 − ℓ) − 2(η³/24 + η⁴/32) − (c₁u³/3 + c₀u²)`. -/
theorem surplusDefect_mul_ge {L β η u c₁ c₀ : ℝ} (hβ : 0 < β) (hu : 0 < u) (huη : u ≤ η)
    (hLη : 2 * η < L) (hL : L ≤ 3 / 4) (hη1 : η ≤ 1 / 2)
    (hc₁ : 1 / (L * (L - 2 * η)) + 1 / 24 + L / 8 ≤ c₁) (hc₀ : L ^ 3 / 250 ≤ c₀) :
    2 * u * (1 - (Real.log (u + η) - Real.log u)) - 2 * (η ^ 3 / 24 + η ^ 4 / 32) -
        (c₁ * u ^ 3 / 3 + c₀ * u ^ 2) ≤
      (β + u) * (2 * surplusPotential (cubicGauge β 1 0 0) η u -
        2 * ∫ v in (0 : ℝ)..η, wideFoldDefect L u v * (1 - (β + v) / (β + u))) := by
  have hG0 : 0 < β + u := by linarith
  have hD := integral_wideFoldDefect_le (L := L) (β := β) (c₁ := c₁) (c₀ := c₀) hβ hu huη hLη hL hc₁ hc₀
  have hU := mul_surplusPotential_cubicGauge_ge β 1 0 0 (L := 1) hu huη hη1
    (by unfold cubicGauge; linarith) (fun _ _ _ _ _ _ => by norm_num)
  have hg : cubicGauge β 1 0 0 u = β + u := by unfold cubicGauge; ring
  rw [hg] at hU
  have hmain : cubicSurplusMain 1 0 0 η u = u * (1 - (Real.log (u + η) - Real.log u)) := by
    unfold cubicSurplusMain; rw [add_comm u η]; ring
  rw [hmain, one_mul] at hU
  have hrem : surplusRemainder η u ≤ η ^ 3 / 24 + η ^ 4 / 32 := by
    unfold surplusRemainder
    nlinarith [mul_nonneg hu.le (sub_nonneg.2 huη), mul_nonneg (mul_nonneg hu.le hu.le) (sub_nonneg.2 huη),
      mul_nonneg (mul_nonneg hu.le (sub_nonneg.2 huη)) (sub_nonneg.2 huη), pow_nonneg hu.le 3,
      mul_nonneg (pow_nonneg hu.le 2) (sub_nonneg.2 huη), mul_nonneg (pow_nonneg hu.le 3) (sub_nonneg.2 huη),
      mul_nonneg (mul_nonneg (pow_nonneg hu.le 2) (sub_nonneg.2 huη)) (sub_nonneg.2 huη),
      mul_nonneg (mul_nonneg hu.le (sub_nonneg.2 huη)) (mul_nonneg hu.le (sub_nonneg.2 huη))]
  set Dint := ∫ v in (0 : ℝ)..η, wideFoldDefect L u v * (1 - (β + v) / (β + u)) with hDint
  set U := surplusPotential (cubicGauge β 1 0 0) η u with hUdef
  have hDG : (β + u) * Dint ≤ c₁ * u ^ 3 / 6 + c₀ * u ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left hD hG0.le
    rwa [mul_div_cancel₀ _ hG0.ne'] at this
  linarith only [hU, hDG, hrem]

/-- The polynomial certificate off the band, `0 ≤ u ≤ 0.1770387099`. -/
theorem twentyThreeFortieths_regimeOne {u : ℝ} (hu : 0 ≤ u) (hub : u ≤ 0.1770387099) :
    0.04 * u ≤ (2 * u - 0.001164 - (6.24 * u ^ 3 / 3 + 0.001333 * u ^ 2) -
      (0.01 + u) * (0.79966 + 0.01 + 0.001847 -
        ((0.6931471803 ^ 2 - (0.6931471803 - u) ^ 2) + (0.6931471803 ^ 3 - (0.6931471803 - u) ^ 3)) / 24 -
        ((0.6931471803 ^ 2 - (0.4647207712 + u) ^ 2) + (0.6931471803 ^ 3 - (0.4647207712 + u) ^ 3)) / 24) +
      1.46 * (u ^ 2 * 0.2284264096 - 0.2284264096 ^ 3 / 3 + (2 * 0.01 + u) * u ^ 2 / 2 + u ^ 3 / 6 +
        (0.01 + u) * (0.2284264096 - u) ^ 2 + (0.2284264096 - u) ^ 3 / 3 - 0.00000000000000000001) -
      (0.01 + u) + 0.02 * (0.6931471803 + 1)) * (u + 0.2284264096) := by
  nlinarith [mul_nonneg hu (sub_nonneg.2 hub), mul_nonneg (pow_nonneg hu 2) (sub_nonneg.2 hub),
    mul_nonneg (pow_nonneg hu 3) (sub_nonneg.2 hub), pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4]

/-- The polynomial certificate on the band, `0.1770386096 ≤ u ≤ 0.2284264099`. -/
theorem twentyThreeFortieths_regimeTwo {u : ℝ} (hub : 0.1770386096 ≤ u) (huη : u ≤ 0.2284264099) :
    0.04 * u ≤ (2 * u - 0.001164 - (6.24 * u ^ 3 / 3 + 0.001333 * u ^ 2) -
      (0.01 + u) * (0.79966 + 0.01 + 0.001847 -
        ((0.6931471803 ^ 2 - (0.6931471803 - u) ^ 2) + (0.6931471803 ^ 3 - (0.6931471803 - u) ^ 3)) / 24 -
        ((0.6931471803 ^ 2 - (0.4647207712 + u) ^ 2) + (0.6931471803 ^ 3 - (0.4647207712 + u) ^ 3)) / 24) +
      1.46 * (u ^ 2 * 0.2284264096 - 0.2284264096 ^ 3 / 3 + (2 * 0.01 + u) * u ^ 2 / 2 + u ^ 3 / 6 +
        (0.01 + u) * (0.2284264096 - u) ^ 2 + (0.2284264096 - u) ^ 3 / 3 - 0.00000000000000000001) -
      (138 / 131 * (u - 0.2027325096 + 1.0554 * (0.2284264099 - u) ^ 2) +
        1.46 * ((u - 0.1770386096) * (u ^ 2 - 0.1770386096 ^ 2))) -
      (0.01 + u) + 0.02 * (0.6931471803 + 1)) * (u + 0.2284264096) := by
  have h0 : 0 ≤ u - 0.1770386096 := by linarith
  have h1 : 0 ≤ 0.2284264099 - u := by linarith
  have hu0 : 0 ≤ u := by linarith
  nlinarith [mul_nonneg h0 h1, mul_nonneg (mul_nonneg h0 h1) hu0, mul_nonneg h1 hu0,
    mul_nonneg h1 (pow_nonneg hu0 2), mul_nonneg h1 (pow_nonneg hu0 3), pow_nonneg hu0 2, pow_nonneg hu0 3]

/-- The polynomial parts of the bound, at the numerical edges of the window. -/
theorem twentyThreeFortieths_polyParts {u : ℝ} (hu : 0 < u) (huη : u ≤ 23 / 40 - Real.log 2 / 2) :
    2 * ((23 / 40 - Real.log 2 / 2) ^ 3 / 24 + (23 / 40 - Real.log 2 / 2) ^ 4 / 32) ≤ 0.001164 ∧
      (3 * (23 / 40 - Real.log 2 / 2) ^ 2 + 7 * (23 / 40 - Real.log 2 / 2) ^ 3) / 24 ≤ 0.01 ∧
      8 * Real.log 2 ^ 4 / 1000 ≤ 0.001847 ∧
      ((0.6931471803 ^ 2 - (0.6931471803 - u) ^ 2) + (0.6931471803 ^ 3 - (0.6931471803 - u) ^ 3)) / 24 ≤
        ((Real.log 2 ^ 2 - (Real.log 2 - u) ^ 2) + (Real.log 2 ^ 3 - (Real.log 2 - u) ^ 3)) / 24 ∧
      ((0.6931471803 ^ 2 - (0.4647207712 + u) ^ 2) + (0.6931471803 ^ 3 - (0.4647207712 + u) ^ 3)) / 24 ≤
        ((Real.log 2 ^ 2 - (Real.log 2 + u - (23 / 40 - Real.log 2 / 2)) ^ 2) +
          (Real.log 2 ^ 3 - (Real.log 2 + u - (23 / 40 - Real.log 2 / 2)) ^ 3)) / 24 := by
  obtain ⟨hη0, hη1, -, -, -, hd0, hd1, -, -, -⟩ := twentyThreeFortieths_window
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  set η := 23 / 40 - Real.log 2 / 2 with hηdef
  set L := Real.log 2 with hL
  have k2 : η ^ 2 ≤ (0.2284264099 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hη1 2
  have k3 : η ^ 3 ≤ (0.2284264099 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hη1 3
  have k4 : η ^ 4 ≤ (0.2284264099 : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) hη1 4
  have kL : L ^ 4 ≤ (0.6931471808 : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) h2.le 4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num at k3 k4 ⊢; linarith
  · norm_num at k2 k3 ⊢; linarith
  · norm_num at kL ⊢; linarith
  · -- increasing in `L` for `0 ≤ u ≤ 2L`
    have hLl : (0.6931471803 : ℝ) ≤ L := h1.le
    have hu1 : u ≤ 1 / 2 := by linarith
    nlinarith [mul_nonneg (mul_nonneg hu.le (sub_nonneg.2 hLl)) (show (0 : ℝ) ≤ 2 + 3 * (L + 0.6931471803) - 3 * u
      by linarith)]
  · -- increasing in `L`, decreasing in `L − η`
    have hLl : (0.6931471803 : ℝ) ≤ L := h1.le
    have hd : L + u - η ≤ 0.4647207712 + u := by linarith
    have hd' : 0 ≤ L + u - η := by linarith
    have e1 : (L + u - η) ^ 2 ≤ (0.4647207712 + u) ^ 2 := pow_le_pow_left₀ hd' hd 2
    have e2 : (L + u - η) ^ 3 ≤ (0.4647207712 + u) ^ 3 := pow_le_pow_left₀ hd' hd 3
    have e3 : (0.6931471803 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hLl 2
    have e4 : (0.6931471803 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hLl 3
    linarith

/-- The recovered shares at the lower edge of `η`: `RecG(u; η) ≥ RecG(u; η_lo) − 10⁻²⁰`. -/
theorem twentyThreeFortieths_recovery_ge {u : ℝ} (huη : u ≤ 23 / 40 - Real.log 2 / 2) :
    u ^ 2 * 0.2284264096 - 0.2284264096 ^ 3 / 3 + (2 * 0.01 + u) * u ^ 2 / 2 + u ^ 3 / 6 +
        (0.01 + u) * (0.2284264096 - u) ^ 2 + (0.2284264096 - u) ^ 3 / 3 - 0.00000000000000000001 ≤
      u ^ 2 * (23 / 40 - Real.log 2 / 2) - (23 / 40 - Real.log 2 / 2) ^ 3 / 3 +
        (2 * (1 / 100) + u) * u ^ 2 / 2 + u ^ 3 / 6 + (1 / 100 + u) * ((23 / 40 - Real.log 2 / 2) - u) ^ 2 +
        ((23 / 40 - Real.log 2 / 2) - u) ^ 3 / 3 := by
  obtain ⟨hη0, hη1, -, -, -, -, -, -, -, -⟩ := twentyThreeFortieths_window
  set η := 23 / 40 - Real.log 2 / 2 with hηdef
  -- the difference is `β(η − η_lo)(η + η_lo − 2u) ≥ −β(η − η_lo)²`
  have e : u ^ 2 * η - η ^ 3 / 3 + (2 * (1 / 100) + u) * u ^ 2 / 2 + u ^ 3 / 6 + (1 / 100 + u) * (η - u) ^ 2 +
      (η - u) ^ 3 / 3 - (u ^ 2 * 0.2284264096 - 0.2284264096 ^ 3 / 3 + (2 * 0.01 + u) * u ^ 2 / 2 +
        u ^ 3 / 6 + (0.01 + u) * (0.2284264096 - u) ^ 2 + (0.2284264096 - u) ^ 3 / 3) =
      1 / 100 * ((η - 0.2284264096) * (η + 0.2284264096 - 2 * u)) := by ring
  have h0 : 0 ≤ η - 0.2284264096 := by linarith
  have hs : (η - 0.2284264096) ^ 2 ≤ (0.0000000003 : ℝ) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
  have hk : -((η - 0.2284264096) ^ 2) ≤ (η - 0.2284264096) * (η + 0.2284264096 - 2 * u) := by
    nlinarith [mul_nonneg h0 (sub_nonneg.2 huη)]
  norm_num at hs
  nlinarith

/-- The wide weight at `r = 23/40`, gauge `1/100 + t`:
`(β + u) ∫_0^η W ≥ 2u(1 − ℓ) − 0.001164 − (2.08u³ + 0.001333u²) + (β + u)(2ℓ − 0.811507 + Q₂ + Q₃)`. -/
theorem twentyThreeFortieths_wide_ge {u : ℝ} (hu : 0 < u) (huη : u ≤ 23 / 40 - Real.log 2 / 2) :
    2 * u * (1 - (Real.log (u + (23 / 40 - Real.log 2 / 2)) - Real.log u)) - 0.001164 -
        (6.24 * u ^ 3 / 3 + 0.001333 * u ^ 2) +
        (0.01 + u) * (2 * (Real.log (u + (23 / 40 - Real.log 2 / 2)) - Real.log u) -
          (0.79966 + 0.01 + 0.001847) +
          ((0.6931471803 ^ 2 - (0.6931471803 - u) ^ 2) + (0.6931471803 ^ 3 - (0.6931471803 - u) ^ 3)) / 24 +
          ((0.6931471803 ^ 2 - (0.4647207712 + u) ^ 2) + (0.6931471803 ^ 3 - (0.4647207712 + u) ^ 3)) / 24) ≤
      (1 / 100 + u) * ∫ v in (0 : ℝ)..(23 / 40 - Real.log 2 / 2), wideFoldWeight (Real.log 2) (1 / 100) u v := by
  obtain ⟨hη0, hη1, -, -, h2p, -, -, -, -, -⟩ := twentyThreeFortieths_window
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  obtain ⟨p1, p2, p3, p4, p5⟩ := twentyThreeFortieths_polyParts hu huη
  set η := 23 / 40 - Real.log 2 / 2 with hηdef
  set L := Real.log 2 with hL
  have hLη : 2 * η < L := by linarith
  have hη12 : η ≤ 1 / 2 := by linarith
  have hL34 : L ≤ 3 / 4 := by linarith
  have hG : 0 < 1 / 100 + u := by linarith
  have hsplit := integral_wideFoldWeight_eq (L := L) (β := 1 / 100) (by norm_num) hu huη hLη hη12
  have hsd := surplusDefect_mul_ge (L := L) (β := 1 / 100) (c₁ := 6.24) (c₀ := 0.001333) (by norm_num) hu huη
    hLη hL34 hη12
    (by
      have hp : 0.163786 ≤ L * (L - 2 * η) := by
        have : (0.2362943606 : ℝ) * 0.6931471803 ≤ (L - 2 * η) * L :=
          mul_le_mul h2p h1.le (by norm_num) (by linarith)
        norm_num at this ⊢; linarith
      have : 1 / (L * (L - 2 * η)) ≤ 1 / 0.163786 := one_div_le_one_div_of_le (by norm_num) hp
      norm_num at this ⊢
      linarith)
    (by
      have : L ^ 3 ≤ (0.6931471808 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) h2.le 3
      norm_num at this ⊢; linarith)
  have hcr := wideCrossRate_integral_ge_sharp (Λ := 0.39983) hu huη hLη hL34 twentyThreeFortieths_logRatio_le
  rw [hsplit]
  set ℓ := Real.log (u + η) - Real.log u with hℓ
  set SD := 2 * surplusPotential (cubicGauge (1 / 100) 1 0 0) η u -
    2 * ∫ v in (0 : ℝ)..η, wideFoldDefect L u v * (1 - (1 / 100 + v) / (1 / 100 + u)) with hSD
  set C4 := ∫ v in (0 : ℝ)..η, wideCrossRate L u v with hC4
  set Q2 := ((L ^ 2 - (L - u) ^ 2) + (L ^ 3 - (L - u) ^ 3)) / 24 with hQ2
  set Q3 := ((L ^ 2 - (L + u - η) ^ 2) + (L ^ 3 - (L + u - η) ^ 3)) / 24 with hQ3
  set K1 := (3 * η ^ 2 + 7 * η ^ 3) / 24 with hK1
  set K4 := 8 * L ^ 4 / 1000 with hK4
  set Q2L := ((0.6931471803 ^ 2 - (0.6931471803 - u) ^ 2) + (0.6931471803 ^ 3 - (0.6931471803 - u) ^ 3)) / 24
  set Q3L := ((0.6931471803 ^ 2 - (0.4647207712 + u) ^ 2) + (0.6931471803 ^ 3 - (0.4647207712 + u) ^ 3)) / 24
  have hcrG := mul_le_mul_of_nonneg_left hcr hG.le
  have hm : (1 / 100 + u) * (2 * ℓ - (0.79966 + 0.01 + 0.001847) + Q2L + Q3L) ≤
      (1 / 100 + u) * (2 * ℓ - 2 * 0.39983 - K1 - K4 + Q2 + Q3) :=
    mul_le_mul_of_nonneg_left (by linarith) hG.le
  have e1 : 2 * surplusPotential (cubicGauge (1 / 100) 1 0 0) η u -
      2 * (∫ v in (0 : ℝ)..η, wideFoldDefect L u v * (1 - (1 / 100 + v) / (1 / 100 + u))) + 4 * C4 =
      SD + 4 * C4 := by rw [hSD]
  rw [e1]
  have e2 : (0.01 : ℝ) + u = 1 / 100 + u := by norm_num
  rw [e2]
  linarith only [hsd, hcrG, hm, p1]

/-- The harmonic weight at `r = 23/40` against the wide weight: `(β + u)(H − W) ≥ 1.46 RecG − band`. -/
theorem twentyThreeFortieths_harmonic_ge_wide {u : ℝ} (hu : 0 < u) (huη : u ≤ 23 / 40 - Real.log 2 / 2) :
    (1 / 100 + u) * (∫ v in (0 : ℝ)..(23 / 40 - Real.log 2 / 2), wideFoldWeight (Real.log 2) (1 / 100) u v) +
        1.46 * (u ^ 2 * (23 / 40 - Real.log 2 / 2) - (23 / 40 - Real.log 2 / 2) ^ 3 / 3 +
          (2 * (1 / 100) + u) * u ^ 2 / 2 + u ^ 3 / 6 + (1 / 100 + u) * ((23 / 40 - Real.log 2 / 2) - u) ^ 2 +
          ((23 / 40 - Real.log 2 / 2) - u) ^ 3 / 3) -
        (if Real.log 3 - 23 / 40 - Real.log 2 / 2 ≤ u then
          138 / 131 * (u - 0.2027325096 + 1.0554 * (0.2284264099 - u) ^ 2) +
            1.46 * ((u - 0.1770386096) * (u ^ 2 - 0.1770386096 ^ 2)) else 0) ≤
      (1 / 100 + u) * ∫ v in (0 : ℝ)..(23 / 40 - Real.log 2 / 2), harmonicFoldWeight (Real.log 2) (1 / 100)
        (219 / 100 / (2 + 1)) (Real.log 3 - 23 / 40 - Real.log 2 / 2) (2 * (1 - 69 / 100) / (2 - 69 / 100)) u v := by
  obtain ⟨hη0, hη1, hb0, hb1, h2p, hd0, hd1, hLb, h2b, hηb⟩ := twentyThreeFortieths_window
  obtain ⟨-, -, -, -, -, -, -, -, -, -, o11, o12, -⟩ := twentyThreeFortieths_omega_rational
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  set η := 23 / 40 - Real.log 2 / 2 with hηdef
  set b := Real.log 3 - 23 / 40 - Real.log 2 / 2 with hbdef
  set L := Real.log 2 with hL
  have hLη : 2 * η < L := by linarith
  have hη12 : η ≤ 1 / 2 := by linarith
  have hG : 0 < 1 / 100 + u := by linarith
  have hlo : (1.71 : ℝ) ≤ archLevyDensity (L - 2 * b) :=
    o12.trans (strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith))
      (mem_Ioi.mpr (by norm_num)) hLb)
  have hhi : archLevyDensity (L - 2 * η) ≤ 2.36 :=
    (strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by norm_num)) (mem_Ioi.mpr (by linarith)) h2p).trans o11
  have hW2 := integral_harmonicFoldWeight_ge (L := L) (β := 1 / 100) (γ := 219 / 100 / (2 + 1))
    (ρ := 2 * (1 - 69 / 100) / (2 - 69 / 100)) (η := η) (b := b) (u := u) (ωlo := 1.71) (ωhi := 2.36)
    (cw := 1.0554) (by norm_num) hu huη hLη hη12 (by norm_num) (by norm_num) (by norm_num) (by linarith)
    (by linarith) hlo hhi (by norm_num) (by
      have : (η - b) ^ 2 ≤ (0.0513878 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hηb 2
      norm_num at this ⊢; linarith)
  set R := u ^ 2 * η - η ^ 3 / 3 + (2 * (1 / 100) + u) * u ^ 2 / 2 + u ^ 3 / 6 + (1 / 100 + u) * (η - u) ^ 2 +
    (η - u) ^ 3 / 3 with hR
  have hγ : 2 * (219 / 100 / (2 + 1) : ℝ) = 1.46 := by norm_num
  have hρ : 2 * (1 - 2 * (1 - 69 / 100) / (2 - 69 / 100) : ℝ) = 138 / 131 := by norm_num
  have hGR : (1 / 100 + u) * (2 * (219 / 100 / (2 + 1)) * (R / (1 / 100 + u))) = 1.46 * R := by
    rw [hγ]; field_simp
  have hW2G := mul_le_mul_of_nonneg_left hW2 hG.le
  by_cases hbu : b ≤ u
  · rw [if_pos hbu] at hW2G ⊢
    rw [mul_sub, mul_add, hGR, mul_div_cancel₀ _ hG.ne', hρ, hγ] at hW2G
    have hw : (η - u) ^ 2 ≤ (0.2284264099 - u) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hb' : (u - b) * (u ^ 2 - b ^ 2) ≤ (u - 0.1770386096) * (u ^ 2 - 0.1770386096 ^ 2) := by
      have e1 : 0 ≤ u - b := by linarith
      have e2 : 0 ≤ u ^ 2 - b ^ 2 := by
        have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ b) hbu 2; linarith
      have e3 : u ^ 2 - b ^ 2 ≤ u ^ 2 - 0.1770386096 ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.1770386096) hb0 2; linarith
      exact mul_le_mul (by linarith) e3 e2 (by linarith)
    have hw' := mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 138 / 131 * 1.0554)
    have hb'' := mul_le_mul_of_nonneg_left hb' (by norm_num : (0 : ℝ) ≤ 1.46)
    linarith only [hW2G, hw', hb'', hb0, hη0]
  · rw [if_neg hbu] at hW2G ⊢
    rw [mul_sub, mul_add, hGR, mul_zero] at hW2G
    linarith only [hW2G]

/-- **The lower bound of the harmonic potential at `r = 23/40`**, before the window ratio `ℓ` is bounded. -/
theorem twentyThreeFortieths_lower {u : ℝ} (hu : 0 < u) (huη : u ≤ 23 / 40 - Real.log 2 / 2) :
    2 * u * (1 - (Real.log (u + (23 / 40 - Real.log 2 / 2)) - Real.log u)) - 0.001164 -
        (6.24 * u ^ 3 / 3 + 0.001333 * u ^ 2) +
        (0.01 + u) * (2 * (Real.log (u + (23 / 40 - Real.log 2 / 2)) - Real.log u) -
          (0.79966 + 0.01 + 0.001847) +
          ((0.6931471803 ^ 2 - (0.6931471803 - u) ^ 2) + (0.6931471803 ^ 3 - (0.6931471803 - u) ^ 3)) / 24 +
          ((0.6931471803 ^ 2 - (0.4647207712 + u) ^ 2) + (0.6931471803 ^ 3 - (0.4647207712 + u) ^ 3)) / 24) +
        1.46 * (u ^ 2 * 0.2284264096 - 0.2284264096 ^ 3 / 3 + (2 * 0.01 + u) * u ^ 2 / 2 + u ^ 3 / 6 +
          (0.01 + u) * (0.2284264096 - u) ^ 2 + (0.2284264096 - u) ^ 3 / 3 - 0.00000000000000000001) -
        (if Real.log 3 - 23 / 40 - Real.log 2 / 2 ≤ u then
          138 / 131 * (u - 0.2027325096 + 1.0554 * (0.2284264099 - u) ^ 2) +
            1.46 * ((u - 0.1770386096) * (u ^ 2 - 0.1770386096 ^ 2)) else 0) ≤
      (1 / 100 + u) * ∫ v in (0 : ℝ)..(23 / 40 - Real.log 2 / 2), harmonicFoldWeight (Real.log 2) (1 / 100)
        (219 / 100 / (2 + 1)) (Real.log 3 - 23 / 40 - Real.log 2 / 2) (2 * (1 - 69 / 100) / (2 - 69 / 100)) u v := by
  have hA := twentyThreeFortieths_wide_ge hu huη
  have hB := twentyThreeFortieths_harmonic_ge_wide hu huη
  have hR := twentyThreeFortieths_recovery_ge huη
  have hR' := mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 1.46)
  linarith only [hA, hB, hR']

/-- The window ratio: `ℓ = log((u + η)/u) ≥ log 2 + 1 − 2u/(u + η_lo)` (tangent of `log` at `2`). -/
theorem twentyThreeFortieths_ratio_ge {u : ℝ} (hu : 0 < u) :
    0.6931471803 + 1 - 2 * u / (u + 0.2284264096) ≤
      Real.log (u + (23 / 40 - Real.log 2 / 2)) - Real.log u := by
  obtain ⟨hη0, -, -, -, -, -, -, -, -, -⟩ := twentyThreeFortieths_window
  have h1 := Real.log_two_gt_d9
  set η := 23 / 40 - Real.log 2 / 2 with hηdef
  have hpos : 0 < u + η := by linarith
  have ht := log_ge_tangent (show 0 < (u + η) / u by positivity) (show (0 : ℝ) < 2 by norm_num)
  rw [Real.log_div hpos.ne' hu.ne'] at ht
  have e : 2 / ((u + η) / u) = 2 * u / (u + η) := by field_simp
  rw [e] at ht
  have hT : 2 * u / (u + η) ≤ 2 * u / (u + 0.2284264096) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  linarith

/-- **The potential of the harmonic fold of `2` at `r = 23/40`.** With the gauge `1/100 + t`, the slope
`2.19`, `κ = 1` and the fraction `69/100` of the band of `S₃` shared, the folded weight integrates over
`[0, η]` to at least `1` at every folded point. -/
theorem twentyThreeFortieths_potential {u : ℝ} (hu : 0 < u) (huη : u ≤ 23 / 40 - Real.log 2 / 2) :
    1 ≤ ∫ v in (0 : ℝ)..(23 / 40 - Real.log 2 / 2), harmonicFoldWeight (Real.log 2) (1 / 100)
      (219 / 100 / (2 + 1)) (Real.log 3 - 23 / 40 - Real.log 2 / 2) (2 * (1 - 69 / 100) / (2 - 69 / 100)) u v := by
  obtain ⟨hη0, hη1, hb0, hb1, -, -, -, -, -, -⟩ := twentyThreeFortieths_window
  have hlow := twentyThreeFortieths_lower hu huη
  have hℓ := twentyThreeFortieths_ratio_ge hu
  set H := ∫ v in (0 : ℝ)..(23 / 40 - Real.log 2 / 2), harmonicFoldWeight (Real.log 2) (1 / 100)
    (219 / 100 / (2 + 1)) (Real.log 3 - 23 / 40 - Real.log 2 / 2) (2 * (1 - 69 / 100) / (2 - 69 / 100)) u v
  set ℓ := Real.log (u + (23 / 40 - Real.log 2 / 2)) - Real.log u with hℓdef
  set T := 2 * u / (u + 0.2284264096) with hTdef
  have hc : 0 < u + 0.2284264096 := by linarith
  have hT : T * (u + 0.2284264096) = 2 * u := by rw [hTdef]; field_simp
  have hG : 0 < 1 / 100 + u := by linarith
  refine le_of_mul_le_mul_left ?_ hG
  rw [mul_one]
  by_cases hbu : Real.log 3 - 23 / 40 - Real.log 2 / 2 ≤ u
  · rw [if_pos hbu] at hlow
    have hpoly := twentyThreeFortieths_regimeTwo (by linarith) (by linarith : u ≤ 0.2284264099)
    rw [show (0.04 : ℝ) * u = 0.02 * T * (u + 0.2284264096) by rw [mul_assoc, hT]; ring] at hpoly
    have key := le_of_mul_le_mul_right hpoly hc
    linarith only [hlow, key, hℓ]
  · rw [if_neg hbu] at hlow
    have hpoly := twentyThreeFortieths_regimeOne hu.le (by linarith : u ≤ 0.1770387099)
    rw [show (0.04 : ℝ) * u = 0.02 * T * (u + 0.2284264096) by rw [mul_assoc, hT]; ring] at hpoly
    have key := le_of_mul_le_mul_right hpoly hc
    linarith only [hlow, key, hℓ]

/-- The potential in the form the harmonic micro-fold consumes. -/
theorem twentyThreeFortieths_hpot {u : ℝ} (hu : 0 < u) (huη : u ≤ (23 / 40 - (Real.log 2 - 23 / 40)) / 2) :
    2 * 1 ≤ ∫ y in (Real.log 2 - 23 / 40)..(23 / 40), harmonicFoldWeight (Real.log 2) (1 / 100)
      (219 / 100 / (2 + 1)) (Real.log 3 - 23 / 40 - Real.log 2 / 2) (2 * (1 - 69 / 100) / (2 - 69 / 100)) u
        |y - Real.log 2 / 2| := by
  obtain ⟨hη0, hη1, -, -, h2p, -, -, -, -, -⟩ := twentyThreeFortieths_window
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have huη' : u ≤ 23 / 40 - Real.log 2 / 2 := by linarith
  have hLη : 2 * (23 / 40 - Real.log 2 / 2) < Real.log 2 := by linarith
  have hη12 : 23 / 40 - Real.log 2 / 2 ≤ 1 / 2 := by linarith
  have h := integral_abs_sub_symm (m := Real.log 2 / 2) (η := 23 / 40 - Real.log 2 / 2)
    (C := (3 / (1 / 100) + 2 * archLevyDensity (2 * ((Real.log 2 - 2 * (23 / 40 - Real.log 2 / 2)) / 2)) *
        (23 / 40 - Real.log 2 / 2) / (1 / 100) + 4 * (archLevyDensity u +
          archLevyDensity (2 * ((Real.log 2 - 2 * (23 / 40 - Real.log 2 / 2)) / 2)))) +
      (2 * (219 / 100 / (2 + 1)) * (2 * (23 / 40 - Real.log 2 / 2) * ((23 / 40 - Real.log 2 / 2) / (1 / 100)) +
        (23 / 40 - Real.log 2 / 2) * (2 + (23 / 40 - Real.log 2 / 2) / (1 / 100))) +
        2 * ((1 / 2 + (23 / 40 - Real.log 2 / 2) / 4 +
          archLevyDensity (2 * ((Real.log 2 - 2 * (23 / 40 - Real.log 2 / 2)) / 2)) *
            (23 / 40 - Real.log 2 / 2)) / (1 / 100)) +
        2 * (219 / 100 / (2 + 1)) * (2 * (23 / 40 - Real.log 2 / 2) * ((23 / 40 - Real.log 2 / 2) / (1 / 100)))))
    (w := fun v => harmonicFoldWeight (Real.log 2) (1 / 100) (219 / 100 / (2 + 1))
      (Real.log 3 - 23 / 40 - Real.log 2 / 2) (2 * (1 - 69 / 100) / (2 - 69 / 100)) u v)
    (by linarith) (measurable_harmonicFoldWeight _ _ _ _ _).of_uncurry_left fun v hv => by
      have k1 := abs_harmonicFoldWeight_le (L := Real.log 2) (β := 1 / 100) (γ := 219 / 100 / (2 + 1))
        (b := Real.log 3 - 23 / 40 - Real.log 2 / 2) (ρ := 2 * (1 - 69 / 100) / (2 - 69 / 100))
        (p := (Real.log 2 - 2 * (23 / 40 - Real.log 2 / 2)) / 2) (by norm_num) (by linarith) hu hv.1 huη'
        hv.2 (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
      have k2 := abs_wideFoldWeight_le (L := Real.log 2) (β := 1 / 100)
        (p := (Real.log 2 - 2 * (23 / 40 - Real.log 2 / 2)) / 2) (by norm_num) (by linarith) hu hv.1 huη' hv.2
        hη12 (by linarith)
      have k3 : archLevyDensity (u + v) ≤ archLevyDensity u :=
        strictAntiOn_archLevyDensity.antitoneOn hu (show 0 < u + v by linarith [hv.1]) (by linarith [hv.1])
      linarith
  rw [show Real.log 2 / 2 - (23 / 40 - Real.log 2 / 2) = Real.log 2 - 23 / 40 by ring,
    show Real.log 2 / 2 + (23 / 40 - Real.log 2 / 2) = 23 / 40 by ring] at h
  rw [h]
  linarith [twentyThreeFortieths_potential hu huη']

/-- The micro-fold constant of the strip of `3` at `r = 23/40`: `λ₃ ≥ 1.8489`, and `69/100` of it pays
the atom of `3`. -/
theorem twentyThreeFortieths_threeStrip_lam :
    (1 + 0) * (2 * vonMangoldtAtom 3) ≤ 69 / 100 * (19 / 10 -
      (23 / 40 - (Real.log 3 - 23 / 40)) / 2 / (Real.log 3 - 23 / 40) -
        3 * ((23 / 40 - (Real.log 3 - 23 / 40)) / 2) ^ 2) := by
  obtain ⟨-, hΛ1⟩ := vonMangoldtAtom_three_bounds
  obtain ⟨l1, l2⟩ := log_three_bounds
  have hp : 0 < Real.log 3 - 23 / 40 := by linarith
  have hq : (23 / 40 - (Real.log 3 - 23 / 40)) / 2 / (Real.log 3 - 23 / 40) ≤ 4908 / 100000 := by
    rw [div_le_iff₀ hp]; linarith
  have hη0 : 0 ≤ (23 / 40 - (Real.log 3 - 23 / 40)) / 2 := by linarith
  have hsq : ((23 / 40 - (Real.log 3 - 23 / 40)) / 2) ^ 2 ≤ (2570 / 100000) ^ 2 :=
    pow_le_pow_left₀ hη0 (by linarith) 2
  norm_num at hsq
  linarith

/-- **Harnack across the overlapping strips of `2` and `3` at `r = 23/40`.** For every odd Lipschitz `F`
supported in `[−23/40, 23/40]`, the atoms of `2` and `3`, the whole prime side (`e^{2r} < 4`), are paid
by the surplus of the strip `S₂ = [log 2 − 23/40, 23/40]` with potential to spare:

    2 Λ(2)/√2 ∫ F F(· + log 2) + 2 Λ(3)/√3 ∫ F F(· + log 3) ≤ 2 stripSurplus_{S₂} − (1/62) ∫_{S₂} F².

The atom of `3` takes `69/100` of the surplus of `S₃ × S₃` (sharp micro-fold, `λ₃ ≥ 1.849`); the atom of
`2` is paid by the harmonic micro-fold of `S₂` with that share withheld (`twentyThreeFortieths_potential`). -/
theorem two_mul_primeTwoThreeShifts_le_stripSurplus_twentyThreeFortieths {F : ℝ → ℝ} {K : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hsupp : ∀ x, 23 / 40 < |x| → F x = 0) :
    2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) +
        2 * (vonMangoldtAtom 3 * ∫ x, F x * F (x + Real.log 3)) ≤
      2 * stripSurplus F (Real.log 2 - 23 / 40) (23 / 40) -
        1 / 62 * ∫ x in (Real.log 2 - 23 / 40)..(23 / 40), F x ^ 2 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  obtain ⟨h3, h4⟩ := log_three_bounds
  obtain ⟨hΛ3, -⟩ := vonMangoldtAtom_three_bounds
  obtain ⟨-, hΛ2⟩ := vonMangoldtAtom_two_bounds
  have hΛ2' := vonMangoldtAtom_two_ge
  have hp : 0 < Real.log 2 - 23 / 40 := by linarith
  have hpr : Real.log 2 - 23 / 40 < 23 / 40 := by linarith
  have hpc : Real.log 2 - 23 / 40 < Real.log 3 - 23 / 40 := by linarith
  have hcr : Real.log 3 - 23 / 40 ≤ 23 / 40 := by linarith
  have hr1 : 23 / 40 - (Real.log 2 - 23 / 40) ≤ 1 := by linarith
  -- the atom of `3` on `69/100` of `S₃ × S₃`
  have hA3 := two_mul_primePowerShift_le_stripSurplus_sub_evenPart (n := 3) (θ := 69 / 100) (t := 0)
    (by norm_num) hF hFc hodd hFL hsupp (by push_cast; linarith) (by push_cast; linarith)
    (by norm_num) (by norm_num) (by push_cast; exact twentyThreeFortieths_threeStrip_lam)
  push_cast at hA3
  -- the atom of `2` on its odd part, with the even part kept at `t = 1/60`
  have hA2 := integral_mul_shift_le_interp hF hFc hodd (r := 23 / 40) (L := Real.log 2) (by norm_num)
    (by linarith) hsupp (t := 1 / 60) (by norm_num)
  -- the harmonic micro-fold of `S₂` with `69/100` of `S₃ × S₃` withheld
  have hW := harmonicMicroFold_strip_ge (L := Real.log 2) (β := 1 / 100) (cs := 219 / 100) (κ := 1)
    (c := Real.log 3 - 23 / 40) (θ := 69 / 100) (lam := 1) hF hFL hp hpr (by ring) hr1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith)
    (fun w hw0 hw => slope_mul_le_archLevyDensity_reflect hw0 (by linarith))
    (fun u v hu0 hu1 hv0 hv1 huv => twentyThreeFortieths_sameCondition hu0 hu1 hv0 hv1 huv)
    (fun u v hu0 hu1 hv0 hv1 hs => twentyThreeFortieths_crossCondition hu0 hu1 hv0 hv1 hs)
    (fun u v hu0 hu1 hv0 hv1 huv => twentyThreeFortieths_bandCondition (by linarith) hu1 (by linarith) hv1 huv)
    fun u hu huη => twentyThreeFortieths_hpot hu huη
  -- the boxes
  have hbox := integral_box_thetaWithheld_eq (θ := 69 / 100) hF hFL hp hpc hcr hr1
  have hT2 := integral_strip_eq_two_mul_stripSurplus hF hFL hp hpr.le hr1
  have hT3 := integral_strip_eq_two_mul_stripSurplus hF hFL (by linarith) hcr (by linarith)
  have hS2 : 0 ≤ ∫ x in (Real.log 2 - 23 / 40)..(23 / 40), F x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have hα : 0 ≤ ∫ x in (Real.log 2 - 23 / 40)..(23 / 40), reflectedOddPart F (Real.log 2) x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have k1 := mul_le_mul_of_nonneg_left hA2 (vonMangoldtAtom_nonneg 2)
  have k2 := mul_le_mul_of_nonneg_right (show vonMangoldtAtom 2 * (1 + 1 / 60) ≤ 1 / 2 by linarith) hα
  have k3 := mul_le_mul_of_nonneg_right (show 1 / 124 ≤ vonMangoldtAtom 2 * (1 / 60) by linarith) hS2
  unfold stripIntegrand at hT2 hT3
  linarith only [hA3, k1, k2, k3, hW, hbox, hT2, hT3]

end GaloisForLFunctions.ArithmeticIncidencePositivity
