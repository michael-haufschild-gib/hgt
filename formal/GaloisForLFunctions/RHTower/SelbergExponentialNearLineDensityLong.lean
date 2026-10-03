import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensity
import GaloisForLFunctions.RHTower.SelbergNearLineTailLong

/-!
# Exponential zero density at the critical scale with rate `e^{−a/14}`

The two-length Barban–Vehov mollifier of `SelbergExponentialNearLineDensity` with the long lengths
`X = ⌊U^{21/50}⌋`, `Y = ⌊U^{21/100}⌋` (made admissible by `exists_bv_window_bound_long`).  The
head `Σ_{Y < n ≤ X} Λ(n) n^{−s}/log(X/Y)` has mean square `≪ T e^{−21a/50}` on
`Re s = 1/2 + a/L`, the combined tail `≪ T e^{−a/7}` (`SelbergNearLineTailLong`), so the mollified
mean square is `T(1 + O(e^{−a/14}))` and Littlewood's lemma gives

`2π (a/L) · #{ρ : Re ρ ≥ 1/2 + 2a/L, T₁ ≤ Im ρ ≤ T₂} ≤ (T₂ − T₁) A e^{−a/14} + K L`

for every `1 ≤ a ≤ (L − 2)/2` simultaneously
(`exists_selberg_exponential_nearLine_zeroDensity_long`),
i.e. `N(σ; U/4, U/2) ≪ U^{1 − (σ − 1/2)/28} log U`, in place of the exponent `1/2400`.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- Size facts for the two lengths `X ≈ e^{21L/50}`, `Y ≈ e^{21L/100}`. -/
theorem twoLength_scale_facts_long {X Y : ℕ} {L : ℝ} (hL : 1000 ≤ L)
    (hXle : (X : ℝ) ≤ Real.exp (21 * L / 50)) (hXgt : Real.exp (21 * L / 50) - 1 < X)
    (hYle : (Y : ℝ) ≤ Real.exp (21 * L / 100)) (hYgt : Real.exp (21 * L / 100) - 1 < Y) :
    2 ≤ Y ∧ Y < X ∧ Real.exp (21 * L / 100) / 2 ≤ Y ∧ Real.exp (21 * L / 100) / 2 ≤ X ∧
      Real.log X ≤ 21 * L / 50 ∧ 0 ≤ Real.log Y ∧ Real.log Y ≤ 21 * L / 100 ∧
      21 * L / 200 ≤ Real.log X - Real.log Y := by
  have he5 := hundred_le_exp_five
  have hE5 : Real.exp 5 ≤ Real.exp (21 * L / 100) := Real.exp_le_exp.mpr (by linarith)
  have hsq : Real.exp (21 * L / 50) = Real.exp (21 * L / 100) * Real.exp (21 * L / 100) := by
    rw [← Real.exp_add]; ring_nf
  have hXbig : 100 * Real.exp (21 * L / 100) ≤ Real.exp (21 * L / 50) := by
    rw [hsq]; nlinarith [Real.exp_pos (21 * L / 100)]
  have hY2 : (2 : ℝ) ≤ Y := by linarith
  have hYX : (Y : ℝ) < X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hXhalf : Real.exp (21 * L / 50) / 2 ≤ X := by linarith
  refine ⟨by exact_mod_cast hY2, by exact_mod_cast hYX, by linarith, by linarith, ?_,
    Real.log_nonneg (by linarith), ?_, ?_⟩
  · have := Real.log_le_log hX0 hXle
    rwa [Real.log_exp] at this
  · have := Real.log_le_log hY0 hYle
    rwa [Real.log_exp] at this
  · have h1 := Real.log_le_log (by positivity) hXhalf
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
    have h2 : Real.log Y ≤ 21 * L / 100 := by
      have := Real.log_le_log hY0 hYle
      rwa [Real.log_exp] at this
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith

/-- `Y^{−2a/L} ≤ 2e^{−21a/50}` for `Y ≥ e^{21L/100}/2` and `2a ≤ L`. -/
theorem rpow_neg_twoLength_le_long {Y : ℕ} {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a)
    (haL : 2 * a ≤ L) (hY : Real.exp (21 * L / 100) / 2 ≤ Y) :
    (Y : ℝ) ^ (-(2 * (a / L))) ≤ 2 * Real.exp (-(21 * a / 50)) := by
  have hb0 : 0 < Real.exp (21 * L / 100) / 2 := by positivity
  have hstep : (Y : ℝ) ^ (-(2 * (a / L))) ≤ (Real.exp (21 * L / 100) / 2) ^ (-(2 * (a / L))) :=
    Real.rpow_le_rpow_of_nonpos hb0 hY (by have h0 : 0 ≤ a / L := div_nonneg ha hL.le; linarith)
  refine hstep.trans ?_
  rw [Real.rpow_def_of_pos hb0, Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have haL' : a / L ≤ 1 / 2 := by rw [div_le_iff₀ hL]; linarith
  have hexp : (21 * L / 100 - Real.log 2) * -(2 * (a / L)) ≤ -(21 * a / 50) + Real.log 2 := by
    have e : (21 * L / 100) * (2 * (a / L)) = 21 * a / 50 := by field_simp; ring
    have h1 : Real.log 2 * (2 * (a / L)) ≤ Real.log 2 := by
      have : 2 * (a / L) ≤ 1 := by linarith
      nlinarith
    nlinarith
  calc Real.exp ((21 * L / 100 - Real.log 2) * -(2 * (a / L)))
      ≤ Real.exp (-(21 * a / 50) + Real.log 2) := Real.exp_le_exp.mpr hexp
    _ = 2 * Real.exp (-(21 * a / 50)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]; ring

/-- **The head mean square at the scale `U = e^L`**: `∫|H|² ≤ 128 (T₂ − T₁) e^{−a/100}`. -/
theorem integral_normSq_twoLengthHead_rightShift_le_long {X Y : ℕ} {L a CM T₁ T₂ : ℝ}
    (hL : 1000 ≤ L) (hLCM : 100 * |CM| ≤ L)
    (hXle : (X : ℝ) ≤ Real.exp (21 * L / 50)) (hXgt : Real.exp (21 * L / 50) - 1 < X)
    (hYle : (Y : ℝ) ≤ Real.exp (21 * L / 100)) (hYgt : Real.exp (21 * L / 100) - 1 < Y)
    (hCM : ∑ k ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log X * (Real.log X + CM))
    (ha : 0 ≤ a) (haL : 2 * a ≤ L) (hT : T₁ ≤ T₂) (hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁) :
    ∫ τ in T₁..T₂, ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
        (((1 / 2 + a / L : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁) * (128 * Real.exp (-(21 * a / 50))) := by
  obtain ⟨hY2, hYX, hYhalf, hXhalf, hlogX, hlogY0, hlogY, hgap⟩ :=
    twoLength_scale_facts_long hL hXle hXgt hYle hYgt
  obtain ⟨-, -, hMVT, -⟩ := nearLine_length_facts_long hL hXle hXhalf
  have hL0 : 0 < L := by linarith
  have hpt : ∀ τ : ℝ, displacedLinePt (-(a / L)) τ = ((1 / 2 + a / L : ℝ) : ℂ) + (τ : ℂ) * I := by
    intro τ
    unfold displacedLinePt
    congr 2
    ring
  have h := integral_normSq_twoLengthHead_le (by omega) hYX (δ := a / L) (by positivity) hCM hT
  simp only [hpt] at h
  refine h.trans ?_
  have h1 : T₂ - T₁ + 8 * X * (1 + Real.log X) ≤ 2 * (T₂ - T₁) := by linarith
  have hYp := rpow_neg_twoLength_le_long hL0 ha haL hYhalf
  have hgap0 : 0 < Real.log X - Real.log Y := by linarith
  have hlogX0 : 0 ≤ Real.log X := by linarith
  have hprod : Real.log X * (Real.log X + CM) ≤ (21 * L / 50) * (2 * (21 * L / 50)) := by
    have hCMa : CM ≤ 21 * L / 50 := by
      have := le_abs_self CM
      linarith
    rcases le_or_gt (Real.log X + CM) 0 with hneg | hpos
    · have : Real.log X * (Real.log X + CM) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlogX0 hneg
      nlinarith
    · exact mul_le_mul hlogX (by linarith) hpos.le (by positivity)
  have h2 : (Y : ℝ) ^ (-(2 * (a / L))) * (Real.log X * (Real.log X + CM)) /
      (Real.log X - Real.log Y) ^ 2 ≤ 64 * Real.exp (-(21 * a / 50)) := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : (21 * L / 200) ^ 2 ≤ (Real.log X - Real.log Y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hgap 2
    have hY0 : 0 ≤ (Y : ℝ) ^ (-(2 * (a / L))) := by positivity
    have hE0 : 0 ≤ Real.exp (-(21 * a / 50)) := (Real.exp_pos _).le
    calc (Y : ℝ) ^ (-(2 * (a / L))) * (Real.log X * (Real.log X + CM))
        ≤ (2 * Real.exp (-(21 * a / 50))) * ((21 * L / 50) * (2 * (21 * L / 50))) := by
          rcases le_or_gt (Real.log X * (Real.log X + CM)) 0 with hneg | hpos
          · have : (Y : ℝ) ^ (-(2 * (a / L))) * (Real.log X * (Real.log X + CM)) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hY0 hneg
            have : 0 ≤ (2 * Real.exp (-(21 * a / 50))) * ((21 * L / 50) * (2 * (21 * L / 50))) := by
              positivity
            linarith
          · exact mul_le_mul hYp hprod hpos.le (by positivity)
      _ = 64 * Real.exp (-(21 * a / 50)) * (21 * L / 200) ^ 2 := by ring
      _ ≤ 64 * Real.exp (-(21 * a / 50)) * (Real.log X - Real.log Y) ^ 2 := by gcongr
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  calc (T₂ - T₁ + 8 * X * (1 + Real.log X)) *
        ((Y : ℝ) ^ (-(2 * (a / L))) * (Real.log X * (Real.log X + CM)) /
          (Real.log X - Real.log Y) ^ 2)
      ≤ (T₂ - T₁ + 8 * X * (1 + Real.log X)) * (64 * Real.exp (-(21 * a / 50))) := by
        refine mul_le_mul_of_nonneg_left h2 ?_
        have := Real.log_nonneg hX1
        nlinarith
    _ ≤ (2 * (T₂ - T₁)) * (64 * Real.exp (-(21 * a / 50))) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (T₂ - T₁) * (128 * Real.exp (-(21 * a / 50))) := by ring

/-- Littlewood count from a mean square `Msq ≤ (T₂ − T₁)(1 + r)`. -/
theorem count_le_of_meanSquare_rate_long {L a r C K₀ T₁ T₂ Mb Msq count : ℝ}
    (hK₀ : 0 ≤ K₀) (hT12 : T₁ < T₂) (hT₂L : Real.log T₂ ≤ L) (hMb : Real.log Mb ≤ 3 * L)
    (hMsq0 : 0 < Msq) (hMsq : Msq ≤ (T₂ - T₁) * (1 + r))
    (hmain : 2 * Real.pi * (a / L * count) ≤
      (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) + C + K₀ * (Real.log T₂ + Real.log Mb)) :
    2 * Real.pi * (a / L * count) ≤ (T₂ - T₁) / 2 * r + (C + 4 * K₀ * L) := by
  refine hmain.trans ?_
  have hT0 : 0 < T₂ - T₁ := by linarith
  have hlog1 : Real.log (Msq / (T₂ - T₁)) ≤ r := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hMsq0 hT0)
    have h2 : Msq / (T₂ - T₁) ≤ 1 + r := by rw [div_le_iff₀ hT0]; linarith
    linarith
  have h1 : (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) ≤ (T₂ - T₁) / 2 * r :=
    mul_le_mul_of_nonneg_left hlog1 (by linarith)
  have h2 : K₀ * (Real.log T₂ + Real.log Mb) ≤ K₀ * (4 * L) :=
    mul_le_mul_of_nonneg_left (by linarith) hK₀
  linarith

/-- The rate `3√η + 2η`, `η = A₀ e^{−a/7}`, is at most `(3√A₀ + 2A₀) e^{−a/14}`. -/
theorem twoLength_rate_le_long {A₀ a : ℝ} (hA₀ : 0 ≤ A₀) (ha : 0 ≤ a) :
    3 * Real.sqrt (A₀ * Real.exp (-(a / 7))) + 2 * (A₀ * Real.exp (-(a / 7))) ≤
      (3 * Real.sqrt A₀ + 2 * A₀) * Real.exp (-(a / 14)) := by
  have hsq : Real.sqrt (A₀ * Real.exp (-(a / 7))) = Real.sqrt A₀ * Real.exp (-(a / 14)) := by
    rw [Real.sqrt_mul hA₀, ← Real.exp_half]
    congr 2
    ring
  have he : A₀ * Real.exp (-(a / 7)) ≤ A₀ * Real.exp (-(a / 14)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hA₀
  rw [hsq]
  nlinarith

/-- The final count at one scale, from the consumer inequality for the two-length mollifier. -/
theorem twoLength_final_count_long {L a C K₀ A₀ T₁ T₂ Mb count : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hK₀ : 0 ≤ K₀) (hA₀ : 0 ≤ A₀) (ha : 0 ≤ a) (hT12 : T₁ < T₂) (hlogT₂ : Real.log T₂ ≤ L)
    (hlogMb : Real.log Mb ≤ 3 * L)
    (hmain : 2 * Real.pi * (a / L * count) ≤
      (T₂ - T₁) / 2 * Real.log ((T₂ - T₁) * (1 + 3 * Real.sqrt (A₀ * Real.exp (-(a / 7))) +
        2 * (A₀ * Real.exp (-(a / 7)))) / (T₂ - T₁)) + C +
        K₀ * (Real.log T₂ + Real.log Mb)) :
    2 * Real.pi * (a / L * count) ≤
      (T₂ - T₁) * ((3 * Real.sqrt A₀ + 2 * A₀) / 2 * Real.exp (-(a / 14))) + (C + 4 * K₀) * L := by
  set r : ℝ := 3 * Real.sqrt (A₀ * Real.exp (-(a / 7))) + 2 * (A₀ * Real.exp (-(a / 7)))
    with hr
  have hT0 : 0 < T₂ - T₁ := by linarith
  have hMsq0 : 0 < (T₂ - T₁) * (1 + 3 * Real.sqrt (A₀ * Real.exp (-(a / 7))) +
      2 * (A₀ * Real.exp (-(a / 7)))) := by positivity
  have hcount := count_le_of_meanSquare_rate_long (r := r) hK₀ hT12 hlogT₂ hlogMb hMsq0
    (le_of_eq (by rw [hr]; ring)) hmain
  have hrate := twoLength_rate_le_long hA₀ ha
  rw [← hr] at hrate
  have h1 : (T₂ - T₁) / 2 * r ≤
      (T₂ - T₁) * ((3 * Real.sqrt A₀ + 2 * A₀) / 2 * Real.exp (-(a / 14))) := by
    calc (T₂ - T₁) / 2 * r
        ≤ (T₂ - T₁) / 2 * ((3 * Real.sqrt A₀ + 2 * A₀) * Real.exp (-(a / 14))) :=
          mul_le_mul_of_nonneg_left hrate (by linarith)
      _ = _ := by ring
  have h2 : C + 4 * K₀ * L ≤ (C + 4 * K₀) * L := by nlinarith
  calc 2 * Real.pi * (a / L * count) ≤ (T₂ - T₁) / 2 * r + (C + 4 * K₀ * L) := hcount
    _ ≤ _ := add_le_add h1 h2

/-- **The combined tail** `(log X · f_X − log Y · f_Y)/log(X/Y)` has mean square
`≤ 120 C_f (T₂ − T₁) e^{−a/7}` once both tails obey the long three-lines bound. -/
theorem integral_normSq_twoLengthTail_le_long {X Y : ℕ} {L a Cf T₁ T₂ : ℝ} (σ₀ : ℝ)
    (hCf : 0 < Cf) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) (hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁)
    (hlogY0 : 0 ≤ Real.log Y) (hlogY : Real.log Y ≤ 21 * L / 100)
    (hgap : 21 * L / 200 ≤ Real.log X - Real.log Y) (hL : 0 < L)
    (hfX : ∫ t in T₁..T₂, ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((2 * a + 1) / 14)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L)))
    (hfY : ∫ t in T₁..T₂, ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((2 * a + 1) / 14)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L))) :
    ∫ t in T₁..T₂, ‖(((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)‖ ^ 2 ≤
      (T₂ - T₁) * (120 * Cf * Real.exp (-(a / 7))) := by
  have hgap0 : 0 < Real.log X - Real.log Y := by
    have : 0 < 21 * L / 200 := by positivity
    linarith
  have hcX := continuousOn_hbMollifiedTail_line X σ₀ (T₂ := T₂) hT₁
  have hcY := continuousOn_hbMollifiedTail_line Y σ₀ (T₂ := T₂) hT₁
  have hiX : IntervalIntegrable (fun t : ℝ => ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume T₁ T₂ := (hcX.norm.pow 2).intervalIntegrable_of_Icc hT
  have hiY : IntervalIntegrable (fun t : ℝ => ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume T₁ T₂ := (hcY.norm.pow 2).intervalIntegrable_of_Icc hT
  have hcg : ContinuousOn (fun t : ℝ =>
      (((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)) (Icc T₁ T₂) :=
    ((continuousOn_const.mul hcX).sub (continuousOn_const.mul hcY)).div_const _
  have hig : IntervalIntegrable (fun t : ℝ =>
      ‖(((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)‖ ^ 2) volume T₁ T₂ :=
    (hcg.norm.pow 2).intervalIntegrable_of_Icc hT
  have hpt : ∀ t ∈ Icc T₁ T₂,
      ‖(((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)‖ ^ 2 ≤
        32 * ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 +
          8 * ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    fun t _ => normSq_twoLength_tail_le (by linarith) hlogY0 hgap0 (by linarith) (by linarith) _ _
  have hmono := intervalIntegral.integral_mono_on hT hig
    ((hiX.const_mul 32).add (hiY.const_mul 8)) hpt
  rw [intervalIntegral.integral_add (hiX.const_mul 32) (hiY.const_mul 8),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  refine hmono.trans ?_
  have he : Real.exp (-((2 * a + 1) / 14)) ≤ Real.exp (-(a / 7)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : T₂ - T₁ + 2 * Real.exp (99 / 100 * L) ≤ 3 * (T₂ - T₁) := by linarith
  have hB : Cf * Real.exp (-((2 * a + 1) / 14)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L)) ≤
      Cf * Real.exp (-(a / 7)) * (3 * (T₂ - T₁)) := by
    have : 0 ≤ T₂ - T₁ + 2 * Real.exp (99 / 100 * L) := by positivity
    gcongr
  have := add_le_add (mul_le_mul_of_nonneg_left (hfX.trans hB) (by norm_num : (0 : ℝ) ≤ 32))
    (mul_le_mul_of_nonneg_left (hfY.trans hB) (by norm_num : (0 : ℝ) ≤ 8))
  linarith

/-- **The two-length mollified mean square on `Re s = 1/2 + a/L`** is
`(T₂ − T₁)(1 + 3√η + 2η)`, `η = (128 + 120 C_f) e^{−a/7}`. -/
theorem integral_normSq_zetaTwoLength_rightShift_le_long {X Y : ℕ} {L a CM Cf T₁ T₂ : ℝ}
    (hL : 1000 ≤ L) (hLCM : 100 * |CM| ≤ L) (hCf : 0 < Cf)
    (hXle : (X : ℝ) ≤ Real.exp (21 * L / 50)) (hXgt : Real.exp (21 * L / 50) - 1 < X)
    (hYle : (Y : ℝ) ≤ Real.exp (21 * L / 100)) (hYgt : Real.exp (21 * L / 100) - 1 < Y)
    (hCM : ∑ k ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log X * (Real.log X + CM))
    (ha : 0 ≤ a) (haL : 2 * a ≤ L) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    (hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁)
    (hfX : ∫ t in T₁..T₂, ‖hbMollifiedTail X (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((2 * a + 1) / 14)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L)))
    (hfY : ∫ t in T₁..T₂, ‖hbMollifiedTail Y (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((2 * a + 1) / 14)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L))) :
    ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X)
          (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁) * (1 + 3 * Real.sqrt ((128 + 120 * Cf) * Real.exp (-(a / 7))) +
        2 * ((128 + 120 * Cf) * Real.exp (-(a / 7)))) := by
  obtain ⟨hY2, hYX, -, -, -, hlogY0, hlogY, hgap⟩ :=
    twoLength_scale_facts_long hL hXle hXgt hYle hYgt
  have hL0 : 0 < L := by linarith
  set σ₀ : ℝ := 1 / 2 + a / L with hσ₀
  have hP := integral_normSq_twoLengthHead_rightShift_le_long hL hLCM hXle hXgt hYle hYgt hCM ha haL
    hT hlen
  have hg := integral_normSq_twoLengthTail_le_long σ₀ hCf hT₁ hT hlen hlogY0 hlogY hgap hL0
    hfX hfY
  set η : ℝ := (128 + 120 * Cf) * Real.exp (-(a / 7)) with hη
  have hη0 : 0 < η := by positivity
  have he : Real.exp (-(21 * a / 50)) ≤ Real.exp (-(a / 7)) := Real.exp_le_exp.mpr (by linarith)
  have hsum : (∫ t in T₁..T₂, ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
        (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) +
      (∫ t in T₁..T₂, ‖(((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)‖ ^ 2) ≤ (T₂ - T₁) * η := by
    have hT0 : 0 ≤ T₂ - T₁ := by linarith
    have h1 : (T₂ - T₁) * (128 * Real.exp (-(21 * a / 50))) ≤
        (T₂ - T₁) * (128 * Real.exp (-(a / 7))) := by gcongr
    rw [hη]
    nlinarith
  have hs : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hPc : ContinuousOn (fun t : ℝ => edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
      (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I)) (Icc T₁ T₂) :=
    ((differentiable_edPoly _ hs).continuous.comp (by fun_prop)).continuousOn
  have hgc : ContinuousOn (fun t : ℝ =>
      (((Real.log X : ℝ) : ℂ) * hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I) -
        ((Real.log Y : ℝ) : ℂ) * hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)) /
          ((Real.log X - Real.log Y : ℝ) : ℂ)) (Icc T₁ T₂) :=
    ((continuousOn_const.mul (continuousOn_hbMollifiedTail_line X σ₀ hT₁)).sub
      (continuousOn_const.mul (continuousOn_hbMollifiedTail_line Y σ₀ hT₁))).div_const _
  have hMsq := integral_normSq_one_add_add_le hT hη0 hPc hgc hsum
  simp only [zeta_mul_twoLength_eq hY2 hYX]
  exact hMsq

/-- **Exponential zero density at the critical scale with rate `e^{−a/14}`.** For all large `U`,
with `L = log U`, admissible heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` exist such that
for every `1 ≤ a` with `2a + 2 ≤ L` the zeros with `Re ρ ≥ 1/2 + 2a/L` between them satisfy
`2π (a/L) · #zeros ≤ (T₂ − T₁) A e^{−a/14} + K L`. -/
theorem exists_selberg_exponential_nearLine_zeroDensity_long :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ a : ℝ, 1 ≤ a → 2 * a + 2 ≤ Real.log U →
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          2 * Real.pi * ((a / Real.log U) *
            ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
            (T₂ - T₁) * (A * Real.exp (-(a / 14))) + K * Real.log U := by
  obtain ⟨C, K₀, hC, hK₀, hcons⟩ := exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide
  obtain ⟨CfX, hCfX, htailX⟩ :=
    exists_eventually_integral_hbMollifiedTail_rightShift_le_long (θ := 21 / 50) (by norm_num)
      le_rfl
  obtain ⟨CfY, hCfY, htailY⟩ :=
    exists_eventually_integral_hbMollifiedTail_rightShift_le_long (θ := 21 / 100) le_rfl
      (by norm_num)
  set Cf : ℝ := CfX + CfY with hCfdef
  have hCf : 0 < Cf := by positivity
  obtain ⟨CM, hCM⟩ := exists_sum_vonMangoldt_sq_div_le
  have hA₀0 : 0 < 128 + 120 * Cf := by positivity
  refine ⟨(3 * Real.sqrt (128 + 120 * Cf) + 2 * (128 + 120 * Cf)) / 2, C + 4 * K₀, by positivity,
    by positivity, ?_⟩
  filter_upwards [htailX, htailY, eventually_ge_atTop (Real.exp (max 1000 (100 * |CM|)))]
    with U htailXU htailYU hUL₀
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hUL₀
  have hL := Real.log_le_log (Real.exp_pos _) hUL₀
  rw [Real.log_exp] at hL
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log U := ⟨_, rfl⟩
  have hUexp : U = Real.exp L := by rw [hLdef, Real.exp_log hU0]
  rw [← hLdef] at hL
  subst hUexp
  simp only [Real.log_exp] at htailXU htailYU ⊢
  have hL1000 : 1000 ≤ L := le_trans (le_max_left _ _) hL
  have hLCM : 100 * |CM| ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hU100 : Real.exp L ^ ((21 : ℝ) / 50) = Real.exp (21 * L / 50) := by
    rw [← Real.exp_mul]; ring_nf
  have hU200 : Real.exp L ^ ((21 : ℝ) / 100) = Real.exp (21 * L / 100) := by
    rw [← Real.exp_mul]; ring_nf
  have hU99 : Real.exp L ^ ((99 : ℝ) / 100) = Real.exp (99 / 100 * L) := by
    rw [← Real.exp_mul]; ring_nf
  set X : ℕ := ZetaGateProductAFE.bvLen (21 / 50) (Real.exp L) with hXdef
  set Y : ℕ := ZetaGateProductAFE.bvLen (21 / 100) (Real.exp L) with hYdef
  have hXle : (X : ℝ) ≤ Real.exp (21 * L / 50) := by
    rw [← hU100]; exact ZetaGateProductAFE.bvLen_le (Real.exp_pos L).le
  have hXgt : Real.exp (21 * L / 50) - 1 < X := by
    rw [← hU100]; exact ZetaGateProductAFE.bvLen_gt _ (Real.exp L)
  have hYle : (Y : ℝ) ≤ Real.exp (21 * L / 100) := by
    rw [← hU200]; exact ZetaGateProductAFE.bvLen_le (Real.exp_pos L).le
  have hYgt : Real.exp (21 * L / 100) - 1 < Y := by
    rw [← hU200]; exact ZetaGateProductAFE.bvLen_gt _ (Real.exp L)
  obtain ⟨hY2, hYX, hYhalf, hXhalf, hlogX, -, -, -⟩ :=
    twoLength_scale_facts_long hL1000 hXle hXgt hYle hYgt
  obtain ⟨-, hHU, -, -, hU160, -⟩ := nearLine_scale_facts (by linarith : (500 : ℝ) ≤ L)
  have hbn : ∀ n ∈ Finset.Icc 1 X, ‖twoLengthCoeff X Y n‖ ≤ 1 :=
    fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn
  obtain ⟨T₁, hT₁, T₂, hT₂, hE1, hE2⟩ := exists_admissible_heights_of_mollifier
    (b := twoLengthCoeff X Y) (N := X) (by omega) (twoLengthCoeff_one (by omega) hYX) hbn
    (A₁ := Real.exp L / 4) (B₁ := Real.exp L / 4 + 1) (A₂ := Real.exp L / 2 - 1)
    (B₂ := Real.exp L / 2) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha haL Z hZ => ?_⟩
  have hT₁₂ : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hlenpos : 0 ≤ T₂ - T₁ + 2 * Real.exp (99 / 100 * L) := by
    have := Real.exp_pos (99 / 100 * L); linarith
  have hfX : ∫ t in T₁..T₂, ‖hbMollifiedTail X (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((2 * a + 1) / 14)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L)) := by
    have h := htailXU a (by linarith) haL T₁ T₂ hT₁.1.le hT₁₂ hT₂.2.le
    rw [hU99] at h
    refine h.trans ?_
    gcongr
    linarith
  have hfY : ∫ t in T₁..T₂, ‖hbMollifiedTail Y (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((2 * a + 1) / 14)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L)) := by
    have h := htailYU a (by linarith) haL T₁ T₂ hT₁.1.le hT₁₂ hT₂.2.le
    rw [hU99] at h
    refine h.trans ?_
    gcongr
    linarith
  have hMsq := integral_normSq_zetaTwoLength_rightShift_le_long hL1000 hLCM hCf hXle hXgt hYle hYgt
    (hCM X (by omega)) (by linarith) (by linarith) (by linarith [hT₁.1]) hT₁₂ hlen hfX hfY
  have hσ₀a : 1 / 4 ≤ 1 / 2 + a / L := by
    have : 0 < a / L := div_pos (by linarith) hL0
    linarith
  have hσ₀b : 1 / 2 + a / L < 2 := by
    have : a / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have hmem : ∀ x ∈ Icc (1 / 2 + a / L) (15 / 2 : ℝ), x ∈ Icc (1 / 4 : ℝ) (15 / 2) :=
    fun x hx => ⟨le_trans hσ₀a hx.1, hx.2⟩
  have hXX : (1 : ℝ) ≤ (X : ℝ) ^ (5 : ℕ) :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ X))
  have hmain := hcons (twoLengthCoeff X Y) X (by omega) (twoLengthCoeff_one (by omega) hYX) hbn
    (fun n _ => conj_twoLengthCoeff X Y n) _ hXX
    (sum_norm_twoLengthCoeff_mul_rpow_le (by omega) hYX) (1 / 2 + a / L) T₁ T₂ _
    hσ₀a hσ₀b (by linarith [hT₁.1]) hT12
    (fun x hx => (hE1 x (hmem x hx)).1) (fun x hx => (hE2 x (hmem x hx)).1)
    (fun x hx => (hE1 x (hmem x hx)).2) (fun x hx => (hE2 x (hmem x hx)).2)
    hMsq Z hZ (a / L) (div_pos (by linarith) hL0).le
  have hfilter : Z.filter (fun w => 1 / 2 + a / L + a / L ≤ w.re) =
      Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re) := by
    refine Finset.filter_congr fun w _ => ?_
    rw [show 1 / 2 + a / L + a / L = 1 / 2 + 2 * a / L by ring]
  rw [hfilter] at hmain
  have hlogT₂ : Real.log T₂ ≤ L := by
    have h1 : T₂ ≤ Real.exp L := le_trans hT₂.2.le (by linarith [Real.exp_pos L])
    have := Real.log_le_log (by linarith [hT₁.1, hT₁.2, hT₂.1]) h1
    rwa [Real.log_exp] at this
  have hlogMb : Real.log ((X : ℝ) ^ (5 : ℕ)) ≤ 3 * L := by
    rw [Real.log_pow]
    push_cast
    linarith
  exact twoLength_final_count_long (by linarith) hC.le hK₀.le hA₀0.le (by linarith) hT12 hlogT₂
    hlogMb hmain

end RHTower
