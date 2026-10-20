import GaloisForLFunctions.BiScaleUncertainty.ExactSingleIntegerBlindSymbolSlack

/-!
# One multiplicatively independent node strictly improves the single-integer bathtub

Let `q ≥ 2`, `ℓ = log q`, and `m_q` the period mean of `γ`. On combinations blind at the powers of
`q` the archimedean part without the pole is at least `m_q` times the mass, and this is exact
(`ExactSingleIntegerBlindSymbolSlack`). Add blindness at one more integer `n ≥ 2`.

* If `n` is a power of `q` nothing changes: the slack stays exactly `−m_q`.
* If `n` is not a power of `q` the bathtub improves by an explicit amount
  (`symbolPeriodMean_add_gain_mul_massOf_le`):
  `A(c) ≥ (m_q + |s|/C) mass(c)`, `s = sin(π log n/ℓ)/(π log n/ℓ) ≠ 0`.

**Mechanism.** Write `ρ(r) = ‖r ℓ mod 2π‖/ℓ ∈ [0, π/ℓ]` for the folded radius. Blindness at the
powers of `q` makes `∫ G cos(t ρ) = s ∫ G` with `t = log n`, while blindness at `n` gives
`∫ G cos(r t) = 0`. So `|s| ∫ G ≤ ∫ G |cos(rt) − cos(tρ)|`. The cosine defect is paid by the fold
defect of the symbol: `|cos(rt) − cos(tρ(r))| ≤ C (γ(r) − γ(ρ(r)))` pointwise, because a frequency
outside the fundamental period either straddles `π/ℓ` (then `γ` has slope at least
`κ = (π/(8ℓ))/(1/16 + π²/ℓ²)²` there, from the first Gauss term) or lies beyond `2π/ℓ` (then the
fold defect is at least `κπ/ℓ`). Integrating, `|s| ∫G ≤ C (∫ Gγ − m_q ∫ G)`.

**Consequences.**
* `blindSymbolSlackOn_insert_iff_of_mem` / `exists_lt_blindSymbolSlackOn_insert_of_not_mem`: the
  single-integer bathtub is improved by one extra node exactly when the node is multiplicatively
  independent of `q`. The constant depends on arithmetic incidence, not on spacing alone.
* `blindSymbolSlack_two_three`: blindness at `2, 4, 8, …` and at `3` gives
  `BlindSymbolSlack (−m₂ − η₂₃)` with explicit `η₂₃ > 0`, strictly below the dyadic constant.
* `zeroPoleBlindSymbolSlackOn_iff_of_gapped`: on every gapped node set the zero-pole slack equals the
  slack; both improvements therefore hold for zero-pole combinations as well.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. The slope of `γ` across `π/ℓ` -/

theorem gaussTerm_zero_eq (r : ℝ) : gaussTerm r 0 = r ^ 2 / (1 / 16 + r ^ 2 / 4) := by
  unfold gaussTerm
  push_cast
  field_simp
  ring

/-- `γ(b) − γ(a)` dominates the difference of the first Gauss terms. -/
theorem gaussTerm_zero_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    gaussTerm b 0 - gaussTerm a 0 ≤ EF.gammaBracket b - EF.gammaBracket a := by
  have h := (hasSum_gaussTerm b).sub (hasSum_gaussTerm a)
  rw [show EF.gammaBracket b - EF.gammaBracket 0 - (EF.gammaBracket a - EF.gammaBracket 0) =
    EF.gammaBracket b - EF.gammaBracket a by ring] at h
  refine le_hasSum h 0 fun j _ => ?_
  have := gaussTerm_le_of_abs_le (s := a) (r := b)
    (by rw [abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]; exact hab) j
  linarith

/-- The crossing slope `κ(ℓ) = (π/(8ℓ))/(1/16 + π²/ℓ²)²`. -/
def crossingSlope (ℓ : ℝ) : ℝ := π / (8 * ℓ) / (1 / 16 + π ^ 2 / ℓ ^ 2) ^ 2

theorem crossingSlope_pos {ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < crossingSlope ℓ := by
  unfold crossingSlope; positivity

/-- **Crossing slope.** If `0 ≤ a ≤ b ≤ 2π/ℓ` and `a + b ≥ 2π/ℓ`, then
`γ(b) − γ(a) ≥ κ(ℓ)(b − a)`. -/
theorem crossingSlope_mul_le {ℓ a b : ℝ} (hℓ : 0 < ℓ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2 * π / ℓ) (hsum : 2 * π / ℓ ≤ a + b) :
    crossingSlope ℓ * (b - a) ≤ EF.gammaBracket b - EF.gammaBracket a := by
  refine le_trans ?_ (gaussTerm_zero_sub_le ha hab)
  rw [gaussTerm_zero_eq, gaussTerm_zero_eq]
  have hca : 0 < 1 / 16 + a ^ 2 / 4 := by positivity
  have hcb : 0 < 1 / 16 + b ^ 2 / 4 := by positivity
  have hdiff : b ^ 2 / (1 / 16 + b ^ 2 / 4) - a ^ 2 / (1 / 16 + a ^ 2 / 4) =
      (b - a) * (b + a) / 16 / ((1 / 16 + a ^ 2 / 4) * (1 / 16 + b ^ 2 / 4)) := by
    field_simp; ring
  rw [hdiff]
  have hb0 : 0 ≤ b := ha.trans hab
  have hB : b ^ 2 / 4 ≤ π ^ 2 / ℓ ^ 2 := by
    have h1 : b ^ 2 ≤ (2 * π / ℓ) ^ 2 := pow_le_pow_left₀ hb0 hb 2
    have h2 : (2 * π / ℓ) ^ 2 / 4 = π ^ 2 / ℓ ^ 2 := by field_simp; ring
    linarith
  have hA : a ^ 2 / 4 ≤ π ^ 2 / ℓ ^ 2 := by
    have : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
    linarith
  have hden : (1 / 16 + a ^ 2 / 4) * (1 / 16 + b ^ 2 / 4) ≤ (1 / 16 + π ^ 2 / ℓ ^ 2) ^ 2 := by
    have hP : 0 ≤ 1 / 16 + π ^ 2 / ℓ ^ 2 := by positivity
    calc (1 / 16 + a ^ 2 / 4) * (1 / 16 + b ^ 2 / 4)
        ≤ (1 / 16 + π ^ 2 / ℓ ^ 2) * (1 / 16 + π ^ 2 / ℓ ^ 2) :=
          mul_le_mul (by linarith) (by linarith) hcb.le hP
      _ = (1 / 16 + π ^ 2 / ℓ ^ 2) ^ 2 := (sq _).symm
  have hba : 0 ≤ b - a := by linarith
  have hnum : (b - a) * (2 * π / ℓ) / 16 ≤ (b - a) * (b + a) / 16 := by
    have := mul_le_mul_of_nonneg_left hsum hba
    linarith
  have hnum0 : 0 ≤ (b - a) * (b + a) / 16 := by positivity
  unfold crossingSlope
  calc π / (8 * ℓ) / (1 / 16 + π ^ 2 / ℓ ^ 2) ^ 2 * (b - a)
      = (b - a) * (2 * π / ℓ) / 16 / (1 / 16 + π ^ 2 / ℓ ^ 2) ^ 2 := by field_simp; ring
    _ ≤ (b - a) * (b + a) / 16 / (1 / 16 + π ^ 2 / ℓ ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (b - a) * (b + a) / 16 / ((1 / 16 + a ^ 2 / 4) * (1 / 16 + b ^ 2 / 4)) :=
        div_le_div_of_nonneg_left hnum0 (by positivity) hden

/-! ### 2. The folded radius -/

/-- The folded radius `ρ(r) = ‖r ℓ mod 2π‖/ℓ ∈ [0, π/ℓ]`. -/
def foldedRadius (ℓ r : ℝ) : ℝ := ‖phase ℓ r‖ / ℓ

theorem continuous_foldedRadius (ℓ : ℝ) : Continuous (foldedRadius ℓ) :=
  (continuous_norm.comp (continuous_phase ℓ)).div_const ℓ

theorem foldedRadius_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℝ) : 0 ≤ foldedRadius ℓ r :=
  div_nonneg (norm_nonneg _) hℓ.le

theorem foldedRadius_le {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℝ) : foldedRadius ℓ r ≤ π / ℓ := by
  have h := AddCircle.norm_le_half_period (2 * π) (x := phase ℓ r) (by positivity)
  rw [abs_of_pos (by positivity), show 2 * π / 2 = π by ring] at h
  exact div_le_div_of_nonneg_right h hℓ.le

theorem foldedRadius_le_abs {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℝ) : foldedRadius ℓ r ≤ |r| := by
  have hn : ‖phase ℓ r‖ ≤ |r * ℓ| := by
    have := QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (2 * π)) (m := r * ℓ)
    simpa [phase, Real.norm_eq_abs] using this
  rw [abs_mul, abs_of_pos hℓ] at hn
  rw [foldedRadius, div_le_iff₀ hℓ]
  exact hn

theorem foldedRadius_neg (ℓ r : ℝ) : foldedRadius ℓ (-r) = foldedRadius ℓ r := by
  have : phase ℓ (-r) = -phase ℓ r := by
    simp only [phase, neg_mul]; exact AddCircle.coe_neg (p := 2 * π)
  rw [foldedRadius, foldedRadius, this, norm_neg]

theorem foldedRadius_abs (ℓ r : ℝ) : foldedRadius ℓ |r| = foldedRadius ℓ r := by
  rcases abs_choice r with h | h <;> rw [h]
  exact foldedRadius_neg ℓ r

/-- A nonnegative frequency is either inside the fundamental period or straddles `π/ℓ`:
`ρ(r) = r` or `r + ρ(r) ≥ 2π/ℓ`. -/
theorem foldedRadius_eq_or {ℓ r : ℝ} (hℓ : 0 < ℓ) (hr : 0 ≤ r) :
    foldedRadius ℓ r = r ∨ 2 * π / ℓ ≤ r + foldedRadius ℓ r := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set x : ℝ := r * ℓ with hx
  have hx0 : 0 ≤ x := mul_nonneg hr hℓ.le
  have hnorm : ‖phase ℓ r‖ = |x - (round ((2 * π)⁻¹ * x) : ℝ) * (2 * π)| :=
    AddCircle.norm_eq (2 * π)
  set m : ℤ := round ((2 * π)⁻¹ * x) with hm
  have hround := abs_sub_round ((2 * π)⁻¹ * x)
  rw [← hm] at hround
  have hm0 : 0 ≤ m := by
    have h1 : (-(1 / 2) : ℝ) ≤ m := by
      have := (abs_le.mp hround).2
      have : 0 ≤ (2 * π)⁻¹ * x := by positivity
      linarith
    by_contra hneg
    have hlt : m + 1 ≤ 0 := Int.lt_iff_add_one_le.mp (lt_of_not_ge hneg)
    have : (m : ℝ) + 1 ≤ 0 := by exact_mod_cast hlt
    linarith
  rcases eq_or_lt_of_le hm0 with h0 | hpos
  · left
    rw [foldedRadius, hnorm, ← h0, Int.cast_zero, zero_mul, sub_zero, abs_of_nonneg hx0, hx]
    field_simp
  · right
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos
    have hge : (m : ℝ) * (2 * π) - x ≤ ‖phase ℓ r‖ := by
      rw [hnorm]; have := neg_le_abs (x - (m : ℝ) * (2 * π)); linarith
    have h2 : 2 * π - x ≤ ‖phase ℓ r‖ := by nlinarith
    have h3 : (2 * π - x) / ℓ ≤ ‖phase ℓ r‖ / ℓ := div_le_div_of_nonneg_right h2 hℓ.le
    have h4 : (2 * π - x) / ℓ = 2 * π / ℓ - r := by rw [hx]; field_simp
    rw [foldedRadius]
    linarith

/-! ### 3. The cosine defect is paid by the fold defect -/

/-- `C(ℓ, t) = t/κ + 2ℓ/(κπ)`. -/
def phaseDefectConstant (ℓ t : ℝ) : ℝ :=
  t / crossingSlope ℓ + 2 * ℓ / (crossingSlope ℓ * π)

theorem phaseDefectConstant_pos {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 ≤ t) :
    0 < phaseDefectConstant ℓ t := by
  have := crossingSlope_pos hℓ
  unfold phaseDefectConstant; positivity

/-- **Pointwise defect law.** `|cos(rt) − cos(ρ(r)t)| ≤ C(ℓ,t) (γ(r) − γ(ρ(r)))`. -/
theorem abs_cos_sub_cos_foldedRadius_le {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 ≤ t) (r : ℝ) :
    |Real.cos (r * t) - Real.cos (foldedRadius ℓ r * t)| ≤
      phaseDefectConstant ℓ t * (EF.gammaBracket r - EF.gammaBracket (foldedRadius ℓ r)) := by
  have hcos : Real.cos (r * t) = Real.cos (|r| * t) := by
    rcases abs_choice r with h | h <;> rw [h]; rw [neg_mul, Real.cos_neg]
  have hγ : EF.gammaBracket r = EF.gammaBracket |r| := by
    rcases abs_choice r with h | h <;> rw [h]; rw [gammaBracket_neg]
  rw [hcos, hγ, ← foldedRadius_abs ℓ r]
  have hx : 0 ≤ |r| := abs_nonneg r
  generalize |r| = x at hx ⊢
  have hκ := crossingSlope_pos hℓ
  have hρ0 := foldedRadius_nonneg hℓ x
  have hρπ := foldedRadius_le hℓ x
  have hρx : foldedRadius ℓ x ≤ x := by
    have := foldedRadius_le_abs hℓ x; rwa [abs_of_nonneg hx] at this
  set ρ := foldedRadius ℓ x with hρdef
  have hγ0 : 0 ≤ EF.gammaBracket x - EF.gammaBracket ρ := by
    have := gammaBracket_le_of_abs_le (s := ρ) (r := x)
      (by rw [abs_of_nonneg hρ0, abs_of_nonneg hx]; exact hρx)
    linarith
  have hC1 : t / crossingSlope ℓ ≤ phaseDefectConstant ℓ t := by
    unfold phaseDefectConstant
    have : 0 ≤ 2 * ℓ / (crossingSlope ℓ * π) := by positivity
    linarith
  have hC2 : 2 * ℓ / (crossingSlope ℓ * π) ≤ phaseDefectConstant ℓ t := by
    unfold phaseDefectConstant
    have : 0 ≤ t / crossingSlope ℓ := by positivity
    linarith
  rcases foldedRadius_eq_or hℓ hx with h | h
  · rw [← hρdef] at h
    rw [h, sub_self, abs_zero, sub_self, mul_zero]
  · rw [← hρdef] at h
    by_cases hx2 : x ≤ 2 * π / ℓ
    · have h1 := crossingSlope_mul_le hℓ hρ0 hρx hx2 (by linarith)
      have h2 : |Real.cos (x * t) - Real.cos (ρ * t)| ≤ t * (x - ρ) := by
        have := Real.abs_cos_sub_cos_le (x * t) (ρ * t)
        have e : |x * t - ρ * t| = t * (x - ρ) := by
          rw [← sub_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ x - ρ), abs_of_nonneg ht]
          ring
        linarith
      have h3 : t * (x - ρ) ≤ t / crossingSlope ℓ * (EF.gammaBracket x - EF.gammaBracket ρ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
        have := mul_le_mul_of_nonneg_left h1 ht
        linarith
      calc
        _ ≤ t * (x - ρ) := h2
        _ ≤ t / crossingSlope ℓ * (EF.gammaBracket x - EF.gammaBracket ρ) := h3
        _ ≤ _ := mul_le_mul_of_nonneg_right hC1 hγ0
    · rw [not_le] at hx2
      have hπℓ : 0 < π / ℓ := by positivity
      have h1 : crossingSlope ℓ * (π / ℓ) ≤
          EF.gammaBracket (2 * π / ℓ) - EF.gammaBracket (π / ℓ) := by
        have := crossingSlope_mul_le hℓ (a := π / ℓ) (b := 2 * π / ℓ) hπℓ.le
          (by rw [mul_div_assoc]; linarith) le_rfl (by rw [mul_div_assoc]; linarith)
        rwa [show 2 * π / ℓ - π / ℓ = π / ℓ by ring] at this
      have h2 : EF.gammaBracket (2 * π / ℓ) ≤ EF.gammaBracket x :=
        gammaBracket_le_of_abs_le (by rw [abs_of_pos (by positivity), abs_of_nonneg hx]; linarith)
      have h3 : EF.gammaBracket ρ ≤ EF.gammaBracket (π / ℓ) :=
        gammaBracket_le_of_abs_le (by rw [abs_of_nonneg hρ0, abs_of_pos hπℓ]; exact hρπ)
      have h4 : |Real.cos (x * t) - Real.cos (ρ * t)| ≤ 2 := by
        have := abs_sub (Real.cos (x * t)) (Real.cos (ρ * t))
        linarith [Real.abs_cos_le_one (x * t), Real.abs_cos_le_one (ρ * t)]
      have h5 : (2 : ℝ) = 2 * ℓ / (crossingSlope ℓ * π) * (crossingSlope ℓ * (π / ℓ)) := by
        field_simp
      calc
        _ ≤ 2 := h4
        _ = 2 * ℓ / (crossingSlope ℓ * π) * (crossingSlope ℓ * (π / ℓ)) := h5
        _ ≤ 2 * ℓ / (crossingSlope ℓ * π) * (EF.gammaBracket x - EF.gammaBracket ρ) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right hC2 hγ0

/-! ### 4. The gain -/

/-- The circle mean `s(ℓ,t) = sin(πt/ℓ)/(πt/ℓ)` of `cos(tθ/ℓ)`. -/
def periodCosineMean (ℓ t : ℝ) : ℝ := ℓ / (π * t) * Real.sin (π * t / ℓ)

theorem integral_cos_mul_eq {ℓ t : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) :
    ℓ / π * ∫ v in (0 : ℝ)..π / ℓ, Real.cos (v * t) = periodCosineMean ℓ t := by
  have h := intervalIntegral.integral_comp_mul_right (a := 0) (b := π / ℓ)
    (fun v => Real.cos v) ht.ne'
  rw [h, zero_mul, integral_cos, Real.sin_zero, sub_zero, smul_eq_mul, periodCosineMean,
    show π / ℓ * t = π * t / ℓ by ring]
  field_simp

/-- **Analytic core.** A nonnegative spectral density whose folded phase is uniform for `γ∘ρ` and
`cos(t ρ)`, and whose cosine moment at `t` vanishes, has `γ`-moment at least
`(m + |s|/C)` times its mass. -/
theorem gain_of_spectral_density {G : ℝ → ℝ} {ℓ t m s : ℝ} (hℓ : 0 < ℓ) (ht : 0 ≤ t)
    (hG0 : ∀ r, 0 ≤ G r) (hGi : Integrable G)
    (hGγ : Integrable fun r => G r * EF.gammaBracket r)
    (hcos : ∫ r, G r * Real.cos (r * t) = 0)
    (hfold : ∫ r, G r * EF.gammaBracket (foldedRadius ℓ r) = (∫ r, G r) * m)
    (hfc : ∫ r, G r * Real.cos (foldedRadius ℓ r * t) = (∫ r, G r) * s) :
    (m + |s| / phaseDefectConstant ℓ t) * ∫ r, G r ≤ ∫ r, G r * EF.gammaBracket r := by
  have hC := phaseDefectConstant_pos hℓ ht
  have hρc := continuous_foldedRadius ℓ
  have iγρ : Integrable fun r => G r * EF.gammaBracket (foldedRadius ℓ r) := by
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := π / ℓ)).exists_bound_of_continuousOn
      WeilHerglotz.continuous_gammaBracket.continuousOn
    exact integrable_mul_bounded hGi (WeilHerglotz.continuous_gammaBracket.comp hρc) (C := B)
      fun r => by
        rw [← Real.norm_eq_abs]
        exact hB _ ⟨foldedRadius_nonneg hℓ r, foldedRadius_le hℓ r⟩
  have icos : Integrable fun r => G r * Real.cos (r * t) :=
    integrable_mul_bounded hGi (by fun_prop) (C := 1) fun r => Real.abs_cos_le_one _
  have icosρ : Integrable fun r => G r * Real.cos (foldedRadius ℓ r * t) :=
    integrable_mul_bounded hGi (Real.continuous_cos.comp (hρc.mul continuous_const)) (C := 1)
      fun r => Real.abs_cos_le_one _
  have idiff : Integrable fun r => G r * (Real.cos (foldedRadius ℓ r * t) - Real.cos (r * t)) := by
    refine (icosρ.sub icos).congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply]; ring
  have h1 : (∫ r, G r) * s =
      ∫ r, G r * (Real.cos (foldedRadius ℓ r * t) - Real.cos (r * t)) := by
    simp_rw [mul_sub]
    rw [integral_sub icosρ icos, hcos, sub_zero, hfc]
  have h2 : |∫ r, G r * (Real.cos (foldedRadius ℓ r * t) - Real.cos (r * t))| ≤
      ∫ r, phaseDefectConstant ℓ t *
        (G r * EF.gammaBracket r - G r * EF.gammaBracket (foldedRadius ℓ r)) := by
    refine (abs_integral_le_integral_abs).trans (integral_mono idiff.abs
      ((hGγ.sub iγρ).const_mul _) fun r => ?_)
    have hp := abs_cos_sub_cos_foldedRadius_le hℓ ht r
    rw [abs_sub_comm] at hp
    rw [abs_mul, abs_of_nonneg (hG0 r)]
    calc
      _ ≤ G r * (phaseDefectConstant ℓ t *
          (EF.gammaBracket r - EF.gammaBracket (foldedRadius ℓ r))) :=
        mul_le_mul_of_nonneg_left hp (hG0 r)
      _ = _ := by ring
  have hmass : 0 ≤ ∫ r, G r := integral_nonneg fun r => hG0 r
  rw [← h1, integral_const_mul, integral_sub hGγ iγρ, hfold, abs_mul,
    abs_of_nonneg hmass] at h2
  have key : |s| * ∫ r, G r ≤ phaseDefectConstant ℓ t *
      ((∫ r, G r * EF.gammaBracket r) - (∫ r, G r) * m) := by linarith
  have e : (m + |s| / phaseDefectConstant ℓ t) * ∫ r, G r =
      m * (∫ r, G r) + (|s| * ∫ r, G r) / phaseDefectConstant ℓ t := by ring
  rw [e]
  have := (div_le_iff₀ hC).mpr (by linarith : |s| * ∫ r, G r ≤
    ((∫ r, G r * EF.gammaBracket r) - (∫ r, G r) * m) * phaseDefectConstant ℓ t)
  linarith

/-- **The incidence gain.** A nonnegative combination blind at every power of `q` and at `n` has
`A(c) ≥ (m_q + |s|/C) mass(c)` with `ℓ = log q`, `t = log n`. -/
theorem symbolPeriodMean_add_gain_mul_massOf_le {q n : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n)
    (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f) (hb : BlindOn (powerNodes q) c)
    (hn0 : nodeVector c ⟨n, hn⟩ = 0) :
    (symbolPeriodMean q + |periodCosineMean (Real.log q) (Real.log n)| /
        phaseDefectConstant (Real.log q) (Real.log n)) * massOf c ≤ nodeArchOnly c := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have ht : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hcos : ∫ r, combinationSpectralDensity c r * Real.cos (r * Real.log n) = 0 := by
    rw [integral_combinationSpectralDensity_mul_cos_log c hn, hn0, mul_zero]
  have hfold := integral_combinationSpectralDensity_mul_periodic hq hc hb
    (continuous_foldedSymbol (Real.log q)) (foldedSymbol_neg (Real.log q))
  rw [integral_foldedSymbol hℓ] at hfold
  have hPc : Continuous fun z : AddCircle (2 * π) => Real.cos (‖z‖ / Real.log q * Real.log n) :=
    Real.continuous_cos.comp ((continuous_norm.div_const _).mul continuous_const)
  have hfc := integral_combinationSpectralDensity_mul_periodic hq hc hb hPc
    (fun z => by simp only [norm_neg])
  rw [integral_haarAddCircle_norm_comp hℓ (F := fun v => Real.cos (v * Real.log n))
    (Real.continuous_cos.comp (continuous_id.mul continuous_const)),
    integral_cos_mul_eq hℓ ht] at hfc
  have h := gain_of_spectral_density hℓ ht.le (combinationSpectralDensity_nonneg hc) (integrable_combinationSpectralDensity c)
    (integrable_combinationSpectralDensity_mul_gammaBracket c) hcos hfold hfc
  rw [integral_combinationSpectralDensity, integral_combinationSpectralDensity_mul_gammaBracket]
    at h
  have hpi : 0 < 2 * π := by positivity
  rw [symbolPeriodMean]
  nlinarith

/-! ### 5. Incidence -/

/-- The circle mean `s` vanishes only at powers of `q`. -/
theorem periodCosineMean_ne_zero {q n : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) (hnq : n ∉ powerNodes q) :
    periodCosineMean (Real.log q) (Real.log n) ≠ 0 := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have ht : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  unfold periodCosineMean
  refine mul_ne_zero (by positivity) fun hsin => hnq ?_
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
  have hkq : Real.log n = k * Real.log q := by
    field_simp at hk; linarith
  have hk0 : 0 < k := by
    have : (0 : ℝ) < k * Real.log q := hkq ▸ ht
    exact_mod_cast pos_of_mul_pos_left this hℓ.le
  refine ⟨k.toNat, by omega, ?_⟩
  have hkn : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0.le
  have hlog : Real.log n = Real.log ((q ^ k.toNat : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow, hkn, hkq]
  have := Real.exp_log (show (0 : ℝ) < n by positivity)
  rw [hlog, Real.exp_log (by positivity)] at this
  exact_mod_cast this.symm

/-- The gain `η(q, n) = |s|/C`. -/
def incidenceGain (q n : ℕ) : ℝ :=
  |periodCosineMean (Real.log q) (Real.log n)| / phaseDefectConstant (Real.log q) (Real.log n)

theorem incidenceGain_pos {q n : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) (hnq : n ∉ powerNodes q) :
    0 < incidenceGain q n := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have ht : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  exact div_pos (abs_pos.mpr (periodCosineMean_ne_zero hq hn hnq))
    (phaseDefectConstant_pos hℓ ht.le)

/-- **A dependent node changes nothing.** -/
theorem blindSymbolSlackOn_insert_iff_of_mem {q n : ℕ} (hq : 2 ≤ q) (hnq : n ∈ powerNodes q)
    (M : ℝ) : BlindSymbolSlackOn (insert n (powerNodes q)) M ↔ -symbolPeriodMean q ≤ M := by
  rw [Set.insert_eq_of_mem hnq, blindSymbolSlackOn_powers_iff hq]

/-- **An independent node strictly improves the bathtub.** -/
theorem blindSymbolSlackOn_insert_of_not_mem {q n : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) :
    BlindSymbolSlackOn (insert n (powerNodes q)) (-symbolPeriodMean q - incidenceGain q n) :=
  fun c hc hb => by
    have h := symbolPeriodMean_add_gain_mul_massOf_le hq hn c hc
      (fun j hj => hb j (Set.mem_insert_of_mem _ hj)) (hb ⟨n, hn⟩ (Set.mem_insert _ _))
    rw [incidenceGain] at *
    linarith

theorem exists_lt_blindSymbolSlackOn_insert_of_not_mem {q n : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n)
    (hnq : n ∉ powerNodes q) :
    ∃ M < -symbolPeriodMean q, BlindSymbolSlackOn (insert n (powerNodes q)) M :=
  ⟨_, by linarith [incidenceGain_pos hq hn hnq], blindSymbolSlackOn_insert_of_not_mem hq hn⟩

/-- **The full grid beats the dyadic bathtub.** Blindness at every integer gives
`BlindSymbolSlack (−m₂ − η(2,3))` with `η(2,3) > 0`. -/
theorem blindSymbolSlack_two_three :
    BlindSymbolSlack (-twoPeriodMean - incidenceGain 2 3) := fun c hc hv => by
  have h := blindSymbolSlackOn_insert_of_not_mem (q := 2) (n := 3) le_rfl (by norm_num) c hc
    (fun j _ => by rw [hv]; rfl)
  rwa [symbolPeriodMean_two] at h

theorem three_not_mem_powerNodes_two : 3 ∉ powerNodes 2 := by
  rintro ⟨j, hj, h⟩
  rcases j with _ | _ | j
  · omega
  · norm_num at h
  · have : 4 ≤ 2 ^ (j + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem incidenceGain_two_three_pos : 0 < incidenceGain 2 3 :=
  incidenceGain_pos le_rfl (by norm_num) three_not_mem_powerNodes_two

/-! ### 6. The pole is invisible to slacks on gapped sets -/

theorem GappedNodeSet.insert {𝒩 : Set ℕ} (h𝒩 : GappedNodeSet 𝒩) (n : ℕ) :
    GappedNodeSet (insert n 𝒩) := by
  intro R
  obtain ⟨T, hRT, hgap⟩ := h𝒩 (max R (Real.log n + 1))
  refine ⟨T, (le_max_left _ _).trans hRT, fun m hm hm2 => ?_⟩
  rcases Set.mem_insert_iff.mp hm with rfl | hm
  · have : Real.log m + 1 ≤ T := (le_max_right _ _).trans hRT
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · exact hgap m hm hm2

/-- **Pole invisibility for slacks.** On a gapped node set the zero-pole slack is the slack. -/
theorem zeroPoleBlindSymbolSlackOn_iff_of_gapped {𝒩 : Set ℕ} (h𝒩 : GappedNodeSet 𝒩) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn 𝒩 M ↔ BlindSymbolSlackOn 𝒩 M := by
  refine ⟨fun h c hc hb => ?_, BlindSymbolSlackOn.zeroPole⟩
  by_contra hneg
  rw [not_le] at hneg
  set g : ℝ := -(nodeArchOnly c + M * massOf c) with hg
  have hgpos : 0 < g := by linarith
  set η : ℝ := g / (2 * (1 + |M|)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨d, hd, hbd, hpd, had, hmd⟩ := exists_blindOn_poleMass_eq_small h𝒩 (-nodePoleMass c) hηpos
  have hpos := h (c + d) (fun f => by rw [Finsupp.add_apply]; exact add_nonneg (hc f) (hd f))
    (fun j hj => by rw [nodeVector_add, Finsupp.add_apply, hb j hj, hbd j hj, add_zero])
    (by rw [nodePoleMass_add, hpd, add_neg_cancel])
  have hE : nodeArchEnergy (c + d) = nodeArchOnly c + nodeArchOnly d := by
    rw [← nodeArchOnly_add, nodeArchOnly, nodePoleMass_add, hpd, add_neg_cancel, sub_zero]
  rw [hE, massOf_add] at hpos
  have hmd0 : 0 ≤ massOf d := massOf_nonneg hd
  have h2 : nodeArchOnly d ≤ η := (le_abs_self _).trans had
  have h3 : M * massOf d ≤ |M| * η :=
    (mul_le_mul_of_nonneg_right (le_abs_self M) hmd0).trans
      (mul_le_mul_of_nonneg_left hmd (abs_nonneg M))
  have h4 : (1 + |M|) * η = g / 2 := by rw [hη]; field_simp
  nlinarith

/-- Both incidence statements hold verbatim for zero-pole combinations. -/
theorem zeroPoleBlindSymbolSlackOn_insert_of_not_mem {q n : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) :
    ZeroPoleBlindSymbolSlackOn (insert n (powerNodes q))
      (-symbolPeriodMean q - incidenceGain q n) :=
  (blindSymbolSlackOn_insert_of_not_mem hq hn).zeroPole

theorem zeroPoleBlindSymbolSlackOn_insert_iff {q n : ℕ} (hq : 2 ≤ q) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn (insert n (powerNodes q)) M ↔
      BlindSymbolSlackOn (insert n (powerNodes q)) M :=
  zeroPoleBlindSymbolSlackOn_iff_of_gapped ((gappedNodeSet_powers hq).insert n) M

end

end GaloisForLFunctions.BiScaleUncertainty
