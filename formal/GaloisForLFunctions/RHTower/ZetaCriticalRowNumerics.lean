import GaloisForLFunctions.RHTower.ZetaCriticalGoodRows

/-!
# The good-row bound at the critical parameters

Fix `α₀ = 1/8`, `R = 16`, `δ = 1/20`, `B₁ = 10¹³`, `B₂ = 32 · 10¹³`, `C = 10⁶⁰`. At height `T`, with
`L = log T`, put `θ = L/8`, `c = L/16`, `τ₁ = B₁/L`, `τ₂ = B₂/L` and the rigidity scale `h = C/L`.

* `critRowBound_scaled_le`: in the variables `L g₋`, `L g₊`, the good-row bound is
  `4096/(L g₋ B₂) + (E − 1)/4 · (2B₂E/(L g₋) + 3)(B₂E + L g₊) + O(B₂³/L²) + 3072(1 + δ)/B₂`.
* `norm_critRow_le_of_countControl_critical`: count control on the grid at `ℓ = uL`,
  `9/20 ≤ u ≤ 1`, and `C/L`-rigidity give `‖Ψ_n‖ ≤ 10⁻⁴` for `|γ_n − t| ≤ τ₁`, once
  `L ≥ 10²⁵`. Here `E = e^{40B₂/C} ≤ 1 + 10⁻⁴⁰`, `L g₋ ≥ 3/2` and `L g₊ ≤ 20`. The spacing is then
  non-resonant for `θ = L/8`, since `θ g₊/2π ≤ 20/16π < 1/2`.
-/

noncomputable section

namespace RHTower

/-- The good-row bound in scaled variables. -/
theorem critRowBound_scaled_le {L B₂ E gl gu ℓ δ Gl Gu : ℝ} (hL : 0 < L) (hB₂ : 0 < B₂)
    (hE1 : 1 ≤ E) (hgl : 0 < gl) (hgu : 0 ≤ gu) (hℓ : ℓ ≤ L) (hδ : 0 ≤ δ)
    (hGl0 : 0 < Gl) (hGl : Gl ≤ L * gl) (hGu : L * gu ≤ Gu) :
    critRowBound (L / 8) (L / 16) (B₂ / L) ℓ δ E gl gu ≤
      4096 / (Gl * B₂) + (E - 1) / 4 * (2 * B₂ * E / Gl + 3) * (B₂ * E + Gu) +
        (2 * B₂ * E / Gl + 3) * ((B₂ * E + Gu) * E) ^ 2 / (4 * L ^ 2) +
        3072 * (1 + δ) / B₂ := by
  unfold critRowBound
  have e1 : 16 / ((L / 16) ^ 2 * gl * (B₂ / L)) = 4096 / (L * gl * B₂) := by
    field_simp; norm_num
  have e2 : (L / 8 + 2 * (L / 16)) * (E - 1) * (2 * (B₂ / L) * E / gl + 3) * (B₂ / L * E + gu) =
      (E - 1) / 4 * (2 * B₂ * E / (L * gl) + 3) * (B₂ * E + L * gu) := by
    field_simp; ring
  have e3 : (2 * (B₂ / L) * E / gl + 3) * ((B₂ / L * E + gu) * E) ^ 2 / 4 =
      (2 * B₂ * E / (L * gl) + 3) * ((B₂ * E + L * gu) * E) ^ 2 / (4 * L ^ 2) := by
    field_simp
  have e4 : 8 / ((L / 16) ^ 2 * (B₂ / L) ^ 2) * (3 * ((1 + δ) * (B₂ / L * ℓ / 2))) =
      3072 * (1 + δ) * (ℓ / L) / B₂ := by
    field_simp; ring
  rw [e1, e2, e3, e4]
  have hℓL : ℓ / L ≤ 1 := by rw [div_le_one hL]; exact hℓ
  have hE0 : 0 ≤ E - 1 := by linarith
  have hE0' : 0 < E := by linarith
  have hgu' : 0 ≤ L * gu := by positivity
  have h1 : 4096 / (L * gl * B₂) ≤ 4096 / (Gl * B₂) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_right hGl hB₂.le
  have h2 : 2 * B₂ * E / (L * gl) ≤ 2 * B₂ * E / Gl :=
    div_le_div_of_nonneg_left (by positivity) hGl0 hGl
  have h3 : (E - 1) / 4 * (2 * B₂ * E / (L * gl) + 3) * (B₂ * E + L * gu) ≤
      (E - 1) / 4 * (2 * B₂ * E / Gl + 3) * (B₂ * E + Gu) := by
    gcongr
  have h4 : (2 * B₂ * E / (L * gl) + 3) * ((B₂ * E + L * gu) * E) ^ 2 / (4 * L ^ 2) ≤
      (2 * B₂ * E / Gl + 3) * ((B₂ * E + Gu) * E) ^ 2 / (4 * L ^ 2) := by
    gcongr
  have h5 : 3072 * (1 + δ) * (ℓ / L) / B₂ ≤ 3072 * (1 + δ) / B₂ := by
    have : 3072 * (1 + δ) * (ℓ / L) ≤ 3072 * (1 + δ) := by
      calc 3072 * (1 + δ) * (ℓ / L) ≤ 3072 * (1 + δ) * 1 := by gcongr
        _ = 3072 * (1 + δ) := mul_one _
    gcongr
  linarith

/-- The rigidity factor `E = e^{40B₂/C}` at the critical constants. -/
theorem critE_bounds :
    1 ≤ Real.exp (40 * (32 * 10 ^ 13) / 10 ^ 60) ∧
      Real.exp (40 * (32 * 10 ^ 13) / 10 ^ 60) ≤ 1 + 1 / 10 ^ 40 := by
  have hx : (0 : ℝ) ≤ 40 * (32 * 10 ^ 13) / 10 ^ 60 := by positivity
  refine ⟨Real.one_le_exp hx, ?_⟩
  have h := Real.abs_exp_sub_one_le (x := 40 * (32 * 10 ^ 13) / 10 ^ 60)
    (by rw [abs_of_nonneg hx]; norm_num)
  rw [abs_of_nonneg hx, abs_le] at h
  have : 2 * (40 * (32 * 10 ^ 13) / 10 ^ 60 : ℝ) ≤ 1 / 10 ^ 40 := by norm_num
  linarith [h.2]

/-- The numerical value of the scaled good-row bound. -/
theorem critRowBound_numeric_le {L E : ℝ} (hL : 10 ^ 25 ≤ L) (hE1 : 1 ≤ E)
    (hE : E ≤ 1 + 1 / 10 ^ 40) :
    4096 / (3 / 2 * (32 * 10 ^ 13)) + (E - 1) / 4 * (2 * (32 * 10 ^ 13) * E / (3 / 2) + 3) *
        ((32 * 10 ^ 13) * E + 20) +
      (2 * (32 * 10 ^ 13) * E / (3 / 2) + 3) * (((32 * 10 ^ 13) * E + 20) * E) ^ 2 / (4 * L ^ 2) +
      3072 * (1 + 1 / 20) / (32 * 10 ^ 13) ≤ 1 / 10000 := by
  have hE2 : E ≤ 2 := by
    have : (1 : ℝ) + 1 / 10 ^ 40 ≤ 2 := by norm_num
    linarith
  have hE0 : 0 ≤ E - 1 := by linarith
  have hL2 : (10 : ℝ) ^ 50 ≤ L ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hL 2
    rw [← pow_mul] at this; exact this
  have hA : 2 * (32 * 10 ^ 13) * E / (3 / 2) + 3 ≤ (2 * (32 * 10 ^ 13) * 2 / (3 / 2) + 3 : ℝ) := by
    gcongr
  have hB : (32 * 10 ^ 13) * E + 20 ≤ ((32 * 10 ^ 13) * 2 + 20 : ℝ) := by gcongr
  have hB0 : (0 : ℝ) ≤ (32 * 10 ^ 13) * E + 20 := by positivity
  have hT2 : (E - 1) / 4 * (2 * (32 * 10 ^ 13) * E / (3 / 2) + 3) * ((32 * 10 ^ 13) * E + 20) ≤
      (1 / 10 ^ 40) / 4 * (2 * (32 * 10 ^ 13) * 2 / (3 / 2) + 3) * ((32 * 10 ^ 13) * 2 + 20) := by
    have : E - 1 ≤ 1 / 10 ^ 40 := by linarith
    gcongr
  have hT3 : (2 * (32 * 10 ^ 13) * E / (3 / 2) + 3) * (((32 * 10 ^ 13) * E + 20) * E) ^ 2 /
        (4 * L ^ 2) ≤
      (2 * (32 * 10 ^ 13) * 2 / (3 / 2) + 3) * (((32 * 10 ^ 13) * 2 + 20) * 2) ^ 2 /
        (4 * 10 ^ 50) := by
    gcongr
  have hnum : 4096 / (3 / 2 * (32 * 10 ^ 13)) +
      (1 / 10 ^ 40) / 4 * (2 * (32 * 10 ^ 13) * 2 / (3 / 2) + 3) * ((32 * 10 ^ 13) * 2 + 20) +
      (2 * (32 * 10 ^ 13) * 2 / (3 / 2) + 3) * (((32 * 10 ^ 13) * 2 + 20) * 2) ^ 2 /
        (4 * 10 ^ 50) +
      3072 * (1 + 1 / 20) / (32 * 10 ^ 13) ≤ (1 / 10000 : ℝ) := by norm_num
  linarith


/-- The window inequality `(1 + δ)τ₁²ℓ/τ₂ < (1 − δ)τ₁ℓ/2` at the critical constants. -/
theorem crit_hnum {L u : ℝ} (hL0 : 0 < L) (hu0 : 0 < u) :
    (1 + 1 / 20) * (10 ^ 13 / L) ^ 2 * (u * L) / (32 * 10 ^ 13 / L) <
      (1 - 1 / 20) * (10 ^ 13 / L * (u * L) / 2) := by
  have e1 : (1 + 1 / 20) * (10 ^ 13 / L) ^ 2 * (u * L) / (32 * 10 ^ 13 / L) =
      (1 + 1 / 20) * 10 ^ 13 * u / 32 := by field_simp
  have e2 : (1 - 1 / 20) * (10 ^ 13 / L * (u * L) / 2) = (1 - 1 / 20) * 10 ^ 13 * u / 2 := by
    field_simp
  rw [e1, e2]; nlinarith

/-- The sparse-sum denominator at the critical constants. -/
theorem crit_D5_ge {L u : ℝ} (hL0 : 0 < L) (hu1 : 9 / 20 ≤ u) :
    19 * 10 ^ 11 ≤ (1 - 1 / 20) * (10 ^ 13 / L * (u * L) / 2) -
      (1 + 1 / 20) * (10 ^ 13 / L) ^ 2 * (u * L) / (32 * 10 ^ 13 / L) - 2 := by
  have e : (1 - 1 / 20) * (10 ^ 13 / L * (u * L) / 2) -
      (1 + 1 / 20) * (10 ^ 13 / L) ^ 2 * (u * L) / (32 * 10 ^ 13 / L) - 2 =
      10 ^ 13 * u * (19 / 40 - 21 / 640) - 2 := by field_simp; ring
  rw [e]; nlinarith

/-- `L g₊ ≤ 20` at the critical constants. -/
theorem crit_Lgu_le {L u E : ℝ} (hL0 : 0 < L) (hu1 : 9 / 20 ≤ u) (hE1 : 1 ≤ E)
    (hE2 : E ≤ 101 / 100) :
    L * critGapUpper (10 ^ 13 / L) (32 * 10 ^ 13 / L) (u * L) (1 / 20) E ≤ 20 := by
  have hD := crit_D5_ge hL0 hu1
  have hD0 : (0 : ℝ) < (1 - 1 / 20) * (10 ^ 13 / L * (u * L) / 2) -
      (1 + 1 / 20) * (10 ^ 13 / L) ^ 2 * (u * L) / (32 * 10 ^ 13 / L) - 2 :=
    lt_of_lt_of_le (by norm_num) hD
  unfold critGapUpper
  rw [mul_div_assoc', div_le_iff₀ hD0]
  have e : L * (Real.pi * (10 ^ 13 / L) * E) = Real.pi * E * 10 ^ 13 := by field_simp
  rw [e]
  have hπ2 := Real.pi_lt_d2
  have : Real.pi * E ≤ 315 / 100 * (101 / 100) :=
    mul_le_mul (hπ2.le.trans (by norm_num)) hE2 (by linarith) (by norm_num)
  nlinarith

/-- `L g₋ ≥ 3/2` at the critical constants. -/
theorem crit_Lgl_ge {L u E : ℝ} (hL0 : 0 < L) (hu0 : 0 ≤ u) (hu2 : u ≤ 1) (hE1 : 1 ≤ E)
    (hE2 : E ≤ 101 / 100) :
    3 / 2 ≤ L * critGapLower (10 ^ 13 / L) (u * L) (1 / 20) E := by
  unfold critGapLower
  have eA : 10 ^ 13 / L * (u * L) = 10 ^ 13 * u := by field_simp
  rw [eA, mul_div_assoc', le_div_iff₀ (by positivity)]
  have e : L * (2 * (10 ^ 13 / L)) = 2 * 10 ^ 13 := by field_simp
  rw [e]
  have h1 : (1 + 1 / 20) * (10 ^ 13 * u) + 1 ≤ (1 + 1 / 20) * 10 ^ 13 + 1 := by nlinarith
  have h2 : E * ((1 + 1 / 20) * (10 ^ 13 * u) + 1) ≤ 101 / 100 * ((1 + 1 / 20) * 10 ^ 13 + 1) :=
    mul_le_mul hE2 h1 (by positivity) (by norm_num)
  nlinarith

/-- **Good rows at the critical parameters.** -/
theorem norm_critRow_le_critical {L t u : ℝ} {B : Finset ℕ} {n : ℕ} (hL : 10 ^ 25 ≤ L)
    (hu1 : 9 / 20 ≤ u) (hu2 : u ≤ 1)
    (ht : 13 * (32 * 10 ^ 13 / L) < t)
    (hC : ∀ j : ℤ, |j| ≤ 6 →
      CountControl (10 ^ 13 / L) (u * L) (1 / 20) (t + 2 * j * (32 * 10 ^ 13 / L)) ∧
        CountControl (32 * 10 ^ 13 / L) (u * L) (1 / 20) (t + 2 * j * (32 * 10 ^ 13 / L)))
    (hrig : ∀ k, |xiOrderedPositiveOrdinate k - t| ≤ 8 * (32 * 10 ^ 13 / L) →
      RigidAt (10 ^ 60 / L) k)
    (hB : ∀ k, |xiOrderedPositiveOrdinate k - t| ≤ 8 * (32 * 10 ^ 13 / L) → k ∈ B)
    (hn : |xiOrderedPositiveOrdinate n - t| ≤ 10 ^ 13 / L) :
    ‖critRow (L / 8) (L / 16) B n‖ ≤ 1 / 10000 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hu0 : 0 < u := by linarith
  have h40 : 40 * (32 * 10 ^ 13 / L) / (10 ^ 60 / L) = 40 * (32 * 10 ^ 13) / 10 ^ 60 := by
    field_simp
  obtain ⟨hE1, hE⟩ := critE_bounds
  rw [← h40] at hE1 hE
  have hE2 : Real.exp (40 * (32 * 10 ^ 13 / L) / (10 ^ 60 / L)) ≤ 101 / 100 := by
    have : (1 : ℝ) + 1 / 10 ^ 40 ≤ 101 / 100 := by norm_num
    linarith
  have hτ₂1 : 32 * 10 ^ 13 / L ≤ 1 := by
    rw [div_le_one hL0]; linarith
  have hLgu := crit_Lgu_le hL0 hu1 hE1 hE2
  have hπ1 := Real.pi_gt_three
  set gu := critGapUpper (10 ^ 13 / L) (32 * 10 ^ 13 / L) (u * L) (1 / 20)
    (Real.exp (40 * (32 * 10 ^ 13 / L) / (10 ^ 60 / L))) with hgu
  have hgu0 : 0 ≤ gu := by
    have := (crit_D5_ge hL0 hu1)
    rw [hgu]; unfold critGapUpper
    have h0 : (0 : ℝ) ≤ (1 - 1 / 20) * (10 ^ 13 / L * (u * L) / 2) -
      (1 + 1 / 20) * (10 ^ 13 / L) ^ 2 * (u * L) / (32 * 10 ^ 13 / L) - 2 := by linarith
    positivity
  have hgτ : gu ≤ 32 * 10 ^ 13 / L := by
    rw [le_div_iff₀ hL0]
    linarith [mul_comm L gu]
  have hθg : L / 8 * gu / (2 * Real.pi) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : L / 8 * gu = L * gu / 8 := by ring
    rw [this]; linarith
  have hcg : L / 16 * gu / (2 * Real.pi) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : L / 16 * gu = L * gu / 16 := by ring
    rw [this]; linarith
  have hgl0 : 0 < critGapLower (10 ^ 13 / L) (u * L) (1 / 20)
      (Real.exp (40 * (32 * 10 ^ 13 / L) / (10 ^ 60 / L))) := by
    unfold critGapLower; positivity
  have hrow := norm_critRow_le_of_countControl (B := B) (n := n) (by positivity : (0 : ℝ) < 10 ^ 13 / L)
    (by gcongr; norm_num) hτ₂1 (by positivity) ht (by norm_num) (by positivity)
    (crit_hnum hL0 hu0) hC hrig hB (by positivity) (by linarith : L / 16 ≤ L / 8) (by linarith)
    (lt_of_lt_of_le (by norm_num) (crit_D5_ge hL0 hu1)) hgτ hθg hcg hn
  refine hrow.trans ?_
  have hsc := critRowBound_scaled_le (L := L) (B₂ := 32 * 10 ^ 13) (ℓ := u * L)
    (δ := 1 / 20) hL0 (by norm_num) hE1 hgl0 hgu0 (by nlinarith) (by norm_num)
    (by norm_num) (crit_Lgl_ge hL0 hu0.le hu2 hE1 hE2) hLgu
  exact hsc.trans (critRowBound_numeric_le hL hE1 hE)

end RHTower
