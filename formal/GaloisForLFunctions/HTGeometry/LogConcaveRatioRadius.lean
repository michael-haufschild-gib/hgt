import Mathlib

/-!
# The ratio limit of a log-concave sequence is the reciprocal radius

Let `b_n > 0` be log-concave: `b_n b_{n+2} ≤ b_{n+1}²`.  Then the ratios `b_{n+1}/b_n` are
nonincreasing, so they converge to `L = inf_n b_{n+1}/b_n ≥ 0`.  If `Σ b_n yⁿ` converges for
`0 ≤ y < D` and diverges for every `y > D`, then `L = 1/D` (`tendsto_ratio_of_logConcave`):

* `L ≤ 1/D`: otherwise `b_n ≥ b_0 Lⁿ` makes the series diverge at some `y ∈ (1/L, D)`;
* `L ≥ 1/D`: otherwise eventually `b_{n+1}/b_n ≤ L + ε < 1/y` for some `y > D`, so the series
  converges at `y`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Log-concave positive sequences have nonincreasing ratios. -/
theorem ratio_antitone_of_logConcave {b : ℕ → ℝ} (hpos : ∀ n, 0 < b n)
    (hlc : ∀ n, b n * b (n + 2) ≤ b (n + 1) ^ 2) :
    Antitone (fun n => b (n + 1) / b n) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [div_le_div_iff₀ (hpos (n + 1)) (hpos n)]
  have := hlc n
  nlinarith [this]

/-- A nonnegative ratio lower bound gives a geometric lower bound. -/
theorem geom_le_of_ratio_ge {b : ℕ → ℝ} (hpos : ∀ n, 0 < b n) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ n, L ≤ b (n + 1) / b n) (n : ℕ) : b 0 * L ^ n ≤ b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hL n
    rw [le_div_iff₀ (hpos n)] at h
    rw [pow_succ, ← mul_assoc]
    calc b 0 * L ^ n * L ≤ b n * L := mul_le_mul_of_nonneg_right ih hL0
      _ = L * b n := mul_comm _ _
      _ ≤ b (n + 1) := h

/-- **The ratio limit is the reciprocal radius.**  For log-concave positive `b`, if `Σ b_n yⁿ`
converges on `[0, D)` and diverges beyond `D`, then `b_{n+1}/b_n → 1/D`. -/
theorem tendsto_ratio_of_logConcave {b : ℕ → ℝ} (hpos : ∀ n, 0 < b n)
    (hlc : ∀ n, b n * b (n + 2) ≤ b (n + 1) ^ 2) {D : ℝ} (hD : 0 < D)
    (hconv : ∀ y : ℝ, 0 ≤ y → y < D → Summable (fun n => b n * y ^ n))
    (hdiv : ∀ y : ℝ, D < y → ¬ Summable (fun n => b n * y ^ n)) :
    Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 (1 / D)) := by
  set r : ℕ → ℝ := fun n => b (n + 1) / b n with hr
  have hanti : Antitone r := ratio_antitone_of_logConcave hpos hlc
  have hr0 : ∀ n, 0 ≤ r n := fun n => div_nonneg (hpos (n + 1)).le (hpos n).le
  have hbdd : BddBelow (Set.range r) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hr0 n⟩
  set L := ⨅ n, r n with hLdef
  have htend : Tendsto r atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbdd
  have hLle : ∀ n, L ≤ r n := fun n => ciInf_le hbdd n
  have hL0 : 0 ≤ L := le_ciInf hr0
  -- `L ≤ 1/D`
  have h1 : L ≤ 1 / D := by
    by_contra hgt
    push Not at hgt
    have hLpos : 0 < L := lt_of_le_of_lt (by positivity) hgt
    obtain ⟨y, hy1, hy2⟩ : ∃ y, 1 / L < y ∧ y < D := by
      refine ⟨(1 / L + D) / 2, ?_, ?_⟩ <;>
        · have : 1 / L < D := by
            rw [div_lt_iff₀ hLpos]
            rw [div_lt_iff₀ hD] at hgt
            linarith
          linarith
    have hy0 : 0 < y := lt_trans (by positivity) hy1
    have hsum := hconv y hy0.le hy2
    have hLy : 1 < L * y := by
      rw [div_lt_iff₀ hLpos] at hy1
      linarith
    have hlow : ∀ n, b 0 * (L * y) ^ n ≤ b n * y ^ n := by
      intro n
      have := geom_le_of_ratio_ge hpos hL0 hLle n
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right this (pow_nonneg hy0.le n)
    have htend0 := hsum.tendsto_atTop_zero
    have hgrow : Tendsto (fun n => b 0 * (L * y) ^ n) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hLy).const_mul_atTop (hpos 0)
    have := tendsto_atTop_mono hlow hgrow
    exact not_tendsto_atTop_of_tendsto_nhds htend0 this
  -- `1/D ≤ L`
  have h2 : 1 / D ≤ L := by
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hLq, hqD⟩ : ∃ q, L < q ∧ q < 1 / D := ⟨(L + 1 / D) / 2, by linarith, by linarith⟩
    have hqpos : 0 < q := lt_of_le_of_lt hL0 hLq
    obtain ⟨y, hDy, hyq⟩ : ∃ y, D < y ∧ y < 1 / q := by
      have : D < 1 / q := by
        rw [lt_div_iff₀ hqpos]
        rw [lt_div_iff₀ hD] at hqD
        linarith
      exact ⟨(D + 1 / q) / 2, by linarith, by linarith⟩
    have hy0 : 0 < y := lt_trans hD hDy
    have hqy : q * y < 1 := by
      rw [lt_div_iff₀ hqpos] at hyq
      linarith
    apply hdiv y hDy
    -- eventually `b_{n+1} y^{n+1} ≤ (q y) b_n yⁿ`: the ratio test
    refine summable_of_ratio_test_tendsto_lt_one (l := L * y) (by nlinarith [hLq, hqy])
      (Eventually.of_forall fun n => (mul_pos (hpos n) (pow_pos hy0 n)).ne') ?_
    have : Tendsto (fun n => r n * y) atTop (𝓝 (L * y)) := htend.mul_const y
    refine this.congr fun n => ?_
    simp only [hr, norm_mul, Real.norm_eq_abs, abs_of_pos (hpos _), abs_of_pos (pow_pos hy0 _),
      pow_succ]
    field_simp [(hpos n).ne', (pow_pos hy0 n).ne']
    rw [abs_of_pos hy0]
  rw [show (1 / D) = L from le_antisymm h2 h1]
  exact htend

end

end GaloisForLFunctions.HTGeometry
