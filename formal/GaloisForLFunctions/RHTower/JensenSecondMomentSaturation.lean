import Mathlib

/-!
# Jensen's bound for a log-mean is saturated under any second-moment constraint

For `m₁ > 0` and any variance `v > 0` there are two-point laws with mean `m₁` and second moment
`m₁² + v` whose log-mean is within `δ` of `log m₁`, for every `δ > 0`: put mass `1 − p` at
`a = m₁ − p d` and mass `p` at `b = m₁ + (1 − p) d`, `d = √(v / (p(1−p)))`, and let `p → 0`.
Hence `sup {E log X : E X = m₁, E X² = m₂} = log m₁` — a fourth moment (or any positive moment)
of `|ζΨ|` cannot improve the Jensen ceiling `E log|ζΨ|² ≤ log E|ζΨ|²`. Only lower-tail
information can.
-/

open Real

namespace RHTower

/-- The two-point family: exact first and second moments. -/
theorem twoPoint_moments {m₁ v p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hv : 0 ≤ v) :
    let d := Real.sqrt (v / (p * (1 - p)))
    (1 - p) * (m₁ - p * d) + p * (m₁ + (1 - p) * d) = m₁ ∧
    (1 - p) * (m₁ - p * d) ^ (2 : ℕ) + p * (m₁ + (1 - p) * d) ^ (2 : ℕ) = m₁ ^ (2 : ℕ) + v := by
  intro d
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  have hd2 : d ^ (2 : ℕ) = v / (p * (1 - p)) := Real.sq_sqrt (div_nonneg hv hpp.le)
  constructor
  · ring
  · have : (1 - p) * (m₁ - p * d) ^ (2 : ℕ) + p * (m₁ + (1 - p) * d) ^ (2 : ℕ)
        = m₁ ^ (2 : ℕ) + p * (1 - p) * d ^ (2 : ℕ) := by ring
    rw [this, hd2, mul_div_cancel₀ _ hpp.ne']

/-- Jensen: the log-mean of a two-point law is at most the log of its mean. -/
theorem twoPoint_logMean_le {a b p : ℝ} (ha : 0 < a) (hb : 0 < b) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.log a + p * Real.log b ≤ Real.log ((1 - p) * a + p * b) := by
  have hcc := (strictConcaveOn_log_Ioi).concaveOn
  have h := hcc.2 (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) (by linarith : (0 : ℝ) ≤ 1 - p) hp0
    (by ring)
  simpa [smul_eq_mul] using h

/-- `log (1 - x) ≥ -2x` for `0 ≤ x ≤ 1/2`. -/
theorem neg_two_mul_le_log_one_sub_jensenSecondMomentSaturation {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  have hy : 0 < 1 - x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hy
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀ hy]
    nlinarith
  linarith

/-- **Saturation.** For every `m₁ > 0`, `v > 0`, `δ > 0` there is a two-point law with mean `m₁`,
second moment `m₁² + v`, positive atoms, and log-mean at least `log m₁ − δ` (and at most
`log m₁` by Jensen). -/
theorem exists_twoPoint_logMean_ge {m₁ v δ : ℝ} (hm : 0 < m₁) (hv : 0 < v) (hδ : 0 < δ) :
    ∃ p a b : ℝ, 0 < p ∧ p < 1 ∧ 0 < a ∧ 0 < b ∧
      (1 - p) * a + p * b = m₁ ∧ (1 - p) * a ^ (2 : ℕ) + p * b ^ (2 : ℕ) = m₁ ^ (2 : ℕ) + v ∧
      Real.log m₁ - δ ≤ (1 - p) * Real.log a + p * Real.log b ∧
      (1 - p) * Real.log a + p * Real.log b ≤ Real.log m₁ := by
  -- choose `p` small: `p ≤ 1/2` and `2 p v ≤ (min δ 1)² m₁² / 16`
  set η : ℝ := min δ 1 with hη
  have hη0 : 0 < η := lt_min hδ one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηδ : η ≤ δ := min_le_left _ _
  set p : ℝ := min (1 / 2) (η ^ (2 : ℕ) * m₁ ^ (2 : ℕ) / (32 * v)) with hp
  have hp0 : 0 < p := lt_min (by norm_num) (by positivity)
  have hp12 : p ≤ 1 / 2 := min_le_left _ _
  have hpv : p ≤ η ^ (2 : ℕ) * m₁ ^ (2 : ℕ) / (32 * v) := min_le_right _ _
  have hp1 : p < 1 := by linarith
  have h1p : 1 / 2 ≤ 1 - p := by linarith
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  set d : ℝ := Real.sqrt (v / (p * (1 - p))) with hd
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d ^ (2 : ℕ) = v / (p * (1 - p)) := Real.sq_sqrt (div_nonneg hv.le hpp.le)
  -- the key size bound: `(p d)² = p v / (1 - p) ≤ 2 p v ≤ η² m₁² / 16`
  have hpd2 : (p * d) ^ (2 : ℕ) ≤ η ^ (2 : ℕ) * m₁ ^ (2 : ℕ) / 16 := by
    have h1 : (p * d) ^ (2 : ℕ) = p * v / (1 - p) := by
      rw [mul_pow, hd2]
      field_simp
    have h2 : p * v / (1 - p) ≤ 2 * (p * v) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_pos hp0 hv]
    have h3 : 2 * (p * v) ≤ η ^ (2 : ℕ) * m₁ ^ (2 : ℕ) / 16 := by
      have := mul_le_mul_of_nonneg_right hpv hv.le
      rw [div_mul_eq_mul_div, mul_div_assoc] at this
      have hv' : v / (32 * v) = 1 / 32 := by field_simp
      rw [hv'] at this
      linarith
    linarith
  have hpd : p * d ≤ η * m₁ / 4 := by
    have hnn : 0 ≤ η * m₁ / 4 := by positivity
    have hsq : (p * d) ^ (2 : ℕ) ≤ (η * m₁ / 4) ^ (2 : ℕ) := by
      calc (p * d) ^ (2 : ℕ) ≤ η ^ (2 : ℕ) * m₁ ^ (2 : ℕ) / 16 := hpd2
        _ = (η * m₁ / 4) ^ (2 : ℕ) := by ring
    exact (pow_le_pow_iff_left₀ (mul_nonneg hp0.le hd0) hnn two_ne_zero).mp hsq
  have hpdm : p * d ≤ m₁ / 4 := le_trans hpd (by nlinarith [hη1, hm])
  have ha : 0 < m₁ - p * d := by linarith
  have hb : 0 < m₁ + (1 - p) * d := by
    have : 0 ≤ (1 - p) * d := mul_nonneg (by linarith) hd0
    linarith
  obtain ⟨hmean, hsq⟩ := twoPoint_moments (m₁ := m₁) hp0 hp1 hv.le
  refine ⟨p, m₁ - p * d, m₁ + (1 - p) * d, hp0, hp1, ha, hb, hmean, hsq, ?_, ?_⟩
  · -- lower bound on the log-mean
    have hx0 : 0 ≤ p * d / m₁ := by positivity
    have hx1 : p * d / m₁ ≤ 1 / 2 := by
      rw [div_le_iff₀ hm]; linarith
    have hloga : Real.log (m₁ - p * d) = Real.log m₁ + Real.log (1 - p * d / m₁) := by
      rw [← Real.log_mul hm.ne' (by linarith : (1 - p * d / m₁) ≠ 0)]
      congr 1
      field_simp
    have hlog1 : -2 * (p * d / m₁) ≤ Real.log (1 - p * d / m₁) :=
      neg_two_mul_le_log_one_sub_jensenSecondMomentSaturation hx0 hx1
    have hlogb : Real.log m₁ ≤ Real.log (m₁ + (1 - p) * d) :=
      Real.log_le_log hm (by linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) hd0])
    have hkey : 2 * (p * d / m₁) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ hm]
      nlinarith [hpd, hηδ, hm]
    have h1p' : 0 ≤ 1 - p := by linarith
    calc Real.log m₁ - δ
        ≤ Real.log m₁ - 2 * (p * d / m₁) := by linarith
      _ ≤ Real.log m₁ + (1 - p) * Real.log (1 - p * d / m₁) := by
          have := mul_le_mul_of_nonneg_left hlog1 h1p'
          nlinarith [hx0, hp0]
      _ = (1 - p) * Real.log (m₁ - p * d) + p * Real.log m₁ := by
          rw [hloga]; ring
      _ ≤ (1 - p) * Real.log (m₁ - p * d) + p * Real.log (m₁ + (1 - p) * d) := by
          have := mul_le_mul_of_nonneg_left hlogb hp0.le
          linarith
  · calc (1 - p) * Real.log (m₁ - p * d) + p * Real.log (m₁ + (1 - p) * d)
        ≤ Real.log ((1 - p) * (m₁ - p * d) + p * (m₁ + (1 - p) * d)) :=
          twoPoint_logMean_le ha hb hp0.le hp1.le
      _ = Real.log m₁ := by rw [hmean]

end RHTower
