import GaloisForLFunctions.RHTower.XiAmplitudeDecay
import GaloisForLFunctions.RHTower.ProlateDunsterComparisonBridge

/-!
# Dunster's amplitude is a half-power symbol on the whole exterior ray

The exterior estimates of the first-row layer are stated beyond the second dilation, where the
amplitude and its derivative obey `|A| ≤ 4/√x` and `|A′| ≤ 4/(x√x)`.  The endpoint layer needs the
same two facts *at* the turning point, where the Liouville–Green amplitude would blow up but the
pole-uniform one does not: `A → 1` as `x → 1⁺`.

Both are already reachable from corpus estimates.  The amplitude bound
`xiAmplitude s x ≤ √(√2)/√x` holds for every `x > 1`, so `|A| ≤ 2/√x` on the whole ray; and the
derivative is the amplitude times `μ/2 − x/(2(x²−s))`, whose two pieces are bounded near the
endpoint by `abs_phaseLogDefect_le_near` and by an elementary rational estimate.  The resulting
uniform bound `|A′| ≤ 6` on `(1,∞)` is what the endpoint variation of a Bessel-modulated amplitude
consumes.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **The half-power symbol bound on the whole exterior ray**, not only beyond the second
dilation. -/
theorem abs_xiAmplitude_le_two_div_sqrt {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    |xiAmplitude s x| ≤ 2 / Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hA : 0 < xiAmplitude s x := xiAmplitude_pos hs0 hs1 hx
  have hAle : xiAmplitude s x ≤ Real.sqrt (Real.sqrt 2) / Real.sqrt x := xiAmplitude_le hs0 hs1 hx
  rw [abs_of_pos hA]
  refine hAle.trans ?_
  gcongr
  exact sqrt_sqrt_two_le_two

/-- The amplitude is bounded by `2` on the whole ray. -/
theorem abs_xiAmplitude_le_two {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    |xiAmplitude s x| ≤ 2 := by
  have hsx : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx.le
  refine (abs_xiAmplitude_le_two_div_sqrt hs0 hs1 hx).trans ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **The amplitude derivative at the turning point.**  Both pieces of the logarithmic derivative
are bounded on the endpoint layer, so the derivative is. -/
theorem abs_xiAmplitudeDeriv_le_near {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx : 1 < x) (hx2 : x ≤ 2) : |xiAmplitudeDeriv s x| ≤ 6 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hn : (0 : ℝ) < x ^ (2 : ℕ) - s := by nlinarith [sq_nonneg (x - 1)]
  have hratio : |x / (x ^ (2 : ℕ) - s)| ≤ 4 := by
    rw [abs_of_pos (div_pos hx0 hn), div_le_iff₀ hn]
    nlinarith [sq_nonneg (x - 1)]
  have hphase := abs_phaseLogDefect_le_near hs0 hs1 hx hx2
  have hAabs : |xiAmplitude s x| ≤ 2 := abs_xiAmplitude_le_two hs0 hs1 hx
  rw [xiAmplitudeDeriv, abs_mul]
  have hhalf : x / (2 * (x ^ (2 : ℕ) - s)) = (x / (x ^ (2 : ℕ) - s)) / 2 := by
    field_simp
  have hsub := abs_sub (phaseLogDefect s x / 2) (x / (2 * (x ^ (2 : ℕ) - s)))
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hhalf,
    abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hsub
  have hsub' : |phaseLogDefect s x / 2 - x / (2 * (x ^ (2 : ℕ) - s))|
      ≤ |phaseLogDefect s x| / 2 + |x / (x ^ (2 : ℕ) - s)| / 2 := by
    rw [hhalf]
    exact hsub
  calc |xiAmplitude s x| * |phaseLogDefect s x / 2 - x / (2 * (x ^ (2 : ℕ) - s))|
      ≤ 2 * (|phaseLogDefect s x| / 2 + |x / (x ^ (2 : ℕ) - s)| / 2) :=
        mul_le_mul hAabs hsub' (abs_nonneg _) (by positivity)
    _ ≤ 6 := by linarith

/-- **The uniform derivative bound on the whole exterior ray.** -/
theorem abs_xiAmplitudeDeriv_le_six {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    |xiAmplitudeDeriv s x| ≤ 6 := by
  by_cases h : x ≤ 2
  · exact abs_xiAmplitudeDeriv_le_near hs0 hs1 hx h
  · have h2 : (2 : ℝ) < x := not_le.mp h
    refine (abs_xiAmplitudeDeriv_le hs0 hs1 h2.le).trans ?_
    have hx0 : (0 : ℝ) < x := by linarith
    have hsx : (1 : ℝ) ≤ Real.sqrt x := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    have hxx : (1 : ℝ) ≤ x * Real.sqrt x := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    linarith


end GaloisForLFunctions.RHTower

end
