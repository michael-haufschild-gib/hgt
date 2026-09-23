import GaloisForLFunctions.RHTower.ProlateRadialEndpointFlux

/-!
# An explicit endpoint-to-Dunster matching point

The point

```text
B(c) = 1 + 9 / (8 c^(2 : ℕ))
```

lies inside the zero-free radial collar and, for `c >= 5`, already satisfies
`c * xi_s(B(c)) >= 1` uniformly for `0 <= s <= 1/2`.  Thus the singular endpoint analysis and the
interior Bessel-envelope estimates overlap at one exact, deterministic point.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Deterministic matching point between the endpoint layer and the interior Dunster region. -/
def dunsterEndpointCrossing (c : ℝ) : ℝ := 1 + 9 / (8 * c ^ (2 : ℕ))

theorem dunsterEndpointCrossing_sub_one {c : ℝ} :
    dunsterEndpointCrossing c - 1 = 9 / (8 * c ^ (2 : ℕ)) := by
  simp [dunsterEndpointCrossing]

theorem dunsterEndpointCrossing_gt_one {c : ℝ} (hc : 0 < c) :
    1 < dunsterEndpointCrossing c := by
  rw [dunsterEndpointCrossing]
  have : 0 < 9 / (8 * c ^ (2 : ℕ)) := by positivity
  linarith

/-- The matching point lies in the elementary `11/10` endpoint collar. -/
theorem dunsterEndpointCrossing_le_eleven_tenths {c : ℝ} (hc : 5 ≤ c) :
    dunsterEndpointCrossing c ≤ 11 / 10 := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hc2 : 25 ≤ c ^ (2 : ℕ) := by nlinarith
  have hden : 0 < 8 * c ^ (2 : ℕ) := by positivity
  have hdelta : 9 / (8 * c ^ (2 : ℕ)) ≤ (1 / 20 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  rw [dunsterEndpointCrossing]
  norm_num at hdelta ⊢
  linarith

/-- The matching point satisfies the quantitative zero-free collar condition exactly. -/
theorem dunsterEndpointCrossing_short {c : ℝ} (hc : 0 < c) :
    3 * c ^ (2 : ℕ) * (dunsterEndpointCrossing c - 1) < 5 := by
  rw [dunsterEndpointCrossing_sub_one]
  have hcne : c ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hc.ne'
  field_simp [hcne]
  norm_num

/-- At the matching point, the endpoint square distance is uniformly small. -/
theorem dunsterEndpointCrossing_sq_sub_one_le {c : ℝ} (hc : 5 ≤ c) :
    dunsterEndpointCrossing c ^ (2 : ℕ) - 1 ≤ 3 / 20 := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hc2 : 25 ≤ c ^ (2 : ℕ) := by nlinarith
  have hden : 0 < 8 * c ^ (2 : ℕ) := by positivity
  let d : ℝ := 9 / (8 * c ^ (2 : ℕ))
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 / 20 := by
    dsimp [d]
    rw [div_le_iff₀ hden]
    nlinarith
  have hdsq : d ^ (2 : ℕ) ≤ d / 20 := by
    have := mul_nonneg hd0 (sub_nonneg.mpr hd1)
    nlinarith
  rw [dunsterEndpointCrossing]
  change (1 + d) ^ (2 : ℕ) - 1 ≤ 3 / 20
  nlinarith

/-- The square-root endpoint coordinate has already reached `3/(2c)`. -/
theorem three_div_two_c_le_sqrt_crossing_sq_sub_one {c : ℝ} (hc : 0 < c) :
    3 / (2 * c) ≤ Real.sqrt (dunsterEndpointCrossing c ^ (2 : ℕ) - 1) := by
  have hden : 0 < 8 * c ^ (2 : ℕ) := by positivity
  let d : ℝ := 9 / (8 * c ^ (2 : ℕ))
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hcross : dunsterEndpointCrossing c = 1 + d := by rfl
  have hrad : 0 ≤ dunsterEndpointCrossing c ^ (2 : ℕ) - 1 := by
    rw [hcross]
    nlinarith
  rw [Real.le_sqrt (by positivity) hrad]
  rw [hcross]
  have hcne : c ≠ 0 := hc.ne'
  dsimp [d]
  field_simp [hcne]
  nlinarith [sq_nonneg (9 : ℝ)]

/-- The Bessel argument is at least one at the matching point, uniformly in the complete
low-separation range. -/
theorem one_le_c_mul_xiEndpointPhase_crossing {s c : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c) :
    1 ≤ c * xiEndpointPhase s (dunsterEndpointCrossing c) := by
  let B : ℝ := dunsterEndpointCrossing c
  let d : ℝ := B ^ (2 : ℕ) - 1
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 : 1 < B := dunsterEndpointCrossing_gt_one hc0
  have hd0 : 0 ≤ d := by dsimp [d]; nlinarith
  have hdsmall : d ≤ 3 / 20 := by
    dsimp [d, B]
    exact dunsterEndpointCrossing_sq_sub_one_le hc
  have hA : (7 / 10 : ℝ) ≤ Real.sqrt (1 - s) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hD : 3 / (2 * c) ≤ Real.sqrt d := by
    dsimp [d, B]
    exact three_div_two_c_le_sqrt_crossing_sq_sub_one hc0
  have hF : (39 / 40 : ℝ) ≤ 1 - d / 6 := by nlinarith
  have hA0 : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hD0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hF0 : 0 ≤ 1 - d / 6 := by linarith
  have hAD : (7 / 10 : ℝ) * (3 / (2 * c))
      ≤ Real.sqrt (1 - s) * Real.sqrt d :=
    mul_le_mul hA hD (by positivity) hA0
  have hADF : (7 / 10 : ℝ) * (3 / (2 * c)) * (39 / 40)
      ≤ Real.sqrt (1 - s) * Real.sqrt d * (1 - d / 6) :=
    mul_le_mul hAD hF (by positivity) (mul_nonneg hA0 hD0)
  have hconst : 1 ≤ c * ((7 / 10 : ℝ) * (3 / (2 * c)) * (39 / 40)) := by
    field_simp [hc0.ne']
    norm_num
  have hnumeric : 1 ≤ c * (Real.sqrt (1 - s) * Real.sqrt d * (1 - d / 6)) :=
    hconst.trans (mul_le_mul_of_nonneg_left hADF hc0.le)
  have hlog := GaloisForLFunctions.HTGeometry.sqrt_mul_one_sub_le_endpointLog hB1.le
  have hphase := sqrt_one_sub_mul_endpointLog_le_xiEndpointPhase hs0 hs1 hB1.le
  change Real.sqrt d * (1 - d / 6)
      ≤ GaloisForLFunctions.HTGeometry.endpointLog B at hlog
  have htoLog : Real.sqrt (1 - s) * Real.sqrt d * (1 - d / 6)
      ≤ Real.sqrt (1 - s) * GaloisForLFunctions.HTGeometry.endpointLog B := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog hA0
  have htoPhase : Real.sqrt (1 - s) * Real.sqrt d * (1 - d / 6)
      ≤ xiEndpointPhase s B := htoLog.trans hphase
  exact hnumeric.trans (mul_le_mul_of_nonneg_left htoPhase hc0.le)

end GaloisForLFunctions.RHTower

end
